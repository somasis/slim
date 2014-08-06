/* slimlock
 * Copyright (c) 2010-2012 Joel Burget <joelburget@gmail.com>
 * Copyright (c) 2014 Roman Kraevskiy <rkraevskiy@gmail.com>

 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 */

#include <cstdio>
#include <cstring>
#include <algorithm>
#include <sys/types.h>
#include <sys/ioctl.h>
#include <linux/vt.h>
#include <X11/keysym.h>
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/Xproto.h>
#include <X11/Xatom.h>
#include <X11/extensions/dpms.h>
#include <security/pam_appl.h>
#include <pthread.h>
#include <err.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/file.h>
#include <errno.h>
#include <sys/file.h>
#include <fcntl.h>
#include <sys/time.h>
#include <syslog.h>

#include "cfg.h"
#include "util.h"
#include "panel.h"

#undef APPNAME
#define APPNAME "slimlock"
#define SLIMLOCKCFG SYSCONFDIR"/slimlock.conf"

//#define DEBUG

#ifdef DEBUG

#define dprintf(...) syslog(LOG_DEBUG,__VA_ARGS__)
#else
#define dprintf(...)
#endif

#define numberof(x) (sizeof(x)/sizeof((x)[0]))


using namespace std;

typedef struct{
    int pipe[2];
}pipe_t;

#define PIPE_DEFINE(x) pipe_t x = {{-1,-1}}

typedef struct
{
    const char * const name;
    Atom * const atom;
} AtomItem;

static void HideCursor();
static bool AuthenticateUser();
static int ConvCallback(int num_msgs, const struct pam_message **msg,
						struct pam_response **resp, void *appdata_ptr);
static string findValidRandomTheme(const string& set);
static void HandleSignal(int sig);
static void *RaiseWindow(void *data);

// I really didn't wanna put these globals here, but it's the only way...
static Display* dpy;
static int scr;
static Window win;
static Window root;
static Cfg* cfg;
static Panel* loginPanel;
static string themeName = "";

static pam_handle_t *pam_handle;
static struct pam_conv conv = {ConvCallback, NULL};

static CARD16 dpms_standby, dpms_suspend, dpms_off, dpms_level;
static BOOL dpms_state, using_dpms;
static int term;
static char screenlock_resname[] = "x11screenlock";
static char app_name[] = APPNAME;
static int (*xerrorxlib)(Display *, XErrorEvent *);
static Time lock_time;
static bool flag_daemonize;
static volatile int was_root;
static volatile int tty_lock;
static volatile int tty_locked=false;
static pthread_mutex_t mutex;
static pthread_cond_t cond;
static volatile bool exit_raiser=false;

static Atom X_WM_LOCKTIME;
static Atom NET_WM_STATE_FULLSCREEN;
static Atom NET_WM_STATE;
static Atom NET_WM_STATE_ABOVE;
static Atom NET_WM_WINDOW_TYPE_NORMAL;
static Atom NET_WM_WINDOW_TYPE;
static Atom NET_WM_ACTION_FULLSCREEN;

static Atom X_SCREENLOCK_WINDOW;
static Atom NET_WM_ALLOWED_ACTIONS;
static PIPE_DEFINE(wait_pipe);
static PIPE_DEFINE(pipefds);


static const AtomItem atoms[] =
{
    { "_X_WM_LOCKTIME",             &X_WM_LOCKTIME},
    { "_NET_WM_STATE_FULLSCREEN",   &NET_WM_STATE_FULLSCREEN},
    { "_NET_WM_STATE",              &NET_WM_STATE},
    { "_NET_WM_STATE_ABOVE",        &NET_WM_STATE_ABOVE},
    { "_NET_WM_WINDOW_TYPE_NORMAL", &NET_WM_WINDOW_TYPE_NORMAL},
    { "_NET_WM_WINDOW_TYPE",        &NET_WM_WINDOW_TYPE},
    { "_X_SCREENLOCK_WINDOW",       &X_SCREENLOCK_WINDOW},
    { "_NET_WM_ALLOWED_ACTIONS",    &NET_WM_ALLOWED_ACTIONS},
    { "_NET_WM_ACTION_FULLSCREEN",  &NET_WM_ACTION_FULLSCREEN},
    //{ "",       &},

};

static void die(const char *errstr, ...) {
    static char buf[2*1024];
	va_list ap;

	va_start(ap, errstr);
	vsnprintf(buf,sizeof(buf), errstr, ap);
	va_end(ap);
#ifdef DEBUG
    syslog(LOG_ERR,"%s",buf);
#endif
    fprintf(stderr,"%s",buf);
	exit(EXIT_FAILURE);
}


static void print_error(const char *str){
    int err = errno;
    dprintf("error opening console '%s'",strerror(err));
    fprintf(stderr,"%s",strerror(err));
}

static Time gettime() {
	static Atom	prop = None;
	static int	data = getpid();
	static char	name[] = "_NET_WM_PID";
	XWindowAttributes wattr;
	XEvent	ev;
	int	i;

	if (XGetWindowAttributes(dpy, win, &wattr) == False) {
		dprintf("gettime: XGetWindowAttributes on window failed.");
		return CurrentTime;
	}

	if (prop==None && (prop=XInternAtom(dpy, name, False)) == None) {
		dprintf("gettime: XInternAtom of '%s' failed.", name);
		return CurrentTime;
	}

	XSelectInput(dpy, win, wattr.your_event_mask | PropertyChangeMask);

	XChangeProperty(dpy, win, prop, XA_CARDINAL, 32, PropModeReplace,
		(unsigned char *)&data, 1);
    XSync(dpy,False);
	for (i=0; i<30; i++) {
		if (XCheckWindowEvent(dpy, win, PropertyChangeMask, &ev))
			break;
        dprintf("gettime %d",i);
        usleep(100);
	}

	if (i >= 10) {
		dprintf("gettime: Didn't receive expected PropertyNotify event");
		return CurrentTime;
	}

	XSelectInput(dpy, win, wattr.your_event_mask);

	return ev.xproperty.time;
}


static int pipe_write(pipe_t* p,void *data, size_t size){
    dprintf("pipe_write %d ",p->pipe[1]);
    return write(p->pipe[1],data,size);
}

static int pipe_read(pipe_t* p,void *data,size_t size){
    dprintf("pipe_read %d ",p->pipe[0]);
    return read(p->pipe[0],data,size);
}


static void pipe_reader(pipe_t*p){
    if (p->pipe[1] != -1){
        close(p->pipe[1]);
        p->pipe[1] = -1;
    }
}

static void pipe_writer(pipe_t*p){
    if (p->pipe[0] != -1){
        close(p->pipe[0]);
        p->pipe[0] = -1;
    }
}

static int pipe_open(pipe_t*p){
    int res;

    res = pipe(p->pipe);
    dprintf("pipe_open %d:%d",p->pipe[0],p->pipe[1]);
    return res;
}


static void pipe_close(pipe_t *p){
    pipe_reader(p);
    pipe_writer(p);
}

static int xerror(Display *dpy, XErrorEvent *ee) {
    if(ee->error_code == BadWindow
            || (ee->request_code == X_SetInputFocus && ee->error_code == BadMatch)
            || (ee->request_code == X_PolyText8 && ee->error_code == BadDrawable)
            || (ee->request_code == X_PolyFillRectangle && ee->error_code == BadDrawable)
            || (ee->request_code == X_PolySegment && ee->error_code == BadDrawable)
            || (ee->request_code == X_ConfigureWindow && ee->error_code == BadMatch)
            || (ee->request_code == X_GrabButton && ee->error_code == BadAccess)
            || (ee->request_code == X_GrabKey && ee->error_code == BadAccess)
            || (ee->request_code == X_CopyArea && ee->error_code == BadDrawable))
        return 0;
    die("X FATAL error: request code=%d, error code=%d\n",
            ee->request_code, ee->error_code);
    return 1;
}

static int fork2() {
    pid_t pid;
    int status;

    pid = fork();
    if (!pid) {
        switch(fork()) {
            case 0:
                return 0;
            case -1:
                _exit(errno);
            default:
                _exit(0);
        }
    }

    if ( (pid<0) || (waitpid(pid,&status,0)<0) ) {
        return -1;
    }

    if (WIFEXITED(status)){
        if (WEXITSTATUS(status) == 0){
            return 1;
        }else{
            errno = WEXITSTATUS(status);
        }
    }else{
        errno = EINTR;
    }
    return -1;
}


static void request_lock() {
    char c = 'L';

    dprintf("request Console lock\n");
    pipe_write(&pipefds,&c,1);
}


static void request_unlock() {
    char c = 'U';

    dprintf("request Console unlock\n");
    pipe_write(&pipefds,&c,1);
}


static void request_quit() {
    char c = 'Q';

    dprintf("request Console quit\n");
    pipe_write(&pipefds,&c,1);
}


static void do_lock(){
    dprintf("Console lock\n");
    if ((ioctl(term, VT_LOCKSWITCH)) == -1){
        print_error("error locking console");
    }else{
        tty_locked = true;
    }
}

static void do_unlock(){
    dprintf("Console unlock\n");
    if ((ioctl(term, VT_UNLOCKSWITCH)) == -1) {
       print_error("error unlocking console");
    }else{
        tty_locked = false;
    }
}

static void root_rights_process(){
    int res;
    char c;
    struct sigaction sa;
    bool bexit=false;

    dprintf("root_rights_process is started\n");
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = SIG_IGN;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGQUIT,&sa,NULL);
    sigaction(SIGTERM,&sa,NULL);
    sigaction(SIGINT,&sa,NULL);
    sigaction(SIGHUP,&sa,NULL);
    sigaction(SIGPIPE,&sa,NULL);


    pipe_reader(&pipefds);

    if ((term = open("/dev/console", O_RDWR)) == -1){
        dprintf("error opening console '%s'",strerror(errno));
        print_error("error opening console");
        exit(EXIT_FAILURE);
    }
    while(!bexit){
        res = pipe_read(&pipefds,&c,1);
        if (res<=0){
            dprintf("pipe closed\n");
            bexit = true;
        }else if (res){
            switch(c){
                case 'L': // lock
                    do_lock();
                    break;
                case 'U': // unlock
                    do_unlock();
                    break;
                case 'Q': // quit
                    bexit = true;
                    break;
            }
        }
    }
    pipe_close(&pipefds);
    if (tty_locked){
        do_unlock();
    }
    close(term);
    dprintf("root_rights_process is finished");
}

static void usage() {
    fprintf(stderr,"usage: "APPNAME" [-vd]\n");
    die("program should to have ROOT setuid to run correctly\n");
}

static void* getatom(Window w, Atom atom, Atom type, unsigned long *n) {
	int format, status;
	unsigned char *p = NULL;
	unsigned long tn, extra;
	Atom real;
    
	status = XGetWindowProperty(dpy, w, atom, 0L, 0x7fffffff, false, type,
			&real, &format, &tn, &extra, (unsigned char **)&p);
    if (status != Success){
        p = NULL;
        tn = 0;
    }else{
        if (real != type){
            dprintf("atom different types %08lx %08lx",type,real);
            if (p){
                XFree(p);
            }
            p = NULL;
            tn = 0;
        }
    }

    if(n!=NULL){
        *n = tn;
    }

   	return p;
}


static bool find_running_copy()
{
    Window *w;
    Time *ts;
    unsigned long number;
    bool res = false;

    w = (Window*)getatom(root,X_SCREENLOCK_WINDOW,XA_WINDOW,&number);

    if (w){
        dprintf("X_SCREENLOCK_WINDOW %08lx\n",*w);
        if (*w != win){
            ts = (Time*)getatom(*w,X_WM_LOCKTIME,X_WM_LOCKTIME,&number);
            if (ts){
                dprintf("Found %08lx their lock_time %lu vs our %lu\n",*w,*ts,lock_time);
                res=true;
            }else{
                XFree(ts);
                dprintf("no X_WM_LOCKTIME property on window\n");
            }
        }
        XFree(w);
    }else{
        dprintf("no X_SCREENLOCK_WINDOW property on root window\n");
    }
    return res;
}

static void closeall(int fd){
    int fdlimit = sysconf(_SC_OPEN_MAX);

    while (fd < fdlimit){
        close(fd++);
    }
}


/* custom daemon function which do not call _exit by parrent */
static int daemonize(int nochdir, int noclose){
    int pid;

    pid = fork();

    if (0 != pid){
        // parent or error
        return pid;
    }
    
    if (setsid() < 0){
        return -1;
    }

    switch (fork()){
        case 0:  break;
        case -1: return -1;
        default: _exit(0);
    }

    if (!nochdir){
        chdir("/");
    }

    if (!noclose){
        closeall(0);
        open("/dev/null",O_RDWR);
        dup(0); dup(0);
    }
    return 0;
}


int main(int argc, char **argv) {
    openlog(APPNAME, LOG_PID, LOG_USER);
    was_root = !geteuid();
    if((argc == 2)){
        if (!strcmp("-v", argv[1])){
            fprintf(stderr,APPNAME"-"VERSION", © 2010-2012 Joel Burget © 2014 Roman Kraevskiy\n");
            die("program should to have ROOT setuid to run correctly!\n");
        }else if (!strcmp("-d", argv[1])){
            flag_daemonize = true;
        }else{
            usage();
        }
    }else if(argc != 1){
        usage();
    }

    struct sigaction sa;

    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = HandleSignal;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGQUIT,&sa,NULL);
    sigaction(SIGTERM,&sa,NULL);
    sigaction(SIGINT,&sa,NULL);
    sigaction(SIGHUP,&sa,NULL);
    sigaction(SIGPIPE,&sa,NULL);

    if (flag_daemonize){
        int res;
        dprintf("Daemonize!!!\n");

        if (pipe_open(&wait_pipe)){
            print_error("pipe() failed");
            exit(EXIT_FAILURE);
        }

        res = daemonize(0,1);
        if (res<0){
            print_error("daemonize error");
            exit(EXIT_FAILURE);
        }
        if (res != 0){
            // parent
            char c;
            pipe_reader(&wait_pipe);
            dprintf("parent before lock");
            pipe_read(&wait_pipe,&c,1);
            dprintf("parent lock taken");
            _exit(0);
        }

        setpgrp();
    }
    dprintf("slock is started\n");
    if (was_root){
        dprintf("has root rights\n");
        if (pipe_open(&pipefds)){
            print_error("pipe() failed");
            exit(EXIT_FAILURE);
        }

        switch(fork2()){
            case 0:
                root_rights_process();
                _exit(0);
            case -1:
                print_error("fork2");
                _exit(0);
            default:
                break;
        }
        pipe_writer(&pipefds);

        // drop root
        int uid = getuid();
        int gid = getgid();

        if (setgid(gid)){
            die("setgid error (%d) ",errno);
        }
        if (setuid(uid)){
            die("setuid error (%d) ",errno);
        }

        // check that we are not root
        if (!setuid(0)){
            die("Cannot run as ROOT!!!");
        }
    }else{
        dprintf("no root rights at start!\n");
    }

    unsigned int cfg_passwd_timeout;
    // Read user's current theme
    cfg = new Cfg;
    cfg->readConf(CFGFILE);
    cfg->readConf(SLIMLOCKCFG);
    string themebase = "";
    string themefile = "";
    string themedir = "";
    themeName = "";
    themebase = string(THEMESDIR) + "/";
    themeName = cfg->getOption("current_theme");
    string::size_type pos;
    if ((pos = themeName.find(",")) != string::npos) {
        themeName = findValidRandomTheme(themeName);
    }

    bool loaded = false;
    while (!loaded) {
        themedir =  themebase + themeName;
        themefile = themedir + THEMESFILE;
        if (!cfg->readConf(themefile)) {
            if (themeName == "default") {
                die("Failed to open default theme file '%s'\n",themefile.c_str());
            } else {
                fprintf(stderr,"Invalid theme in config '%s'\n",themeName.c_str());
                themeName = "default";
            }
        } else {
            loaded = true;
        }
    }

    const char *display = getenv("DISPLAY");
    if (!display)
        display = DISPLAY;


    /*
     * The XInitThreads() function initializes Xlib support for concurrent threads.
     * This function must be the first Xlib function a multi-threaded program calls,
     * and it must complete before any other Xlib call is made.
     */
    if (!XInitThreads()) {
        die("Xlib not thread safe\n");
    }

    xerrorxlib = XSetErrorHandler(xerror);

    if(!(dpy = XOpenDisplay(display)))
        die("cannot open display\n");
    scr = DefaultScreen(dpy);

    for(unsigned int i=0;i<numberof(atoms);i++){
        *atoms[i].atom = XInternAtom(dpy, atoms[i].name, false);
        if (None==*atoms[i].atom){
            die("fatal: could not get atom '%s'",atoms[i].name);
        }
    }

    XSetWindowAttributes wa;
    wa.override_redirect = true;
    wa.background_pixel = BlackPixel(dpy, scr);

    // Create a full screen window
    root = RootWindow(dpy, scr);
    win = XCreateWindow(dpy,
            root,
            0,
            0,
            DisplayWidth(dpy, scr),
            DisplayHeight(dpy, scr),
            0,
            DefaultDepth(dpy, scr),
            CopyFromParent,
            DefaultVisual(dpy, scr),
            CWOverrideRedirect | CWBackPixel,
            &wa);

    dprintf("My window %08lx",win);
    XClassHint *ch;

    if (!(ch = XAllocClassHint())){
        die("failed to allocate memory for class hints");
    }
    ch->res_name = screenlock_resname;
    ch->res_class = app_name;
    XSetClassHint(dpy,win,ch);
    XFree(ch);
    XStoreName(dpy,win,APPNAME);
    XSync(dpy,False);
    /*if (!gettime(&lock_time)){
        die("could not get current time");
    }*/

    XGrabServer(dpy);
    lock_time = gettime();

    XChangeProperty(dpy,win,X_WM_LOCKTIME,X_WM_LOCKTIME,32,PropModeReplace,(unsigned char*)&lock_time,1);
    XSync(dpy,False);
    if (find_running_copy()){
       XUngrabServer(dpy);
       die("already running, die...\n");
    }else{
       XChangeProperty(dpy,root,X_SCREENLOCK_WINDOW,XA_WINDOW,32,PropModeReplace,(unsigned char*)&win,1);
    }
    XUngrabServer(dpy);
    dprintf("locktime %lu\n",lock_time);

    const Atom states[] = {NET_WM_STATE_FULLSCREEN,NET_WM_STATE_ABOVE};

    XChangeProperty(dpy,win, NET_WM_STATE, XA_ATOM, 32, PropModeReplace, (unsigned char*)states, numberof(states));
    XChangeProperty(dpy,win, NET_WM_WINDOW_TYPE, XA_ATOM, 32, PropModeReplace, (unsigned char*)&NET_WM_WINDOW_TYPE_NORMAL, 1);

    XSync(dpy,False);
    dprintf("We are choosen one!\n");
    XMapWindow(dpy, win);
    for (int len = 1000; len; len--) {
        if(XGrabKeyboard(dpy, root, True, GrabModeAsync, GrabModeAsync, CurrentTime)
                == GrabSuccess)
            break;
        usleep(100);
    }
    XSelectInput(dpy, win, ExposureMask | KeyPressMask);
    // This hides the cursor if the user has that option enabled in their
    // configuration
    HideCursor();
    loginPanel = new Panel(dpy, scr, win, cfg, themedir, Panel::Mode_Lock);
    XRaiseWindow(dpy, win);

    int ret = pam_start(APPNAME, loginPanel->GetName().c_str(), &conv, &pam_handle);
    // If we can't start PAM, just exit because slimlock won't work right
    if (ret != PAM_SUCCESS)
        die("PAM: %s\n", pam_strerror(pam_handle, ret));

    // disable tty switching
    tty_lock = (cfg->getOption("tty_lock") == "1");
    if(tty_lock) {
        if (!was_root){
            dprintf("tty_lock==1 and no root rights => stop process with root rights\n");
            request_quit();
            fprintf(stderr,"program should be ROOT setuid to run correctly!\n");
        }else{
            request_lock();
        }
    }else{
        if (was_root){
            dprintf("root rights are not needed (tty_lock!=1) => stop process with root rights\n");
            request_quit();
        }
    }

    // Set up DPMS
    unsigned int cfg_dpms_standby, cfg_dpms_off;
    cfg_dpms_standby = Cfg::string2int(cfg->getOption("dpms_standby_timeout").c_str());
    cfg_dpms_off = Cfg::string2int(cfg->getOption("dpms_off_timeout").c_str());
    using_dpms = DPMSCapable(dpy) && (cfg_dpms_standby > 0);
    if (using_dpms) {

        // restore DPMS settings should slimlock be killed in the line of duty
        DPMSGetTimeouts(dpy, &dpms_standby, &dpms_suspend, &dpms_off);

        DPMSSetTimeouts(dpy, cfg_dpms_standby,
                cfg_dpms_standby, cfg_dpms_off);

        DPMSInfo(dpy, &dpms_level, &dpms_state);
        if (!dpms_state)
            DPMSEnable(dpy);
    }

    // Get password timeout
    cfg_passwd_timeout = Cfg::string2int(cfg->getOption("wrong_passwd_timeout").c_str());
    // Let's just make sure it has a sane value
    cfg_passwd_timeout = cfg_passwd_timeout > 60 ? 60 : cfg_passwd_timeout;


    pthread_condattr_t condattr;
    pthread_condattr_init(&condattr);
    pthread_condattr_setclock(&condattr, CLOCK_MONOTONIC);

    pthread_cond_init(&cond, &condattr);
    pthread_mutex_init(&mutex, 0);

    pthread_t raise_thread;
    pthread_create(&raise_thread, NULL, RaiseWindow, NULL);


    // Main loop
    if (flag_daemonize){
        char c = ' ';
        // children
        dprintf("child before lock");
        pipe_writer(&wait_pipe);
        pipe_write(&wait_pipe,&c,1);
        dprintf("child after lock");
    }

    while (true)
    {
        loginPanel->ResetPasswd();

        // AuthenticateUser returns true if authenticated
        if (AuthenticateUser()){
            dprintf("authenticated!\n");
            break;
        }
        dprintf("wrong password!\n");
        loginPanel->WrongPassword(cfg_passwd_timeout);
    }

    // Get DPMS stuff back to normal
    if (using_dpms) {
        DPMSSetTimeouts(dpy, dpms_standby, dpms_suspend, dpms_off);
        // turn off DPMS if it was off when we entered
        if (!dpms_state)
            DPMSDisable(dpy);
    }

    if(tty_lock) {
        if (was_root){
            request_unlock();
        }
    }

    request_quit();

    dprintf("stop raiser thread...\n");
    // kill thread before destroying the window that it's supposed to be raising
    pthread_mutex_lock(&mutex);
    exit_raiser = true;
    pthread_cond_signal(&cond);
    pthread_mutex_unlock(&mutex);
    dprintf("wait for raiser thread...\n");
    pthread_join(raise_thread,NULL);
    dprintf("raiser thread is finished\n");

    loginPanel->ClosePanel();
    delete loginPanel;


    XCloseDisplay(dpy);

    dprintf("all finished!\n");
    return 0;
}

static void HideCursor()
{
	if (cfg->getOption("hidecursor") == "true") {
		XColor black;
		char cursordata[1];
		Pixmap cursorpixmap;
		Cursor cursor;
		cursordata[0] = 0;
		cursorpixmap = XCreateBitmapFromData(dpy, win, cursordata, 1, 1);
		black.red = 0;
		black.green = 0;
		black.blue = 0;
		cursor = XCreatePixmapCursor(dpy, cursorpixmap, cursorpixmap,
									 &black, &black, 0, 0);
		XFreePixmap(dpy, cursorpixmap);
		XDefineCursor(dpy, win, cursor);
	}
}

static int ConvCallback(int num_msgs, const struct pam_message **msg,
						struct pam_response **resp, void *appdata_ptr)
{
	loginPanel->EventHandler(Panel::Get_Passwd);

	// PAM expects an array of responses, one for each message
	if (num_msgs == 0 ||
		(*resp = (pam_response*) calloc(num_msgs, sizeof(struct pam_message))) == NULL)
		return PAM_BUF_ERR;

	for (int i = 0; i < num_msgs; i++) {
		if (msg[i]->msg_style != PAM_PROMPT_ECHO_OFF &&
			msg[i]->msg_style != PAM_PROMPT_ECHO_ON)
			continue;

		// return code is currently not used but should be set to zero
		resp[i]->resp_retcode = 0;
		if ((resp[i]->resp = strdup(loginPanel->GetPasswd().c_str())) == NULL) {
			free(*resp);
			return PAM_BUF_ERR;
		}
	}

	return PAM_SUCCESS;
}

static bool AuthenticateUser()
{
	return(pam_authenticate(pam_handle, 0) == PAM_SUCCESS);
}

static string findValidRandomTheme(const string& set)
{
	// extract random theme from theme set; return empty string on error
	string name = set;
	struct stat buf;

	if (name[name.length() - 1] == ',') {
		name.erase(name.length() - 1);
	}

	Util::srandom(Util::makeseed());

	vector<string> themes;
	string themefile;
	Cfg::split(themes, name, ',');
	do {
		int sel = Util::random() % themes.size();

		name = Cfg::Trim(themes[sel]);
		themefile = string(THEMESDIR) +"/" + name + THEMESFILE;
		if (stat(themefile.c_str(), &buf) != 0) {
			themes.erase(find(themes.begin(), themes.end(), name));
			cerr << APPNAME << ": Invalid theme in config: "
				 << name << endl;
			name = "";
		}
	} while (name == "" && themes.size());
	return name;
}

static void HandleSignal(int sig)
{
    dprintf("Got signal %d\n",sig);
    if ((SIGQUIT == sig) || (SIGTERM == sig) || (SIGINT == sig)){
        // Get DPMS stuff back to normal
        if (using_dpms) {
            DPMSSetTimeouts(dpy, dpms_standby, dpms_suspend, dpms_off);
            // turn off DPMS if it was off when we entered
            if (!dpms_state)
                DPMSDisable(dpy);
        }
        exit_raiser = true;
        if (tty_lock){
            request_unlock();
        }
        die("Caught signal; dying\n");
    }
}

static void* RaiseWindow(void *data) {
    struct timespec timeout;
    int res = 0;

    dprintf("raiser thread is started!\n");
    while (!exit_raiser){
        dprintf("raise!\n");
        XRaiseWindow(dpy, win);
        clock_gettime(CLOCK_MONOTONIC,&timeout);
        dprintf("%lu.%lu current time\n",timeout.tv_sec,timeout.tv_nsec);
        timeout.tv_sec+=1;      // 1 sec
        dprintf("%lu.%lu wakeup time\n",timeout.tv_sec,timeout.tv_nsec);
        res = 0;
        pthread_mutex_lock(&mutex);
        while(!exit_raiser && (res==0)){
            res = pthread_cond_timedwait(&cond, &mutex, &timeout);
        }
        pthread_mutex_unlock(&mutex);
    }
    dprintf("raiser thread exit\n");
    return (void *)0;
}

