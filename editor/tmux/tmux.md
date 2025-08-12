# tmux
* https://github.com/tmux/tmux

> tmux is a terminal multiplexer: it enables a number of terminals to be created, accessed, and controlled from a single screen. tmux may be detached from a screen and continue running in the background, then later reattached.
>
>This release runs on OpenBSD, FreeBSD, NetBSD, Linux, macOS and Solaris.

Tutorial:
* [Tmux 使用教程](https://www.ruanyifeng.com/blog/2019/10/tmux.html) 2019-10
* https://www.redhat.com/en/blog/introduction-tmux-linux
* https://www.ruanyifeng.com/blog/2019/10/tmux.html

books:
* [tmux 3: Productive Mouse-Free Development](https://tmuxbook.com/)

cheatsheet:
* https://tmuxcheatsheet.com/

# Terminology
- session: 会话
- window: 窗口
- pane: 窗格
- attach/detach: 加入/脱离

# Usage

## Installation
- Git Bash
	- msys2-x86_64-20250622.exe
	- Git-2.50.1-64-bit.exe
```shell
$ pacman -S tmux

# copy D:\software\msys64\usr\bin to C:\Program Files\Git\usr\bin
tmux.exe
msys-event-2-1-7 1.dll
msys-event_core-2-1-7 1.dll
msys-event_extra-2-1-7 1.dll
msys-event_openssl-2-1-7 1.dll
msys-event_pthreads-2-1-7 1.dll

$ tmux -V
tmux 3.5a
```

## Session, Window, Pane
session:
```shell
# 创建会话
tmux new-session -s <session name>
tmux new -s <session name>
tmux new -s <session name> -d       # detached session

# 查看会话
tmux list-sessions
tmux ls

# 加入会话
tmux attach                       # 加入唯一的会话
tmux attach -t <session name>

# 结束会话
tmux kill-session -t <session name>
```
window:
```shell
tmux new -s <session name> -n <first window name>

# 创建新窗口
PREFIX c

# 重命名窗口
PREFIX ,

# 窗口间移动
PREFIX n              # 下一个窗口
PREFIX p              # 前一个窗口
PREFIX <window index> # 窗口n  

PREFIX w              # 显示窗口列表的菜单
PREFIX f              # 搜索包含文本的窗口

PREFIX &              # 关闭当前窗口: 有确认
exit
```
pane:
```shell
PREFIX %              # 左右划分窗口
PREFIX \"              # 上下划分窗口

# 窗格间移动
PREFIX o
PREFIX ↑
PREFIX ↓ 
PREFIX ←
PREFIX →

# 窗格布局
PREFIX Space

# 关闭窗格
PREFIX x
```

自定义模式
```shell
PREFIX : customize-mode
# 或者
PREFIX C
```

## Commands

```shell
# 进入命令模式
PREFIX :

new-window -n <window name>             # 创建窗口
new-window -n <window name> "<command>" # 创建窗口, 并指定窗口的初始执行命令
```




## Configuration

配置文件查看顺序
- `/etc/tmux.conf`
- `~/.config/tmux/tmux.conf`
- `~/.tmux.conf`

reload:
```shell
PREFIX : source-file ~/.tmux.conf
```

设置命令
```shell
set
bind
unbind
```
- 自定义键, 命令, 用户输入
- 修改TMUX可视部分
- 修改状态行内容: left panel, window list, right panel


###.1 Options

```shell
$ tmux show-options -g
```

## Text, Buffers
Copy Mode:
```shell
PREFIX [

set -w -g mode-keys vi

# left, down, up, right 
h,i,j,k
# word
w, b
# character
f, F
# page
Ctrl+b
Ctrl+f
# top, bottom
g
G

# search
?   # upward
/   # backward
n   # next match
N   # previous match
```

copy and paste text: in Copy Mode
```shell
# cursor at text beginning
SPACE
# move cursor
ENTER # copy to paste buffer

# paste
PREFIX ]
```

pane content
```shell
PREFIX : capture-pane # copy pane's visible content to paste buffer
```

show/save paste buffer
```shell
PREFIX : show-buffer
# or in tmux session
tmux show-buffer

save-buffer

# capture pane and save to buffer.txt
PREFIX : capture-pane ; save-buffer buffer.txt

```

paste buffer stack: shared across all running sessions
```shell
# list buffers
PREFIX : list-buffers
tmux list-buffers

# choose buffer
PREFIX : choose-buffer
tmux choose-buffer
ENTER # to select, insert to selected pane

# paste a specific buffer
PREFIX : paste-buffer -b <buffer name>

# rename buffer
PREFIX : set-buffer -b <buffer name> -n <buffer new name>

# load text to buffer
PREFIX : load-buffer -b <buffer name> <file name>
```

remapping copy/paste to vim
```shell
bind Escape copy-mode
bind -T copy-mode-vi v send -X begin-selection # v: start visual mode to select text
bind -T copy-mode-vi y send -X copy-selection  # y: yank text into buffer
unbind p
bind p paste-buffer                            # p: paste
```

## Workflow
### Panes and Windows
```shell
# turn pane into window
PREFIX !

# turn window into pane
# move a windwo into a pane in the current window
PREFIX : join-pane -s <session name>:[<window index>]
# move pane around
PREFXI : join-pane -s <source session name>:[<source window index>].<source pane index> -t <target session name>:[<target window index>].<target pane index>
```

```shell
# maximize and restore panes
PREFIX z
# or
PREFIX : resize-pane # witn -Z option
```

execute commands when launch a window or pane
```shell
new-session "<command>"
split-window "<command>"

# example: PREFIX R to open Node.js
bind-key R run "(tmux split-window -v node)"
```

open a pane in the current directory
```shell
# same directory as the current pane or window
PREFIX : split-window -v -c "${pane_current_path}"
```

issue command in many panes simultaneously
```shell
PREFIX : set-option synchronize-panes on
PREFIX : set-option synchronize-panes off

# Shortcut for synchronize-panes toggle
bind C-s set-window-option synchronize-panes
```

popup window
```shell
# -E: ensure popup close when command exit
# otherwise: press ESC
PREFIX : display-pop -E "<command>"

# more options
display pop -d "~/" \               # starting directory
	-x C -y C -w 50% -h 50% \       # on-screen position and dimensions
	-e "POPUP=true" -E "bash"       # environment options
```

### Sessions
move between sessions
```shell
PREFIX (  # move to previous session
PREFIX )  # move to next session
PREFIX s  # select session to move
```

move window between sessions
```shell
PREFIX : move-window <target session>

# on window to move
PREFIX . 
# then input <target session name>

tmux move-window -s <source session name>:[source window index] -t <target session name>
```

create new session without leaving tmux
```shell
PREFIX : new-session -s <new session name> -c <directory name>
```

create or attach to a session
```shell
tmux has-session

# -A
tmux new-session -A -s dev
```
### OS
- use another shell
- launch tmux by default: `TMUX_PANE` environment variable
- os specific configuration: `if-shell` command
- `pipe-pane` command: capture output of a session to a log
- add battery life to status line
- integrate with Vim: `vim-tmux-navigator` plugin for Vim
### Customize workflow
- access shortcuts throug popup menu: `display-menu` command
- hook into tmux events: `set-hook`
- extend tmux with plugins: tpm

# Key Bindings

command prefix `PREFIX`: default `Ctrl-b`

| Command           | Description                                                |                        |
| :---------------- | ---------------------------------------------------------- | ---------------------- |
| `PREFIX Space `   | Select next layout                                         | 选择下一个窗格布局     |
| `PREFIX !     `   | Break pane to a new window                                 |                        |
| `PREFIX "     `   | Split window vertically                                    | 上下划分窗口           |
| `PREFIX #     `   | List all paste buffers                                     |                        |
| `PREFIX $     `   | Rename current session                                     | 重命名当前会话         |
| `PREFIX %     `   | Split window horizontally                                  | 左右划分窗口           |
| `PREFIX &     `   | Kill current window                                        |                        |
| `PREFIX '     `   | Prompt for window index to select                          |                        |
| `PREFIX (     `   | Switch to previous client                                  |                        |
| `PREFIX )     `   | Switch to next client                                      |                        |
| `PREFIX ,     `   | Rename current window                                      | 重命名当前窗口         |
| `PREFIX .     `   | Move the current window                                    |                        |
| `PREFIX /     `   | Describe key binding                                       |                        |
| `PREFIX 0     `   | Select window 0                                            |                        |
| `PREFIX 1     `   | Select window 1                                            |                        |
| `PREFIX 2     `   | Select window 2                                            |                        |
| `PREFIX 3     `   | Select window 3                                            |                        |
| `PREFIX 4     `   | Select window 4                                            |                        |
| `PREFIX 5     `   | Select window 5                                            |                        |
| `PREFIX 6     `   | Select window 6                                            |                        |
| `PREFIX 7     `   | Select window 7                                            |                        |
| `PREFIX 8     `   | Select window 8                                            |                        |
| `PREFIX 9     `   | Select window 9                                            |                        |
| `PREFIX :     `   | Prompt for a command                                       | 进入命令模式           |
| `PREFIX ;     `   | Move to the previously active pane                         |                        |
| `PREFIX =     `   | Choose a paste buffer from a list                          |                        |
| `PREFIX ?     `   | List key bindings                                          | 查看键绑定             |
| `PREFIX C     `   | Customize options                                          |                        |
| `PREFIX D     `   | Choose and detach a client from a list                     |                        |
| `PREFIX E     `   | Spread panes out evenly                                    |                        |
| `PREFIX M     `   | Clear the marked pane                                      |                        |
| `PREFIX [     `   | Enter copy mode                                            |                        |
| `PREFIX ]     `   | Paste the most recent paste buffer                         |                        |
| `PREFIX c     `   | Create a new window                                        | 创建新窗口             |
| `PREFIX d     `   | Detach the current client                                  | 脱离会话               |
| `PREFIX f     `   | Search for a pane                                          |                        |
| `PREFIX i     `   | Display window information                                 |                        |
| `PREFIX m     `   | Toggle the marked pane                                     |                        |
| `PREFIX n     `   | Select the next window                                     | 选择下一个窗口         |
| `PREFIX o     `   | Select the next pane                                       | 选择下一个窗格         |
| `PREFIX p     `   | Select the previous window                                 | 选择前一个窗口         |
| `PREFIX q     `   | Display pane numbers                                       |                        |
| `PREFIX r     `   | Redraw the current client                                  |                        |
| `PREFIX s     `   | Choose a session from a list                               | 从列表中选择会话       |
| `PREFIX t     `   | Show a clock                                               | 显示时钟               |
| `PREFIX w     `   | Choose a window from a list                                | 从列表中选择窗口       |
| `PREFIX x     `   | Kill the active pane                                       | 关闭活跃窗格           |
| `PREFIX z     `   | Zoom the active pane                                       |                        |
| `PREFIX {     `   | Swap the active pane with the pane above                   |                        |
| `PREFIX }     `   | Swap the active pane with the pane below                   |                        |
| `PREFIX ~     `   | Show messages                                              |                        |
| `PREFIX DC    `   | Reset so the visible part of the window follows the cursor |                        |
| `PREFIX PPage `   | Enter copy mode and scroll up                              |                        |
| `PREFIX Up    ` ↑ | Select the pane above the active pane                      | 选择活跃窗格上面的窗格 |
| `PREFIX Down  ` ↓ | Select the pane below the active pane                      | 选择活跃窗格下面的窗格 |
| `PREFIX Left  `←  | Select the pane to the left of the active pane             | 选择活跃窗格左边的窗格 |
| `PREFIX Right ` → | Select the pane to the right of the active pane            | 选择活跃窗格右边的窗格 |
| `PREFIX M-1   `   | Set the even-horizontal layout                             |                        |
| `PREFIX M-2   `   | Set the even-vertical layout                               |                        |
| `PREFIX M-3   `   | Set the main-horizontal layout                             |                        |
| `PREFIX M-4   `   | Set the main-vertical layout                               |                        |
| `PREFIX M-5   `   | Select the tiled layout                                    |                        |
| `PREFIX M-6   `   | Set the main-horizontal-mirrored layout                    |                        |
| `PREFIX M-7   `   | Set the main-vertical-mirrored layout                      |                        |
| `PREFIX M-n   `   | Select the next window with an alert                       |                        |
| `PREFIX M-o   `   | Rotate through the panes in reverse                        |                        |
| `PREFIX M-p   `   | Select the previous window with an alert                   |                        |
| `PREFIX M-Up  `   | Resize the pane up by 5                                    |                        |
| `PREFIX M-Down`   | Resize the pane down by 5                                  |                        |
| `PREFIX M-Left`   | Resize the pane left by 5                                  |                        |
| `PREFIX M-Right`  | Resize the pane right by 5                                 |                        |
| `PREFIX C-o   `   | Rotate through the panes                                   |                        |
| `PREFIX C-z   `   | Suspend the current client                                 |                        |
| `PREFIX C-Up  `   | Resize the pane up                                         |                        |
| `PREFIX C-Down`   | Resize the pane down                                       |                        |
| `PREFIX C-Left`   | Resize the pane left                                       |                        |
| `PREFIX C-Right`  | Resize the pane right                                      |                        |
| `PREFIX S-Up  `   | Move the visible part of the window up                     |                        |
| `PREFIX S-Down`   | Move the visible part of the window down                   |                        |
| `PREFIX S-Left`   | Move the visible part of the window left                   |                        |
| `PREFIX S-Right`  | Move the visible part of the window right                  |                        |

# FAQ
- `tmux ls` blocked: kill the process

# See Also
- [tmuxinator](https://github.com/tmuxinator/tmuxinator): Create and manage tmux sessions easily. - Ruby
- [tpm](https://github.com/tmux-plugins/tpm): Tmux Plugin Manager
	- https://github.com/tmux-plugins
	- ex: https://github.com/tmux-plugins/tmux-resurrect
		- Persists tmux environment across system restarts.
	- ex: https://github.com/tmux-plugins/tmux-open
		- Tmux key bindings for quick opening of a highlighted file or url
- [Upterm](https://upterm.dev/): Upterm is an open-source tool enabling developers to share terminal sessions securely over the web. It’s perfect for remote pair programming, accessing computers behind NATs/firewalls, remote debugging, and more.