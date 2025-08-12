if ! tmux has-session -t dev
then
  # create new session 'dev', first window 'editor', then detach <-- window 0
  tmux new-session -s dev -n editor -d

  # send keys to session 'dev': enter project 'project'
  # C-m: ENTER key
  mkdir -p project
  tmux send-keys -t dev 'cd ./project' C-m

  # open vi
  tmux send-keys -t dev 'vi' C-m

  # split window: up/down                                        <-- windown 0: pane 0, 1
  tmux split-window -v -t dev
  # layout
  tmux select-layout -t dev main-horizontal

  # [session]:[window].[pane]
  tmux send-keys -t dev:0.1 'cd ./project' C-m

  # create new window 'console'                                  <-- window 1
  tmux new-window -n console -t dev            
  tmux send-keys -t dev:1 'cd ./project' C-m

  # select window: index 0
  tmux select-window -t dev:0
fi

# attach to session 'dev'
tmux attach -t dev