##What is this repo?

This repo has my custom configuration for vim, bash, git as I use on my system.
The makefile template is one I use for my projects.

##Which file does what?

1. git-prompt.sh generates prompts for git completion. Taken from udacity [course] (https://www.udacity.com/course/how-to-use-git-and-github--ud775).
2. gitconfig configures some colours for the terminal. Taken form udacity [course] (https://www.udacity.com/course/how-to-use-git-and-github--ud775).
3. git-completion.bash adds some completion features for the git prompt.
4. bashrc sources the git-prompt.sh and git-completion.bash files and has some
   customization for the bash terminal.
5. vimrc, you know what it is.
6. snippets file, modified from [here] (https://github.com/honza/vim-snippets) for use with [Ultisnips plugin] (https://github.com/SirVer/ultisnips) of vim.
7. ycm_extra_conf.py sample for use with [YouCompleteMe plugin] (https://github.com/Valloric/YouCompleteMe) of vim. Keep it in root of project or your home directory for defaults.

##Using this vimrc
1. Get [Vundle] (https://github.com/VundleVim/Vundle.vim).
2. Get [rainbow parantheses] (http://www.vim.org/scripts/script.php?script_id=1561). Some other similar plugins are available.
3. Get [matchit] (http://www.vim.org/scripts/script.php?script_id=39). I use it solely for verilog. Can be left out.
4. Run PluginInstall. This should do.
5. Install YouCompleteMe as instructed. Use python2.7 to avoid some headaches.
6. Feel free to experiment.
