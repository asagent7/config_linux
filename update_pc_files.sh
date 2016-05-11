#!/bin/sh

./backup_current.sh

sudo cp vimrc /etc/vim/vimrc
cp bashrc ~/.bashrc
cp gitconfig ~/.gitconfig
cp git-prompt.sh ~/git-prompt.sh
cp ycm_extra_conf.py ~/ycm_extra_conf.py
cp -r .vim ~/.vim
