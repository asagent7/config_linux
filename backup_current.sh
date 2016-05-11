#!/bin/sh

if [ ! -d backup_config ]; then
	mkdir backup_config
fi

sudo cp /etc/vim/vimrc backup_config/vimrc
cp ~/.bashrc backup_config/bashrc
