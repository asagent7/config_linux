" All system-wide defaults are set in $VIMRUNTIME/debian.vim and sourced by
" the call to :runtime you can find below.  If you wish to change any of those
" settings, you should do it in this file (/etc/vim/vimrc), since debian.vim
" will be overwritten everytime an upgrade of the vim packages is performed.
" It is recommended to make changes after sourcing debian.vim since it alters
" the value of the 'compatible' option.

" This line should not be removed as it ensures that various options are
" properly set to work with the Vim-related packages available in Debian.
runtime! debian.vim

" Uncomment the next line to make Vim more Vi-compatible
" NOTE: debian.vim sets 'nocompatible'.  Setting 'compatible' changes numerous
" options, so any other options should be set AFTER setting 'compatible'.
"set compatible

" Vim5 and later versions support syntax highlighting. Uncommenting the next

" If using a dark background within the editing area and syntax highlighting
" turn on this option as well
set background=dark
" Uncomment the following to have Vim jump to the last position when
" reopening a file
"if has("autocmd")
"  au BufReadPost * if line("'\"") > 1 && line("'\"") <= line("$") | exe "normal! g'\"" | endif
"endif
""vundle {
""{1
" " needed to run vundle (but i want this anyways)
set nocompatible

" " vundle needs filtype plugins off
" " i turn it on later
 filetype plugin indent off
 syntax off

" " set the runtime path for vundle
 set rtp+=~/.vim/bundle/Vundle.vim
 set rtp+=~/.vim/bundle/vim-snippets
" " start vundle environment
 call vundle#begin()

" " list of plugins {
"" {2
" " let Vundle manage Vundle (this is required)
 Plugin 'VundleVim/Vundle.vim'
 Plugin 'Valloric/YouCompleteMe'
 Plugin 'airblade/vim-gitgutter'
 Plugin 'ervandew/supertab'
 Plugin 'SirVer/ultisnips'
 Plugin 'honza/vim-snippets'
 Plugin 'vim-airline/vim-airline'
 Plugin 'vim-airline/vim-airline-themes'
 Plugin 'tpope/vim-fugitive'
 Plugin 'ntpeters/vim-better-whitespace'
 Plugin 'Shougo/vimproc.vim'
 Plugin 'Shougo/unite.vim'
"
" " to install a plugin add it here and run :PluginInstall.
" " to update the plugins run :PluginInstall! or :PluginUpdate
" " to delete a plugin remove it here and run :PluginClean
" "
" " YOUR LIST OF PLUGINS GOES HERE LIKE THIS:
"
" " add plugins before this
call vundle#end()
"
" " now (after vundle finished) it is save to turn filetype plugins on
 filetype plugin indent on
 syntax on

"Using the molokai colorscheme
colorscheme jellybeans
""let g:molokai_original=1

"Set global configure file for YouCompleteMe
let g:ycm_global_ycm_extra_conf = '~/.ycm_extra_conf.py'
let g:ycm_confirm_extra_conf=0
let g:ycm_add_preview_to_completeopt=1
let g:ycm_autoclose_preview_window_after_completion=1
let g:ycm_autoclose_preview_window_after_insertion=1

""make YCM compatible with UltiSnips (using supertab)
let g:ycm_key_list_select_completion = ['<C-n>', '<Down>']
let g:ycm_key_list_previous_completion = ['<C-p>', '<Up>']
let g:SuperTabDefaultCompletionType = '<C-n>'

" " better key bindings for UltiSnipsExpandTrigger
let g:UltiSnipsExpandTrigger = "<tab>"
let g:UltiSnipsJumpForwardTrigger = "<tab>"
let g:UltiSnipsJumpBackwardTrigger = "<s-tab>"
""let g:UltiSnipsExpandTrigger="<C-s>"
""let g:UltiSnipsJumpForwardTrigger="<C-b>"
""let g:UltiSnipsJumpBackwardTrigger="<C-z>"
"
" }}
" }"
" Uncomment the following to have Vim load indentation rules and plugins
" according to the detected filetype.

" The following are commented out as they cause vim to behave a lot
" differently from regular Vi. They are highly recommended though.
set t_Co=256        " Set 256 colors.
set showcmd 		" Show (partial) command in status line.
set showmatch		" Show matching brackets.
set ignorecase		" Do case insensitive matching
set smartcase		" Do smart case matching
set incsearch		" Incremental search
set hlsearch
set autowrite		" Automatically save before commands like :next and :make
set hidden		    " Hide buffers when they are abandoned
set mouse=a		    " Enable mouse usage (all modes)
set number
set showmode
set autoindent
set smartindent
set cindent
set tabstop=4
set shiftwidth=4    " Using shiftwidth 4 for indentation
set expandtab       " Using softtab
set nobackup        " No backup to be generated
set noswapfile
set undolevels=1000
set cursorline      " Highlight the current line
set nowrap
set textwidth=79    " Max text width is 79 and colorcolumn to check so
set formatoptions=qrn1
set laststatus=2
""set statusline=%<%F%h%m%r\ [%{&ff}]\ (%{strftime(\"%H:%M\ %d/%m/%Y\",getftime(expand(\"%:p\")))})%=%l,%c%V\ %P

try
        set colorcolumn=80
    catch
endtry
" Colorcolumn color to match the colorscheme
highlight ColorColumn ctermbg=100

" Save file on no focus
au FocusLost * :wa

" Automatic enable rainbow parantheses
au VimEnter * RainbowParenthesesToggle
au Syntax * RainbowParenthesesLoadRound
au Syntax * RainbowParenthesesLoadSquare
au Syntax * RainbowParenthesesLoadBraces

" Enable NERDTree on enter and shift focus to file
"autocmd vimenter * NERDTree | wincmd p

" Open NERDTree in empty file
"autocmd StdinReadPre * let s:std_in=1

" Close NERDTree automatically
"autocmd VimEnter * if argc() == 0 && !exists("s:std_in") | NERDTree | endif
"autocmd bufenter * if (winnr("$") == 1 && exists("b:NERDTree") && b:NERDTree.isTabTree()) | q | endif

" Map commands to move between split windows
map <C-h> <C-w>h
map <C-j> <C-w>j
map <C-k> <C-w>k
map <C-l> <C-w>l
nnoremap <C-Left> :tabprevious<CR>
nnoremap <C-Right> :tabnext<CR>

if !exists('g:airline_symbols')
      let g:airline_symbols = {}
endif
let g:airline_symbols.space = "\ua0"

let g:airline#extensions#hunks#enabled=1
let g:airline#extensions#branch#enabled=1
let g:airline#extensions#tabline#show_tabs = 1
let g:airline#extensions#tabline#buffer_min_count = 0
let g:airline_section_y = '%{strftime("%c")}'
let g:airline_left_sep = ''
let g:airline_right_sep = ''

let g:unite_source_history_yank_enable = 1
try
  let g:unite_source_rec_async_command='ag --nocolor --nogroup -g ""'
  call unite#filters#matcher_default#use(['matcher_fuzzy'])
catch
endtry
" search a file in the filetree
nnoremap <space>r :<C-u>Unite -start-insert file/async<cr>
nnoremap <space>f :<C-u>Unite -start-insert file<cr>
" reset not it is <C-l> normally
:nnoremap <space><space> <Plug>(unite_restart)


set backspace=indent,eol,start
set dictionary=/usr/share/dict/words
inoremap ( ()<Esc>i
inoremap [ []<Esc>i
inoremap < <><Esc>i
inoremap { {<CR>}<Esc>O
inoremap ' ''<Esc>i
inoremap " ""<Esc>i
filetype plugin on
""set omnifunc=syntaxcomplete#Complete
" Changing behaviour of ENTER when popup menu is on
:inoremap <expr> <CR> pumvisible() ? "\<C-y>" : "\<C-g>u\<CR>"

source ~/.vim/plugin/matchit.vim
" Configuring matchit for verilog syntax
if exists('loaded_matchit')
    let b:match_ignorecase=0
	let b:match_words=
         \ '\<begin\>:\<end\>,' .
         \ '\<if\>:\<else\>,' .
         \ '\<module\>:\<endmodule\>,' .
         \ '\<class\>:\<endclass\>,' .
         \ '\<program\>:\<endprogram\>,' .
         \ '\<clocking\>:\<endclocking\>,' .
         \ '\<property\>:\<endproperty\>,' .
         \ '\<sequence\>:\<endsequence\>,' .
         \ '\<package\>:\<endpackage\>,' .
         \ '\<covergroup\>:\<endgroup\>,' .
         \ '\<primitive\>:\<endprimitive\>,' .
         \ '\<specify\>:\<endspecify\>,' .
         \ '\<generate\>:\<endgenerate\>,' .
         \ '\<interface\>:\<endinterface\>,' .
         \ '\<function\>:\<endfunction\>,' .
         \ '\<task\>:\<endtask\>,' .
         \ '\<case\>\|\<casex\>\|\<casez\>:\<endcase\>,' .
         \ '\<fork\>:\<join\>\|\<join_any\>\|\<join_none\>,' .
         \ '`ifdef\>:`else\>:`endif\>,'
endif
" Source a global configuration file if available
if filereadable("/etc/vim/vimrc.local")
    source /etc/vim/vimrc.local
endif
