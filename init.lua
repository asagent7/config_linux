local g = vim.g
local cmd = vim.cmd
local map = vim.api.nvim_set_keymap
local bufmap = vim.api.nvim_buf_set_keymap
local opts = {noremap = true, silent = true}

--plugins

require "paq" {
    "savq/paq-nvim";
    "tpope/vim-fugitive";
    "ntpeters/vim-better-whitespace";
    "edeneast/nightfox.nvim";
    "nvim-lua/plenary.nvim";
    "nvim-telescope/telescope.nvim";
    {"nvim-telescope/telescope-fzy-native.nvim", run = "make -C deps/fzy-lua-native"};
    {"nvim-telescope/telescope-fzf-native.nvim", run = "make"};
    {"nvim-treesitter/nvim-treesitter", run = function() cmd "TSUpdate" end};
    "p00f/nvim-ts-rainbow";
    "neovim/nvim-lspconfig";
    "hrsh7th/cmp-nvim-lsp";
    "hrsh7th/cmp-buffer";
    "hrsh7th/cmp-path";
    "hrsh7th/cmp-cmdline";
    "hrsh7th/nvim-cmp";
    "windwp/nvim-autopairs";
    "L3MON4D3/LuaSnip";
    "honza/vim-snippets";
    "saadparwaiz1/cmp_luasnip"
}

-- colorscheme

require('nightfox').load('nordfox')

-- global options

local o = vim.o

o.showcmd = true
o.showmatch = true
o.ignorecase = true
o.smartcase = true
o.hlsearch = true
o.incsearch = true
o.autowrite = true
o.hidden = true
o.mouse = 'a'
o.showmode = true
o.backup = false
o.laststatus = 2
o.termguicolors = true
o.completeopt = 'menu,menuone,noselect'
o.autoindent = true
o.smartindent = true
o.tabstop = 4
o.shiftwidth = 4
o.expandtab = true
o.swapfile = false
o.textwidth = 79
o.formatoptions = 'qrnj1'

-- window options

local wo = vim.wo

wo.number = true
wo.cursorline = true
wo.wrap = false
wo.colorcolumn = '81'

--buffer options

--local bo = vim.bo

--bo.autoindent = true
--bo.smartindent = true
--bo.tabstop = 4
--bo.shiftwidth = 4
--bo.expandtab = true
--bo.swapfile = false
--bo.textwidth = 79
--bo.formatoptions = 'qrnj1'

-- key mappings

map('', '<Space>', '<Nop>', opts)
g.mapleader = ' '

map('', '<C-Left>', '<C-w>h', opts)
map('', '<C-Right>', '<C-w>l', opts)
map('', '<C-Up>', '<C-w>k', opts)
map('', '<C-Down>', '<C-w>j', opts)
map('', '<Esc><Esc>', ':nohlsearch<cr>', opts)

-- telescope settings

local actions = require('telescope.actions')
require('telescope').setup {
    defaults = {
        mappings = {
            i = {
                ['<esc>'] = actions.close
            },
        },
    },
}

require('telescope').load_extension('fzy_native')


_G.project_files = function()
  local ok = pcall(require"telescope.builtin".git_files, {previewer = false})
  if not ok then require"telescope.builtin".find_files({previewer = false}) end
end

map('n', '<leader>f', "<cmd>lua require('telescope.builtin').find_files({previewer = false})<cr>", {noremap = true, silent=true})
map('n', '<leader>r', "<cmd>lua project_files()<cr>", {noremap = true, silent=true})
map('n', '<leader>c', "<cmd>lua require('telescope.builtin').find_files({previewer = false, cwd = vim.fn.expand('%:p:h')})<cr>", {noremap = true, silent=true})
map('n', '<leader>b', "<cmd>lua require('telescope.builtin').buffers({previewer = false})<cr>", {noremap = true, silent=true})
map('n', '<leader>m', "<cmd>lua require('telescope.builtin').oldfiles({previewer = false})<cr>", {noremap = true, silent=true})
map('n', '<leader>g', "<cmd>lua require('telescope.builtin').live_grep()<cr>", {noremap = true, silent=true})

-- treesitter settings

require('nvim-treesitter.configs').setup {
    highlight = {
        enable = true,
    },
    incremental_selection = {
        enable = true,
        keymaps = {
            init_selection = '<leader>tv',
            node_incremental = "<leader>tn",
            scope_incremental = "<leader>ta",
            node_decremental = "<leader>tp",
        },
    },
    indent = {
        enable = false
    },
    rainbow = {
        enable = true,
        extended_mode = true,
        max_file_lines = nil,
  }
}

-- lsp settings

local runtime_path = vim.split(package.path, ';')
table.insert(runtime_path, 'lua/?.lua')
table.insert(runtime_path, 'lua/?/init.lua')

map('n', '<leader>vn', '<cmd>lua vim.diagnostic.goto_next()<cr>', opts)
map('n', '<leader>vp', '<cmd>lua vim.diagnostic.goto_prev()<cr>', opts)
map('n', '<leader>fm', '<cmd>lua vim.lsp.buf.formatting()<cr>', opts)

local on_attach = function (_, bufnr)
    bufmap(bufnr, 'n', 'gd', '<cmd>lua vim.lsp.buf.definition()<cr>', opts)
    bufmap(bufnr, 'n', 'gde', '<cmd>lua vim.lsp.buf.declaration()<cr>', opts)
    bufmap(bufnr, 'n', '<leader>h', '<cmd>lua vim.lsp.buf.hover()<cr>', opts)
    bufmap(bufnr, 'n', 'gi', '<cmd>lua vim.lsp.buf.implementation()<cr>', opts)
    bufmap(bufnr, 'n', '<leader>rn', '<cmd>lua vim.lsp.buf.rename()<cr>', opts)
    bufmap(bufnr, 'n', '<leader>l', '<cmd>lua vim.lsp.buf.references()<cr>', opts)
    bufmap(bufnr, 'n', '<leader>ca', '<cmd>lua vim.lsp.buf.code_action()<cr>', opts)
    bufmap(bufnr, 'n', '<leader>wa', '<cmd>lua vim.lsp.buf.add_workspace_folder()<cr>', opts)
    bufmap(bufnr, 'n', '<leader>wr', '<cmd>lua vim.lsp.buf.remove_workspace_folder()<cr>', opts)
    bufmap(bufnr, 'n', '<leader>wl', '<cmd>lua print(vim.inspect(vim.lsp.buf.list_workspace_folders()))<cr>', opts)
end

local capabilities = vim.lsp.protocol.make_client_capabilities()
capabilities = require('cmp_nvim_lsp').update_capabilities(capabilities)

local lspconfig = require('lspconfig')
local servers = {'sumneko_lua'}

for _, lsp in ipairs(servers) do
    lspconfig[lsp].setup {
        on_attach = on_attach,
        capabilities = capabilities,
    }
end

lspconfig.sumneko_lua.setup {
    on_attach = on_attach,
    capabilities = capabilities,
    settings = {
        Lua = {
            runtime = {
                -- Tell the language server which version of Lua you're using (most likely LuaJIT in the case of Neovim)
                version = 'LuaJIT',
                -- Setup your lua path
                path = runtime_path,
            },
            diagnostics = {
                -- Get the language server to recognize the `vim` global
                globals = { 'vim' },
            },
            workspace = {
                -- Make the server aware of Neovim runtime files
                library = vim.api.nvim_get_runtime_file('', true),
            },
            -- Do not send telemetry data containing a randomized but unique identifier
            telemetry = {
                enable = false,
            },
        },
    },
}

-- snippet settings

local luasnip = require('luasnip')
require("luasnip.loaders.from_snipmate").load()

-- autocomplete settings

local cmp = require('cmp')

local has_words_before = function()
    local line, col = unpack(vim.api.nvim_win_get_cursor(0))
    return col ~= 0 and vim.api.nvim_buf_get_lines(0, line - 1, line, true)[1]:sub(col, col):match("%s") == nil
end

cmp.setup {
    mapping = {
        ['<CR>'] = cmp.mapping.confirm {
          behavior = cmp.ConfirmBehavior.Replace,
          select = true,
        },
        ['<Tab>'] = function(fallback)
          if cmp.visible() then
            cmp.select_next_item()
          elseif luasnip.expand_or_jumpable() then
            luasnip.expand_or_jump()
    	  elseif has_words_before() then
	    cmp.complete()
          else
            fallback()
          end
        end,
        ['<S-Tab>'] = function(fallback)
          if cmp.visible() then
            cmp.select_prev_item()
          elseif luasnip.jumpable(-1) then
            luasnip.jump(-1)
          else
            fallback()
          end
        end,
    },
    sources = {
        {name = 'nvim_lsp'},
        {name = 'buffer'},
        {name = 'luasnip'},
    },
}

cmp.setup.cmdline('/', {
    sources = {
        {name = 'buffer'}
    }
})

-- autopairs

require('nvim-autopairs').setup {
    enable_check_bracket_line = false,
    ignored_next_char = "[%w%.]",
}

local cmp_autopairs = require('nvim-autopairs.completion.cmp')
cmp.event:on( 'confirm_done', cmp_autopairs.on_confirm_done({  map_char = { tex = '' } }))
