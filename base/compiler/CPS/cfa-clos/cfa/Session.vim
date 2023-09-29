let SessionLoad = 1
let s:so_save = &g:so | let s:siso_save = &g:siso | setg so=0 siso=0 | setl so=-1 siso=-1
let v:this_session=expand("<sfile>:p")
silent only
silent tabonly
cd ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cfa-clos/cfa
if expand('%') == '' && !&modified && line('$') <= 1 && getline(1) == ''
  let s:wipebuf = bufnr('%')
endif
let s:shortmess_save = &shortmess
if &shortmess =~ 'A'
  set shortmess=aoOA
else
  set shortmess=aoO
endif
badd +1 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/ElabData/basics
badd +7 0cfa.sml
badd +160 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cps/cps.sig
badd +5 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cps/cps-util.sml
badd +12 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cps/ppcps.sml
badd +131 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cps/cps.sml
badd +177 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/clos/freemap.sml
badd +384 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/clos/freeclose.sml
badd +24 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/clos/globalfix.sml
badd +252 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/clos/closure.sml
badd +8 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/clos/allocprof.sml
badd +121 labelled-cps.sml
badd +19 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cfa-clos/closure.sml
badd +2 ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/ElabData/basics/lambdavar.sig
badd +19 cfa.sig
argglobal
%argdel
$argadd 0cfa.sml
edit ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cps/cps.sig
let s:save_splitbelow = &splitbelow
let s:save_splitright = &splitright
set splitbelow splitright
wincmd _ | wincmd |
vsplit
wincmd _ | wincmd |
vsplit
2wincmd h
wincmd w
wincmd w
let &splitbelow = s:save_splitbelow
let &splitright = s:save_splitright
wincmd t
let s:save_winminheight = &winminheight
let s:save_winminwidth = &winminwidth
set winminheight=0
set winheight=1
set winminwidth=0
set winwidth=1
exe 'vert 1resize ' . ((&columns * 20 + 95) / 191)
exe 'vert 2resize ' . ((&columns * 74 + 95) / 191)
exe 'vert 3resize ' . ((&columns * 95 + 95) / 191)
argglobal
enew
balt ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cps/cps.sig
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
lcd ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/ElabData/basics
wincmd w
argglobal
balt ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cfa-clos/cfa/labelled-cps.sml
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let &fdl = &fdl
let s:l = 137 - ((30 * winheight(0) + 25) / 50)
if s:l < 1 | let s:l = 1 | endif
keepjumps exe s:l
normal! zt
keepjumps 137
normal! 0
wincmd w
argglobal
if bufexists(fnamemodify("~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cfa-clos/cfa/0cfa.sml", ":p")) | buffer ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cfa-clos/cfa/0cfa.sml | else | edit ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cfa-clos/cfa/0cfa.sml | endif
if &buftype ==# 'terminal'
  silent file ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cfa-clos/cfa/0cfa.sml
endif
balt ~/Documents/School/Research/master-thesis/smlnj-legacy/base/compiler/CPS/cfa-clos/closure.sml
setlocal fdm=manual
setlocal fde=0
setlocal fmr={{{,}}}
setlocal fdi=#
setlocal fdl=0
setlocal fml=1
setlocal fdn=20
setlocal fen
silent! normal! zE
let &fdl = &fdl
let s:l = 318 - ((26 * winheight(0) + 25) / 50)
if s:l < 1 | let s:l = 1 | endif
keepjumps exe s:l
normal! zt
keepjumps 318
normal! 0
wincmd w
2wincmd w
exe 'vert 1resize ' . ((&columns * 20 + 95) / 191)
exe 'vert 2resize ' . ((&columns * 74 + 95) / 191)
exe 'vert 3resize ' . ((&columns * 95 + 95) / 191)
tabnext 1
if exists('s:wipebuf') && len(win_findbuf(s:wipebuf)) == 0 && getbufvar(s:wipebuf, '&buftype') isnot# 'terminal'
  silent exe 'bwipe ' . s:wipebuf
endif
unlet! s:wipebuf
set winheight=1 winwidth=20
let &shortmess = s:shortmess_save
let &winminheight = s:save_winminheight
let &winminwidth = s:save_winminwidth
let s:sx = expand("<sfile>:p:r")."x.vim"
if filereadable(s:sx)
  exe "source " . fnameescape(s:sx)
endif
let &g:so = s:so_save | let &g:siso = s:siso_save
set hlsearch
doautoall SessionLoadPost
unlet SessionLoad
" vim: set ft=vim :
