%!
TeXDict begin
/!BP{ 72 72.27 div dup scale } def /!arrowhead { /L2 exch def /L1 exch
def /ang exch def /dist exch def /nb exch def 180 rotate 1 1 nb { newpath
0 0 moveto L1 ang cos mul L1 ang sin mul 2 copy lineto L2 0 lineto
neg lineto closepath L2 0 eq { stroke } { fill } ifelse dist 0 translate
} for } def /!psvect { newpath 0 0 moveto 2 copy lineto stroke 2 copy
translate 2 copy 0 eq exch 0 eq and {pop pop 1 0} if exch atan rotate
!arrowhead } def /!psrectpath { /y1 exch def /x1 exch def /y0 exch
def /x0 exch def newpath x0 y0 moveto x1 y0 lineto x1 y1 lineto x0
y1 lineto closepath } def /!pscirclepath { newpath 0 360 arc closepath
} def /!psovalpath { /rmax exch dup 0.1 le { pop 0.1 } if def /H exch
2 div dup 0.1 le { pop 0.1 } if def /W exch 2 div dup 0.1 le { pop
0.1 } if def /y exch def /x exch def H W le { /R H def }{ /R W def
} ifelse rmax R le { /R rmax def } if newpath x y H add moveto x W
add y H add x W add y R arct x W add y H sub x y H sub R arct x W sub
y H sub x W sub y R arct x W sub y H add x y H add R arct closepath
} def /!ps_cbezier { /y3 exch def /x3 exch def /y2 exch def /x2 exch
def /y1 exch def /x1 exch def /y0 exch def /x0 exch def newpath x0
y0 moveto x1 y1 x2 y2 x3 y3 curveto stroke x3 y3 translate y3 y2 sub
x3 x2 sub 2 copy 0 eq exch 0 eq and {pop pop 0 1} if atan rotate !arrowhead
} def /!ps_qbezier { /y3 exch def /x3 exch def /yy exch def /xx exch
def /y0 exch def /x0 exch def /x1 xx 2 mul x0 add 3 div def /y1 yy
2 mul y0 add 3 div def /x2 xx 2 mul x3 add 3 div def /y2 yy 2 mul y3
add 3 div def newpath x0 y0 moveto x1 y1 x2 y2 x3 y3 curveto stroke
x3 y3 translate y3 y2 sub x3 x2 sub 2 copy 0 eq exch 0 eq and {pop
pop 0 1} if atan rotate !arrowhead } def /!max 10 def /!ps_r_cbezier
{ /y3 exch def /x3 exch def /y2 exch def /x2 exch def /y1 exch def
/x1 exch def /y0 exch def /x0 exch def /xa x1 x2 sub 3 mul x3 x0 sub
add def /xb x0 x1 sub x1 sub x2 add 3 mul def /xc x1 x0 sub 3 mul def
/ya y1 y2 sub 3 mul y3 y0 sub add def /yb y0 y1 sub y1 sub y2 add 3
mul def /yc y1 y0 sub 3 mul def /t1 0 def /t2 1 def 0 1 !max { pop
/t t1 t2 add 2 div def t !calculx t !calculy path!a inufill { /t1 t
def } { /t2 t def } ifelse } for /ta t def /t1 0 def /t2 1 def 0 1
!max { pop /t t1 t2 add 2 div def t !calculx t !calculy path!b inufill
{ /t2 t def } { /t1 t def } ifelse } for /tb t def /x2 tb !calculdx
3 div ta tb sub mul tb !calculx add def /y2 tb !calculdy 3 div ta tb
sub mul tb !calculy add def /x3 tb !calculx def /y3 tb !calculy def
newpath ta !calculx ta !calculy moveto ta !calculdx 3 div tb ta sub
mul ta !calculx add ta !calculdy 3 div tb ta sub mul ta !calculy add
x2 y2 x3 y3 curveto stroke x3 y3 translate y3 y2 sub x3 x2 sub 2 copy
0 eq exch 0 eq and {pop pop 0 1} if atan rotate !arrowhead } def /!calculx
{ dup dup xa mul xb add mul xc add mul x0 add } def /!calculy { dup
dup ya mul yb add mul yc add mul y0 add } def /!calculdx { dup 3 xa
mul mul 2 xb mul add mul xc add } def /!calculdy { dup 3 ya mul mul
2 yb mul add mul yc add } def /!sign {dup 0 lt {pop -1} {0 eq {0} {1}
ifelse} ifelse} def /!pslatexline { /L exch def /b exch def /a exch
def a 0 eq {0 L b !sign mul} {L a !sign mul dup b mul a div} ifelse
newpath 0 0 moveto lineto stroke } def /!pslatexvector { /L exch def
/b exch def /a exch def a 0 eq {0 L b !sign mul} {L a !sign mul dup
b mul a div} ifelse 2 copy newpath 0 0 moveto lineto stroke translate
a 0 eq b 0 eq and {/a 1 def} if b a atan rotate !arrowhead } def /!pscircle
{ 2 div newpath 0 0 3 2 roll 0 360 arc stroke } def /!psdisk { 2 div
newpath 0 0 3 2 roll 0 360 arc fill } def
end