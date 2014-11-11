! Copyright (C) 2014 Tom Wright.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs colors.constants combinators
formatting grouping io io.styles kernel make math math.functions
math.order math.parser math.vectors random sets sequences ui
ui.gadgets ui.gadgets.labels ui.gadgets.panes ui.gestures
vectors ;
FROM: sequences => change-nth ;
IN: threes

: bigpiece ( board -- n ) supremum 8 / 3 max ;

: regulars ( -- x ) { 1 2 3 1 2 3 } clone ;

: surplus ( -- x ) regulars randomize 2 head ;

: bag ( board -- bag )
[ bigpiece , regulars % surplus % ] V{ } make randomize ;

: restock ( board bag -- bag )
dup empty? [ drop bag ] [ nip ] if ;

: next-piece ( board bag -- bag p ) dup pop [ restock ] dip ;

: empty-board ( -- b ) 16 0 <array> ;

: indices ( seq -- is ) length iota ;

: zero-indices ( seq -- is )
dup indices zip [ first zero? ] filter [ second ] map ;

: put-random ( n b -- b )
[ zero-indices random ] [ [ set-nth ] keep ] bi ;

: beginning ( -- b )
empty-board [ bag ] keep [ swap put-random ] reduce ;

: rows ( board -- rs ) 4 group ;

CONSTANT: one-style H{
    { foreground COLOR: blue }
}

CONSTANT: two-style H{
    { foreground COLOR: red }
}

CONSTANT: max-style H{
    { font-style bold }
}

: is-max? ( board p -- ? ) [ supremum ] dip = ;

: draw-piece ( board p -- )
dup zero? [ drop "" ] [ number>string ] if
{
    { [ dup "1" = ]     [ one-style ] }
    { [ dup "2" = ]     [ two-style ] }
    { [ 2dup is-max? ]  [ max-style ] }
    [ H{ } clone ]
} cond [ "%5s " printf ] with-style drop ;

: draw-row ( board row -- )
[ 2dup draw-piece drop " " write ] each drop ;

: draw-next ( board piece -- )
dup 3 > [ 2drop "+" write ] [ draw-piece ] if ;

: draw ( board bag -- )
swap dup rows [ 2dup draw-row drop nl nl ] each
swap last "next piece: " write draw-next ;

CONSTANT: valid-merges
{ 3 6 12 24 48 96 192 384 768 1536 3072 6144 }
: merges? ( p1 p2 -- ? ) + valid-merges member? ;

: boardindex ( c -- i ) first2 [ 4 * ] dip + ;
: @ ( b c -- p ) boardindex swap nth ;

: square-empty? ( b c -- ? ) @ 0 = ;

: above ( s -- d ) clone dup [ 0 ] dip [ 1 - ] change-nth ;

: above-merges? ( b s -- ? )
[ @ ] [ above @ ] 2bi merges? ;

: lifts? ( b s -- ? )
[ above square-empty? ] [ above-merges? ] 2bi or ;

: sources ( -- seq )
{ 1 2 3 } { 0 1 2 3 } cartesian-product concat ;

: shiftleft ( seq -- seq' ) 4 tail 4 0 <array> append ;

: one-at ( i -- board )
1 swap empty-board [ set-nth ] keep ;

: negate-shifted ( board -- board ) -1 v*n shiftleft ;

: merge-vec ( board s -- v )
boardindex [ one-at v* -1 v*n ] [ one-at v* shiftleft ] 2bi v+ ;

: lift-square ( b c -- b ) 2dup merge-vec nip v+ ;

: cr>coord ( c r -- s ) swap 2array ;

: try-lift ( b s -- b )
2dup lifts? [ lift-square ] [ drop ] if ;

: lift-column ( b col -- b )
{ 1 2 3 } [
    3dup cr>coord try-lift
    nip swap rot drop
] each drop ;

: (rotate) ( b -- b ) rows [ reverse ] map flip { } join ;

! Accept negative numbers, by using remainder to get equivalent
! # of positive turns.
: rotate ( b n -- b ) 4 rem [ (rotate) ] times ;

: positives ( a -- is )
dup indices zip [ first 0 > ] filter [ second ] map ;

: last-row ( is -- i ) [ 12 >= ] filter ;

: (lift) ( b -- b ) { 0 1 2 3 } [ lift-column ] each ;

! Use the difference between the board and the lifted board to
! find valid indices in the last row, and pick one at random.
: placement-idx ( b -- i )
(lift) zero-indices last-row random ;

: board-lifts? ( bd -- ? ) dup (lift) v- [ zero? not ] any? ;

: lift ( bd bg -- bd bg )
over board-lifts? [
    [ next-piece ] [ drop placement-idx ] [ drop (lift) ] 2tri
    [ set-nth ] keep swap
] when ;

: up ( bd bg -- bd bg ) lift ;

: right ( bd bg -- bd bg )
[ 1 rotate ] dip up [ -1 rotate ] dip ;

: down ( bd bg -- bd bg )
[ 2 rotate ] dip up [ -2 rotate ] dip ;

: left ( bd bg -- bd bg )
[ 3 rotate ] dip up [ -3 rotate ] dip ;

: game-over? ( board -- ? )
{ 0 1 2 3 } [ over swap rotate placement-idx ] any? not nip ;

: value ( piece -- n ) 3 / log2 1 + 3 swap ^ ;

: remove-lows ( board -- board' ) { 0 1 2 } without ;

: score ( board -- n ) remove-lows 0 [ value + ] reduce ;

TUPLE: threes-gadget < gadget
    board bag ;

M: threes-gadget pref-dim* drop { 690 285 } ;

CONSTANT: threes-style H{
    { font-size 36 }
}

: update-board ( threes -- )
dup clear-gadget
[
    threes-style [ dup [ board>> ] [ bag>> ] bi draw ] with-style
] make-pane
add-gadget drop ;

: update-game-over ( threes -- )
dup clear-gadget
[ threes-style [
    "game over." print
    "score: " write
    dup board>> score number>string print
    "press n for new game." print
] with-style ]
make-pane
add-gadget drop ;

: update ( threes -- )
dup board>> game-over? [
    update-game-over
] [
    update-board
] if ;

: <threes-gadget> ( -- g )
threes-gadget new beginning
[ >>board ] [ bag >>bag ] 2bi
update ;

: move ( threes q -- threes )
[ dup [ board>> ] [ bag>> ] bi ] dip
call
[ >>board ] [ >>bag ] bi* ; inline

threes-gadget H{
    { T{ button-down f f 1 }     [ request-focus ] }
    { T{ key-down f f "UP" }     [ [ up ] move update ] }
    { T{ key-down f f "LEFT" }   [ [ left ] move update ] }
    { T{ key-down f f "RIGHT" }  [ [ right ] move update ] }
    { T{ key-down f f "DOWN" }   [ [ down ] move update ] }
    { T{ key-down f f "n" }      [ beginning [ >>board ] [ bag >>bag ] bi update ] }
} set-gestures

MAIN-WINDOW: threes { { title "Threes!" } }
<threes-gadget> >>gadgets ;
