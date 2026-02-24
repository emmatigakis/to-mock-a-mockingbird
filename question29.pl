:- use_module(library(clpz)).
:- use_module(library(lists)).

:- set_prolog_flag(occurs_check, true).

:- op(900, xfx, <*>).

size(xL, 1).
size(X <*> Y, S) :- size(X,SX), size(Y,SY), S #= SX + SY.

sameBird(xL,xL,N,refl) :- N #> 0.
sameBird(X,Y,N1,[sym, P]) :-
    N1 #> 0,
    N #= N1 - 1,
    sameBird(Y,X,N, P).
sameBird(X,Z,N1,[trans, P1, P2]) :-
    N1 #> 0,
    N #= N1 - 1,
    sameBird(X,Y,N, P1),
    sameBird(Y,Z,N, P2).
sameBird(X <*> Y, Z <*> W,N1,[cong2, [<*>], P1, P2]) :-
    N1 #> 0,
    N #= N1 - 1,
    sameBird(X, Z,N, P1),
    sameBird(Y, W,N, P2).
sameBird((xL <*> X) <*> Y, X <*> (Y <*> Y),N, [lark, [X], [Y]]) :- N #> 0.

%?- length(_, N), sameBird(E <*> E, E, N,P), E \= ((xL<*>((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL))))<*>(xL<*>(xL<*>xL))), size(E,S), S #< 12.
%@    error('$interrupt_thrown',repl/0).

%@    N = 5, E = ((xL<*>((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL))))<*>(xL<*>(xL<*>xL))), P = [trans,[trans,[trans,[lark,[(xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL))],[xL<*>(xL<*>xL)]],[cong2,[<*>],[lark,[xL<*>xL],[xL<*>(xL<*>xL)]],[lark,[xL<*>xL],[xL<*>(xL<*>xL)]]]],[cong2,[<*>],[lark,[xL],[(xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL))]],[sym,[lark,[xL<*>xL],[xL<*>(xL<*>xL)]]]]],[sym,[trans,[cong2,[<*>],[lark,[(xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL))],[xL<*>(xL<*>xL)]],[lark,[(xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL))],[xL<*>(xL<*>xL)]]],[sym,[lark,[((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL)))<*>((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL)))],[(xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL))]]]]]], S = 10
%@ ;  ... .





