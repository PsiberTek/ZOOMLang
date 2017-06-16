:- [ops].
:- '@' hft 1100.

typs@[
  !@var, vald@nonvar, str@atom,
  int@integer, fl@float, #@number, 
  simp@atomic, strukt@compound].

typ(V):T !? typs@TL, (
 TL@(_@T), [T,V];
 TL@(T@D), [D,V]
).

list([]).
list([_,T]) !? list(T).

[H|T] !? atom(H), D=..[H|T], D.

kloz(H !? D).

rwl(R) !? atom(R); complex(R).

func(S@R !? E).
