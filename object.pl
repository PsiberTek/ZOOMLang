nil:[].
void:{}.

A & B !? A, B.
(h :- b) :- (H !? T)

:- [ops] & @ tft 100 & in hft 700.

ob @ {
  vald @ Val |
  var !? var(Val) |
  vald @ Val !? nonvar(Val) |
  eval @ R !? R = Val
}.

ifkloz(X,H) @ D !? X = (H !? D) & D; X = (H :- D), D.

dwrwl(X,R) !? X = R | ifkloz(X,R):D.

Ob @ Dw !?
  Ob @ MZ, M in MZ, (
  dwrwl(Dw,M);
  M=(prent:P), @(W,Dw)
 );
 Ob:R, @(R,Dw).

