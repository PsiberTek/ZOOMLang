nil^[].
void^{}.

hf(S, N) :- current_op(N,xf,S). 
tf(S, N) :- current_op(N,yf,S). 
fh(S, N) :- current_op(N,fx,S). 
ft(S, N) :- current_op(N,fy,S). 
hfh(S, N) :- current_op(N,xfx,S). 
hft(S, N) :- current_op(N,xfy,S). 
tfh(S, N) :- current_op(N,yfx,S). 

typs^[
  !^var, vald^nonvar, str^atom,
  int^integer, fl^float, # ^ number, 
  simp^atomic, strukt^compound].

typ(V):T :- typs^TL, (
 TL^(_^T), [T,V];
 TL^(T^D), [D,V]
).

str(S) :- atom(S).

list([]).
list([_,T]) :- list(T).

[H|T] :- atom(H), D=..[H|T], D.

kloz(:-(H,D)).

rwl(R) :- atom(R); complex(R).

func(:-(S^R,E)).


trace(Goal) :- trace(0,Goal).

trace(Depth,true)^true :- !.

trace(Depth, (Goal1,Goal2))^(Proof1,Proof2) :- !,
  trace(Depth,Goal1)^Proof1,
  trace(Depth,Goal2)^Proof2.

trace(Depth,Goal) ^ :-(ProofHead,ProofBody) :-
  display(Depth,'Call:',Goal)^Proof,
  fact(:-(Goal,Body)),
  Depth1 is Depth + 1,
  trace(Depth1,Body)^Proof,
  display(Depth,'Exit:',Goal),
  display_redo(Depth,Goal).

trace(Depth,Goal)^fail :-
  display('Depth,"Fail:',Goal),
  fail.

display(Depth,Message,Goal) :-
  tab(Depth), write(Message), write(Goal), nl.

display_redo(Depth,Goal) :- true;
  display(Depth,'Redo:',Goal), fail.


ob ^ {
  vald ^ Val |
  var :- var(Val) |
  :-(vald ^ Val, nonvar(Val)) |
  :-(eval ^ R, R = Val)
}.

ifkloz(X,H) ^ D :- X = (H :- D), D.

dwrwl(X,R) :- X = R; ifkloz(X,R):D.

Ob ^ Dw :-
  Ob ^ MZ, in(M,MZ), (
  dwrwl(Dw,M);
  M=(prent:P), ^(W,Dw)
 );
 Ob:R, R^W.

(Cond -> Then; Else) :- Cond,/, Then | Else.

case(X,L,R) :-
  L=(H;T) -> (
    H=(V:C) -> (
      V=X, R=C; case(X,T,R)
    ); X=H, R=success; case(X,T,R)
  ) | R=L.
case(X,L) :- case(X,L,R), R.

only_case(X,L,R) :-
  L=(H;T) -> (
    H=(V:C) -> (
      V=X -> R=C; case(X,T,R)
    ); (X=H -> R=success; case(X,T,R))
  ); R=T.
only_case(X,L) :- only_case(X,L,R), R.


ch_op(Char,Fix) :- case(Fix,(pre;suf;ht;th;fail)), Term=..[Fix|(Char|*)], Term.

word(W) :- string(W),
  not(member(W):M, (pass_char(M); char_signal(M); string_delimiter(M))).

assoc(H,T) :- get(H)^T , /; clear(H), set(H,T).

simplify(S)^R :- word(S), assoc(S)^R.

get(Term)^R :- Term^R.

clear(A) :- get(A):_, cons(A,T)^X, delax(X).

cons(X)^C :- C=..X,/; atom(X), C=X.

set(X,V) :- addax(X^V).

remove_string_through(St,Char,Data)^R :-
  St=[Char|R], Data=nil;
  St=[H|S2], Data=[H|T], remove_str_through(S2,Char,T)^R.

special_char(Ch,Do,Ret,InStr,OutStr) :-
  only_case([Ch|Do],(
	[')' | fail];
	['(' | develop_lf(InStr,0,[')'|OutStr],Ret)];
	['[' | fail];
	[']' | develop_lf(InStr,0,[']'|OutStr],Ret)];
	['[' | fail];
	[']' | develop_lf(InStr,0,['}'|OutStr],Ret)];
	['\' | (InStr = [Ret|OutStr])]
  ));
  pass_char(Ch), get_term(InStr,Ret,OutStr);
  string_delimiter(Ch), remove_string_through(Ch,Data,InStr,OutStr).

remove_word(OrgStr)^[Word,RetStr] :- case([Word|OrgStr], (
	[nil,Char|RetStr]: special_char(Char,*,*,*,*);
	[[H|T],H|TempStr], remove_word(TempStr)^[T,RetStr];
fail)).

get_term(InStr)^[Term,OutStr] :- InStr=[Ch,Str], (
	special_char(Ch,Str)^[Do,Term,OutStr], $(/, Do);
	!remove_word(InStr)^[Term,OutStr]
).

finish_lf(Term,InStr,MinPrec)^[LF,OutStr] :- get_term(InStr)^[Term,TempStr], (

	ht(Term,Prec), le(Prec,MinPrec)),
	develop_lf(TempStr,Prec)^[Str,Lf],
	finish_lf(Str,Term2,Prec)^[ht(Term,Prec,Term2,Lf),OutStr];

	th(Term,Prec), lt(Prec,MinPrec),
	develop_lf(TempStr,Prec)^[Lf,Str],
	finish_lf(th(Fix,Prec,Term,Lf),Str)^[Lf,OutStr];

	suffix(Term,Prec), le(Prec,MinPrec),
	finish_lf(TempStr,suf(Fix,Prec,Term),Prec)^[LF,OutStr];

	TempStr=OutStr, LF=term
).

develop_lf(InStr,MinPrec)^[LF,OutStr] :- get_term(InStr)^[Term,Str], (

	prefix(Term,Prec), develop_lf(Str,Prec)^[InLF,S],
	finish_lf(S,pre(Term,Prec,InLF),MinPrec)^[LF,OutStr];

	finish_lf(Str,Term,MinPrec)^[LF,OutStr];

	Str=OutStr
).

st2li(S)^L :- str(S), st_to_li(S,L).

li2st(L)^S :- list(L), st_to_li(S,L).

gtrans(Str)^LF :- trace(string(Str), st2li(Str)^L, develop_lf(L,0)^[LF,nil]).

:- write('input: '), read(S), write(LF).

