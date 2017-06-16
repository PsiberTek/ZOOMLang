:- consult(trace).
:- '->' ht 15, ';' ht 15, ':' ht 20.

(Cond -> Then; Else) !? Cond &/& Then | Else.

case(X,L,R) !?
  L=(H;T) -> (
    H=(V:C) -> (
      V=X & R=C | case(X,T,R)
    ); X=H & R=success | case(X,T,R)
  ) | R=L.
case --> <case(R) & $R.

only_case(X,L,R) !?
  L=(H;T) -> (
    H=(V:C) -> (
      V=X -> R=C; case(X,T,R)
    ); (X=H -> R=success; case(X,T,R))
  ); R=T.
only_case(X,L) !? only_case(X,L,R) & R.

ch_op Char !? $(case(Fix,pre;suf;ht;th;fail) & Term=..Fix.(char Char).*)))

word(W) !? string(W) & 
  not(member(W):M & (pass_char(M) | char_signal(M) | string_delimiter(M))).

assoc(H,T) !? get(H)@T & / | clear(H) & set(H,T).

simplify(S):R !? word(S) & assoc(S):R.

get(Term)@R !? Term@R.

clear(A) !? get(A):_ & cons(A,T)@X & delax(X).

cons(X)@C <- C=..X &/| atom(X) & C=X.

set(X,V) !? addax(X@V).

!remove_string_through(Char,Data) -->
  +Char & $Data=nil |
  +H & $Data=H.T & !remove_str_through(Char,T).

special_char(Ch,Do,Ret,InStr,OutStr) <- only_case(Ch.Do,
	')'.fail;
	'('.develop_lf(InStr,0,')'.OutStr,Ret);
	'['.fail;
	']'.develop_lf(InStr,0,']'.OutStr,Ret);
	'['.fail;
	']'.develop_lf(InStr,0,'}'.OutStr,Ret);
	'\'.(InStr=Ret.OutStr);
	(1 pass_char).get_term(InStr,Ret,OutStr);
	(1 string_delimiter).remove_string_through(Ch,Data,InStr,OutStr);
fail).

remove_word(OrgStr)@[Word,RetStr] !? case(Word.OrgStr,
	nil.Char.RetStr: special_char(Char,*,*,*,*);
	(H.T).H.TempStr & remove_word(TempStr)@[T,RetStr];
fail).

!get_term(InStr)@[Term,OutStr] !? InStr=[Ch,Str] & (
	special_char(Ch,Str)@[Do,Term,OutStr] & $(/ & Do) |
	!remove_word(InStr)@[Term,OutStr]
).

!finish_lf(Term,InStr,MinPrec)@[LF,OutStr] !? get_term(InStr)@[Term,TempStr] & (

	Term ht Prec & le(Prec,MinPrec)) &
	develop_lf(TempStr,Prec)@[Str,Lf] &
	finish_lf(Str,Term2,Prec)@[ht(Term,Prec,Term2,Lf),OutStr] |

	Term th Prec & lt(Prec,MinPrec) &
	develop_lf(TempStr,Prec)@[Lf,Str] &
	finish_lf(th(Fix,Prec,Term,Lf),Str)@[Lf,OutStr] |

	Term suffix Prec & le(Prec,MinPrec) &
	finish_lf(TempStr,suf(Fix,Prec,Term),Prec)@[LF,OutStr] |

	TempStr=OutStr & LF=term
).

!develop_lf(InStr,MinPrec)@[LF,OutStr] !? get_term(InStr)@[Term,Str] & (

	Term prefix Prec & develop_lf(Str,Prec)@[InLF,S] &
	finish_lf(S,pre(Term,Prec,InLF),MinPrec)@[LF,OutStr] |

	finish_lf(Str,Term,MinPrec)@[LF,OutStr] |

	Str=OutStr.

st2li(S)@L !? String(S), st_to_li(S,L).

li2st(L)@S !? List(L), st_to_li(S,L).

gtrans(Str)@LF !? trace(string(Str) & st2li(Str)@L & develop_lf(L,0)@[,nil]).

:- write('input: '), read(S), gtrans(S)@LF, write(LF).