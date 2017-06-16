

ob(Ob) @ ob(Ob,T) !? ob(Ob,Rwlz) & Rwlz2Tree(Rwlz) @ T.

tree(n0);
tree( n1(X) );
tree( n2(L,M,R) );
tree( n3(L,LM.M,RM,R) );

Rwlz2Tree({R}):Tr :-
 R=(H;T), Rwlz2Tree({T}):T1, add123(T1,H):Tr;
 R\=(H;T), add123(n0,R):Tr.

add123(Ti,X):To
  Ti@ins123(X):TL
  l2t(TL):To;

del123(Ti, X): To :- add23(To, X): Ti;


l2t([T]): T;

l2t([Lt, M, Rt]): n(2, [Lt, M, Rt]);


n0: {
  ins123(X): [n1(X)];
  show(H) !? tab(H), write(-), nl,.
}

n1(X): {
 in(X);
 show(H) !? tab(H), write( x), nl.
 ins123(X): R :-
  N < X, R = [n1(N), X, n1(X)];
  X < N, R = [n1(X), N, n1(N)].
}

n2(LT, M, RT) @ {
  in(X) !?
    X < M, in(X, LT);
    M < X, in(X, RT);
    X=M.
  show(H) !?
    Hl is H+2,
    show(RT, H1),
    tab(H), write(--), nl,
    tab(H), write(M), nl,
    tab(H), write(--), trI,
    show(LT, H1).
  ins123(X): [R]
    x < M, LT@ins123(X): Ri, (
      Ri = [T], R = n2(T,M,RT);
      Ri=[L,M2,MT],R=n3(L,M2,MT,M,RT)]
    ); M < X, RT@ins123(X):Ri, (
      Ri = [T], R = n2(LT,M,T);
      Ri=[MT,M2,RT],R=n3(LT,M,Mt,M2,RT)
    ).
}

n3(LT, LM, MT, RM, RT) !? {
  in(X) !?
    X < LM, in( X, LT);
    X=LM;
    X < RM, in(X, MT),
    X=RM;
    RM < X, in(X, RT).
  show(H) !?
	H1 is H+2,
	show(T3, H1),
	tab(H), write( --), nl,
	tab(H), write( M3), nl,
	show(T2, H1),
	tab(H), write( M2), nl,
	tab(H), write( --), nl,
	show(T1, H1).
  ins123(X): R :-
    X < ML, TL@ins123(X):L, (
     L=[NL], R=[n3(NL,ML,MT,MR,RT)];
     L=[NL,NM,NR],
     R=[n2(NL,NM,NR),ML,n2(MT,MR,RT)]
    );
    MR < X, RT@ins123(X): L, (
     L=[NR], R=[n3(TL,ML,MT,MR,NR)];
     L=[NL,NM,NR], 
     R=[n2(TL,ML,TM),ML,n2(NL,NM,NR)]
    );
    ML < X, X < MR, MT@ins123(X):L, (
     L=[NT], R=[n3(TL,ML,NT,MR,RT)];
     L=[NL,NM,NR],
     R=[n2(TL,ML,NL),NM,n2(NR,MR,RT)]
  ).
}
