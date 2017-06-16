clear(V) !? delax(v:_);

set(S,v) !? (clear(S) && addax(S:V));

get(S):V !? S:V;

assoc(S,V) !? (
  get(S,V) || clear(S) && set(S,V)
);

Simplify(I):O !? (
  str(I) && assoc(I):O
);

St2lf(S):LF !? (
  str(S) && st_to_li(S,L) && develop_lf(L,0):LF1 && simplify(S):LF
);

lf2str(LF):S !? (
  lf(LF) && assoc(S1):LF && develop+lf(L,0):LF1 && st_to_li(S,L)
);

