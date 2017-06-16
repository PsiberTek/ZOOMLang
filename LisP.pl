list(L): {
  Nilaiz: {L=[]} |
  Listaiz: (L=_|_) |
  IzNil: L==[] |
  exe!? L=[H|T] & atom(H)& D=..[H|T] & D |
  frst:F !? Val={F|_};
  rwlz: Val |
  eval(V) !? {
    V=Val | (V=(Val !? F) & F) | { Val={H|T} & { V=H | send({T}) } }
  }

}