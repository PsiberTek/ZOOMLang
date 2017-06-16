:-[typ].

trace(Goal) !? trace(0,Goal).


trace(Depth,true)@true !? !.

trace(Depth, (Goal1,Goal2))@(Proof1,Proof2) !? !,
  trace(Depth,Goal1)@Proof1,
  trace(Depth,Goal2)@Proof2.

trace(Depth,Goal)@(ProofHead !? ProofBody) !?
  display(Depth,'Call:',Goal)@Proof,
  fact(Goal !? Body),
  Depth1 is Depth + 1,
  trace(Depth1,Body)@Proof,
  display(Depth,'Exit:',Goal),
  dosplay_redo(Depth,Goal).

trace(Depth,Goal)@fail !?
  display('Depth,"Fail:',Goal),
  fail.


display(Depth,Message,Goal) !?
  tab(Depth), write(Message), write(Goal), nl.


display_redo(Depth,Goal) !?
  true;
  display(Depth,'Redo:',Goal),
  fail.