:- write('preop '), op(1200,xfy,[&,hft,'!?',hf,tf,fh,ft,hfh,hft,tfh]),
   write('linop '), op(1150, xfy, '->'), write('rinop '), op(1100, xfy, @), write('postop '),
   (op(X,Y,Z) :- A), write(A).