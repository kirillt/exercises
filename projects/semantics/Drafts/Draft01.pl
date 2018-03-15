variable(V)              :- atom(V), not(bool(V)).
binding(bind(K,V))       :- variable(K), integer(V).

state([]).
state([KV|T])            :- binding(KV), state(T).

put(S1,KV,S2)            :- state(S1), binding(KV), put_(S1,KV,S2).
% impl
put_([],KV,[KV]).
put_([bind(K,_)|T],bind(K,V2),[bind(K,V2)|T]) :- !.
put_([KV1|T1],KV2,[KV1|T2])
  :- put_(T1,KV2,T2).

get(S,K,V)               :- state(S), variable(K), get_(S,K,V).
% impl
get_([bind(K,V)|_],K,V) :- !.
get_([bind(_,_)|T],K2,V)
  :- get_(T,K2,V).

arith(const(N))          :- integer(N).
arith(plus(X,Y))         :- arith(X), arith(Y).
arith(star(X,Y))         :- arith(X), arith(Y).
arith(var(V))            :- variable(V).

eval_a(S, A, R)          :- state(S), arith(A), eval_a_(S,A,R).
% impl
eval_a_(_,const(N),N) :- !.
eval_a_(S,plus(X,Y),R)
  :- eval_a_(S,X,R1), eval_a_(S,Y,R2), R is R1 + R2,
     !.
eval_a_(S,star(X,Y),R)
  :- eval_a_(S,X,R1), eval_a_(S,Y,R2), R is R1 * R2,
     !.
eval_a_(S,var(K),R)
  :- get(S,K,R),
     !.

bool(true).
bool(false).

logic(const(A))          :- bool(A).
logic(conj(X,Y))         :- logic(X), logic(Y).
logic(less(X,Y))         :- arith(X), arith(Y).
logic(equal(X,Y))        :- arith(X), arith(Y).
logic(neg(A))            :- logic(A).

eval_b(S, B, R)          :- state(S), logic(B), eval_b_(S,B,R).
% impl
eval_b_(_,const(B),B)       :- !.
eval_b_(S,conj(X,Y),true)
  :- eval_b_(S,X,true),  eval_b_(S,Y,true),
     !.
eval_b_(S,conj(X,Y),false)
  :- eval_b_(S,X,_), eval_b_(S,Y,_),
     !.
eval_b_(S,less(X,Y),true)
  :- eval_a(S,X,R1), eval_a(S,Y,R2), R1 < R2,
     !.
eval_b_(S,less(X,Y),false)
  :- eval_a(S,X,_), eval_a(S,Y,_),
     !.
eval_b_(S,equal(X,Y),true)
  :- eval_a(S,X,R1), eval_a(S,Y,R2), R1 = R2,
     !.
eval_b_(S,equal(X,Y),false)
  :- eval_a(S,X,_), eval_a(S,Y,_),
     !.
eval_b_(S,neg(A),false)
  :- eval_b_(S,A,true),
     !.
eval_b_(S,neg(A),true)
  :- eval_b_(S,A,_),
     !.

statement(skip).
statement(comp(S,T))     :- statement(S), statement(T).
statement(as(V,A))       :- variable(V), arith(A).
statement(branch(C,L,R)) :- logic(C), statement(L), statement(R).
statement(while(C,S))    :- logic(C), statement(S).

transition(skip, S1,S1, skip)
  :- !.
transition(as,   S1,S2, as(K,A))
  :- eval_a(S1,A,V), put(S1,bind(K,V),S2),
     !.
transition(comp(T1,T2), S1,S3, comp(P1,P2))
  :- statement(P1), statement(P2),
     transition(T1,S1,S2,P1),
     transition(T2,S2,S3,P2),
     !.
transition(ift(T), S1,S2, branch(C,L,R))
  :- logic(C), statement(L), statement(R),
     eval_b(S1,C,true),
     transition(T,S1,S2,L),
     !.
transition(iff(T), S1,S2, branch(C,L,R))
  :- logic(C), statement(L), statement(R),
     eval_b(S1,C,false),
     transition(T,S1,S2,R),
     !.
transition(wlf, S1,S1, while(C,P))
  :- logic(C), statement(P),
     eval_b(S1,C,false),
     !.
transition(wlt(T1,T2), S1,S3, while(C,P))
  :- logic(C), statement(P),
     eval_b(S1,C,true),
     transition(T1,S1,S2,P),
     transition(T2,S2,S3,while(C,P)),
     !.

% test
factorial(comp(y as const(1), while(neg(equal(var(x), const(1))), comp(y as star(var(y), var(x)), x as plus(var(x), const(-1)))))).
