debug(Info)
  :- %write(Info), nl
     .

variable(V)              :- atom(V), not(bool(V)).
binding(bind(K,V))       :- variable(K), integer(V).

state([]).
state([KV|T])            :- binding(KV), state(T).

put(S1,KV,S2)            :- state(S1), binding(KV), put_(S1,KV,S2).
% impl
put_([],KV,[KV]).
put_([bind(K,V1)|T],bind(K,V2),[bind(K,V2)|T]) :- !.
put_([KV1|T1],KV2,[KV1|T2])
  :- put_(T1,KV2,T2).

get(S,K,V)               :- state(S), variable(K), get_(S,K,V).
% impl
get_([bind(K,V)|T],K,V) :- !.
get_([bind(K1,V1)|T],K2,V)
  :- get_(T,K2,V).

arith(const(N))          :- integer(N).
arith(plus(X,Y))         :- arith(X), arith(Y).
arith(star(X,Y))         :- arith(X), arith(Y).
arith(var(V))            :- variable(V).

eval_a(S, A, R)          :- state(S), arith(A), eval_a_(S,A,R).
% impl
eval_a_(S,const(N),N) :- !.
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
eval_b_(S,const(B),B)       :- !.
eval_b_(S,conj(X,Y),true)
  :- eval_b_(S,X,true),  eval_b_(S,Y,true),
     !.
eval_b_(S,conj(X,Y),false)
  :- eval_b_(S,X,R1), eval_b_(S,Y,R2),
     !.
eval_b_(S,less(X,Y),true)
  :- eval_a(S,X,R1), eval_a(S,Y,R2), R1 < R2,
     !.
eval_b_(S,less(X,Y),false)
  :- eval_a(S,X,R1), eval_a(S,Y,R2),
     !.
eval_b_(S,equal(X,Y),true)
  :- eval_a(S,X,R1), eval_a(S,Y,R2), R1 = R2,
     !.
eval_b_(S,equal(X,Y),false)
  :- eval_a(S,X,R1), eval_a(S,Y,R2),
     !.
eval_b_(S,neg(A),false)
  :- eval_b_(S,A,true),
     !.
eval_b_(S,neg(A),true)
  :- eval_b_(S,A,R),
     !.

statement(skip).
statement(comp(S,T))     :- statement(S), statement(T).
statement(as(V,A))       :- variable(V), arith(A).
statement(branch(C,L,R)) :- logic(C), statement(L), statement(R).
statement(while(C,S))    :- logic(C), statement(S).

transition(skip, S1,S1, skip)
  :- debug([skip,S1]),
     !.
transition(as,   S1,S2, as(K,A))
  :- debug([assign,S1,S2]),
     eval_a(S1,A,V), put(S1,bind(K,V),S2),
     !.
transition(comp(T1,T2), S1,S3, comp(P1,P2))
  :- debug([composition,S1,S2,S3]),
     statement(P1), statement(P2),
     transition(T1,S1,S2,P1),
     transition(T2,S2,S3,P2),
     !.
transition(ift(T), S1,S2, branch(C,L,R))
  :- debug([if_true,S1,S2]),
     logic(C), statement(L), statement(R),
     eval_b(S1,C,true),
     transition(T,S1,S2,L),
     !.
transition(iff(T), S1,S2, branch(C,L,R))
  :- debug([if_false,S1,S2]),
     logic(C), statement(L), statement(R),
     eval_b(S1,C,false),
     transition(T,S1,S2,R),
     !.
transition(wlf, S1,S1, while(C,P))
  :- debug([while_false,S1]),
     logic(C), statement(P),
     eval_b(S1,C,false),
     !.
transition(wlt(T1,T2), S1,S3, while(C,P))
  :- debug([while_true,S1,S2,S3]),
     logic(C), statement(P),
     eval_b(S1,C,true),
     transition(T1,S1,S2,P),
     transition(T2,S2,S3,while(C,P)),
     !.

% test
init_y(as(y,const(1))).
cond_x_not_1(neg(equal(var(x),const(1)))).
mul_y_with_x(as(y,star(var(y),var(x)))).
dec_x(as(x,plus(var(x),const(-1)))).
factorial(comp(I,W))
  :- init_y(I),
     cond_x_not_1(C),
     mul_y_with_x(M),
     dec_x(D),
     W = while(C,comp(M,D)).

run(V,S,T)
  :- factorial(X), transition(T, [bind(x,V)], S, X).
