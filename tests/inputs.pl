% inputs.pl - 150 generated programs for insights/2 and 50 for
% optimise_verify/2 (programs defining p/2, run on 6 input lists).
input(Id, insights, P) :- between(1, 150, Id), gen_prog(Id, P).
input(Id, optimise_verify, P-p-Ins) :- between(151, 200, Id), gen_prog(Id, P),
    Ins = [[], [1], [2, 3], [4, 5, 6], [1, 1], [9, 8, 7, 6]].

lcg(S0, S) :- S is (S0 * 1103515245 + 12345) mod 2147483648.
rnd(M, S0, S, X) :- lcg(S0, S), X is (S >> 16) mod M.

gen_prog(Id, [s([], 0), SumC, (p(L, R) :- Body)|Extra]) :-
    S0 is Id * 6151,
    rnd(2, S0, S1, SK), sum_clause(SK, SumC),
    rnd(4, S1, S2, NG0), NG is NG0 + 2,
    gen_goals(NG, L, R0, S2, S3, Gs),
    append(Gs, [R = R0], Gs2), conj(Gs2, Body),
    rnd(3, S3, _, E), extra(E, Extra).

sum_clause(0, (s([H|T], S) :- s(T, S0), S is S0 + H)).
sum_clause(1, (s([H|T], S) :- s(T, S0), S is H * S0)).

extra(0, []).
extra(1, [(q(X, L) :- member(X, L), !)]).
extra(2, [(q(L, N) :- findall(X, member(X, L), Xs), length(Xs, N))]).

conj([G], G) :- !.
conj([G|Gs], (G, B)) :- conj(Gs, B).

% gen_goals(N, In, Out, S0, S, Goals): a chain of goals threading In to Out.
gen_goals(0, L, L, S, S, []) :- !.
gen_goals(N, L, R, S0, S, Gs) :-
    rnd(9, S0, S1, K), template(K, L, M, G1),
    N1 is N - 1, gen_goals(N1, M, R, S1, S, G2),
    append(G1, G2, Gs).

template(0, L, M, [append([x], L, M)]).
template(1, L, L, [_ is 2 + 3]).
template(2, L, L, [Z is 1 + 1, true, Z is 1 + 1]).
template(3, L, L, [length(L, N), N > 0]) :- N = N.
template(4, L, L, [true]).
template(5, L, M, [reverse(L, B), reverse(B, M)]).
template(6, L, L, [findall(X, member(X, L), Xs), length(Xs, _)]).
template(7, L, M, [msort(L, M)]).
template(8, L, M, [A is 4 * 5, M = [A|L]]).
