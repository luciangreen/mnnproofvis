% spec.pl - independent oracle for mnnproofvis. Detection is re-written as
% one scan per rule over indexed goal lists (I-Goal pairs), and the
% optimisation verdict is the theorem itself: the optimised program is
% equivalent on every input.

spec_for(insights, spec_insights).
spec_for(optimise_verify, spec_optimise_verify).

spec_optimise_verify(P-_-Ins, verdict(N, equivalent(L))) :-
    spec_insights(P, Is), length(Is, N), length(Ins, L).

spec_insights(Prog, All) :-
    spec_number(Prog, 1, NCs),
    findall(I, ( member(K-C0, NCs), spec_clause(K, C0, I) ), All).

spec_number([], _, []).
spec_number([C|Cs], K, [K-C|R]) :- K1 is K + 1, spec_number(Cs, K1, R).

spec_clause(K, C0, I) :-
    copy_term(C0, C),
    ( C = (H :- B) -> true ; H = C, B = true ),
    ( B == true -> Gs = [] ; spec_flat(B, Gs) ),
    spec_number(Gs, 1, IGs),
    member(Rule, [app, fold, dup, len, tru, dead, rev, cnt, mchk, acc]),
    spec_rule(Rule, K, C, H, IGs, I),
    spec_name(C-I, 0, _).

spec_flat(B, [B]) :- var(B), !.
spec_flat((A, B), L) :- !, spec_flat(A, LA), spec_flat(B, LB), append(LA, LB, L).
spec_flat(G, [G]).

spec_nv(G, T) :- nonvar(G), G = T.

spec_rule(app, K, _, _, IGs, insight(optimise(append_singleton), K, J, append([X], L, R), R = [X|L], law(append_singleton))) :-
    member(J-G, IGs), spec_nv(G, append(L1, L, R)), nonvar(L1), L1 = [X|T], T == [].
spec_rule(fold, K, _, _, IGs, insight(optimise(constant_fold), K, J, (X is E), X = V, law(evaluation_deterministic))) :-
    member(J-G, IGs), spec_nv(G, (X is E)), ground(E), \+ number(E), catch(V is E, _, fail).
spec_rule(dup, K, _, _, IGs, I) :- spec_dups(IGs, [], K, Is), member(I, Is).
spec_rule(len, K, C, _, IGs, insight(optimise(length_positive), K, I, (length(L, N), N > 0), L = [_|_], law(length_positive))) :-
    member(I-G1, IGs), spec_nv(G1, length(L, N)), var(N),
    member(J-G2, IGs), J > I, spec_nv(G2, (N2 > Z)), N2 == N, Z == 0,
    spec_count(N, C, 2).
spec_rule(tru, K, C, _, IGs, insight(unneeded(true_goal), K, J, true, removed, law(conjunction_identity))) :-
    C \== true, member(J-G, IGs), G == true.
spec_rule(dead, K, C, _, IGs, insight(unneeded(dead_result), K, J, (X is E), removed, law(unused_pure_result))) :-
    member(J-G, IGs), spec_nv(G, (X is E)), var(X), ground(E), spec_count(X, C, 1),
    \+ catch(\+ _ is E, _, true).   % E evaluates without error
spec_rule(rev, K, C, _, IGs, insight(optimise(reverse_involution), K, I, (reverse(A, B), reverse(B, D)), D = A, law(reverse_involutive))) :-
    append(_, [I-G1, _-G2|_], IGs), spec_nv(G1, reverse(A, B)), var(B),
    spec_nv(G2, reverse(B2, D)), B2 == B, spec_count(B, C, 2).
spec_rule(cnt, K, C, _, IGs, insight(optimise(count_solutions), K, I, (findall(T, G, L), length(L, N)), aggregate_all(count, G, N), law(count_of_solutions))) :-
    append(_, [I-G1, _-G2|_], IGs), spec_nv(G1, findall(T, G, L)), var(L),
    spec_nv(G2, length(L2, N)), L2 == L, spec_count(L, C, 2).
spec_rule(mchk, K, _, _, IGs, insight(optimise(memberchk), K, I, (member(X, L), !), memberchk(X, L), law(first_solution_member))) :-
    append(_, [I-G1, _-G2|_], IGs), spec_nv(G1, member(X, L)), G2 == !.
spec_rule(acc, K, _, H, IGs, insight(optimise(accumulator), K, 0, P/2, P/3, law(sum_accumulator))) :-
    nonvar(H), H =.. [P, A1, S], nonvar(A1), A1 = [Hd|T],
    member(I-G1, IGs), nonvar(G1), G1 =.. [P, T2, S0], T2 == T,
    member(J-G2, IGs), J > I, spec_nv(G2, (S2 is E)), S2 == S,
    ( E = S1 + H1 ; E = H1 + S1 ), S1 == S0, H1 == Hd.

% spec_dups lists every goal that repeats an earlier pure goal, in order.
spec_dups([], _, _, []).
spec_dups([J-G|T], Seen, K, Out) :-
    (   spec_pure(G), \+ \+ ( member(S, Seen), S == G )
    ->  Out = [insight(unneeded(duplicate_goal), K, J, G, true, law(idempotence))|R]
    ;   Out = R ),
    spec_dups(T, [G|Seen], K, R).

spec_pure(G) :- nonvar(G), functor(G, F, A),
    member(F/A, [(is)/2, (=)/2, (<)/2, (>)/2, (=<)/2, (>=)/2, (=:=)/2, (=\=)/2, (==)/2,
                 length/2, atom_length/2, msort/2]), !.

spec_count(V, T, N) :- spec_vars(T, Vs), include(==(V), Vs, Hits), length(Hits, N).
spec_vars(T, [T]) :- var(T), !.
spec_vars(T, Vs) :- compound(T), !, T =.. [_|As], spec_vars_l(As, Vs).
spec_vars(_, []).
spec_vars_l([], []).
spec_vars_l([A|As], Vs) :- spec_vars(A, V1), spec_vars_l(As, V2), append(V1, V2, Vs).

spec_name(T, N0, N) :- var(T), !, atom_concat('V', N0, T), N is N0 + 1.
spec_name(T, N0, N) :- compound(T), !, T =.. [_|As], spec_name_l(As, N0, N).
spec_name(_, N, N).
spec_name_l([], N, N).
spec_name_l([A|As], N0, N) :- spec_name(A, N0, N1), spec_name_l(As, N1, N).
