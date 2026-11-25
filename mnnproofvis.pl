% mnnproofvis - Prolog MNN Proof Visualiser.
% Annotates Prolog algorithms with insights about possible optimisations and
% unneeded computation, each backed by a named law that is proved in
% proofs.pl (exhaustively on bounded domains, with the inductive argument in
% comments), and can apply the rewrites and verify the optimised program
% gives the same outputs.
%
% insight(Kind, ClauseNo, GoalNo, Before, After, law(Law))
%   Kind is optimise(Name) or unneeded(Name).
%
% Try:  ?- example(P), visualise(P).
%       ?- example(P), optimise(P, P2), portray_clauses(P2).

:- ensure_loaded('mi.pl').

% ---- entry points used by the tests ----------------------------------------
insights(Prog, Insights) :-
    findall(I, ( nth1(K, Prog, C), clause_insights(K, C, Is), member(I, Is) ), Insights).

% optimise_verify(+Prog-Pred-Inputs, -verdict(NumInsights, Result))
optimise_verify(Prog-Pred-Ins, verdict(N, R)) :-
    insights(Prog, Is), length(Is, N),
    optimise(Prog, Opt), equivalent(Prog, Opt, Pred, Ins, R).

% ---- detection --------------------------------------------------------------
clause_insights(K, C0, Is) :-
    copy_term(C0, C), parts(C, H, B), body_goals(B, Gs),
    findall(C-I, detect(K, C, H, Gs, I), Ps),
    findall(I, ( member(CI-I, Ps), name_vars(CI-I, 0, _) ), Is).

body_goals(B, []) :- B == true, !.
body_goals(B, Gs) :- conj_list(B, Gs).

conj_list(B, Gs) :- var(B), !, Gs = [B].
conj_list((A, B), Gs) :- !, conj_list(A, GA), conj_list(B, GB), append(GA, GB, Gs).
conj_list(G, [G]).

detect(K, C, _, Gs, insight(optimise(append_singleton), K, J, append([X], L, R), R = [X|L], law(append_singleton))) :-
    nth1(J, Gs, G), nonvar(G), G = append(L1, L, R), nonvar(L1), L1 = [X|T], T == [], C = C.
detect(K, _, _, Gs, insight(optimise(constant_fold), K, J, (X is E), X = V, law(evaluation_deterministic))) :-
    nth1(J, Gs, G), nonvar(G), G = (X is E), ground(E), \+ number(E), catch(V is E, _, fail).
detect(K, _, _, Gs, insight(unneeded(duplicate_goal), K, J, G, true, law(idempotence))) :-
    nth1(J, Gs, G), pure(G), once(( nth1(I, Gs, G0), I < J, G0 == G )).
detect(K, C, _, Gs, insight(optimise(length_positive), K, I, (length(L, N), N > 0), L = [_|_], law(length_positive))) :-
    nth1(I, Gs, G1), nonvar(G1), G1 = length(L, N), var(N),
    nth1(J, Gs, G2), J > I, nonvar(G2), G2 = (N2 > Z), N2 == N, Z == 0,
    occurrences(N, C, 2).
detect(K, C, _, Gs, insight(unneeded(true_goal), K, J, true, removed, law(conjunction_identity))) :-
    nth1(J, Gs, G), G == true, \+ C = true.
detect(K, C, _, Gs, insight(unneeded(dead_result), K, J, (X is E), removed, law(unused_pure_result))) :-
    nth1(J, Gs, G), nonvar(G), G = (X is E), var(X), ground(E), occurrences(X, C, 1),
    catch(_ is E, _, fail).   % only if E evaluates: X is 1/0 raises an error, so it must stay
detect(K, C, _, Gs, insight(optimise(reverse_involution), K, I, (reverse(A, B), reverse(B, D)), D = A, law(reverse_involutive))) :-
    nth1(I, Gs, G1), nonvar(G1), G1 = reverse(A, B), var(B),
    J is I + 1, nth1(J, Gs, G2), nonvar(G2), G2 = reverse(B2, D), B2 == B,
    occurrences(B, C, 2).
detect(K, C, _, Gs, insight(optimise(count_solutions), K, I, (findall(T, G, L), length(L, N)), aggregate_all(count, G, N), law(count_of_solutions))) :-
    nth1(I, Gs, G1), nonvar(G1), G1 = findall(T, G, L), var(L),
    J is I + 1, nth1(J, Gs, G2), nonvar(G2), G2 = length(L2, N), L2 == L,
    occurrences(L, C, 2).
detect(K, _, _, Gs, insight(optimise(memberchk), K, I, (member(X, L), !), memberchk(X, L), law(first_solution_member))) :-
    nth1(I, Gs, G1), nonvar(G1), G1 = member(X, L),
    J is I + 1, nth1(J, Gs, G2), G2 == !.
detect(K, _, H, Gs, insight(optimise(accumulator), K, 0, P/2, P/3, law(sum_accumulator))) :-
    nonvar(H), H =.. [P, A1, S], nonvar(A1), A1 = [Hd|T],
    nth1(I, Gs, G1), nonvar(G1), G1 =.. [P, T2, S0], T2 == T,
    nth1(J, Gs, G2), J > I, nonvar(G2), G2 = (S2 is E), S2 == S,
    ( E = S1 + H1 ; E = H1 + S1 ), S1 == S0, H1 == Hd.

pure(G) :- nonvar(G), functor(G, F, A), memberchk(F/A, [(is)/2, (=)/2, (<)/2, (>)/2, (=<)/2, (>=)/2,
    (=:=)/2, (=\=)/2, (==)/2, length/2, atom_length/2, msort/2]).

occurrences(V, T, N) :- occ(T, V, 0, N).
occ(T, V, N0, N) :- var(T), !, ( T == V -> N is N0 + 1 ; N = N0 ).
occ(T, V, N0, N) :- compound(T), !, T =.. [_|As], foldl(occ_(V), As, N0, N).
occ(_, _, N, N).
occ_(V, T, N0, N) :- occ(T, V, N0, N).

name_vars(T, N0, N) :- var(T), !, atom_concat('V', N0, T), N is N0 + 1.
name_vars(T, N0, N) :- compound(T), !, T =.. [_|As], foldl(name_vars, As, N0, N).
name_vars(_, N, N).

% ---- rewriting --------------------------------------------------------------
% optimise(+Prog, -Prog2): applies every goal-level rewrite (the accumulator
% insight is reported, and acc_version/2 shows the rewritten predicate).
optimise(Prog, Opt) :- maplist(opt_clause, Prog, Opt).

opt_clause(C, C2) :-
    parts(C, H, B), body_goals(B, Gs),
    rewrite(Gs, Gs1), dedupe(Gs1, [], Gs2), drop_dead(Gs2, C, Gs3),
    list_conj(Gs3, B2),
    ( B2 == true -> C2 = H ; C2 = (H :- B2) ).

rewrite([], []).
rewrite([G|Gs], [G2|R]) :- var(G), !, G2 = G, rewrite(Gs, R).
rewrite([append(L1, L, R)|Gs], [R = [X|L]|Rs]) :- nonvar(L1), L1 = [X|T], T == [], !, rewrite(Gs, Rs).
rewrite([(X is E)|Gs], [X = V|Rs]) :- ground(E), \+ number(E), catch(V is E, _, fail), !, rewrite(Gs, Rs).
rewrite([length(L, N), G2|Gs], Rs) :- var(N), nonvar(G2), G2 = (N2 > Z), N2 == N, Z == 0,
    \+ ( member(G, Gs), occurrences(N, G, K), K > 0 ), !, rewrite([L = [_|_]|Gs], Rs).
rewrite([reverse(A, B), reverse(B2, D)|Gs], Rs) :- B2 == B, var(B),
    \+ ( member(G, Gs), occurrences(B, G, K), K > 0 ), !, rewrite([D = A|Gs], Rs).
rewrite([findall(T, G, L), length(L2, N)|Gs], [aggregate_all(count, G, N)|Rs]) :- L2 == L, var(L),
    \+ ( member(G0, Gs), occurrences(L, G0, K), K > 0 ), !, rewrite(Gs, Rs), T = T.
rewrite([member(X, L), C|Gs], [memberchk(X, L)|Rs]) :- C == !, !, rewrite(Gs, Rs).
rewrite([G|Gs], Rs) :- G == true, !, rewrite(Gs, Rs).
rewrite([G|Gs], [G|Rs]) :- rewrite(Gs, Rs).

dedupe([], _, []).
dedupe([G|Gs], Seen, R) :-
    ( pure(G), member(S, Seen), S == G -> R = R1 ; R = [G|R1] ),
    dedupe(Gs, [G|Seen], R1).

drop_dead(Gs, C, R) :- exclude(dead(C, Gs), Gs, R).
dead(C, _, G) :- nonvar(G), G = (X is E), var(X), ground(E), occurrences(X, C, 1), catch(_ is E, _, fail).
dead(C, _, G) :- nonvar(G), G = (X = V), var(X), number(V), occurrences(X, C, 1).

list_conj([], true).
list_conj([G], G) :- !.
list_conj([G|Gs], (G, B)) :- list_conj(Gs, B).

parts((H :- B), H, B) :- !.
parts(H, H, true).

% acc_version(+P, -Clauses): the accumulator form proved equal by law(sum_accumulator).
acc_version(P, [(H :- HA), Base, (Rec :- A1 is A0 + X, RecCall)]) :-
    atom_concat(P, '_acc', PA),
    H =.. [P, L, S], HA =.. [PA, L, 0, S],
    Base =.. [PA, [], A, A],
    Rec =.. [PA, [X|T], A0, S2], RecCall =.. [PA, T, A1, S2].

% ---- verification -----------------------------------------------------------
equivalent(P1, P2, Pred, Ins, R) :-
    (   member(In, Ins), out(P1, Pred, In, O1), out(P2, Pred, In, O2), O1 \== O2
    ->  R = differs(In)
    ;   length(Ins, N), R = equivalent(N)
    ).

out(P, Pred, In, O) :-
    G =.. [Pred, In, X],
    ( catch(once(mi(G, P, 50)), _, fail) -> ( ground(X) -> O = X ; O = nonground ) ; O = fails ).

% ---- visualisation ----------------------------------------------------------
visualise(Prog) :-
    insights(Prog, Is),
    forall(nth1(K, Prog, C0),
           ( copy_term(C0, C), name_vars(C, 0, _), format("~w. ~w.~n", [K, C]),
             forall(member(insight(Kind, K, J, B, A, law(L)), Is),
                    format("     ^ goal ~w ~w: ~w  ==>  ~w   [proof: ~w]~n", [J, Kind, B, A, L])) )),
    length(Is, N), format("~w insight(s). Laws are proved in proofs.pl.~n", [N]).

portray_clauses(P) :- forall(member(C0, P), ( copy_term(C0, C), name_vars(C, 0, _), format("~w.~n", [C]) )).

example([ (total([], 0)),
          (total([H|T], S) :- total(T, S0), S is S0 + H),
          (prep(L, R) :- append([start], L, R0), reverse(R0, R1), reverse(R1, R), true),
          (stats(L, N) :- length(L, K), K > 0, findall(X, member(X, L), Xs), length(Xs, N), W is 2 * 21),
          (seen(X, L) :- member(X, L), !) ]).
