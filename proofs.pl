% proofs.pl - the laws behind every insight, each proved exhaustively on a
% bounded domain (lists up to length 4 over {0,1,2}); the comment gives the
% general (inductive) argument.
:- ensure_loaded('mnnproofvis.pl').
:- ensure_loaded('spec.pl').
:- ensure_loaded('tests/inputs.pl').

list_upto(L) :- between(0, 4, N), length(L, N), maplist(digit, L).
digit(D) :- member(D, [0, 1, 2]).

% append([X], L, R) <=> R = [X|L]. Proof: one unfolding of append/3's second
% clause, then its first clause with T = [].
proof(append_singleton, forall(( list_upto(L), digit(X) ), ( append([X], L, R), R == [X|L] ))).

% reverse(reverse(L)) = L. Proof: induction on L with reverse(A++B) = rev(B)++rev(A).
proof(reverse_involutive, forall(list_upto(L), ( reverse(L, B), reverse(B, D), D == L ))).

% length(L, N), N > 0 succeeds exactly when L is a non-empty list.
proof(length_positive, forall(list_upto(L), ( ( length(L, N), N > 0 ) -> L = [_|_] ; L == [] ))).

% findall + length counts solutions, as aggregate_all(count, ...) does.
proof(count_of_solutions, forall(list_upto(L), ( findall(X, member(X, L), Xs), length(Xs, N),
                                                aggregate_all(count, member(_, L), M), N == M ))).

% member(X, L), ! has the same first answer as memberchk(X, L).
proof(first_solution_member, forall(( list_upto(L), digit(X) ),
      ( ( member(X, L), ! -> A = yes ; A = no ), ( memberchk(X, L) -> B = yes ; B = no ), A == B ))).

% Evaluating a ground expression twice gives the same number (determinism),
% so 'X is E' may be replaced by 'X = V'; and repeating a pure goal adds nothing.
proof(evaluation_deterministic, forall(( digit(A), digit(B) ), ( X is A * 3 + B, Y is A * 3 + B, X == Y ))).
proof(idempotence, forall(( digit(A), digit(B) ), ( ( A < B, A < B ) -> A < B ; \+ A < B ))).

% A pure goal whose result is never used can be dropped when it evaluates
% without error: it then succeeds once, binding only a variable nothing else
% reads. Ground arithmetic can raise an error (1/0, 1 mod 0, foo + 1), so the
% rule checks that the expression evaluates; this law covers exactly that case.
proof(unused_pure_result, forall(( digit(A), dead_expr(A, E) ),
      ( catch(_ is E, _, fail) -> ( once(_ is E), findall(x, _ is E, [x]) ) ; true ))).

% A dead result that raises an error is never reported, and optimise/2 keeps it,
% so the optimised program still raises the same error (seen as fails by mi/3).
proof(error_raising_result_kept, forall(( digit(A), dead_expr(A, E), \+ catch(_ is E, _, fail) ),
      ( P = [(p(_, ok) :- _ is E)], insights(P, Is), \+ member(insight(unneeded(dead_result), _, _, _, _, _), Is),
        optimise(P, O), equivalent(P, O, p, [[], [1]], equivalent(2)) ))).

dead_expr(A, A + 1).
dead_expr(A, A / 0).
dead_expr(A, A mod 0).
dead_expr(A, A // 0).
dead_expr(_, foo + 1).

% true is the identity of conjunction.
proof(conjunction_identity, forall(digit(A), ( ( true, A >= 0 ) -> A >= 0 ; true ))).

% The accumulator version of a sum equals the recursive sum.
% Proof: by induction on L, acc(L, A, S) gives S = A + sum(L) (+ is associative
% and commutative), so acc(L, 0, S) gives sum(L).
proof(sum_accumulator, forall(list_upto(L), (
      acc_version(t, Cs), P = [t([], 0), (t([H|T], S) :- t(T, S0), S is S0 + H)|Cs],
      once(mi(t(L, X), [t([], 0), (t([H|T], S) :- t(T, S0), S is S0 + H)], 20)),
      once(mi(t(L, Y), [(t(L2, S2) :- t_acc(L2, 0, S2))|Cs], 20)), X == Y, P = P ))).

% optimise/2 preserves the meaning of every sample program.
proof(optimise_preserves_meaning, forall(between(151, 175, Id), ( gen_prog(Id, P), optimise(P, O),
      equivalent(P, O, p, [[], [1], [2, 3], [4, 5, 6]], equivalent(4)) ))).

% Refinement: implementation and spec report identical insights.
proof(implementation_equals_spec, forall(between(1, 60, Id), ( gen_prog(Id, P), insights(P, A), spec_insights(P, B), A == B ))).
