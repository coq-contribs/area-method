(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.         *)
(* Julien Narboux (Julien.Narboux@inria.fr)                                              *)
(* LIX/INRIA FUTURS 2004-2006                                                            *)
(***************************************************************************)

Require Export "elimination_lemmas".


Import F_scope.

Theorem C7ex: forall P Q R U V:Point,
 ~(parallel P Q U V) -> 
 exists Y:Point, (parallel Y R P Q) /\ (Col Y U V).
Proof with Geometry.
intros.
assert (P<>Q).
unfold not;intro.
assert (parallel P Q U V).
subst P.
Geometry.
intuition.

cases_col R P Q.

assert {Y : Point | Col Y P Q /\ Col Y U V}.
apply inter_llex...
DecompEx H2 Y.
exists Y.
intuition idtac.
cut (parallel P Q R Y).
Geometry.
unfold parallel,S4.
replace (S P R Q) with (- S R P Q).
2:symmetry;Geometry.
replace (S P Q Y) with (S Y P Q).
2:symmetry;Geometry.
rewrite H1.
rewrite H2.
ring.

assert ({Y':Point | (parallel P Q R Y') /\ R<>Y'}).
apply euclid_parallel_existence_strong...
DecompExAnd H2 Y'.

suppose (~ parallel Y' R U V).

assert {Y:Point | (Col Y Y' R) /\ (Col Y U V) }.
eapply inter_llex...

DecompExAnd H3 Y.
exists Y.
split;try assumption.

cut (parallel P Q R Y).
Geometry.
eapply col_par_par.
apply H5.
assumption.
Geometry.

unfold not;intro.
assert (parallel P Q U V).
eapply parallel_transitivity;eauto.
Geometry.
intuition.
Qed.

Theorem C8ex: forall P Q R U V W:Point,
 ~(parallel P Q U V) -> 
{Y:Point | (parallel Y R P Q) /\ (parallel Y W U V)}.
Proof with Geometry.
intros.

assert (P<>Q).
unfold not;intro.
assert (parallel P Q U V).
subst P.
Geometry.
intuition.

assert (U<>V).
unfold not;intro.
assert (parallel P Q U V).
subst U.
Geometry.
intuition.

assert ({R':Point | (parallel P Q R R') /\ R<>R'}).
apply euclid_parallel_existence_strong...
DecompExAnd H2 R'.

assert ({W':Point | (parallel U V W W') /\ W<>W'}).
apply euclid_parallel_existence_strong...
DecompExAnd H2 W'.

assert {Y : Point | Col Y R R' /\ Col Y W W'}.
apply inter_llex...

unfold not;intro.
assert (parallel R R' U V).
eapply parallel_transitivity.
apply H7.
Geometry.
Geometry.
assert (parallel P Q U V).
eapply parallel_transitivity;apply H5 || Geometry .
intuition.

DecompExAnd H2 Y.
exists Y.
split.

cut (parallel P Q R Y).
Geometry.
eapply col_par_par.
apply H5.
Geometry.
Geometry.

cut (parallel U V W Y).
Geometry.
eapply col_par_par.
apply H7.
Geometry.
Geometry.
Qed.






