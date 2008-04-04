(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.*)
(* Julien Narboux (Julien.Narboux@inria.fr)                                     *)
(* LIX/INRIA FUTURS 2004-2006                                                     *)
(***************************************************************************)

Require Export elimination_lemmas.
Require Import Classical.
Import F_scope.


(** For the first time, we need decidability of the parallel predicate *)

Lemma parallel_dec : forall A B C D, parallel A B C D \/ ~ parallel A B C D.
Proof.
intros.
apply classic.
Qed.

Ltac cases_parallel A B C D := elim (parallel_dec A B C D);intros.

Definition Det3 (x1 x2 x3 y1 y2 y3 z1 z2 z3 : F) : F :=
  x1 * (y2 * z3) - x1 * (y3 * z2) - x2 * (y1 * z3) + x2 * (y3 * z1) +
  x3 * (y1 * z2) - x3 * (y2 * z1).


Lemma freepoint_elimination_aux : forall O U V B Y:Point, ~ Col O U V ->
S O B Y = 1/ (S O U V) * (S O B V * S O U Y + S O B U * S O Y V).
Proof with Geometry.
intros.

cases_parallel U V O Y.
rename H into T.
assert (O**Y / U**V = S U O Y / S O V U).
apply l2_15...
assert (S O B Y = S O B O + (O**Y/U**V) * S4 O U B V).
apply elim_area_on_parallel.
unfold on_parallel;repeat split...
eauto with Geom.
rewrite H in H1.
basic_simpl.
unfold S4 in *.
assert (parallel O Y U V).
Geometry.
unfold parallel, S4 in *.
IsoleVarRing (S O Y V) H2.
rewrite H2.
rewrite H1.
unify_signed_areas.
field.
split...

assert (exists W, inter_ll W U V O Y).
apply inter_ll_ex...
DecompEx H1 W.

cases_equality W O.
subst W.
unfold inter_ll in *.
intuition.
rename H1 into Hdiff.

assert (S B O W = 1 / S4 U O V Y * (S U O Y * S B O V + S V Y O * S B O U)).
apply  elim_area_inter_ll...
replace (S4 U O V Y) with (- S4 O U Y V) in H1.
2:Geometry.
replace ((S U O Y * S B O V + S V Y O * S B O U)) with 
(S O B V * S O U Y + S O B U * S O Y V) in H1.
2:unify_signed_areas;field.
unfold inter_ll in *;DecompAndAll.
assert (O ** W / O ** Y = S O U V / S4 O U Y V).
apply co_side_ter...
cases_col B O W.

cases_equality V W.
subst W.
assert (Col O Y B).
eapply col_trans_1 with (B:=V)...
unfold Col in *.
unify_signed_areas.
rewrite H4.
rewrite H5.
rewrite H7.
ring.

cases_equality O B.
subst B.
basic_simpl.
ring.

cases_col  V O B.
assert (Col O Y B).
eapply col_trans_1 with (B:= W)...
assert (Col O Y V).
eapply col_trans_1 with (B:= B)...
unfold Col in *.
unify_signed_areas.
rewrite H9.
rewrite H10.
rewrite H11.
ring.

assert (U**W/V**W = S U O B / S V O B).
apply co_side...

cases_col V O Y.

cases_equality Y O.
subst Y.
basic_simpl.
ring.

assert (Col Y W V).
eapply col_trans_1 with (B:= O)...
assert (Col W U Y).
eapply col_trans_1 with (B:= V)...

cases_equality Y W.
subst W.
clear H13 H12 H5.
assert (Col O V B).
eapply col_trans_1 with (B:= Y)...
unfold Col in *.
unify_signed_areas.
rewrite H4.
replace (S V O B) with (-0).
rewrite H11.
ring.
rewrite <- H5.
ring.

assert (Col Y U O).
eapply col_trans_1 with (B:= W)...
assert (Col O U V).
eapply col_trans_1 with (B:= Y)...
intuition.

assert (U**W/V**W = S U O Y / S V O Y).
apply co_side...
rewrite H10 in H12.

assert (Col O B Y).
eapply col_trans_1 with (B:= W)...
rewrite H13.
unify_signed_areas.
RewriteVar (S O B U) H12.
2:Geometry.
field.
split...

(** Second case *)
assert (O**Y / O**W = S B O Y / S B O W).
apply A6...
assert (O**Y / O**W = S4 O U Y V / S O U V).
replace (O ** Y / O ** W) with (1/(O ** W / O ** Y)). 
rewrite H2.
field.
Geometry.
repeat apply nonzeromult...
field.
split...
unfold not;intro.
assert (O=Y).
Geometry.
subst Y.
assert (parallel U V O O)...
rewrite H7 in H8.
set (S O B V * S O U Y + S O B U * S O Y V) in *.
rewrite H1 in H8.
replace (S B O Y) with (-S O B Y) in H8.
2:Geometry.

RewriteVar (S O B Y) H8.
field;split...
apply nonzeromult...
apply nonzerodiv...

unfold not;intro.
rewrite H9 in H1.
basic_simpl.
assert (Col O Y B).
eapply col_trans_1 with (B:=W)...
Geometry.

Qed.




Lemma  freepoint_elimination :
    forall O U V A B Y : Point, 
    S O U V <> 0 ->
    S A B Y =
    Det3 (S O U A) (S O V A) 1 (S O U B) (S O V B) 1 (S O U Y) (S O V Y) 1 /
    S O U V.
Proof with Geometry.
intros.
unfold Det3.
replace (S A B Y) with (S A B O + S A O Y + S O B Y)...

replace (S A O Y) with (- S O A Y).
2:symmetry;Geometry.
replace (S O A Y) with (1/ (S O U V) * (S O A V * S O U Y + S O A U * S O Y V)).
2:symmetry;eapply freepoint_elimination_aux...
replace (S O B Y) with (1/ (S O U V) * (S O B V * S O U Y + S O B U * S O Y V)).
2:symmetry;eapply freepoint_elimination_aux...
replace (S A B O) with (S O A B).
2:Geometry.
replace (S O A B) with (1/ (S O U V) * (S O A V * S O U B + S O A U * S O B V)).
2:symmetry;eapply freepoint_elimination_aux...
unify_signed_areas.
field...
Qed.

