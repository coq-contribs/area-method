(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export geometry_tools.

Theorem field_prop1 : forall a : F, -a=0 -> a=0.
Proof with try solve [ ring | congruence ].
intros.
assert (- -a=-0).
rewrite H...
assert (- -a=a)...
assert (-0=0)...
Qed.

Hint Resolve field_prop1 : Geom.

(** Some propositions about Col *)

Theorem col_1 : forall A B C : Point, Col A B C -> Col B A C.
Proof with uniformize_signed_areas;Geometry.
unfold Col in |- *.
intros...
Qed.

Theorem col_2 : forall A B C : Point, Col A B C -> Col A C B.
Proof with uniformize_signed_areas;Geometry.
unfold Col in |- *.
intros...
Qed.

Theorem col_3 : forall A B C : Point, Col A B C -> Col B C A.
Proof with uniformize_signed_areas;Geometry.
unfold Col in |- *.
intros...
Qed.

Theorem col_4 : forall A B C : Point, Col A B C -> Col C B A.
Proof with uniformize_signed_areas;Geometry.
unfold Col in |- *.
intros...
Qed.

Theorem col_5 : forall A B C : Point, Col A B C -> Col C A B.
Proof with uniformize_signed_areas;Geometry.
unfold Col in |- *.
intros...
Qed.

Hint Resolve col_1 col_2 col_3 col_4 col_5: Geom.

(** Proposition about equality and nullity of geometric quantities *)

Theorem noteqnotzero : forall A B : Point, A <> B -> A ** B <> 0.
intros.
assert (A ** B = 0 <-> A = B).
apply A1b.
intuition.
Qed.
Hint Resolve noteqnotzero: Geom.

Theorem egalcol : forall A B C : Point, A = B -> Col A B C.
Proof with try solve [ Geometry | congruence ].
intros.
unfold Col.
rewrite H...
Qed.

Theorem notcolnotegal_1 : forall A B C : Point, ~ Col A B C -> A <> B.
unfold Col in |- *.
intros.
intuition.
assert (T := egalcol A B C H0).
auto.
Qed.

Theorem notcolnotegal_2 : forall A B C : Point, ~ Col A B C -> B <> C.
intros.
assert (~ Col A B C -> ~ Col B C A).
intuition.
assert (~ Col B C A).
auto.
eapply notcolnotegal_1.
apply H1.
Qed.

Theorem notcolnotegal_3 : forall A B C : Point, ~ Col A B C -> A <> C.
intros.
assert (~ Col A B C -> ~ Col A C B).
intuition.
assert (~ Col A C B).
auto.
eapply notcolnotegal_1.
apply H1.
Qed.

Hint Resolve notcolnotegal_1 notcolnotegal_2 notcolnotegal_3: Geom.

Theorem notparallelnotegal_1 : forall A B C D, 
 ~ parallel A B C D -> A<>B.
Proof.
intros.
unfold not;intro.
subst.
auto with Geom.
Qed.

Theorem notparallelnotegal_2 : forall A B C D, 
 ~ parallel A B C D -> C<>D.
Proof.
intros.
unfold not;intro.
subst.
auto with Geom.
Qed.

Hint Resolve notparallelnotegal_1 notparallelnotegal_2 : Geom.

(** Some usefull lemmas about ratios of signed distances *)

Theorem dirseg_1 :
 forall A B C D : Point, D ** C <> 0 -> A ** B / C ** D = B ** A / D ** C.
Proof with Geometry.
intros.
uniformize_dir_seg.
field...
Qed.
Hint Resolve dirseg_1: Geom.

Theorem dirseg_2 : forall A B C D : Point, A ** B = C ** D -> B ** A = D ** C.
Proof with Geometry.
intros.
uniformize_dir_seg.
rewrite H.
auto.
Qed.
Hint Resolve dirseg_2: Geom.

(*
Theorem dirseg_1 : (A,B,C,D:Point) C<>D -> -(A**B/C**D) = B**A /C**D.
Proof with Geometry.
Intros.
Replace A**B with -B**A.
Field.
Symmetry.
Qed.

Theorem dirseg_2 : (A,B,C,D:Point) C<>D -> -(A**B/C**D) = A**B /D**C.
Proof with Geometry.
Intros.
Replace C**D with -D**C.
Field.
Symmetry.
Qed.


Hints Resolve dirseg_1 dirseg_2 : Geom.
*)

Theorem dirseg_3 :
 forall A B C D : Point, C ** D <> 0 -> A ** B / C ** D = - (B ** A / C ** D).
Proof with Geometry.
intros.
uniformize_dir_seg.
field...
Qed.

Theorem dirseg_4 :
 forall A B C D : Point, C ** D <> 0 -> A ** B / C ** D = - (A ** B / D ** C).
Proof with Geometry.
intros...
uniformize_dir_seg.
field...
Qed.

Hint Resolve dirseg_3 dirseg_4: Geom.

Theorem dirseg_simpl_1 : 
 forall A B, A<>B -> A**B / A**B = 1.
Proof.
intros.
field;auto with Geom.
Qed.

Theorem dirseg_simpl_2 : 
 forall A B, A<>B -> B**A / A**B = -(1).
Proof.
intros.
replace (B**A) with (- A**B).
field;auto with Geom.
symmetry;auto with Geom.
Qed.


Theorem dirsur_1 :
 forall A B C D E F : Point,
 ~ Col D E F -> S A B C / S D E F = S A C B / S D F E.
Proof with Geometry.
intros.
uniformize_signed_areas.
field...
Qed.
Hint Resolve dirsur_1: Geom.



Theorem col_trans_1 :
 forall A B C D : Point, A <> B -> Col A B C -> Col A B D -> Col A C D.
Proof with Geometry.
intros. 
assert (S A B C = S A B D + S A D C + S D B C)...
rewrite H0 in H2. 
rewrite H1 in H2.
cases_col A D C...
cases_equality C A...
apply egalcol...
NormalizeRing H2...
assert (C ** B / C ** A = S D C B / S D C A)...
assert (C ** A + A ** B = C ** B)...
rewrite <- H6 in H5...
assert ((C ** A + A ** B) / C ** A = 1 + A ** B / C ** A)...
field...
rewrite H7 in H5.
clear H7 H6.

assert (S D B C = - S D C B)...
rewrite H6 in H2...

assert (S A D C = S D C A)...
rewrite H7 in H2...
IsoleVarRing (S D C B) H2... 
rewrite H2 in H5...
assert (S D C A / S D C A = 1)...
field...
rewrite H8 in H5.
clear H6 H7 H8.
IsoleVarRing (A ** B) H5...
assert (A = B)...
intuition...
Qed.

Hint Resolve col_trans_1.

Lemma build_point_not_collinear_1 : forall A B, A<>B -> exists C, ~ Col A B C. 
Proof with Geometry.
assert ({A : Point &  {B : Point &  {C : Point | ~ Col A B C}}}).
apply A4.
intros.
elim H;intro X;intros.
elim p;intro Y;intros.
elim p0;intro Z;intros.
cases_col A B X.
cases_col A B Y.
cases_col A B Z.
cases_equality Y A.
subst Y.
assert (Col A X Z).
eapply col_trans_1 with (B:=B)...
assert (Col X A Z)...
intuition.
assert (Col A Y Z).
eapply col_trans_1 with (B:=B)...
assert (Col A Y X).
eapply col_trans_1 with (B:=B)...
assert (Col Y X Z).
eapply col_trans_1 with (B:=A)...
assert (Col X Y Z)...
intuition.
exists Z...
exists Y...
exists X...
Qed.

Lemma build_point_not_collinear_2 : forall A, exists B, exists C, ~ Col A B C. 
Proof with Geometry.
intros.
assert ({A : Point &  {B : Point &  {C : Point | ~ Col A B C}}}).
apply A4.
DecompEx H A1.
DecompEx p B.
DecompEx p0 C.
cases_equality A B.
subst A.
exists A1.
exists C...
assert  (T:=build_point_not_collinear_1 A B H).
DecompEx T C1.
exists B.
exists C1...
Qed.

Theorem col_not_col_1 :
 forall A B O P : Point, A <> O -> Col A P O -> ~ Col P A B -> ~ Col O A B.
Proof with Geometry.
intros.
unfold not in |- *; intro.
assert (Col A O P)...
assert (Col A O B)...
assert (Col A P B)...
eauto with Geom...
Qed.

Hint Resolve col_not_col_1.

Theorem A6_1 :
 forall P Q A M : Point,
 M <> Q -> ~ Col Q A M -> Col P Q M -> P ** M / Q ** M = S P A M / S Q A M.
Proof with try solve [ Geometry | congruence ].
intros...
assert (P ** M / Q ** M = M ** P / M ** Q)...
assert (M ** P / M ** Q = S A M P / S A M Q)...
assert (S A M P = S P A M)...
assert (S A M Q = S Q A M)...
Qed.
Hint Resolve A6_1: Geom.

Theorem A6_2 :
 forall P Q R A : Point,
 P <> Q -> ~ Col Q A P -> Col P Q R -> P ** R / P ** Q = S R A P / S Q A P.
Proof with try solve [ Geometry | congruence ].
intros...
assert (P ** R / P ** Q = S A P R / S A P Q)...
assert (S A P R = S R A P)... 
assert (S A P Q = S Q A P)... 
Qed.
Hint Resolve A6_2: Geom.

Theorem A6_3 :
 forall A B C P : Point,
 A <> C -> ~ Col P A C -> Col A B C -> C ** B / A ** C = S P C B / S P A C.
Proof with Geometry.
intros...
assert (C ** A = - A ** C)...
assert (S P C A = - S P A C)...
assert (C ** B / C ** A = S P C B / S P C A)...
rewrite H3 in H4...
rewrite H2 in H4...

RewriteVar (C ** B) H4...
field...
Qed.
Hint Resolve A6_3: Geom.

Theorem A6_4 :
 forall A B C P : Point,
 A <> B -> ~ Col P A B -> Col A B C -> C ** A / A ** B = S P C A / S P A B.
Proof with Geometry.
intros...
assert (A ** C / B ** A = S P A C / S P B A)...
assert (A ** C / B ** A = C ** A / A ** B)...
assert (S P C A / S P A B = S P A C / S P B A)...
congruence...
Qed.
Hint Resolve A6_4: Geom.

Theorem A6_5 :
 forall A B O P : Point,
 O <> A -> ~ Col O A B -> Col P A O -> P ** A / O ** A = S P A B / S O A B.
Proof with Geometry.
intros...
assert (P ** A / O ** A = S P B A / S O B A)...
assert (S P A B = - S P B A)...
assert (S O A B = - S O B A)...
rewrite H3...
rewrite H4...
rewrite H2...
assert (S O B A <> 0)...
field...
Qed.

Hint Resolve A6_5: Geom.

Theorem A6_6 :
 forall A B R Q : Point,
 A <> Q -> ~ Col Q A B -> Col A R Q -> A ** R / A ** Q = S R A B / S Q A B.
Proof with Geometry.
intros...
assert (S R A B / S Q A B = S R B A / S Q B A)...
rewrite H2...
Qed.

Hint Resolve A6_6: Geom.

Theorem l2_7 :
 forall A B C D P : Point,
 Col C A B ->
 Col D A B ->
 ~ Col P C A -> ~ Col P A B -> A <> B -> S P C D / S P A B = C ** D / A ** B.
Proof with try solve [ Geometry | congruence | field; Geometry ].
intros...
cases_equality C A...
assert (Col A B D)...
rewrite H4...
symmetry  in |- *...
assert (S P C D / S P A B = S P C D / S P C A * (S P C A / S P A B))...
assert (A <> C)...
assert (Col C D A)...
eauto with Geom...
assert (C ** D / C ** A = S P C D / S P C A)...
assert (A ** C / A ** B = S P A C / S P A B)...
assert (C ** A / A ** B = S P C A / S P A B)...
assert (C ** D / C ** A * (C ** A / A ** B) = C ** D / A ** B)...
Qed.


Theorem par_aux_1 : forall P Q U V : Point, ~ parallel P Q U V -> P <> Q.
Proof with Geometry.
intros...
unfold parallel in H...
  unfold S4 in H...
  unfold not in |- *; intro...
  assert (S P U Q = 0)...
  rewrite H0...
  assert (S P Q V = 0)...
  rewrite H0...
  rewrite H1 in H...
  rewrite H2 in H...
Qed.



Theorem par_not_all_col :
 forall P Q U V : Point, ~ parallel P Q U V -> ~ Col P U Q \/ ~ Col P Q V. 
intros.
cases_col P U Q.
unfold parallel in H.
unfold S4 in H.
rewrite H0 in H.
assert (0 + S P Q V = S P Q V).
ring.
rewrite H1 in H.
right.
unfold Col in |- *.
trivial.
left.
trivial.
Qed.

Theorem co_side_main :
 forall A B P Q M : Point,
 ~ Col Q A B ->
 ~ Col P A M ->
 ~ Col Q A M ->
 Q <> M -> Col A B M -> Col P Q M -> P ** M / Q ** M = S P A B / S Q A B.
Proof with try solve [ Geometry | congruence | field; Geometry ].
intros...
assert
 (S P A B / S Q A B =
  S P A B / S P A M * (S P A M / S Q A M * (S Q A M / S Q A B)))...
assert (A <> B); eauto with Geom...
assert (A <> M); eauto with Geom...
assert (A ** B / A ** M * (P ** M / Q ** M * (A ** M / A ** B)) = P ** M / Q ** M)...
assert (A ** B / A ** M = S P A B / S P A M)...
assert (P ** M / Q ** M = S P A M / S Q A M)...
assert (A ** M / A ** B = S Q A M / S Q A B)...
Qed.


Theorem co_side :
 forall A B P Q M : Point,
 ~ Col Q A B ->
 Q <> M -> Col A B M -> Col P Q M -> P ** M / Q ** M = S P A B / S Q A B.
Proof with Geometry.
intros...
cases_equality M A...
rewrite H3...
rewrite H3 in H0...
rewrite H3 in H2...
assert (~ Col Q A M)...
unfold not in |- *; intro...
assert (Col Q M A)...
assert (Col Q M P)...
assert (Col Q A P); eauto with Geom...
assert (Col A M Q)...
assert (Col A M B)...
assert (Col A B Q); eauto with Geom...

cases_equality P M...
rewrite <- H5 in H1...
assert (Col P A B)...
rewrite H6...
assert (P ** M = 0)...
rewrite H7...
field...

cases_equality P Q...
rewrite H6...
field...

assert (~ Col P A M)...
unfold not in |- *; intro...
assert (Col P M A)...
assert (Col P M Q)...
assert (Col P A Q); eauto with Geom...

apply co_side_main...
Qed.






Hint Resolve co_side: Geom.

Theorem inter_unicity :
 forall A B P Q M : Point,
 ~ parallel P Q A B -> Col A B M -> Col P Q M -> A = Q -> A = M.
Proof with Geometry.
intros...
cases_equality A M...
assert (Col A M B)...
assert (Col Q M P)...
rewrite <- H2 in H5...
assert (Col A B P)...
eauto with Geom...
assert (~ Col P A Q \/ ~ Col P Q B)...
apply par_not_all_col...
case H7; intro...
assert (Col P A A)...
rewrite <- H2 in H8...
intuition...
rewrite H2 in H6...
assert (Col P Q B)...
intuition...
Qed.

Theorem inter_unicity_2 :
 forall A B P Q M N: Point,
 ~ parallel P Q A B -> 
 Col A B M -> Col P Q M -> 
 Col A B N -> Col P Q N -> 
 M = N.
Proof with Geometry.
intros.
assert (A<>B)
 by (intro;subst;auto with Geom).
assert (P<>Q)
 by (intro;subst;auto with Geom).
assert (Col A M N)
 by (apply (col_trans_1 A B M N);auto).
assert (Col P M N)
 by (apply (col_trans_1 P Q M N);auto).
cases_equality M N;auto.
assert (Col M A P) 
by (apply (col_trans_1 M N A P); auto with Geom).

assert (Col B M N) 
 by (apply (col_trans_1 B A M N);auto with Geom).
assert (Col Q M N)
 by (apply (col_trans_1 Q P M N);auto with Geom).
assert (Col M Q B) 
 by (apply (col_trans_1 M N Q B);auto with Geom).

cases_equality P M.
subst.
unfold parallel, S4 in *.
rewrite H12 in H.
basic_simpl.
clear H7 H9 H1 H3.
assert (Col M A Q)
 by (apply  (col_trans_1 M N A Q);auto with Geom).
intuition.

assert (Col P A Q) 
by (apply (col_trans_1 P M A Q);auto with Geom).

unfold parallel, S4 in *.
rewrite H14 in H.
basic_simpl.

cases_equality Q M.
subst.
clear H1 H11 H12 H14.
assert (Col M P B) 
by (apply (col_trans_1 M N P B);auto with Geom).
assert (Col P M B) by auto with Geom.
intuition.

assert (Col Q B P)
by (apply (col_trans_1 Q M B P);auto with Geom).
assert (Col P Q B) by auto with Geom.
intuition.
Qed.




Theorem co_side_bis :
 forall A B P Q M : Point,
 ~ parallel P Q A B ->
 Col A B M -> Col P Q M -> Q ** M / P ** Q = S Q A B / S4 P A Q B.

Proof with Geometry.
intros...
assert (P <> Q)...
eapply par_aux_1; apply H...
cases_equality Q M...
assert (Q ** M = 0)...
rewrite H4...
rewrite <- H3 in H0...
assert (Col Q A B)...
unfold parallel in H...
rewrite H5; field...

cases_equality A Q...
assert (A = M)...
apply (inter_unicity A B P Q M H H0 H1 H4)...
rewrite H4...
assert (Q = M)...
congruence...
assert (Q ** M = 0)...
assert (S Q Q B = 0)...
rewrite H7...
rewrite H8...
field...

assert (~ Col Q A B)...
unfold not in |- *; intro...
unfold parallel in H...
unfold S4 in H...
assert (S P A B = S P A Q + S P Q B + S Q A B)...
rewrite H5 in H6...
IsoleVar (S P A Q) H6...
rewrite H6 in H...
assert (S P A B - 0 - S P Q B + S P Q B = S P A B)...
ring...
rewrite H7 in H...
clear H6 H7...
assert (Col A B Q)...
assert (A <> B)...
unfold not in |- *; intro...
assert (S P A B = 0)...
rewrite H7...
assert (Col A M Q); eauto with Geom...
assert (Col Q M P)...
assert (Col Q M A)...
assert (Col Q A P); eauto with Geom...
assert (Col A Q B)...
assert (Col A Q P)...

assert (Col A B P); eauto with Geom...
assert (Col P A B)...

assert (P ** M / Q ** M = S P A B / S Q A B)...
assert (Q ** M / P ** Q * (P ** Q / Q ** M) = 1)...
field...
assert (P ** M / Q ** M - 1 = P ** Q / Q ** M).
replace (P ** Q) with (P ** M - Q ** M).
field...
assert (Q ** M = - M ** Q)...
rewrite H8 in |- *.
ring_simplify...

rewrite <- H8 in H7.
clear H8.
rewrite H6 in H7.
assert (S4 P A Q B = S P A B - S Q A B)...
rewrite H8.
clear H8.
IsoleVar (Q ** M / P ** Q) H7...
rewrite H7.
field...
split...
assert (S4 P A Q B = S P A B - S Q A B)...
unfold parallel in H.
rewrite H9 in H...
assert (S P A B / S Q A B - 1 = (S P A B - S Q A B) / S Q A B).
field...
rewrite H8...
apply nonzerodiv...
assert (S4 P A Q B = S P A B - S Q A B)...
rewrite <- H9...
Qed.

Hint Resolve co_side_bis: Geom.


Theorem co_side_ter :
 forall A B P Q M : Point,
 ~ parallel P Q A B ->
 Col A B M -> Col P Q M -> P ** M / P ** Q = S P A B / S4 P A Q B.
Proof with Geometry.
intros...
assert (Q ** M / P ** Q = S Q A B / S4 P A Q B)...
assert (P ** Q + Q ** M = P ** M)...
rewrite <- H3...
RewriteVar (Q ** M) H2...
assert (S P A B = S P A Q + S P Q B + S Q A B)...
rewrite H5...
unfold S4 in |- *...
field...
assert (P <> Q)...
eapply par_aux_1; apply H...
Qed.

Hint Resolve co_side_ter: Geom.


Theorem l2_9_weak :
 forall A B P Q R : Point,
 P <> Q ->
 ~ Col Q A P ->
 ~ Col Q P B ->
 Col R P Q -> S R A B = P ** R / P ** Q * S Q A B + R ** Q / P ** Q * S P A B.
Proof with Geometry.
intros...
assert (S R A B = S R A P + S R P B + S P A B)...
assert (P ** R / P ** Q = S R A P / S Q A P)...

RewriteVar (S R A P) H4...
clear H4...

assert (P ** R / P ** Q = S B P R / S B P Q)...
assert (- S B P R = S R P B)...
rewrite <- H6 in H3...
RewriteVar (S B P R) H4...
clear H4 H6...

assert (S R A B = P ** R / P ** Q * (S Q A P - S B P Q) + S P A B)...
rewrite H3...
field...
clear H3...
assert (S A P Q - S B P Q = S4 A P B Q)...
unfold S4 in H3...
assert (S Q A P = S A P Q)...
rewrite <- H6 in H3...
rewrite H3 in H4...
clear H3 H6...
assert (S A B Q = S Q A B)...
rewrite H3 in H4...
clear H3...
assert (S A P B = - S P A B)...
rewrite H3 in H4...
clear H3...
assert
 (P ** R / P ** Q * (- S P A B + S Q A B) + S P A B =
  P ** R / P ** Q * S Q A B + (1 - P ** R / P ** Q) * S P A B)...
field...
rewrite H3 in H4...
clear H3...
assert (1 - P ** R / P ** Q = R ** Q / P ** Q)...
assert (R ** P + P ** Q = R ** Q)...
rewrite <- H3...
assert (R ** P = - P ** R)...
rewrite H6.
field...
congruence...
Qed.

Theorem l2_9aux :
 forall A B P Q R : Point,
 P <> Q ->
 Col R P Q ->
 Col Q A P ->
 ~ Col Q P B -> S R A B = P ** R / P ** Q * S Q A B + R ** Q / P ** Q * S P A B.
Proof.
intros.
cases_equality Q A.
assert (Col Q A B).
apply egalcol.
auto.
rewrite H4.
ring_simplify.
rewrite <- H3.
assert (R ** Q / P ** Q = S R Q B / S P Q B); Geometry.
rewrite H5.
field; Geometry.

assert (~ Col Q A B).
unfold not in |- *; intro.
assert (Col Q P B).
eauto with Geom.
auto.

assert (Col Q R A).
assert (Col P Q R); Geometry.
assert (Col P Q A); Geometry.
eauto with Geom.

assert (A ** R / A ** Q = S R A B / S Q A B); Geometry.
assert (A ** P / A ** Q = S P A B / S Q A B); Geometry.

RewriteVar (S R A B) H6.
RewriteVar (S P A B) H7.
2: trivial.

assert (A ** R / A ** Q = P ** R / P ** Q + R ** Q / P ** Q * (A ** P / A ** Q)).

assert (A ** Q + Q ** R = A ** R).
apply chasles.
Geometry.
assert (A ** R * P ** Q = A ** Q * P ** Q + Q ** R * P ** Q).
rewrite <- H9.
ring.

assert (P ** R + R ** Q = P ** Q).
apply chasles.
Geometry.
assert
 (A ** Q * P ** Q + Q ** R * P ** Q = A ** Q * (P ** R + R ** Q) + Q ** R * P ** Q).
rewrite <- H11.
ring.
rewrite H12 in H10.
clear H12.
NormalizeRing H10.

assert (P ** Q * Q ** R + A ** Q * R ** Q = R ** Q * A ** P).
assert (A ** Q + Q ** P = A ** P).
apply chasles.
Geometry.

rewrite <- H12.
assert (P ** Q = - Q ** P); Geometry.
rewrite H13.
assert (Q ** R = - R ** Q); Geometry.
rewrite H14.
ring.

assert (P ** Q * A ** R = A ** Q * P ** R + R ** Q * A ** P).
replace (P ** Q * A ** R) with (A ** R * P ** Q) by  ring.
rewrite H10.
rewrite <- H12.
ring.

clear H9 H10 H11 H12. 
IsoleVar (A ** R) H13.
rewrite H13.
field; Geometry.
Geometry.

rewrite H9.
ring.
Qed.

Theorem l2_9 :
 forall A B P Q R : Point,
 P <> Q ->
 Col R P Q -> S R A B = P ** R / P ** Q * S Q A B + R ** Q / P ** Q * S P A B.
Proof.
intros.
cases_col Q A P.
cases_col Q P B.
assert (Col Q P A); Geometry.
clear H1.
assert (Col Q A B).
eauto with Geom.
assert (Col P A B).
eauto with Geom. 
rewrite H1.
rewrite H4.
ring_simplify.
change (Col R A B) in |- *.
assert (Col Q R B).
eauto with Geom.
assert (Col Q R A).
eauto with Geom.
assert (Col R Q B); Geometry.
assert (Col R Q A); Geometry.
cases_equality R Q.
rewrite H9; trivial.
eauto with Geom.

apply l2_9aux; auto.
cases_col Q P B.
assert (S R B A = P ** R / P ** Q * S Q B A + R ** Q / P ** Q * S P B A).
apply l2_9aux; Geometry.

assert (S R A B = - S R B A); Geometry.
assert (S Q A B = - S Q B A); Geometry.
assert (S P A B = - S P B A); Geometry.
rewrite H4.
rewrite H5.
rewrite H6.
rewrite H3.
ring.

apply l2_9_weak; auto.
Qed.


(********************************************************************)
(* Construction lemmas                                              *)
(********************************************************************)

Theorem A2bgen :
 forall (A B P P' : Point) (r : F),
 Col A B P -> A ** P = r * A ** B -> Col A B P' -> A ** P' = r * A ** B -> P = P'.
Proof with Geometry.
intros...
cases_equality A B...
assert (A ** B = 0)...
rewrite H4 in H2...
rewrite H4 in H0...
NormalizeRing H2...
NormalizeRing H0...
assert (A = P')...
assert (A = P)...
congruence...
(* exemple de conflis proof with et metavariable ici *)
apply (A2b A B P P' r H3 H H0 H1 H2)...
Qed.


Definition mid_point (I A B : Point) : Prop := 
  Col A B I /\ A ** I = I ** B.

Definition symmetric_point (I A B : Point) : Prop :=
  Col A B I /\ A ** B = B ** I.


Theorem mid_point_ex : forall A B : Point, {O : Point | mid_point O A B}.
Proof with try solve [ Geometry | field; Geometry | congruence ].
intros...
assert (T := A2a A B (1 / 2))...
elim T; intros; clear T...
exists x...
intuition...
assert (A ** x + x ** B = A ** B)...
unfold mid_point in |- *...
intuition...
RewriteVar (A ** x) H0...
RewriteVar (x ** B) H1...
Qed.


Theorem symmetric_point_ex :
 forall A O : Point, {A' : Point | Col A O A' /\ A ** O = O ** A'}.
Proof with try solve [ Geometry | ring | congruence ].
intros...
assert (T := A2a A O 2)...
elim T; intros; clear T...
exists x...
unfold symmetric_point in |- *...
intuition...
assert (O ** x = - x ** O)...
assert (A ** x + x ** O = A ** O)...
rewrite H1; clear H1...
RewriteVar (A ** x) H0...
RewriteVar (x ** O) H2...
Qed.



Lemma mid_point_comm :
  forall A B C,
  mid_point A B C -> mid_point A C B.
Proof with Geometry.
unfold mid_point.
intuition.
Qed.

Hint Immediate mid_point_comm : Geom.


Theorem diag_mid_point_parallel : forall O A P B Q,
mid_point O A P -> mid_point O B Q -> parallel A B P Q.
Proof with Geometry.
intros.
unfold mid_point in *.
DecompAndAll.
rename H0 into H.
assert (Col B O Q)...
clear H1.
rename H0 into H1.
rename H3 into H0.




cases_equality A P...
assert (A = O)...
assert (A ** O + O ** P = A ** P)...
assert (A ** P = 0)...
rewrite H5 in H4; clear H5...
rewrite <- H0 in H4...
assert (A ** O + A ** O = 2 * A ** O)...
ring...
rewrite H5 in H4; clear H5...
IsoleVar (A ** O) H4...
assert (0 / 2 = 0)...
field...
rewrite H6 in H4...
unfold parallel in |- *...
unfold S4 in |- *...
rewrite H3...
assert (S P P B = 0)...
rewrite H5...
ring_simplify.
assert (Col P B Q)...
rewrite <- H3...
rewrite <- H4 in H1...


assert (A <> O)...
  unfold not in |- *; intro...
  assert (A ** O = 0)...
  rewrite H5 in H0...
  assert (O = P)...
  assert (A = P)...
  congruence...

cases_equality B O...
unfold parallel in |- *...
unfold S4 in |- *...
assert (B ** O = 0)...
rewrite H6 in H2...
assert (O = Q)...
assert (B = Q)...
congruence...
rewrite H7 in H...
rewrite H8...
rewrite H...
assert (S A Q Q = 0)...
rewrite H9...

cases_col O A B...
unfold parallel in |- *...
unfold S4 in |- *...
assert (Col A O B)...
assert (Col A O P)...
assert (Col A P B); eauto with Geom...
assert (Col B O Q)...
assert (Col B O A)...
assert (Col B Q A); eauto with Geom...
rewrite H9...
assert (Col A B Q)...
rewrite H13...


assert (Q ** B / O ** B = S Q A B / S O A B)...

assert (Q <> O)...
unfold not in |- *; intro...
assert (O ** Q = 0)...
assert (B ** O = 0)...
congruence...


assert (Q ** B / O ** B = 2)...
assert (Q ** B = Q ** O + O ** B)...
symmetry  in |- *...
rewrite H9...
assert (O ** B = Q ** O)...
rewrite H10...
field...

assert (O <> P)...
unfold not in |- *; intro...
assert (O ** P = 0)...
assert (A ** O = 0)...
congruence...

assert (P ** A / O ** A = S P A B / S O A B)...
assert (P ** A / O ** A = A ** P / A ** O)...
assert (A ** O + O ** P = A ** P)...
rewrite <- H13 in H12...
rewrite H0 in H12...
assert ((O ** P + O ** P) / O ** P = 2)...
field...

rewrite H14 in H12...
unfold parallel in |- *...

assert (S Q A B / S O A B = S P A B / S O A B)...
congruence...
assert (S Q A B = S A B Q)...
assert (S A P B = - S P A B)...
unfold S4 in |- *...
rewrite <- H16...
rewrite H17...
RewriteVar (S Q A B) H15...
field...
Qed.


Theorem euclid_parallel_existence_strong :
 forall A B P : Point, A<>B -> {Q : Point | parallel A B P Q /\ P<>Q}.
Proof with Geometry.
intros.
assert (Op := mid_point_ex A P)... 
elim Op; intro O; clear Op...
intros...
elim p; intros; clear p...
assert (Op := symmetric_point_ex B O)...
elim Op; intro Q; clear Op...
intros...
elim p; intros; clear p...
exists Q...

split.
eapply diag_mid_point_parallel;unfold mid_point;split.
apply H0.
assumption.
Geometry.
assumption.

unfold not;intro.
subst Q.
rewrite <- H1 in H3.
cases_equality O P.
subst P.
replace (O**O) with 0 in H1.
2:symmetry;Geometry.
assert (A=O).
Geometry.
subst A.
replace (O**O) with 0 in H3.
assert (B=O).
Geometry.
subst B.
intuition.
assert (Col O A B).
eapply col_trans_1 with (B:=P)...
assert (A**O+O**B=A**B)...
rewrite <- H3 in H6.
replace (B**O) with (-O**B) in H6.
NormalizeRing H6.
assert (A=B)...
symmetry;Geometry.
Qed.

Theorem euclid_parallel_existence :
 forall A B P : Point, {Q : Point | parallel A B P Q}.
Proof with Geometry.
intros.
assert (Op := mid_point_ex A P)... 
elim Op; intro O; clear Op...
intros...
elim p; intros; clear p...
assert (Op := symmetric_point_ex B O)...
elim Op; intro Q; clear Op...
intros...
elim p; intros; clear p...
exists Q...


eapply diag_mid_point_parallel;unfold mid_point;split.
apply H.
assumption.
Geometry.
assumption.
Qed.


(*******************************)
(* Some lemmas about parallels *)
(*******************************)

Theorem par_1 : forall A B C D : Point, 
   parallel A B C D -> parallel B A C D.
Proof with Geometry.
unfold parallel, S4 in |- *.
intros.
uniformize_signed_areas.
RewriteVar (S A C B) H.
ring.
Qed.

Hint Resolve par_1: Geom.

Theorem par_2 : forall A B C D : Point, 
   parallel A B C D -> parallel C D A B.
Proof with Geometry.
unfold parallel in |- *.
intros.
assert (S4 A C B D = - S4 C A D B)...
rewrite H0 in H...
Qed.

Hint Resolve par_2: Geom.

Theorem not_parallel_not_eq_1 : forall A B C D,
  ~ parallel A B C D -> A<>B. 
Proof with Geometry.
intros.
unfold not;intro;subst A...
Qed.

Theorem not_parallel_not_eq_2 : forall A B C D,
  ~ parallel A B C D -> C<>D. 
Proof with Geometry.
intros.
unfold not;intro;subst C...
Qed.

Hint Resolve not_parallel_not_eq_1 not_parallel_not_eq_2 : Geom.

Lemma mid_point_degenerated_1 : forall A B, mid_point A A B -> A=B.
Proof.
intros.
unfold mid_point in H.
DecompAndAll.
basic_simpl.
Geometry.
Qed.

Lemma mid_point_degenerated_2 : forall A B, mid_point A B B -> A=B.
Proof with Geometry.
intros.
unfold mid_point in H.
DecompAndAll.
replace (A**B) with (- B**A) in H1.
2:symmetry...
assert (B**A = 0)...
symmetry;Geometry.
Qed.

Lemma mid_point_degenerated_3 : forall A B, mid_point A B A -> A=B.
Proof.
intros.
unfold mid_point in H.
DecompAndAll.
basic_simpl.
symmetry;Geometry.
Qed.


Hint Resolve mid_point_degenerated_1 mid_point_degenerated_2 mid_point_degenerated_3:Geom.

Lemma eq_diff_diff : forall A B C D, A<>B -> A**B=C**D -> C<>D.
Proof with Geometry.
intuition idtac.
subst C.
basic_simpl...
Qed.

Hint Resolve eq_diff_diff : Geom.