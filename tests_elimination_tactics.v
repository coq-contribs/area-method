(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien.Narboux@inria.fr)                                *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(***************************************************************************)

Require  Import "area_method".
Import F_scope.

(** Area elimination *)

(** on_line *)

Lemma test_area_on_line_1 : forall I B C, 
  on_line I B C -> S I B C = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

Lemma test_area_on_line_2 : forall I B C, 
  on_line I B C -> S B C I = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

Lemma test_area_on_line_3 : forall I B C, 
  on_line I B C -> S B I C = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

(** on_line_d *)

Lemma test_area_on_line_d_1 : forall I B C, forall x:F, 
  on_line_d I B C x -> S B I C = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

Lemma test_area_on_line_d_2 : forall I B C, forall x:F, 
  on_line_d I B C x -> S I B C = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

Lemma test_area_on_line_d_3 : forall I B C, forall x:F, 
  on_line_d I B C x -> S B C I = 0.
Proof.
geoInit.
eliminate I.
basic_simpl.
auto.
Qed.

(* inter_ll *)

Lemma test_area_inter_ll_1 : forall I A B C D X Y,
 inter_ll I A B C D -> S X Y I = 1 / S4 A C B D * (S A C D * S X Y B + S B D C * S X Y A) .
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_inter_ll_2  : forall I A B C D X Y,
 inter_ll I A B C D -> S I X Y = 1 / S4 A C B D * (S A C D * S X Y B + S B D C * S X Y A) .
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_inter_ll_3  : forall I A B C D X Y,
 inter_ll I A B C D -> S Y I X = 1 / S4 A C B D * (S A C D * S X Y B + S B D C * S X Y A) .
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_1  : forall I B C D X Y,
 on_parallel I B C D -> S X Y I = S X Y B + B ** I / C ** D * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_2  : forall I B C D X Y,
 on_parallel I B C D -> S Y I X = S X Y B + B ** I / C ** D * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_3  : forall I B C D X Y,
 on_parallel I B C D -> S I X Y = S X Y B + B ** I / C ** D * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_d_1  : forall I B C D X Y r,
 on_parallel_d I B C D r -> S I X Y = S X Y B + r * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_d_2  : forall I B C D X Y r,
 on_parallel_d I B C D r -> S X Y I = S X Y B + r * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_parallel_d_3  : forall I B C D X Y r,
 on_parallel_d I B C D r -> S Y I X = S X Y B + r * S4 X C Y D.
Proof.
geoInit.
eliminate I.
reflexivity.
Qed.

Lemma test_area_on_inter_line_parallel_1 : forall I A B C D E X Y,
  on_inter_line_parallel I A B C D E -> False -> 
  S X Y I = (S4 D B E A * S X Y C - S4 D C E A * S X Y B) / S4 D B E C .
Proof.
geoInit.
eliminate I.
2:reflexivity.
intuition.
Qed.

Lemma test_area_on_inter_parallel_parallel_1 : forall I A B C D E F X Y,
  on_inter_parallel_parallel I A B C D E F ->
  False -> 
  S X Y I = S4 B D C A / S4 B E C F * S4 X E Y F + S X Y D.
Proof.
geoInit.
eliminate I.
2:reflexivity. 
intuition.
Qed.


(***********************)
(* Ratios elimination *)
(***********************)

Lemma test_on_line_4 : forall I X Y A B C , 
  on_line I X Y -> B<>C -> parallel A I B C ->
  False ->
  A**I/B**C = 1.
Proof.
geoInit.
eliminate I.
intuition.
intuition.
intuition.
Qed.

(** Test on_line_d in a ratio *)

Lemma test_on_line_d_11 : forall Y P Q A C D lambda,
  on_line_d Y P Q lambda ->  C<>D -> parallel A Y C D ->
  False -> A**Y/C**D =  1.
Proof.
geoInit.
eliminate Y.
intuition.
intuition.
intuition.
Qed.

Lemma test_on_line_d_12 : forall Y P Q A C D lambda,
  on_line_d Y P Q lambda ->  C<>D -> parallel Y A C D ->
  False ->
  Y**A/C**D = 1.
Proof.
intros.
eliminate Y.
intuition.
intuition.
intuition.
Qed.

Lemma test_on_line_d_13 : forall Y P Q A C D lambda,
  on_line_d Y P Q lambda ->  Y<>A -> parallel C D Y A ->
  False ->
  C**D/Y**A = C**D.
Proof.
geoInit.
eliminate Y.
intuition.
intuition.
intuition.
Qed.


(** Test inter_ll in a ratio *)

(** Test cases where Y occurs both in denominator and numerator *)

Lemma test_inter_ll_1 :  forall Y P Q U V,
  inter_ll Y P Q U V ->  V<>Y -> parallel U Y V Y ->
  U**Y/V**Y = S U P Q / S V P Q.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_2 :  forall Y P Q U V,
  inter_ll Y P Q U V ->  U<>Y -> parallel V Y U Y ->
  V**Y/U**Y = S V P Q / S U P Q.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_3 :  forall Y P Q U V,
  inter_ll Y P Q U V ->  Q<>Y -> parallel P Y Q Y ->
  P**Y/Q**Y =S P U V / S Q U V.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_4 :  forall Y P Q U V,
  inter_ll Y P Q U V ->  P<>Y -> parallel Q Y P Y ->
  Q**Y/P**Y =S Q U V / S P U V.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.


Lemma test_inter_ll_1b :  forall Y P Q U V,
  inter_ll Y P Q U V ->  Y<>V -> parallel Y U Y V ->
  Y**U/Y**V = S U P Q / S V P Q.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_2b :  forall Y P Q U V,
  inter_ll Y P Q U V ->  Y<>U -> parallel V Y Y U ->
  V**Y/Y**U = - (S V P Q / S U P Q).
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_3b :  forall Y P Q U V,
  inter_ll Y P Q U V ->  Q<>Y -> parallel Y P Q Y ->
  Y**P/Q**Y = - (S P U V / S Q U V).
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.

Lemma test_inter_ll_4b :  forall Y P Q U V,
  inter_ll Y P Q U V ->  P<>Y -> parallel Q Y P Y ->
  Q**Y/P**Y =S Q U V / S P U V.
Proof.
geoInit.
eliminate Y.
reflexivity.
Qed.


Lemma test_inter_ll_5 :  forall Y P Q U V A C,
  inter_ll Y P Q U V ->  C<>Y -> parallel A Y C Y ->
  A**Y/C**Y = A**Y/C**Y.
Proof.
intros.
eliminate Y;reflexivity.
Qed.

Lemma test_inter_ll_gen_1 :  forall Y P Q U V A C D,
  inter_ll Y P Q U V ->  C<>D -> parallel A Y C D ->
  False ->
  A**Y/C**D = 1.
Proof.
geoInit.
eliminate Y.
intuition.
intuition.
intuition.
Qed.

Lemma test_inter_ll_gen_2 :  forall Y P Q U V A C D,
  inter_ll Y P Q U V ->  C<>D -> parallel A Y C D -> parallel Y A C D -> A<>Y -> Y<>A ->
  A**Y/C**D + Y**A/C**D=0.
Proof.
area_method.
Qed.

Lemma test_inter_ll_gen_3 :  forall Y P Q U V A C D,
  inter_ll Y P Q U V ->  A<>Y -> C<>D -> parallel C D A Y ->
  C**D/A**Y = C**D/A**Y.
Proof.
intros.
eliminate Y.
reflexivity.
reflexivity.
Qed.

Lemma test_on_parallel_d_1 : forall A C D Y R P Q lambda,
  on_parallel_d Y R P Q lambda ->
  C<>D ->
  parallel A Y C D ->
  False ->
  A**Y/C**D = 1.
Proof.
intros.
eliminate Y.
intuition.
intuition.
intuition.
intuition.
Qed.
