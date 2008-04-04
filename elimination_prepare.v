(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien.Narboux@inria.fr)                                *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(***************************************************************************)

Require Export "elimination_lemmas".
Import F_scope.

(** Tactics to distinguish cases if necessary *)

(** If S A B C = 0 is in the context then Tac1 is used *)
(** If S A B C <>0 is in the context then Tac2 is used *)
(** othewise we use Col decidability and perform Tac1 and Tac2 in each branch *)
(** We do not use the defiinition Col, to save the burden of managing the unfold *)

Lemma  col_decS : forall A B C:Point, S A B C = 0 \/ S A B C <>0.
Proof.
unfold Col.
apply col_dec.
Qed.

Ltac named_cases_colS A B C H := elim (col_decS A B C);intro H.

Ltac test_col A B C Tac1 Tac2 := 
 match goal with 
| HCol : S A B C = 0 |- _ => Tac1 HCol
| HCol : S A B C <>0 |- _ => Tac2 HCol
| _ => let HCol := fresh in 
      (named_cases_colS A B C HCol;
   [ Tac1 HCol | Tac2 HCol])
end.

(* TO DO modulo point order *)

(** The same for point equality *)

Ltac test_equality A B Tac1 Tac2 := 
 match goal with 
| H : A = B |- _ => Tac1 H
| H : A<>B |- _ => Tac2 H
| _ => let H := fresh in 
      (named_cases_equality A B H;
   [ Tac1 H | Tac2 H])
end.

(** Change A<>B into B<>A *)


Ltac invdiffhyp A B :=
  let H := HypOfType (A <> B) in
  let Hnew := fresh in
  (assert (Hnew := ldiff A B H); clear H).

(** Unification tactic for signed areas but just concerning one point, 
and puting this point in last position *)
(** The use of this specific tactic during the elimination process is 
faster than normalization of signed areas for every quantities *)

Ltac put_on_the_right_areas P :=
  repeat match goal with
    | |- context[S P ?X1 ?X2] => 
         replace_all (S P X1 X2) (S X1 X2 P);
         [idtac|symmetry;apply S_1]
    | |- context[S ?X1 P ?X2] => 
         replace_all (S X1 P X2) (S X2 X1 P);
         [idtac|symmetry;apply S_0]
end.

(** This tactics remove one parallel hypotheses and replace it
by the new one *)

Ltac changeparhyp A B C D lpar :=
  let Hpar := HypOfType (parallel A B C D) in
  let HparNew := fresh in
  (assert (HparNew := lpar A B C D Hpar); clear Hpar).

(** Put Y on the upper right position *)

Ltac put_on_the_right_ratios Y :=
  repeat match goal with
  |_:_ |- context [(?X5 ** Y / Y ** ?X7)] =>
      replace (X5 ** Y / Y ** X7) with (- (X5 ** Y / X7 ** Y));
       [ changeparhyp X5 Y Y X7 lpar1; invdiffhyp Y X7
       | symmetry  in |- *; apply dirseg_4; Geometry ]
  | _:_ |- context [(Y ** ?X5 / ?X7 ** Y)] =>
      replace (Y ** X5 / X7 ** Y) with (- (X5 ** Y / X7 ** Y));
       [ changeparhyp Y X5 X7 Y lpar2
       | symmetry  in |- *; apply dirseg_4; Geometry ]
  | _:_ |- context [(Y ** ?X5 / ?X6 ** ?X7)] =>
      replace (Y ** X5 / X6 ** X7) with (X5 ** Y / X7 ** X6);
       [ changeparhyp Y X5 X6 X7 lpar3; invdiffhyp X6 X7 | Geometry ]
  | _:_ |- context [(?X5 ** ?X6 / Y ** ?X7)] =>
      replace (X5 ** X6 / Y ** X7) with (X6 ** X5 / X7 ** Y);
       [ changeparhyp X5 X6 Y X7 lpar3; invdiffhyp Y X7 | Geometry ]
end.   


Ltac case_equal X5 X6 X7 Y Heq := rewrite Heq in *.

Lemma invariant_inverse_ratio : forall A B C D,
 A<>B -> C<>D -> C**D/ A**B <> 0.
intros.
apply nonzerodiv;Geometry.
Qed.

Ltac case_not_equal X5 X6 X7 Y Heq :=
 let T:= fresh in
  assert (T:X7**Y/X5**X6 <> 0);[apply (invariant_inverse_ratio X5 X6 X7 Y );try assumption|idtac];
 (replace (X5**X6 / X7**Y) with (1/(X7**Y / X5 ** X6));[changeparhyp X5 X6 X7 Y par_2|symmetry;apply inverse_ratio;Geometry]).

(** This tactic assumes that Y is on the right *)

Ltac put_on_the_upper_right_ratios Y :=
 repeat match goal with
   |_:_ |- context [(?X5 ** Y / ?X6 ** Y)] => fail 1
   |_:_ |- context [(?X5 ** ?X6 / ?X7**Y)] => 
          test_equality X5 X6 ltac:(case_equal X5 X6 X7 Y) ltac:(case_not_equal X5 X6 X7 Y)
end.    

Ltac unify_signed_areas_point P :=
  repeat
   match goal with
   |  |- context [(S ?X1 ?X1 ?X2)] =>
       replace (S X1 X1 X2) with 0; [ idtac | apply trivial_col1 ]
   |  |- context [(S ?X2 ?X1 ?X1)] =>
       replace (S X2 X1 X1) with 0; [ idtac | apply trivial_col2 ]
   |  |- context [(S ?X1 ?X2 ?X1)] =>
       replace (S X1 X2 X1) with 0; [ idtac | apply trivial_col3 ]
   |  |- context [(S ?X1 ?X2 P)] =>
    ( let Truc := fresh in
    match goal with
       |  |- context [(S ?X4 ?X5 P)] =>
            (assert (Truc : S X4 X5 P = - S X1 X2 P);
             [ apply S_3 || apply S_2 || apply S_4
             | rewrite_all Truc; clear Truc ]) ||
             (assert (Truc : S X4 X5 P = S X1 X2 P);
               [ apply S_0 || apply S_1 | rewrite_all Truc; clear Truc ])
       end)
   end.

(** This tactic prepares the elimination process by putting
the point on the right and unifying the geometric quantities
concerning the point *)

Ltac unify_signed_areas_and_put_on_the_right P :=
 put_on_the_right_areas P;
 put_on_the_right_ratios P;
 put_on_the_upper_right_ratios P;
 unify_signed_areas_point P.


Lemma test_1 : forall A B C, S A B C + S B A C = 0.
Proof.
intros.
unify_signed_areas_and_put_on_the_right B.
ring.
Qed.

Lemma test_2 : forall Y A C D, parallel Y A C D -> C<>D -> 
 Y**A / C**D = (A**Y / D**C).
Proof.
intros.
put_on_the_right_ratios Y.
reflexivity.
Qed.

Lemma test_3 :forall Y A C D, parallel C D A Y -> A<>Y -> 
C<>D -> C**D / A**Y = 1/(A**Y / C**D).
Proof.
intros.
unify_signed_areas_and_put_on_the_right Y.
reflexivity.
Qed.
