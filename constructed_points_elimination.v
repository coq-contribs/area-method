(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien.Narboux@inria.fr)                                *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(***************************************************************************)

Require Export ratios_elimination_lemmas.
Require Export elimination_prepare.

Import F_scope.

(*
Ltac decomposeallconstructions :=
  repeat
   match goal with
   | H:context [(on_line ?X1 ?X2 ?X3)] |- _ =>
       unfold on_line in H; unfold Col in H; decompose [and] H; clear H
   | H:context [(on_line_d ?X1 ?X2 ?X3 ?X4)] |- _ =>
       unfold on_line_d in H; unfold Col in H; decompose [and] H; clear H
   | H:context [(inter_ll ?X1 ?X2 ?X3 ?X4 ?X5)] |- _ =>
       unfold inter_ll in H; unfold parallel in H; decompose [and] H; clear H
   | H:context [(on_parallel ?X1 ?X2 ?X3 ?X4)] |- _ =>
       unfold on_parallel in H; unfold parallel in H; decompose [and] H; clear H
   | H:context [(on_parallel_d ?X1 ?X2 ?X3 ?X4 ?X5)] |- _ =>
       unfold on_parallel_d in H; unfold parallel in H; decompose [and] H; clear H
   | H:context [(on_inter_line_parallel ?X1 ?X2 ?X3 ?X4 ?X5 ?X6)] |- _ =>
       unfold on_inter_line_parallel in H; unfold parallel in H; decompose [and] H; clear H
   | H:context [(on_inter_parallel_parallel ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7)] |- _ =>
       unfold on_inter_parallel_parallel in H; unfold parallel in H; decompose [and] H; clear H
   end;
   repeat
    match goal with
    | H:context [(Col ?X1 ?X2 ?X3)] |- _ => unfold Col in H
    end; unify_signed_areas4; unify_signed_areas.
*)

Ltac elimi_inter_ll_col  A C D U V P Q Y H  Hdenom Hpar Hneq HCol :=  
  let T1 := fresh in 
  (assert 
  (T1 :=non_zero_denom_inter_ll_2_length_ratio  A C D U V P Q Y H HCol Hdenom Hneq Hpar);
   rewrite_all
             (elim_length_ratio_inter_ll_2 A C D U V P Q Y H HCol Hdenom Hpar Hneq)).
 
Ltac elimi_inter_ll_not_col  A C D U V P Q Y H  Hdenom Hpar HCol :=  
  let T1 := fresh in 
  (assert 
  (T1 :=non_zero_denom_inter_ll_1_length_ratio  A C D U V P Q Y H HCol Hpar Hdenom);
   rewrite_all
             (elim_length_ratio_inter_ll_1 A C D U V P Q Y H HCol Hdenom Hpar)).

(** In the collinear case we don't have a special formula *)
Ltac elimi_inter_ll_col_spec A C D U V P Q Y H  Hdenom Hpar HCol := 
elimi_inter_ll_col A C D U V P Q Y H  Hdenom Hpar HCol.

Ltac elimi_inter_ll_not_col_spec A C D U V P Q Y H  Hdenom Hpar HCol :=  
  rewrite_all (elim_length_ratio_inter_ll_1_spec A C U V P Q Y H HCol Hdenom Hpar).
 
Ltac test_equality_and_subst Hc A B Tac := 
 match goal with 
| H : A = B |- _ => rewrite_all_inv H;rewrite H in Hc
| H : A<>B |- _ => Tac H
| _ => let H := fresh in 
      (named_cases_equality A B H;
   [ rewrite_all_inv H;rewrite H in Hc | Tac H])
end.

Ltac elimi_inter_ll_gen  P Q U V A Y C D H Hneq :=
    let Hdenom := HypOfType (C <> D) in
    let Hpar := HypOfType (parallel A Y C D) in
              test_col  A U V 
              ltac: (elimi_inter_ll_col A C D U V P Q Y H Hdenom Hpar Hneq)
              ltac: (elimi_inter_ll_not_col A C D U V P Q Y H Hdenom Hpar).

Ltac elimi_inter_ll P Q U V A Y C D H :=
  let Hi := fresh in
  (assert (Hi : C <> D); [ Geometry | idtac ];
    match constr:(A, (C, D)) with
(** In the first cases we know the points are collinear *)
    | (U, (V, Y)) =>
        let Hfresh := fresh in
        assert (Hfresh := aux_co_side_1 P Q U V Y Hi H);
        rewrite_all (co_side_elim_1 P Q U V Y  Hi H);clear Hi
    | (V, (U, Y)) =>
        let Hfresh := fresh in
        assert (Hfresh := aux_co_side_2 P Q U V Y Hi H);
        rewrite_all (co_side_elim_2 P Q U V Y  Hi H);clear Hi
    | (P, (Q, Y)) =>
        let Hfresh := fresh in
        assert (Hfresh := aux_co_side_3 P Q U V Y Hi H);
        rewrite_all (co_side_elim_3 P Q U V Y  Hi H);clear Hi
    | (Q, (P, Y)) =>
        let Hfresh := fresh in
        assert (Hfresh := aux_co_side_4 P Q U V Y Hi H);
        rewrite_all (co_side_elim_4 P Q U V Y  Hi H);clear Hi
(** In the other cases we have to perform classical reasoning. *)
   | (A,(C,Y)) =>
              let Hdenom := HypOfType (C <> D) in
              let Hpar := HypOfType (parallel A Y C D) in
              test_col  A U V 
              ltac: (elimi_inter_ll_col_spec)
              ltac: (elimi_inter_ll_not_col_spec A C D U V P Q Y H  Hdenom Hpar)
(** The most general case *)
   | _ =>  
         test_equality_and_subst H A Y ltac: (elimi_inter_ll_gen P Q U V A Y C D H )
   
end).

(** on_line_d : elimination in length ratio in the case Col *)

Ltac elimi_on_line_d_col_aux P Q lambda A Y C D H Hdenom Hpar HCol Hdiff :=
let T3 := fresh in (assert
            (T3 :=
             invariant_par_on_line_d_1_length_ratio_2 A C D P Q Y lambda H HCol Hdiff Hpar);
            rewrite_all
             (elim_length_ratio_on_line_d_1 A C D P Q Y lambda H HCol Hdenom)).

Ltac elimi_on_line_d_col P Q lambda A Y C D H Hdenom Hpar HCol:=
let T1 := fresh in
(assert (T1 := non_zero_denom_on_line_d_1_length_ratio Y P Q lambda H);
let T2 := fresh in
(assert (T2 := invariant_par_on_line_d_1_length_ratio A C D P Q Y lambda H HCol Hpar);
let T4 := fresh in
(assert (T4 :=invariant_par_on_line_d_1_length_ratio_3 A C D P Q Y lambda H HCol Hpar);
test_equality_and_subst H A Y
ltac:(elimi_on_line_d_col_aux P Q lambda A Y C D H Hdenom Hpar HCol) 
  ))).
 
(** on_line_d : elimination in length ratio in the case not Col *)

Ltac elimi_on_line_d_not_col  P Q lambda A Y C D H Hdenom Hpar HCol :=
let T := fresh in
      (assert
        (T :=
         non_zero_denom_on_line_d_2_length_ratio A C D P Q Y lambda H HCol Hpar Hdenom);
        rewrite_all
         (elim_length_ratio_on_line_d_2 A C D P Q Y lambda H HCol Hdenom Hpar)).

Ltac elimi_on_line_d P Q lambda A Y C D H :=
  let Hdenom := HypOfType (C <> D) in
  let Hpar := HypOfType (parallel A Y C D) in
  test_col  A P Q 
  ltac: (elimi_on_line_d_col P Q lambda A Y C D H Hdenom Hpar)
  ltac: (elimi_on_line_d_not_col P Q lambda A Y C D H Hdenom Hpar).

(** on_parallel_d : elimination in length ratio *)

Ltac elimi_on_parallel_d_col_aux_2 R P Q lambda A Y C D H Hdenom Hpar HCol Hneq Hneq2 :=
 let T1 := fresh in
      (assert
        (T1 := non_zero_denom_on_parallel_d_1_length_ratio A C D P Q R Y lambda H HCol);
        let T2 := fresh in
        (assert
          (T2 :=
           invariant_par_on_parallel_d_1_length_ratio A C D P Q R Y lambda H HCol Hneq Hpar);
          let T3 := fresh in
          (assert
            (T3 :=
             invariant_par_on_parallel_d_1_length_ratio_2 A C D P Q R Y lambda H HCol Hneq
             Hneq2 Hpar);
            rewrite_all
             (elim_length_ratio_on_parallel_d_1 A C D P Q R Y lambda H HCol Hdenom)))).

(** There are two case-distinctions on point equality *)

Ltac elimi_on_parallel_d_col_aux  R P Q lambda A Y C D H Hdenom Hpar HCol Hneq :=
  test_equality_and_subst H A Y
  ltac:(elimi_on_parallel_d_col_aux_2 R P Q lambda A Y C D H Hdenom Hpar HCol Hneq).

Ltac elimi_on_parallel_d_col R P Q lambda A Y C D H Hdenom Hpar HCol :=
   test_equality_and_subst H R Y
    ltac:(elimi_on_parallel_d_col_aux R P Q lambda A Y C D H Hdenom Hpar HCol).

Ltac elimi_on_parallel_d R P Q lambda A Y C D H :=
  let Hdenom := HypOfType (C <> D) in
  let Hpar := HypOfType (parallel A Y C D) in
  let HCol := fresh in
  (named_cases_col A R Y HCol;
    [ elimi_on_parallel_d_col R P Q lambda A Y C D H Hdenom Hpar HCol 
    | let T1 := fresh in
      (assert
        (T1 := non_zero_denom_on_parallel_d_2_length_ratio A C D P Q R Y lambda H Hpar Hdenom HCol);
        rewrite_all
         (elim_length_ratio_on_parallel_d_2 A C D P Q R Y lambda H HCol Hdenom Hpar))  ]).

Ltac elimi_area_on_inter_line_parallel X4 X5 X1 X2 X3 Y X6 X7 H Hneq := 
assert (S4 X4 X2 X5 X3 <> 0);
       [ exact (non_zero_denom_on_inter_line_parallel_area Y X1 X2 X3 X4 X5 H) | idtac ];
       rewrite_all (elim_area_on_inter_line_parallel X4 X5 X1 X2 X3 Y X6 X7 H Hneq).

(* 
We suppose that :
- the goal does not contain degenerated 
signed areas or length ratios 
- the point to eliminate is on the right
*)


Ltac elimi Y :=
  match goal with
  
       (* signed area cases *)
  | H:(on_line_d Y ?X1 ?X2 ?X3) |- context [(S ?X5 ?X6 Y)] =>
      rewrite_all (elim_area_on_line_d X5 X6 X1 X2 Y X3 H)
  | H:(inter_ll Y ?X1 ?X2 ?X3 ?X4) |- context [(S ?X5 ?X6 Y)] =>
      assert (S4 X1 X3 X2 X4 <> 0);
       [ exact (non_zero_denom_inter_ll_area Y X1 X2 X3 X4 H) | idtac ];
       rewrite_all (elim_area_inter_ll X5 X6 X1 X2 X3 X4 Y H)

  | H:(on_parallel_d Y ?X1 ?X2 ?X3 ?X4) |- context [(S ?X5 ?X6 Y)] =>
      rewrite_all (elim_area_on_parallel_d X5 X6 X2 X3 X1 Y X4 H)
  | H:(on_inter_line_parallel Y ?X1 ?X2 ?X3 ?X4 ?X5) |- context [(S ?X6 ?X7 Y)] =>
          test_equality_and_subst H X1 Y ltac:(elimi_area_on_inter_line_parallel X4 X5 X1 X2 X3 Y X6 X7 H )     
(*
let Hneq := fresh in
      (named_cases_equality X1 Y Hneq;[rewrite_all_inv Hneq;rewrite Hneq in H|
	assert (S4 X4 X2 X5 X3 <> 0);
       [ exact (non_zero_denom_on_inter_line_parallel_area Y X1 X2 X3 X4 X5 H) | idtac ];
       rewrite_all (elim_area_on_inter_line_parallel X4 X5 X1 X2 X3 Y X6 X7 H Hneq)]) 
*)

  | H:(on_inter_parallel_parallel Y ?X1 ?X2 ?X3 ?X4 ?X5 ?X6) |- context [(S ?X7 ?X8 Y)] =>
          let Hneq := fresh in
      (named_cases_equality X1 Y Hneq;[rewrite_all_inv Hneq;rewrite Hneq in H|
       assert (S4 X2 X5 X3 X6 <> 0);
       [ exact (non_zero_denom_on_inter_parallel_parallel_area Y X1 X2 X3 X4 X5 X6 H) | idtac ];
       rewrite_all
        (elim_area_on_inter_parallel_parallel X2 X3 X1 X5 X6 X4 Y X7 X8 H Hneq)])        
        
        (* ratios cases *)

  | H:(on_line_d Y ?X1 ?X2 ?X3) |- context [(?X5 ** Y / ?X6 ** ?X7)] =>
      elimi_on_line_d X1 X2 X3 X5 Y X6 X7 H
  | H:(inter_ll Y ?X1 ?X2 ?X3 ?X4) |- context [(?X5 ** Y / ?X6 ** ?X7)] =>
      elimi_inter_ll X1 X2 X3 X4 X5 Y X6 X7 H
  | H:(on_parallel_d Y ?X1 ?X2 ?X3 ?X4) |- context [(?X5 ** Y / ?X6 ** ?X7)] =>
      elimi_on_parallel_d X1 X2 X3 X4 X5 Y X6 X7 H
  | H:(on_inter_line_parallel Y ?X1 ?X2 ?X3 ?X4 ?X8) |- context [(?X5 ** Y / ?X6 ** ?X7)] =>
      fail
  | H:(on_inter_parallel_parallel Y ?X1 ?X2 ?X3 ?X4 ?X8 ?X9) |- context [(?X5 ** Y / ?X6 ** ?X7)] =>
      fail
   end.

Ltac ClearConstructedPointDef Y :=
  match goal with
  | H:(on_line Y _ _) |- _ => clear H
  | H:(on_line_d Y _ _ _) |- _ => clear H
  | H:(inter_ll Y _ _ _ _) |- _ => clear H
  | H:(on_parallel Y _ _ _) |- _ => clear H
  | H:(on_parallel_d Y _ _ _ _) |- _ => clear H
  | H:(on_inter_line_parallel Y _ _ _ _ _) |- _ => clear H
  | H:(on_inter_parallel_parallel Y _ _ _ _ _ _) |- _ => clear H
  end.

(** Warning this definition suppose that we have no extra assumptions *)
(** A constructed point is defined only by its construction *)


Ltac ClearConstructedPointNDG Y :=
  repeat
   match goal with
  | H:(parallel Y _ _ _) |- _ => clear H
  | H:(parallel _ Y _ _) |- _ => clear H
  | H:(parallel _ _ Y _) |- _ => clear H
  | H:(parallel _ _ _ Y) |- _ => clear H
  | H:(_ <> Y) |- _ => clear H
  | H:(Y <> _) |- _ => clear H
end. 


Ltac eliminate_aux Y := 
   unify_signed_areas_and_put_on_the_right Y;
   repeat elimi Y;
   CleanDuplicatedHyps;
   ClearConstructedPointDef Y.
(*   ClearConstructedPointNDG Y. *) 



(** Computes the point that is constructed with A 
and so on until no point is constructed with A *)

Ltac is_used_to_construct A :=
  match goal with
  | H:context [(on_line ?X1 A _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_line ?X1 _ A)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_line_d ?X1 A _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_line_d ?X1 _ A _)] |- _ =>
      is_used_to_construct X1
  | H:context [(inter_ll ?X1 A _ _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(inter_ll ?X1 _ A _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(inter_ll ?X1 _ _ A _)] |- _ =>
      is_used_to_construct X1
  | H:context [(inter_ll ?X1 _ _ _ A)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_parallel ?X1 A _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_parallel ?X1 _ A _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_parallel ?X1 _ _ A)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_parallel_d ?X1 A _ _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_parallel_d ?X1 _ A _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_parallel_d ?X1 _ _ A _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_inter_line_parallel ?X1 A _ _ _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_inter_line_parallel ?X1 _ A _ _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_inter_line_parallel ?X1 _ _ A _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_inter_line_parallel ?X1 _ _ _ A _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_inter_line_parallel ?X1 _ _ _ _ A)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_inter_parallel_parallel ?X1 A _ _ _ _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_inter_parallel_parallel ?X1 _ A _ _ _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_inter_parallel_parallel ?X1 _ _ A _ _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_inter_parallel_parallel ?X1 _ _ _ A _ _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_inter_parallel_parallel ?X1 _ _ _ _ A _)] |- _ =>
      is_used_to_construct X1
  | H:context [(on_inter_parallel_parallel ?X1 _ _ _ _ _ A)] |- _ =>
      is_used_to_construct X1
  | _ => A
  end.

Ltac eliminate A := eliminate_aux A; unfold S4 in *;  basic_simpl.

Ltac Remove_last A :=
   eliminate ltac:(is_used_to_construct A).

Ltac eliminate_All :=
  repeat
   match goal with
   | H:context [(on_line ?X1 _ _)] |- _ =>
       Remove_last X1
   | H:context [(on_line_d ?X1 _ _ _)] |- _ =>
       Remove_last X1
   | H:context [(inter_ll ?X1 _ _ _ _)] |- _ =>
       Remove_last X1
   | H:context [(on_parallel ?X1 _ _ _)] |- _ =>
       Remove_last X1
   | H:context [(on_parallel_d ?X1 _ _ _ _)] |- _ =>
       Remove_last X1
   | H:context [(on_inter_line_parallel ?X1 _ _ _ _ _)] |- _ =>
       Remove_last X1
   | H:context [(on_inter_parallel_parallel ?X1 _ _ _ _ _ _)] |- _ => 
       Remove_last X1
   end.
