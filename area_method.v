(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.         *)
(* Julien Narboux (Julien.Narboux@inria.fr)                                              *)
(* LIX/INRIA FUTURS 2004-2006                                                            *)
(***************************************************************************)

Require Export general_tactics.
Require Export Rgeometry_tools.
Require Export constructed_points_elimination.
Require Export free_points_elimination.
Require Export simplify_constructions.
Require Export construction_tactics.
(* Require Export NField_tac.*)
Require Export my_field_tac.

Import F_scope.

(*
Ltac kill_not_eq :=
   (match goal with
     | H: ?X <> F0 |- _  =>
        ((let tmp := fresh in
          ( intros tmp; case H; rewrite <- tmp); newring; fail) ||
        clear H); kill_not_eq
   end).

Ltac kill_cond_tac :=
   repeat (remove_hyp_div_not_eq_zero; repeat split; auto; try Geometry);
   try newfield; (repeat split); auto; try Geometry;
   try split_goal_not_eq_zero; auto; unfold_field; kill_not_eq.


Ltac field_and_conclude :=  
abstract kill_cond_tac.
*)

Ltac old_field_and_conclude := 
  abstract (field; repeat assumption || apply nonzeromult; Geometry).

Ltac field_and_conclude := abstract Ffield.

Ltac DecomposeMratio :=
  repeat
   match goal with
   | H:(mratio _ _ _ _) |- _ =>
       unfold mratio in H; decompose [and] H; clear H
   end.

(** This tactic change 
on_line into on_line_d
on_parallel into on_parallel_d 
by setting the distance as a parameter.*)
(** This has the advantage to reduce the number of cases 
in the elimination process and to ease the development because
then all constructed point can be eliminated, otherwise we get ratios such
as A**Y/C**D which are parameters of the problem, here Y can not be eliminated. *)


Ltac prepare_half_free_construction :=
repeat  match goal with
   | H:(on_line ?X1 ?X2 ?X3) |- _ => 
    let T:= fresh in 
    (assert (T:=(on_line_to_on_line_d X1 X2 X3 H));clear H;set ((X2**X1)/(X2**X3)) in * )
   | H:(on_parallel ?X1 ?X2 ?X3 ?X4) |- _ =>    
    let T:= fresh in (assert (T:=(on_parallel_to_on_parallel_d X1 X2 X3 X4 H));clear H;set ((X2**X1)/(X3**X4)) in *)
end.

Ltac add_non_zero_hyps :=
 repeat
 match goal with 
   | H:?A<>?B |- _ =>  
           assert_if_not_exist (A**B<>0);[apply neq_not_zero;assumption|revert H]
end;intros.

Ltac geoInit :=
  unfold is_midpoint in * |- *; intros; unfold parallel,S4 in |- *;unfold Col in *;  DecomposeMratio;
  prepare_half_free_construction;add_non_zero_hyps; put_on_inter_line_parallel;repeat split.

Ltac am_before_field :=  geoInit; eliminate_All;
  Runify_signed_areas;basic_simpl.

Ltac set_all := repeat
   match goal with
   | H:context[(S ?X1 ?X2 ?X3)] |- _ => set (S X1 X2 X3) in *
   | _:_ |- context[(S ?X1 ?X2 ?X3)] => set (S X1 X2 X3) in *
   end.

Ltac area_method := am_before_field;
   solve [intuition idtac] || (solve [set_all; field_and_conclude ] || (only_use_area_coordinates;set_all; field_and_conclude)).











