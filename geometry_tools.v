(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.*)
(* Julien Narboux (Julien.Narboux@inria.fr)                                     *)
(* LIX/INRIA FUTURS 2004-2006                                                     *)
(***************************************************************************)

Require Export geometry_tools_lemmas.
Require Export my_field_tac.
Import F_scope.

(***********************************************)
(* Unification tactic for signed areas         *)
(***********************************************)
(* Simplification is necessary for termination *)
(***********************************************)

Ltac unify_signed_areas_goal :=
  repeat
   match goal with
   |  |- context [(- - ?X1)] =>
       replace (- - X1) with X1 by apply simplring1
   |  |- context [(S ?X1 ?X1 ?X2)] =>
       replace (S X1 X1 X2) with 0 by apply trivial_col1
   |  |- context [(S ?X2 ?X1 ?X1)] =>
       replace (S X2 X1 X1) with 0 by apply trivial_col2
   |  |- context [(S ?X1 ?X2 ?X1)] =>
       replace (S X1 X2 X1) with 0 by apply trivial_col3
   |  |- context [(S ?X1 ?X2 ?X3)] =>
    ( let Truc := fresh in
    match goal with
       |  |- context [(S ?X4 ?X5 ?X6)] =>
            (assert (Truc : S X4 X5 X6 = - S X1 X2 X3);
             [ apply S_3 || apply S_2 || apply S_4
             | rewrite Truc; clear Truc ]) ||
             (assert (Truc : S X4 X5 X6 = S X1 X2 X3);
               [ apply S_0 || apply S_1 | rewrite Truc; clear Truc ])
       end)
   end.

Ltac generalize_all_areas :=
   repeat match goal with
          H: context [(S ?X1 ?X2 ?X3)] |- _=> revert H
 end.

Ltac unify_signed_areas :=
  generalize_all_areas;unify_signed_areas_goal;intros.


Lemma S4Simpl_1 : forall A B C : Point, S4 A B B C = S A B C.
intros.
unfold S4 in |- *.
unify_signed_areas.
ring.
Qed.

Lemma S4Simpl_2 : forall A B C : Point, S4 A B C C = S A B C.
intros.
unfold S4 in |- *.
unify_signed_areas.
ring.
Qed.

Lemma S4Simpl_3 : forall A B C : Point, S4 A A B C = S A B C.
intros.
unfold S4 in |- *.
unify_signed_areas.
ring.
Qed.

Lemma S4Simpl_4 : forall A B C : Point, S4 A B C A = S A B C.
intros.
unfold S4 in |- *.
unify_signed_areas.
ring.
Qed.


Lemma S4Simpl_5 : forall A C D : Point, S4 C A D A = 0.
Proof.
intros.
unfold S4 in |- *.
unify_signed_areas.
ring.
Qed.

Lemma S4Simpl_6 : forall A C D : Point, S4 A C A D = 0.
Proof.
intros.
unfold S4 in |- *.
unify_signed_areas.
ring.
Qed.


Ltac unify_signed_areas4_goal :=
  repeat
   match goal with
   |  |- context [(- - ?X1)] =>      
       replace (- - X1) with X1; [ idtac | apply simplring1 ]
   |  |- context [(S4 ?X1 ?X2 ?X1 ?X3)] =>
       assert (Truc : S4 X1 X2 X1 X3 = 0);
        [ apply S4Simpl_6 | rewrite Truc; clear Truc ]
   |  |- context [(S4 ?X2 ?X1 ?X3 ?X1)] =>
       assert (Truc : S4 X2 X1 X3 X1 = 0);
        [ apply S4Simpl_5 | rewrite Truc; clear Truc ]
   |  |- context [(S4 ?X1 ?X2 ?X2 ?X3)] =>
       assert (Truc : S4 X1 X2 X2 X3 = S X1 X2 X3);
        [ apply S4Simpl_1 | rewrite Truc; clear Truc ]
   |  |- context [(S4 ?X1 ?X2 ?X3 ?X3)] =>
       assert (Truc : S4 X1 X2 X3 X3 = S X1 X2 X3);
        [ apply S4Simpl_2 | rewrite Truc; clear Truc ]
   |  |- context [(S4 ?X1 ?X1 ?X2 ?X3)] =>
       assert (Truc : S4 X1 X1 X2 X3 = S X1 X2 X3);
        [ apply S4Simpl_3 | rewrite Truc; clear Truc ]
   |  |- context [(S4 ?X1 ?X2 ?X3 ?X1)] =>
       assert (Truc : S4 X1 X2 X3 X1 = S X1 X2 X3);
        [ apply S4Simpl_4 | rewrite Truc; clear Truc ]
   |  |- context [(S4 ?X1 ?X2 ?X3 ?X4)] =>
       match goal with
       |  |- context [(S4 ?X5 ?X6 ?X7 ?X8)] =>
           (assert (Truc : S4 X5 X6 X7 X8 = - S4 X1 X2 X3 X4);
             [ apply S4_5 || apply S4_6 || apply S4_7 || apply S4_8
             | rewrite Truc; clear Truc ]) ||
             (assert (Truc : S4 X5 X6 X7 X8 = S4 X1 X2 X3 X4);
               [ apply S4_2 || apply S4_3 || apply S4_4
               | rewrite Truc; clear Truc ])
       end
   end.

Ltac generalize_all_areas4 :=
   repeat match goal with
          H: context [(S4 ?X1 ?X2 ?X3 ?X4)] |- _=> revert H
 end.

Ltac unify_signed_areas4 :=
  generalize_all_areas4;unify_signed_areas4_goal;intros.




(****************************************)
(* Signed distance unification tactic   *)
(****************************************)

Ltac unify_dirseg_goal :=
  repeat
   match goal with
   |  |- context [(- - ?X1)] =>
       replace (- - X1) with X1; [ idtac | apply simplring1 ]
   |  |- context [(?X1 ** ?X1)] =>
       replace (X1 ** X1) with 0; [ idtac | apply nuldirseg ]
   |  |- context [(?X1 ** ?X2)] =>
       match goal with
       |  |- context [(?X3 ** ?X4)] =>
           match constr:(X3, X4) with
           | (?X2, ?X1) =>
               assert (Truc : X1 ** X2 = - X2 ** X1);
                [ apply A1a | rewrite Truc; clear Truc ]
           end
       end
   end.

Ltac generalize_all_seg :=
   repeat match goal with
          H: context [(?X1 ** ?X2)] |- _=> revert H
 end.

Ltac unifydirseg :=
  generalize_all_seg;unify_dirseg_goal;intros.

(*************************)
(* Simplification tactic *)
(*************************)

Ltac basic_geometric_simpl_goal :=
  let Truc := fresh in (
  repeat
   match goal with
 (* Geometric quantities simplifications *)
  | _:_ |- context [(?X2 ** ?X2)] =>
       replace (X2 ** X2) with 0; [ idtac | apply nuldirseg ]
   | _:_ |- context [(S ?X2 ?X2 ?X1)] =>
       replace (S X2 X2 X1) with 0; [ idtac | symmetry  in |- *; Geometry ]
   | _:_ |- context [(S ?X2 ?X1 ?X2)] =>
       replace (S X2 X1 X2) with 0; [ idtac | symmetry  in |- *; Geometry ]
   | _:_ |- context [(S ?X1 ?X2 ?X2)] =>
       replace (S X1 X2 X2) with 0; [ idtac | symmetry  in |- *; Geometry ]
   |  |- context [(S4 ?X1 ?X2 ?X1 ?X3)] =>
       assert (Truc : S4 X1 X2 X1 X3 = 0);
        [ apply S4Simpl_6 | rewrite Truc; clear Truc ]
   |  |- context [(S4 ?X2 ?X1 ?X3 ?X1)] =>
       assert (Truc : S4 X2 X1 X3 X1 = 0);
        [ apply S4Simpl_5 | rewrite Truc; clear Truc ]
   |  |- context [(S4 ?X1 ?X2 ?X2 ?X3)] =>
       assert (Truc : S4 X1 X2 X2 X3 = S X1 X2 X3);
        [ apply S4Simpl_1 | rewrite Truc; clear Truc ]
   |  |- context [(S4 ?X1 ?X2 ?X3 ?X3)] =>
       assert (Truc : S4 X1 X2 X3 X3 = S X1 X2 X3);
        [ apply S4Simpl_2 | rewrite Truc; clear Truc ]
   |  |- context [(S4 ?X1 ?X1 ?X2 ?X3)] =>
       assert (Truc : S4 X1 X1 X2 X3 = S X1 X2 X3);
        [ apply S4Simpl_3 | rewrite Truc; clear Truc ]
   |  |- context [(S4 ?X1 ?X2 ?X3 ?X1)] =>
       assert (Truc : S4 X1 X2 X3 X1 = S X1 X2 X3);
        [ apply S4Simpl_4 | rewrite Truc; clear Truc ]
 
  (* Arithmetic simplifications *)
(*   | _:_ |- context [(1 * ?X1)] =>
       rewrite simp_3 in *
(*       assert (Truc : 1 * X1 = X1); [ ring | rewrite Truc; clear Truc ] *)
   | _:_ |- context [(?X1 * 1)] =>
       assert (Truc : X1 * 1 = X1); [ ring | rewrite Truc; clear Truc ]
   | _:_ |- context [(0 * ?X1)] =>
       assert (Truc : 0 * X1 = 0); [ ring | rewrite Truc; clear Truc ]
   | _:_ |- context [(?X1 * 0)] =>
       assert (Truc : X1 * 0 = 0); [ ring | rewrite Truc; clear Truc ]
   | _:_ |- context [(0 + ?X1)] =>
       assert (Truc : 0 + X1 = X1); [ ring | rewrite Truc; clear Truc ]
   | _:_ |- context [(?X1 + 0)] =>
       assert (Truc : X1 + 0 = X1); [ ring | rewrite Truc; clear Truc ]
   | _:_ |- context [(0 - ?X1)] =>
       assert (Truc : 0 - X1 = - X1); [ ring | rewrite Truc; clear Truc ]
   | _:_ |- context [(?X1 - 0)] =>
       assert (Truc : X1 - 0 = X1); [ ring | rewrite Truc; clear Truc ]
   | _:_ |- context [(?X1 - ?X1)] =>
       assert (Truc : X1 - X1 = 0); [ ring | rewrite Truc; clear Truc ] 
   | _:_ |- context [(-?X1 + ?X1)] =>
       assert (Truc : -X1 + X1 = 0); [ ring | rewrite Truc; clear Truc ]
  | _:_ |- context [(?X1 + -?X1)] =>
       assert (Truc : X1 + -X1 = 0); [ ring | rewrite Truc; clear Truc ] 
  | _:_ |- context [(?X1 + -?X2)] =>
       assert (Truc : X1 + -X2 = X1 - X2); [ ring | rewrite Truc; clear Truc ]
  |_:_ |- context [(- (0))] =>
       assert (Truc : - (0) = 0); [ ring | rewrite Truc; clear Truc ]
  |_:_ |- context [(- - ?X1)] =>
       assert (Truc : - - X1 = X1); [ ring | rewrite Truc; clear Truc ]
  | _:_ |- context [(-?X1 * -?X2)] =>
       assert (Truc : -X1 * -X2 = X1 * X2); [ ring | rewrite Truc; clear Truc ]
  | _:_ |- context [(-?X1 * ?X2)] =>
       assert (Truc : -X1 * X2 = -(X1 * X2)); [ ring | rewrite Truc; clear Truc ]
  | _:_ |- context [(?X1 * -?X2)] =>
       assert (Truc : X1 * -X2 = -(X1 * X2)); [ ring | rewrite Truc; clear Truc ] *)
  | _:_ |- context [(1 - 1 / 2)] =>
       assert (Truc : 1 - 1 / 2 = 1 / 2);
        [ field; Geometry | rewrite Truc; clear Truc ]

    end).

Ltac generalize_all_eq :=
   repeat match goal with
          H: context [?X1 = ?X2] |- _=> revert H
 end.

Ltac basic_non_field_simpl :=
  generalize_all_eq;
  repeat (progress (basic_geometric_simpl_goal;autorewrite with ring_simplification));
  intros.

(* We define another tactic for field simplifications because we need to perform simplifications
in the goal and in the hypotheses at the same time.
We can not do the "generalize" trick
because we need to keep the non nullity hypotheses in the context. *)
(*
Ltac basic_field_simpl :=
 let Truc := fresh in (
  repeat
   match goal with
  |  |- context [?X1 / ?X1] =>
           assert (Truc : X1 / X1 = 1);[ (field;assumption) | rewrite Truc; clear Truc ]
  |  |- context [(-?X1) / ?X1] =>
           assert (Truc : (-X1) / X1 = -(1));[ (field;assumption) | rewrite Truc; clear Truc ]
  |  |- context [?X1 / (-?X1)] =>
           assert (Truc : X1 / (-X1) = -(1));[ (field;assumption) | rewrite Truc; clear Truc ]  
  |  |- context [(-?X1) / (-?X1)] =>
           assert (Truc : (-X1) / (-X1) = 1);[ (field;assumption) | rewrite Truc; clear Truc ]
  |  |- context [(-?X1) / ?X2] =>
           assert (Truc : (-X1) / X2 = -(X1 / X2));[ (field;assumption) | rewrite Truc; clear Truc ]
  |  |- context [0 / ?X1] =>
           assert (Truc : 0 / X1 = 0);[ (field;assumption) | rewrite Truc; clear Truc ]
  |  |- context [(?X1 * ?X2) / ?X1] =>
           assert (Truc : (X1*X2) / X1 = X2);[ (field;assumption) | rewrite Truc; clear Truc ]
  |  |- context [(?X1 * ?X2) / ?X2] =>
           assert (Truc : (X1*X2) / X2 = X1);[ (field;assumption) | rewrite Truc; clear Truc ]
  |  |- context [?X1 * (1/ ?X1)] =>
           assert (Truc : X1 * (1 / X1) = 1);
        [ field;Geometry | rewrite Truc; clear Truc ]
 (* We duplicate the rules for the context *)
  | H:context [?X1 / ?X1] |- _ =>
           assert (Truc : X1 / X1 = 1);[ (field;assumption) | rewrite Truc in H; clear Truc ]
  | H:context [(-?X1) / ?X1] |- _ =>
           assert (Truc : (-X1) / X1 = -(1));[ (field;assumption) | rewrite Truc in H; clear Truc ]
  | H:context [?X1 / (-?X1)] |- _ =>
           assert (Truc : X1 / (-X1) = -(1));[ (field;assumption) | rewrite Truc in H; clear Truc ]
  | H:context [(-?X1) / (-?X1)] |- _ =>
           assert (Truc : (-X1) / (-X1) = 1);[ (field;assumption) | rewrite Truc in H; clear Truc ]
  | H:context [(-?X1) / ?X2] |- _ =>
           assert (Truc : (-X1) / X2 = -(X1 / X2));[ (field;assumption) | rewrite Truc in H; clear Truc ]
  | H:context [0 / ?X1] |- _ =>
           assert (Truc : 0 / X1 = 0);[ (field;assumption) | rewrite Truc in H; clear Truc ]
  | H:context [(?X1 * ?X2) / ?X1] |- _ =>
           assert (Truc : (X1*X2) / X1 = X2);[ (field;assumption) | rewrite Truc in H; clear Truc ]
  | H:context [(?X1 * ?X2) / ?X2] |- _ =>
           assert (Truc : (X1*X2) / X2 = X1);[ (field;assumption) | rewrite Truc in H; clear Truc ]
  | H:context [?X1 * (1/ ?X1)] |- _=>
           assert (Truc : X1 * (1 / X1) = 1);
        [ field;Geometry | rewrite Truc; clear Truc ]
   end).
*)

Ltac basic_simpl := repeat (progress (basic_non_field_simpl;basic_field_simpl)).


