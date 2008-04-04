(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.*)
(* Julien Narboux (Julien.Narboux@inria.fr)                                     *)
(* LIX/INRIA FUTURS 2004-2006                                                     *)
(***************************************************************************)

Ltac rewrite_all H := 
 match type of H with
 | ?t1 = ?t2 => 
   let rec aux H :=
     match goal with
     | id : context [t1] |- _ => 
       match type of id with 
       | t1 = t2 => fail 1 
       | _ => revert id; try aux H; intro id
       end
     | _ => try rewrite H
     end in
   aux H
 end.

Ltac rewrite_all_inv H := 
 match type of H with
 | ?t1 = ?t2 => 
   let rec aux H :=
     match goal with
     | id : context [t2] |- _ => 
       match type of id with 
       | t1 = t2 => fail 1 
       | _ => revert id; try aux H; intro id
       end
     | _ => try rewrite <- H
     end in
   aux H
 end.

Ltac replace_all term1 term2 :=
let Hn := fresh in 
 (cut (term2=term1);[intro Hn;rewrite <- Hn;rewrite_all_inv Hn; clear Hn|idtac]).


Ltac ExistHyp t := match goal with
                   | H1:t |- _ => idtac
                   end.

Ltac HypOfType t := match goal with
                    | H1:t |- _ => H1
                    end.

Ltac CleanDuplicatedHyps :=
  repeat match goal with
         | H:?X1 |- _ => clear H; ExistHyp X1
         end.

Ltac not_exist_hyp t := match goal with
  | H1:t |- _ => fail 2
 end || idtac.

Ltac assert_if_not_exist H :=
  not_exist_hyp H;assert H.


Ltac suppose t := cut t;[intro|idtac].


Ltac DecompEx H P := elim H;intro P;intro;clear H.

Ltac DecompExAnd H P :=
  elim H;intro P;
  let id:=fresh in intro id;decompose [and] id;clear id;clear H.

Ltac DecompAndAll :=
 repeat
 match goal with
   | H:(?X1 /\ ?X2) |- _ => decompose [and] H;clear H
end.
