Require Import Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.
Require Import Coq.ZArith.ZArith.

Require Import UkModulo.Digits.AccountDigits.
Require Import UkModulo.Notations.Vector.

Open Scope Z.
Open Scope vector_scope.

Definition t := Vector.t Z 14.

Definition dot_mul (w : t) (d : AccountDigits.t) : {r : t | forall n : Fin.t 14, r[@n] = w[@n] * (digit_value d[@n])}.
  remember (as_vector_z d)    as d1  eqn: Heqd1.
  remember (proj1_sig d1)     as v   eqn: Heq1.
  remember (proj2_sig d1)     as Hd1 eqn: Heq2.
  remember (fun a b => a * b) as f   eqn: Heqf.
  refine (exist _ (map2 f w v) _).
  intros n.
  rewrite <- (Hd1 n).
  rewrite <- Heq1.
  now apply VectorSpec.nth_map2.
Defined.

Definition sum (weights : t) :
    {total : Z | forall (u v w x y z a b c d e f g h : Z), weights = [u; v; w; x; y; z; a; b; c; d; e; f; g; h] ->
                    total = u + v + w + x + y + z + a + b + c + d + e + f + g + h}.
  refine (exist _ (fold_left Z.add 0 weights) _).
  intros; subst weights.
  now unfold fold_left.
Defined.

Section Sum_digits.

(*  Definition sum_digits : Z -> Z :=
*)

End Sum_digits.
