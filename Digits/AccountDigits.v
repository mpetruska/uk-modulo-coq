Require Import Coq.Vectors.Vector.
Require Import Coq.ZArith.ZArith.

Require Import UkModulo.Notations.Vector.

Open Scope Z.
Open Scope vector_scope.

Definition digit : Set := {n : Z | 0 <= n <= 9}.

Definition digit_value (d : digit) : Z := proj1_sig d.

Definition t : Set := Vector.t digit 14.

Definition as_vector_z (d : t) : {r : Vector.t Z 14 | forall m : Fin.t 14, r[@m] = digit_value d[@m]}.
  refine (exist _ (map digit_value d) _).
  intros m; now apply VectorSpec.nth_map.
Defined.

Section Digits.

  Definition digit_check (n : Z) : Prop := 0 <= n <= 9.

  Ltac digit_proof := split; compute; discriminate.

  Lemma digit_0 : 0 <= 0 <= 9. digit_proof. Qed.
  Lemma digit_1 : 0 <= 1 <= 9. digit_proof. Qed.
  Lemma digit_2 : 0 <= 2 <= 9. digit_proof. Qed.
  Lemma digit_3 : 0 <= 3 <= 9. digit_proof. Qed.
  Lemma digit_4 : 0 <= 4 <= 9. digit_proof. Qed.
  Lemma digit_5 : 0 <= 5 <= 9. digit_proof. Qed.
  Lemma digit_6 : 0 <= 6 <= 9. digit_proof. Qed.
  Lemma digit_7 : 0 <= 7 <= 9. digit_proof. Qed.
  Lemma digit_8 : 0 <= 8 <= 9. digit_proof. Qed.
  Lemma digit_9 : 0 <= 9 <= 9. digit_proof. Qed.

  Definition _0 : digit := exist digit_check 0 digit_0.
  Definition _1 : digit := exist digit_check 1 digit_1.
  Definition _2 : digit := exist digit_check 2 digit_2.
  Definition _3 : digit := exist digit_check 3 digit_3.
  Definition _4 : digit := exist digit_check 4 digit_4.
  Definition _5 : digit := exist digit_check 5 digit_5.
  Definition _6 : digit := exist digit_check 6 digit_6.
  Definition _7 : digit := exist digit_check 7 digit_7.
  Definition _8 : digit := exist digit_check 8 digit_8.
  Definition _9 : digit := exist digit_check 9 digit_9.

End Digits.

Section Proofs.

  Theorem digit_value_correct :
       digit_value _0 = 0
    /\ digit_value _1 = 1
    /\ digit_value _2 = 2
    /\ digit_value _3 = 3
    /\ digit_value _4 = 4
    /\ digit_value _5 = 5
    /\ digit_value _6 = 6
    /\ digit_value _7 = 7
    /\ digit_value _8 = 8
    /\ digit_value _9 = 9.
  Proof.
    repeat (split; auto).
  Qed.

  Definition a : t :=
    [ _0; _8; _9; _9; _9; _9;
      _6; _6; _3; _7; _4; _9; _5; _8 ].

End Proofs.
