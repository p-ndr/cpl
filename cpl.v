(* Import Nat. *)

Require Import List.
Import List.ListNotations.

Definition atomic := nat.

Inductive formula : Type :=
| atom : atomic -> formula
| conjunction : formula -> formula -> formula
| disjunction : formula -> formula -> formula
| arrow : formula -> formula -> formula
| negation : formula -> formula
| top : formula
| bot : formula.

Notation "⊥" := bot (at level 200).
Notation "⊤" := top (at level 200).

Definition context : Type := list formula. 

Fixpoint eqf (A B : formula) : bool :=
    match A, B with
    | (atom a), (atom b) => PeanoNat.Nat.eqb a b
    | (conjunction a a'), (conjunction b b') => andb (eqf a b) (eqf a' b')
    | (disjunction a a'), (disjunction b b') => andb (eqf a b) (eqf a' b')
    | (arrow a a'), (arrow b b') => andb (eqf a b) (eqf a' b')
    | (negation a), (negation b) => (eqf a b)
    | top, top => true 
    | bot, bot => true 
    | _, _ => false 
    end.

Fixpoint checkprop (A : formula) (Γ : context) : bool :=
    match Γ with
    | nil => false 
    | x :: l => if (eqf A x) then true else (checkprop A l)
    end.

Inductive NP : context -> formula -> Prop :=
| axiom : forall (Γ : context) (A : formula), (checkprop A Γ = true) -> (NP Γ A)
| ande_left : forall (Γ : context) (A B : formula), (NP Γ (conjunction A B)) -> (NP Γ A)
| ande_right : forall (Γ : context) (A B : formula), (NP Γ (conjunction A B)) -> (NP Γ B)
| andi : forall (Γ : context) (A B : formula), (NP Γ A) -> (NP Γ B) -> (NP Γ (conjunction A B))
| ore : forall (Γ : context) (A B C : formula),
        (NP (A :: Γ) C) -> (NP (B :: Γ) C) -> (NP ((disjunction A B) :: Γ) C)

| ori_left : forall (Γ : context) (A B : formula), (NP Γ A) -> (NP Γ (disjunction A B))
| ori_right : forall (Γ : context) (A B : formula), (NP Γ B) -> (NP Γ (disjunction A B))
| MP : forall (Γ : context) (A B : formula), (NP Γ A) -> (NP Γ (arrow A B)) -> (NP Γ B)
| arrowi : forall (Γ : context) (A B : formula), (NP (A :: Γ ) B) -> (NP Γ (arrow A B))
| eneg : forall (Γ : context) (A : formula), (NP Γ A) -> (NP Γ (negation A)) -> (NP Γ (⊥))
| ineg : forall (Γ : context) (A : formula), (NP (A :: Γ) (⊥)) -> (NP Γ (negation A))
| RAA : forall (Γ : context) (A : formula), (NP ((negation A) :: Γ) (⊥)) -> (NP Γ A)
| ibot : forall (Γ : context) (A : formula), (NP Γ (⊥)) -> (NP Γ A).

Infix "⊢" := NP (at level 100).

(* Lemma membership_preservation

Lemma weakening : forall (A B: formula) (Γ : context),
    (Γ ⊢ A) -> ((B :: Γ) ⊢ A).
    Proof. intros A B Γ. intros. induction H.
    - apply axiom in H.  *)