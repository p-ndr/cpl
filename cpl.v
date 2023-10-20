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

Notation "⊥" := bot (at level 95).
Notation "⊤" := top (at level 95).
Infix "→" := arrow (at level 90).
Infix "∨" := disjunction (at level 85).
Infix "∧" := conjunction (at level 85).
Notation "¬" := negation (at level 80).


Definition context : Type := list formula. 

Fixpoint eqf (A B : formula) : bool :=
    match A, B with
    | (atom a), (atom b) => PeanoNat.Nat.eqb a b
    | (a ∧ a'), (b ∧ b') => andb (eqf a b) (eqf a' b')
    | (a ∨ a'), (b ∨ b') => andb (eqf a b) (eqf a' b')
    | (a → a'), (b → b') => andb (eqf a b) (eqf a' b')
    | (¬a), (¬b) => (eqf a b)
    | ⊤, ⊤ => true 
    | ⊥, ⊥ => true 
    | _, _ => false 
    end.

Fixpoint checkprop (A : formula) (Γ : context) : bool :=
    match Γ with
    | nil => false 
    | x :: l => if (eqf A x) then true else (checkprop A l)
    end.

Reserved Notation "⊢" (at level 100).

Inductive NP : context -> formula -> Prop :=
| axiom : forall (Γ : context) (A : formula), (checkprop A Γ = true) -> (Γ ⊢ A)
| ande_left : forall (Γ : context) (A B : formula), (Γ ⊢ (A ∧ B)) -> (Γ ⊢ A)
| ande_right : forall (Γ : context) (A B : formula), (Γ ⊢ (A ∧ B)) -> (Γ ⊢ B)
| andi : forall (Γ : context) (A B : formula), (Γ ⊢ A) -> (Γ ⊢ B) -> (Γ ⊢ (A ∧ B))
| ore : forall (Γ : context) (A B C : formula), ((A :: Γ) ⊢ C) -> ((B :: Γ) ⊢ C) -> (((A ∨ B) :: Γ) ⊢ C)

| ori_left : forall (Γ : context) (A B : formula), (Γ ⊢ A) -> (Γ ⊢ (A ∨ B))
| ori_right : forall (Γ : context) (A B : formula), (Γ ⊢ B) -> (NP Γ (A ∨ B))
| MP : forall (Γ : context) (A B : formula), (Γ ⊢ A) -> (Γ ⊢ (A → B)) -> (Γ ⊢ B)
| arrowi : forall (Γ : context) (A B : formula), ((A :: Γ ) ⊢ B) -> (Γ ⊢ (A → B))
| eneg : forall (Γ : context) (A : formula), (Γ ⊢ A) -> (Γ ⊢ (¬A)) -> (Γ ⊢ (⊥))
| ineg : forall (Γ : context) (A : formula), ((A :: Γ) ⊢ (⊥)) -> (Γ ⊢ (¬A))
| RAA : forall (Γ : context) (A : formula), (((¬A) :: Γ) ⊢ (⊥)) -> (Γ ⊢ A)
| ibot : forall (Γ : context) (A : formula), (Γ ⊢ (⊥)) -> (Γ ⊢ A)
where "x ⊢ y" := (NP x y).

(* Lemma membership_preservation

Lemma weakening : forall (A B: formula) (Γ : context),
    (Γ ⊢ A) -> ((B :: Γ) ⊢ A).
    Proof. intros A B Γ. intros. induction H.
    - apply axiom in H.  *)