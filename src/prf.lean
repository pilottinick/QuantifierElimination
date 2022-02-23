import language

namespace first_order

section prf

variables {L : language}

inductive Prf : list (formula L) → formula L → Prop
| Axiom : ∀ {Γ : list _} n φ, Γ.nth n = some φ → Prf Γ φ
| Bot_elim : ∀ {Γ} φ, Prf Γ F → Prf Γ φ
| Not_elim : ∀ {Γ} φ ψ, Prf Γ φ → Prf Γ ∼φ → Prf Γ ψ
| By_contradiction : ∀ {Γ} φ, Prf (∼φ::Γ) F → Prf Γ φ
| Or_intro_left : ∀ {Γ} φ ψ, Prf Γ φ → Prf Γ (φ or ψ)
| Or_intro_right : ∀ {Γ} φ ψ, Prf Γ ψ → Prf Γ (φ or ψ)
| Or_elim : ∀ {Γ} φ ψ χ, Prf Γ (φ or ψ) → Prf (φ::Γ) χ → Prf (ψ::Γ) χ → Prf Γ χ
| Cut : ∀ {Γ} φ ψ, Prf Γ φ → Prf (φ::Γ) ψ → Prf Γ ψ

open Prf

/- Using ⊢ doesn't compile -/
infix ` ▸ ` := Prf

notation φ` ▸ `ψ := Prf (φ::[]) ψ

notation ` ▸ `φ := Prf list.nil φ

variables {p q r : formula L}

variables {Γ γ : list (formula L)}

example : p ▸ (p or q) := begin
    apply Or_intro_left,
    apply Axiom 0, refl,
  end

lemma nth_append_some : ∀ {A : Type} {l1 l2 : list A} n x, l1.nth n = some x → (l1 ++ l2).nth n = some x
| A (y :: l1) l2 0 x h := h
| A (y :: l1) l2 (n+1) x h := @nth_append_some A l1 l2 n x h

lemma nth_cons_some : ∀ {A : Type} {l1 l2 : list A},
  (∀ n x, l1.nth n = some x → ∃ m, l2.nth m = some x) -> ∀ y,
  (∀ n x, (y :: l1).nth n = some x → ∃ m, (y :: l2).nth m = some x) :=
  begin
    intros, cases n, { existsi 0, assumption },
    { simp at *, cases (ᾰ _ _ ᾰ_1),
        existsi w.succ, assumption },
  end

def weakening : (forall n x, γ.nth n = some x -> ∃ m, Γ.nth m = some x) →
  γ ▸ p → Γ ▸ p := begin
    intros h γp, revert Γ h,
    induction γp, all_goals { intros Γ h },
      { cases (h _ _ γp_ᾰ), apply Axiom, assumption, },
      apply Bot_elim, apply γp_ih, assumption,
      apply Not_elim,
        { apply γp_ih_ᾰ, assumption },
        { apply γp_ih_ᾰ_1, assumption },
      apply By_contradiction, apply γp_ih, apply nth_cons_some, assumption,
      apply Or_intro_left, apply γp_ih, assumption,
      apply Or_intro_right, apply γp_ih, assumption,
      apply Or_elim,
        { apply γp_ih_ᾰ, assumption },
        { apply γp_ih_ᾰ_1, apply nth_cons_some, assumption },
        { apply γp_ih_ᾰ_2, apply nth_cons_some, assumption },
      apply Cut,
        { apply γp_ih_ᾰ, assumption },
        { apply γp_ih_ᾰ_1, apply nth_cons_some, assumption },
  end

def weakening_append : (γ ▸ p) → ((γ ++ Γ) ▸ p) := begin
    apply weakening,
    intros, existsi n,
    apply nth_append_some, assumption,
  end

def Impl_elim_ : [p, p ⇒ q] ▸ q := begin
    apply Or_elim,
    apply Axiom 1, refl,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
    apply Axiom 0, refl,
  end

def Impl_elim : (Γ ▸ p) → (Γ ▸ (p ⇒ q)) → (Γ ▸ q) := begin
    assume H1 H2,
    apply Cut,
      apply H1,
      apply Cut,
        apply (weakening _ H2),
          { intros, existsi n.succ, assumption },
          { simp, apply weakening _ (@Impl_elim_ _ p q),
              { intros n _ _, cases n,
                  { existsi 1, assumption },
                  { cases n,
                      { existsi 0, assumption },
                      { contradiction }, }
               } }
  end

def Bot_elim_ : F ▸ p := begin
    apply Bot_elim, apply Axiom 0, refl,
  end

def Not_elim_ : [p, ∼p] ▸ q := begin
    apply Not_elim, 
    apply Axiom 0, refl,
    apply Axiom 1, refl,
  end

def Not_intro_ : (p ⇒ F) ▸ ∼p := begin
    apply Or_elim, 
    apply Axiom 0, refl,
    apply Axiom 0, refl,
    apply Bot_elim, 
    apply Axiom 0, refl,
  end

def Not_intro : (p::Γ) ▸ F → Γ ▸ ∼p := sorry

def Double_negation_elim_ : ∼∼p ▸ p := begin
    apply (By_contradiction p),
    apply Not_elim,
    apply Axiom 0, refl,
    apply Axiom 1, refl,
  end

def Double_negation_elim : Γ ▸ ∼∼p → Γ ▸ p := sorry

def Double_negation_intro_ : p ▸ ∼∼p := begin
    apply Not_intro,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
  end

def Double_negation_intro : Γ ▸ p → Γ ▸ ∼∼p := sorry

def By_contradiction_ : (∼p ⇒ F) ▸ p := begin
    apply Or_elim,
    apply Axiom 0, refl,
    apply Double_negation_elim,
    apply Axiom 0, refl,
    apply Bot_elim,
    apply Axiom 0, refl,
  end

def Or_intro_left_ : p ▸ (p or q) := begin
    apply Or_intro_left,
    apply Axiom 0, refl,
  end

def Or_intro_right_ : q ▸ (p or q) := begin
    apply Or_intro_right, 
    apply Axiom 0, refl,
  end

def Or_elim_ : [p or q, p ⇒ r, q ⇒ r] ▸ r := begin
    apply Or_elim, 
    apply Axiom 0, refl,
    apply Impl_elim,
    apply Axiom 0, refl,
    apply Axiom 2, refl,
    apply Impl_elim,
    apply Axiom 0, refl,
    apply Axiom 3, refl,
  end

def And_intro_ : [p, q] ▸ (p and q) := begin
    apply Not_intro, 
    apply Or_elim,
    apply Axiom 0, refl,
    apply Not_elim,
    apply Axiom 2, refl,
    apply Axiom 0, refl,
    apply Not_elim,
    apply Axiom 3, refl,
    apply Axiom 0, refl,
  end

def And_intro : Γ ▸ p → Γ ▸ q → Γ ▸ (p and q) := sorry

def And_elim_left_ : (p and q) ▸ p := begin
      apply By_contradiction,
      apply Not_elim,
      apply Axiom 1, refl,
      apply Double_negation_intro,
      apply Or_intro_left,
      apply Axiom 0, refl,
    end

def And_elim_left : Γ ▸ (p and q) → Γ ▸ p := sorry

def And_elim_right_ : (p and q) ▸ q := begin
      apply By_contradiction,
      apply Not_elim,
      apply Axiom 1, refl,
      apply Double_negation_intro,
      apply Or_intro_right,
      apply Axiom 0, refl,
    end

def And_elim_right : Γ ▸ (p and q) → Γ ▸ q := sorry

def DeMorganNotOr_ : ∼(p or q) ▸ (∼p and ∼q) := begin
    apply Not_intro,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Double_negation_intro,
    apply Or_elim,
    apply Axiom 0, refl,
    apply Or_intro_left,
    apply Double_negation_elim,
    apply Axiom 0, refl,
    apply Or_intro_right,
    apply Double_negation_elim,
    apply Axiom 0, refl,
  end

def DeMorganNotOr : Γ ▸ ∼(p or q) → Γ ▸ (∼p and ∼q) := sorry

def DeMorganOr_ : (∼p or ∼q) ▸ ∼(p and q) := begin
    apply Not_intro,
    apply Or_elim,
    apply Axiom 1, refl,
    apply Not_elim,
    apply Axiom 0, refl,
    apply Double_negation_intro,
    apply And_elim_left,
    apply Axiom 1, refl,
    apply Not_elim,
    apply Axiom 0, refl,
    apply Double_negation_intro,
    apply And_elim_right,
    apply Axiom 1, refl,
  end

def DeMorganOr : Γ ▸ (∼p or ∼q) → Γ ▸ ∼(p and q) := sorry

def DeMorganNotAnd_ : ∼(p and q) ▸ (∼p or ∼q) := begin
    apply By_contradiction,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Double_negation_intro,
    apply Axiom 0, refl,
  end

def DeMorganNotAnd : Γ ▸ ∼(p and q) → Γ ▸ (∼p or ∼q) := sorry

-- TODO
def DeMorganAnd_ : (∼p and ∼q) ▸ ∼(p or q) := sorry

def DeMorganAnd : Γ ▸ (∼p and ∼q) → Γ ▸ ∼(p or q) := sorry

def NonContradiction_ : (p and ∼p) ▸ F := begin
    apply Not_elim,
    apply And_elim_left_,
    apply And_elim_right_,
  end

def NonContradiction : Γ ▸ (p and ∼p) → Γ ▸ F := sorry

def ExcludedMiddle_ : ▸ (p or ∼p) := sorry

def ExcludedMiddle : Γ ▸ (p or ∼p) := sorry

def AndProves : (Γ ▸ p) ∧ (Γ ▸ q) → (Γ ▸ (p and q)) := begin
    intro h,
    apply And_intro,
    apply and.elim_left h,
    apply and.elim_right h,
  end

def NotProves : ¬(Γ ▸ p) → (Γ ▸ ∼p) := sorry

def Prove_impl_ : (p ▸ q) → (▸ p ⇒ q) := sorry

def prove_transitive : p ▸ q → q ▸ r → p ▸ r := sorry

def DistributionAndOr_ : (p and (q or r)) ▸ ((p and q) or (p and r)) := sorry

def DistributionAndOr : Γ ▸ (p and (q or r)) → Γ ▸ ((p and q) or (p and r)):= sorry

def DistributionOrAnd_ : (p or (q and r)) ▸ ((p or q) and (p or r)) := sorry

def DistributionOrAnd : Γ ▸ (p or (q and r)) → Γ ▸ ((p or q) and (p or r)) := sorry

end prf

end first_order
