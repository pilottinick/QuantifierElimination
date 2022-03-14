import language
import data.nat.parity

namespace first_order

section prf

variables {L : language} {n m : ℕ}

inductive Prf : (ℕ → (formula L)) → formula L → Prop
| Axiom : ∀ {Γ : ℕ → (formula L)} n φ, Γ n = φ → Prf Γ φ
| Bot_elim : ∀ {Γ : ℕ → (formula L)} φ, Prf Γ F → Prf Γ φ
| Not_elim : ∀ {Γ : ℕ → (formula L)} φ ψ, Prf Γ ∼φ → Prf Γ φ → Prf Γ ψ
| By_contradiction : ∀ {Γ : ℕ → (formula L)} φ, Prf (∼φ::Γ) F → Prf Γ φ
| Or_intro_left : ∀ {Γ : ℕ → (formula L)} φ ψ, Prf Γ φ → Prf Γ (φ or ψ)
| Or_intro_right : ∀ {Γ : ℕ → (formula L)} φ ψ, Prf Γ ψ → Prf Γ (φ or ψ)
| Or_elim : ∀ {Γ : ℕ → (formula L)} φ ψ χ, Prf Γ (φ or ψ) → Prf (φ::Γ) χ → Prf (ψ::Γ) χ → Prf Γ χ
| All_intro : ∀ {Γ : ℕ → (formula L)} φ n m, var_not_free_in_axioms m Γ → 
    Prf Γ (replace_formula_with n (term.var m) φ) → Prf Γ (formula.all n φ)
| All_elim : ∀ {Γ : ℕ → (formula L)} n t φ ψ, Prf Γ (formula.all n φ) → 
    Prf ((replace_formula_with n t φ) :: Γ) ψ → Prf Γ ψ
| Cut : ∀ {Γ : ℕ → (formula L)} φ ψ, Prf Γ φ → Prf (φ::Γ) ψ → Prf Γ ψ

open Prf

@[simp]
def list_to_func (Γ : list (formula L)) : ℕ → (formula L) :=
λ n, match Γ.nth n with
    | none       := T
    | some a     := a
    end

@[simp]
def Prf_list (Γ : list (formula L)) (φ : formula L) : Prop := 
  Prf (list_to_func Γ) φ

/- Using ⊢ doesn't compile -/
infix ` ▸ ` := Prf

infix ` ▸ ` := Prf_list

notation φ` ▸ `ψ := Prf (λ n, φ) ψ

variables {p p₁ p₂ q q₁ q₂ r s φ : formula L}

variables {Γ γ : ℕ → formula L} {P Q : list (formula L)}

-- If a set of axioms is consistent
def is_consistent (Γ : ℕ → formula L) :=  ∀ φ : formula L, ¬(Γ ▸ φ ∧ Γ ▸ ∼φ)

-- If a set of axiom is complete
def is_complete (Γ : ℕ → formula L) := ∀ φ : formula L, Γ ▸ φ ∨ Γ ▸ ∼φ

-- Weakening
lemma nth_append_some : ∀ {A : Type} {l1 l2 : ℕ → A} n, (l1 n) = (l1 ++ l2) (2 * n) := begin
  intros, simp,
  have two_even : even 2 := even_bit0 1,
  have two_n_even : even (2 * n) := nat.even.mul_left two_even n,
  simp [two_n_even],
end

lemma nth_cons_some : ∀ {A : Type} {l1 l2 : ℕ → A},
  (∀ n x, l1 n = x → ∃ m, l2 m = x) -> ∀ y,
  (∀ n x, (y :: l1) n = x → ∃ m, (y :: l2) m = x) :=
  begin
    intros, cases n, existsi 0, simp at *, assumption,
    simp at ᾰ, apply exists.elim (ᾰ n),
    intros m h, existsi m.succ, rw ← ᾰ_1, simp, assumption,
  end

lemma nth_cons_r : ∀ {A : Type} {a : A} {l : ℕ → A} n,
  (a::l) (n + 1) = l n := by { intros, simp, }

lemma nth_even_append_r : ∀ {A : Type} {l1 l2 : ℕ → A} n, 
  (even n) → (l1 ++ l2) n = l1 (n / 2) := by { intros, simp, intro, contradiction, }

lemma nth_odd_append_r : ∀ {A : Type} {l1 l2 : ℕ → A} n,
  ¬(even n) → (l1 ++ l2) n = l2 ((n - 1) / 2) := by { intros, simp, intro, contradiction, }

def weakening : (forall n x, γ n = x -> ∃ m, Γ m = x) → γ ▸ p → Γ ▸ p := begin
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
      admit,
      admit,
      apply Cut,
        { apply γp_ih_ᾰ, assumption },
        { apply γp_ih_ᾰ_1, apply nth_cons_some, assumption },
  end

def weakening_append : (γ ▸ p) → ((γ ++ Γ) ▸ p) := begin
    apply weakening,
    intros, existsi 2 * n,
    have nth_append : γ n = (γ++Γ) (2 * n) := by apply nth_append_some,
    rw ← nth_append, assumption,
  end

-- Converting natural deduction rules into sequent calculus rules
def To_Right_Rule : (p ▸ q) → (Γ ▸ p → Γ ▸ q) := begin
    intros pq Γp,
    apply Cut,
    apply Γp,
    apply weakening _ pq,
    intros n φ pn_eq_φ,
    existsi 0, simp, assumption,
  end

variables (h : formula L) (l : ℕ → formula L)

def To_Right_Rule_List (l : list (formula L)) : ((h::l) ▸ q) → ∀ Γ : list (formula L), Γ ▸ h → ((l ++ Γ) ▸ q) := begin
    intros hlq Γ Γq,
    apply Cut,
    apply weakening _ hlq,
    intros n x hln_eq_x,
    existsi (2 * (n - 1)),
    rw nth_even_append_r, simp,
    rw ← hln_eq_x,
    apply nth_cons_r,
    apply weakening,
    intros n2 h5 h6,
    apply nth_cons_some,
    intros n3 h7 h8,
    existsi n3,
    apply nth_append_some,
    apply h8,
    apply h6,
    apply h1,
  end


def To_Left_Rule : (p ▸ q) → Γ ▸ p → (q::Γ) ▸ r → Γ ▸ r := begin
    intros h1 h2 h3,
    apply Cut,
    apply To_Right_Rule,
    apply h1,
    apply h2,
    apply h3,
  end

def Proves_impl : ((p::Γ) ▸ q) → Γ ▸ (p ⇒ q) := begin
  intro h, simp,
  apply By_contradiction,
  apply Not_elim,
  apply Axiom 0, refl,
  apply Cut p,
  apply By_contradiction,
  apply Not_elim,
  apply Axiom 1, refl,
  apply Or_intro_left,
  apply Axiom 0, refl,
  apply Or_intro_right,
  apply weakening _ h,
  intros n φ h1,
  cases n,
  existsi 0,
  simp at *,
  apply h1,
  existsi n.succ.succ,
  simp at *,
  apply h1,
end

def To_Not_Rule_ : p ▸ q → ∼p ▸ ∼q := sorry

def Rule_To_Not_Rule_R : (Γ ▸ p → Γ ▸ q) → (Γ ▸ ∼p → Γ ▸ ∼q) := sorry

def Equiv_Rule_To_Not_Rule_R : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ ∼p ↔ Γ ▸ ∼q) := sorry

def Rule_To_Not_Rule_L : (Γ ▸ p → Γ ▸ q) → (Γ ▸ ∼p → (∼q::Γ) ▸ r → Γ ▸ r) := sorry

def Rule_To_Left_Or_Rule_R : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (p or r) → Γ ▸ (q or r)) := sorry

def Equiv_Rule_To_Left_Or_Rule_R : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ (p or r) ↔ Γ ▸ (q or r)) := sorry

def Rule_To_Right_Or_Rule_R : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (r or p) → Γ ▸ (r or q)) := sorry

def Equiv_Rule_To_Right_Or_Rule_R : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ (r or p) ↔ Γ ▸ (r or q)) := sorry

def Rule_To_Or_Rule_R : (Γ ▸ p₁ → Γ ▸ q₁) → (Γ ▸ p₂ → Γ ▸ q₂) → (Γ ▸ (p₁ or p₂) → (Γ ▸ (q₁ or q₂))) := sorry

def Equiv_Rule_To_Or_Rule_R : (Γ ▸ p₁ ↔ Γ ▸ q₁) → (Γ ▸ p₂ ↔ Γ ▸ q₂) → (Γ ▸ (p₁ or p₂) ↔ (Γ ▸ (q₁ or q₂))) := sorry

def Rule_To_Left_And_Rule_R : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (p and r) → Γ ▸ (q and r)) := sorry

def Equiv_Rule_To_Left_And_Rule_R : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ (p and r) ↔ Γ ▸ (q and r)) := sorry

def Rule_To_Right_And_Rule_R : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (r and p) → Γ ▸ (r and q)) := sorry

def Rule_To_And_Rule_R : (Γ ▸ p₁ → Γ ▸ q₁) → (Γ ▸ p₂ → Γ ▸ q₂) → (Γ ▸ (p₁ and p₂) → (Γ ▸ (q₁ and q₂))) := sorry

def Equiv_Rule_To_And_Rule_R : (Γ ▸ p₁ ↔ Γ ▸ q₁) → (Γ ▸ p₂ ↔ Γ ▸ q₂) → (Γ ▸ (p₁ and p₂) ↔ (Γ ▸ (q₁ and q₂))) := sorry

def Rule_To_All_Rule_R : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (all n p) → Γ ▸ (all n q)) := sorry

def Equiv_Rule_To_All_Rule_R : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ (all n p) ↔ Γ ▸ (all n q)) := sorry

def Rule_To_All_Rule_L : (Γ ▸ p → Γ ▸ q) → ((Γ ▸ (all n p)) → ((all n q)::Γ) ▸ r → Γ ▸ r) := sorry 

def Rule_To_Ex_Rule_R : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (exi n p) → Γ ▸ (exi n q)) := sorry 

def Equiv_Rule_To_Ex_Rule_R : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ (exi n p) ↔ Γ ▸ (exi n q)) := sorry 

-- Basic intro and elim ND rules
def Not_intro_ : (p ⇒ F) ▸ ∼p := begin
    apply Or_elim,
    apply Axiom 0, refl,
    apply Axiom 0, refl,
    apply Bot_elim,
    apply Axiom 0, refl,
  end

def Not_intro : Γ ▸ (p ⇒ F) → Γ ▸ ∼p := To_Right_Rule Not_intro_

def Not_impl_ : ∼p ▸ (p ⇒ F) := begin
  apply Or_intro_left,
  apply Axiom 0, refl,
end

def Not_impl : Γ ▸ ∼p → Γ ▸ (p ⇒ F) := To_Right_Rule Not_impl_

def Impl_not_ : (p ⇒ F) ▸ ∼p := begin
  apply Or_elim,
  apply Axiom 0, refl,
  apply Axiom 0, refl,
  apply Not_intro,
  apply Axiom 1, refl,
end

def Impl_not : Γ ▸ (p ⇒ F) → Γ ▸ ∼p := To_Right_Rule Impl_not_

def Double_negation_elim_ : ∼∼p ▸ p := begin
    apply (By_contradiction p),
    apply Not_elim,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
  end

def Double_negation_elim_R : Γ ▸ ∼∼p → Γ ▸ p := To_Right_Rule Double_negation_elim_

def Double_negation_elim_L : Γ ▸ ∼∼p → (p::Γ) ▸ r → Γ ▸ r := To_Left_Rule Double_negation_elim_

def Double_negation_intro_ : p ▸ ∼∼p := begin
    apply Not_intro,
    apply Proves_impl,
    apply Not_elim,
    apply Axiom 0, refl,
    apply Axiom 1, refl,
  end

def Double_negation_intro_R : Γ ▸ p → Γ ▸ ∼∼p := To_Right_Rule Double_negation_intro_

def Double_negation_intro_L : Γ ▸ p → (∼∼p::Γ) ▸ r → Γ ▸ r := To_Left_Rule Double_negation_intro_

def Double_negation_R : Γ ▸ ∼∼p ↔ Γ ▸ p := sorry

def Top_intro_ : p ▸ T := begin
  apply By_contradiction,
  apply Double_negation_elim_R,
  apply Axiom 0, refl,
end

def Top_intro_R : Γ ▸ p → Γ ▸ T := To_Right_Rule Top_intro_

def Top_intro_L : Γ ▸ p → (T::Γ) ▸ r → Γ ▸ r := To_Left_Rule Top_intro_

def By_contradiction_ : (∼p ⇒ F) ▸ p := begin
    apply Or_elim,
    apply Axiom 0, refl,
    apply Double_negation_elim_R,
    apply Axiom 0, refl,
    apply Bot_elim,
    apply Axiom 0, refl,
  end

def Impl_elim_ : [p, p ⇒ q] ▸ q := begin
    apply Or_elim,
    apply Axiom 1, refl,
    apply Not_elim,
    apply Axiom 0, refl,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
  end

def Impl_elim : (Γ ▸ p) → (Γ ▸ (p ⇒ q)) → (Γ ▸ q) := begin
    intros h1 h2,
    apply Cut,
    apply h2,
    apply To_Right_Rule_List _ _ Impl_elim_,
  end

def And_intro_ : [p, q] ▸ (p and q) := begin
    apply Not_intro,
    apply Proves_impl,
    apply Or_elim,
    apply Axiom 0, refl,
    apply Not_elim,
    apply Axiom 0, refl,
    apply Axiom 2, refl,
    apply Not_elim,
    apply Axiom 0, refl,
    apply Axiom 3, refl,
  end

def And_intro : Γ ▸ p → Γ ▸ q → Γ ▸ (p and q) := begin
    intros h1 h2,
    apply Cut,
    apply h2,
    apply To_Right_Rule_List _ _ And_intro_,
    apply h1,
  end

def And_elim_left_ : (p and q) ▸ p := begin
      apply By_contradiction,
      apply Not_elim,
      apply Axiom 1, refl,
      apply Or_intro_left,
      apply Axiom 0, refl,
    end

def And_elim_left_R : Γ ▸ (p and q) → Γ ▸ p := To_Right_Rule And_elim_left_

def And_elim_left_L : Γ ▸ (p and q) → (p::Γ) ▸ r → Γ ▸ r := To_Left_Rule And_elim_left_

def And_elim_right_ : (p and q) ▸ q := begin
      apply By_contradiction,
      apply Not_elim,
      apply Axiom 1, refl,
      apply Or_intro_right,
      apply Axiom 0, refl,
    end

def And_elim_right_R : Γ ▸ (p and q) → Γ ▸ q := To_Right_Rule And_elim_right_

def And_elim_right_L : Γ ▸ (p and q) → (q::Γ) ▸ r → Γ ▸ r := To_Left_Rule And_elim_right_

def NonContradiction_ : (p and ∼p) ▸ F := begin
    apply Not_elim,
    apply And_elim_right_,
    apply And_elim_left_,
  end

def NonContradiction : Γ ▸ (p and ∼p) → Γ ▸ F := To_Right_Rule NonContradiction_

-- DeMorgan laws
def DeMorganNotAnd_ : ∼(p and q) ▸ (∼p or ∼q) := begin
    apply By_contradiction,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
  end

def DeMorganNotAnd_R : Γ ▸ ∼(p and q) → Γ ▸ (∼p or ∼q) := To_Right_Rule DeMorganNotAnd_

def DeMorganNotAnd_L : Γ ▸ ∼(p and q) → ((∼p or ∼q)::Γ) ▸ r → Γ ▸ r := To_Left_Rule DeMorganNotAnd_ 

def DeMorganNotOr_ : ∼(p or q) ▸ (∼p and ∼q) := begin
    apply Not_intro,
    apply Proves_impl,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Or_elim,
    apply Axiom 0, refl,
    apply Or_intro_left,
    apply Double_negation_elim_R,
    apply Axiom 0, refl,
    apply Or_intro_right,
    apply Double_negation_elim_R,
    apply Axiom 0, refl,
  end

def DeMorganNotOr_R : Γ ▸ ∼(p or q) → Γ ▸ (∼p and ∼q) := To_Right_Rule DeMorganNotOr_

def DeMorganNotOr_L : Γ ▸ ∼(p or q) → ((∼p and ∼q)::Γ) ▸ r → Γ ▸ r := To_Left_Rule DeMorganNotOr_

def ExcludedMiddle_ : p ▸ (q or ∼q) := begin
  apply By_contradiction,
  apply DeMorganNotOr_L,
  apply Axiom 0, refl,
  apply And_elim_left_L,
  apply Axiom 0, refl,
  apply Not_elim,
  apply Axiom 2, refl,
  apply Or_intro_right,
  apply Axiom 0, refl,
end

def ExcludedMiddle_R : Γ ▸ p → Γ ▸ (p or ∼p) := To_Right_Rule ExcludedMiddle_

def ExcludedMiddle_L : Γ ▸ p → ((p or ∼p)::Γ) ▸ r → Γ ▸ r := To_Left_Rule ExcludedMiddle_

def DeMorganOr_ : (∼p or ∼q) ▸ ∼(p and q) := begin
    apply Not_intro,
    apply Proves_impl,
    apply Or_elim,
    apply Axiom 1, refl,
    apply Not_elim,
    apply Axiom 0, refl,
    apply And_elim_left_L,
    apply Axiom 1, refl,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
    apply And_elim_right_L,
    apply Axiom 1, refl,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
  end

def DeMorganOr_R : Γ ▸ (∼p or ∼q) → Γ ▸ ∼(p and q) := To_Right_Rule DeMorganOr_

def DeMorganOr_L : Γ ▸ (∼p or ∼q) → ((∼(p and q))::Γ) ▸ r → Γ ▸ r := To_Left_Rule DeMorganOr_

def DeMorganAnd_ : (∼p and ∼q) ▸ ∼(p or q) := begin
  apply By_contradiction,
  apply Double_negation_elim_L,
  apply Axiom 0, refl,
  apply Or_elim,
  apply Axiom 0, refl,
  apply And_elim_left_L,
  apply Axiom 3, refl,
  apply Not_elim,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
  apply And_elim_right_L,
  apply Axiom 3, refl,
  apply Not_elim,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
end

def DeMorganAnd_R : Γ ▸ (∼p and ∼q) → Γ ▸ ∼(p or q) := To_Right_Rule DeMorganAnd_

def DeMorganAnd_L : Γ ▸ (∼p and ∼q) → ((∼(p or q))::Γ) ▸ r → Γ ▸ r := To_Left_Rule DeMorganAnd_

-- Distribution of and and or
-- TODO: Right now there are 8 distribution rules, is there any way to simplify this?
def DistributionAndOrInLeft_ : (r and (p or q)) ▸ ((r and p) or (r and q)) := begin
    apply And_elim_right_L,
    apply Axiom 0, refl,
    apply And_elim_left_L,
    apply Axiom 1, refl,
    apply Or_elim,
    apply Axiom 1, refl,
    apply Or_intro_left,
    apply And_intro,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
    apply Or_intro_right,
    apply And_intro,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
  end

def DistributionAndOrInLeft_R : Γ ▸ (r and (p or q)) → Γ ▸ ((r and p) or (r and q)):= To_Right_Rule DistributionAndOrInLeft_

def DistributionAndOrInLeft_L : Γ ▸ (r and (p or q)) → (((r and p) or (r and q))::Γ) ▸ s → Γ ▸ s := To_Left_Rule DistributionAndOrInLeft_

def DistributionAndOrInRight_ : ((p or q) and r) ▸ ((p and r) or (q and r)) := begin
  apply And_elim_left_L,
  apply Axiom 0, refl,
  apply And_elim_right_L,
  apply Axiom 1, refl,
  apply Or_elim,
  apply Axiom 1, refl,
  apply Or_intro_left,
  apply And_intro,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
  apply Or_intro_right,
  apply And_intro,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
end

def DistributionAndOrInRight_R : Γ ▸ ((p or q) and r) → Γ ▸ ((p and r) or (q and r)) := To_Right_Rule DistributionAndOrInRight_

def DistributionAndOrInRight_L : Γ ▸ ((p or q) and r) → (((p and r) or (q and r))::Γ) ▸ s → Γ ▸ s := To_Left_Rule DistributionAndOrInRight_

def DistributionAndOrOutLeft_ : ((r and q) or (r and q)) ▸ (r and (p or q)) := begin
  apply And_intro,
  apply Or_elim,
  apply Axiom 0, refl,
  any_goals { by {
    apply And_elim_left_L,
    repeat { apply Axiom 0, refl, }
  } },
  apply Or_elim,
  apply Axiom 0, refl,
  any_goals { by {
    apply And_elim_right_L,
    apply Axiom 0, refl,
    { apply Or_intro_left, apply Axiom 0, refl } 
      <|>
    { apply Or_intro_right, apply Axiom 0, refl }
  } },
end

def DistributionAndOrOutLeft_R : Γ ▸ ((r and q) or (r and q)) → Γ ▸ (r and (p or q)) := To_Right_Rule DistributionAndOrOutLeft_

def DistributionAndOrOutLeft_L : Γ ▸ ((r and q) or (r and q)) → ((r and (p or q))::Γ) ▸ s → Γ ▸ s := To_Left_Rule DistributionAndOrOutLeft_

def DistributionAndOrOutRight_ : ((p and r) or (q and r)) ▸ ((p or q) and r) := begin
  apply And_intro,
  apply Or_elim,
  apply Axiom 0, refl,
  any_goals { 
    apply And_elim_left_L,
    apply Axiom 0, refl,
    { apply Or_intro_left, apply Axiom 0, refl }
      <|>
    { apply Or_intro_right, apply Axiom 0, refl }
  },
  apply Or_elim,
  apply Axiom 0, refl,
  all_goals {
    apply And_elim_right_L,
    repeat { apply Axiom 0, refl },
  },
end

def DistributionAndOrOutRight_R : Γ ▸ ((p and r) or (q and r)) → Γ ▸ ((p or q) and r) := To_Right_Rule DistributionAndOrOutRight_

def DistributionAndOrOutRight_L : Γ ▸ ((p and r) or (q and r)) → (((p or q) and r)::Γ) ▸ s → Γ ▸ s := To_Left_Rule DistributionAndOrOutRight_

def DistributionOrAndInLeft_ : (r or (p and q)) ▸ ((r or p) and (r or q)) := begin
    apply Or_elim, 
    apply Axiom 0, refl,
    apply And_intro,
    apply Or_intro_left,
    apply Axiom 0, refl,
    apply Or_intro_left,
    apply Axiom 0, refl,
    apply And_intro,
    apply And_elim_left_L,
    apply Axiom 0, refl,
    apply Or_intro_right,
    apply Axiom 0, refl,
    apply And_elim_right_L,
    apply Axiom 0, refl,
    apply Or_intro_right,
    apply Axiom 0, refl,
  end

def DistributionOrAndInLeft_R : Γ ▸ (r or (p and q)) → Γ ▸ ((r or p) and (r or q)) := To_Right_Rule DistributionOrAndInLeft_

def DistributionOrAndInLeft_L : Γ ▸ (r or (p and q)) → (((r or p) and (r or q))::Γ) ▸ s → Γ ▸ s := To_Left_Rule DistributionOrAndInLeft_

def DistributionOrAndOutRight_ : ((p or r) and (q or r)) ▸ ((p and q) or r) := begin
  apply And_elim_left_L,
  apply Axiom 0, refl,
  apply And_elim_right_L,
  apply Axiom 1, refl,
  apply Or_elim,
  apply Axiom 0, refl,
  apply Or_elim,
  apply Axiom 2, refl,
  apply Or_intro_left,
  apply And_intro,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
  all_goals {
    apply Or_intro_right,
    apply Axiom 0, refl
  },
end

def DistributionOrAndOutRight_R : Γ ▸ ((p or r) and (q or r)) → Γ ▸ ((p and q) or r) := To_Right_Rule DistributionOrAndOutRight_

def DistributionOrAndOutRight_L : Γ ▸ ((p or r) and (q or r)) → (((p and q) or r)::Γ) ▸ s → Γ ▸ s := To_Left_Rule DistributionOrAndOutRight_

def DistributionOrAndOutLeft_ : ((r or p) and (r or q)) ▸ (r or (p and q)) := begin
  apply And_elim_left_L,
  apply Axiom 0, refl,
  apply And_elim_right_L,
  apply Axiom 1, refl,
  apply Or_elim,
  apply Axiom 0, refl,
  apply Or_intro_left,
  apply Axiom 0, refl,
  apply Or_elim,
  apply Axiom 2, refl,
  apply Or_intro_left,
  apply Axiom 0, refl,
  apply Or_intro_right,
  apply And_intro,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
end

def DistributionOrAndOutLeft_R : Γ ▸ ((r or p) and (r or q)) → Γ ▸ (r or (p and q)) := To_Right_Rule DistributionOrAndOutLeft_

def DistributionOrAndOutLeft_L : Γ ▸ ((r or p) and (r or q)) → ((r or (p and q))::Γ) ▸ s → Γ ▸ s := To_Left_Rule DistributionOrAndOutLeft_

def DistributionOrAndInRight_ : ((p or q) and r) ▸ ((p and r) or (q and r)) := begin
  apply And_elim_left_L,
  apply Axiom 0, refl,
  apply And_elim_right_L,
  apply Axiom 1, refl,
  apply Or_elim,
  apply Axiom 1, refl,
  apply Or_intro_left,
  apply And_intro,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
  apply Or_intro_right,
  apply And_intro,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
end

def DistributionOrAndInRight_R : Γ ▸ ((p or q) and r) → Γ ▸ ((p and r) or (q and r)) := To_Right_Rule DistributionOrAndInRight_

def DistributionOrAndInRight_L : Γ ▸ ((p or q) and r) → (((p and r) or (q and r))::Γ) ▸ s → Γ ▸ s := To_Left_Rule DistributionOrAndInRight_

-- Commutativity rules 
def Or_comm_ : (p or q) ▸ (q or p) := begin
  apply Or_elim,
  apply Axiom 0, refl,
  apply Or_intro_right,
  apply Axiom 0, refl,
  apply Or_intro_left,
  apply Axiom 0, refl,
end

def Or_comm_R : Γ ▸ (p or q) → Γ ▸ (q or p) := To_Right_Rule Or_comm_

def Or_comm_L : Γ ▸ (p or q) → ((q or p)::Γ) ▸ r → Γ ▸ r := To_Left_Rule Or_comm_

def And_comm_ : (p and q) ▸ (q and p) := begin
  apply And_intro,
  apply And_elim_right_L,
  apply Axiom 0, refl,
  apply Axiom 0, refl,
  apply And_elim_left_L,
  apply Axiom 0, refl,
  apply Axiom 0, refl,
end

def And_comm_R : Γ ▸ (p and q) → Γ ▸ (q and p) := To_Right_Rule And_comm_

def And_comm_L : Γ ▸ (p and q) → ((q and p)::Γ) ▸ r → Γ ▸ r := To_Left_Rule And_comm_

def AndProves : (Γ ▸ p) ∧ (Γ ▸ q) → (Γ ▸ (p and q)) := begin
    intros h,
    apply And_intro,
    apply and.elim_left h,
    apply and.elim_right h,
  end

def Contrapose_ : (p ⇒ q) ▸ (∼q ⇒ ∼p) := begin
  simp,
  apply Or_elim,
  apply Axiom 0, refl,
  apply Or_intro_right,
  apply Axiom 0, refl,
  apply Proves_impl,
  apply Not_elim,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
end

def Contrapose_R : Γ ▸ (p ⇒ q) → Γ ▸ (∼q ⇒ ∼p) := To_Right_Rule Contrapose_

def Contrapose_L : Γ ▸ (p ⇒ q) → ((∼q ⇒ ∼p)::Γ) ▸ r → Γ ▸ r := To_Left_Rule Contrapose_

def All_To_Ex_ : (all n p) ▸ ∼(exi n ∼p) := begin
  apply Double_negation_intro_R,
  apply Right_Rule_To_All_Rule_R Double_negation_intro_R,
  apply Axiom 0, refl,
end

def All_To_Ex_R : Γ ▸ (all n p) → Γ ▸ ∼(exi n ∼p) := To_Right_Rule All_To_Ex_

def All_To_Ex_L : Γ ▸ (all n p) → (∼(exi n ∼p)::Γ) ▸ r → Γ ▸ r := To_Left_Rule All_To_Ex_

def Ex_To_All_ : ∼(exi n ∼p) ▸ (all n p) := begin
  apply Right_Rule_To_All_Rule_R Double_negation_elim_R,
  apply Double_negation_elim_R,
  apply Axiom 0, refl,
end

def Ex_To_All_R : Γ ▸ ∼(exi n ∼p) → Γ ▸ (all n p) := To_Right_Rule Ex_To_All_

def Ex_To_All_L : Γ ▸ ∼(exi n ∼p) → ((all n p)::Γ) ▸ r → Γ ▸ r := To_Left_Rule Ex_To_All_

def NotAll_ : ∼(all n p) ▸ (exi n ∼p) := begin
  apply Right_Rule_To_Not_Rule_R (Right_Rule_To_All_Rule_R Double_negation_intro_R),
  apply Axiom 0, refl,
end

def NotAll_R : (Γ ▸ ∼(all n p)) → (Γ ▸ (exi n ∼p)) := To_Right_Rule NotAll_

def AllNot_ : (all n ∼p) ▸ ∼(exi n p) := begin
  apply Double_negation_intro_R,
  apply Axiom 0, refl,
end

def AllNot_R : (Γ ▸ (all n ∼p)) → (Γ ▸ ∼(exi n p)) := To_Right_Rule AllNot_  

def NotEx_ : ∼(exi n p) ▸ (all n ∼p) := begin
  apply Double_negation_elim_L,
  apply Axiom 0, refl,
  apply Axiom 0, refl,
end

def NotEx_R : (Γ ▸ ∼(exi n p)) → (Γ ▸ (all n ∼p)) := To_Right_Rule NotEx_

def ExNot_ : (exi n ∼p) ▸ ∼(all n p) := begin
  apply Right_Rule_To_Not_Rule_L (Right_Rule_To_All_Rule_R Double_negation_elim_R),
  apply Axiom 0, refl,
  apply Axiom 0, refl,
end

def ExNot_R : (Γ ▸ (exi n ∼p)) → (Γ ▸ ∼(all n p)) := To_Right_Rule ExNot_

def AllOrOut_ : ((all n p) or (all n q)) ▸ (all n (p or q)) := begin
  apply All_intro _ _ n, simp,
  rw replace_formula_with_idem,
  apply Or_elim, apply Axiom 0, refl,
  all_goals { 
    apply All_elim n (v n),
    apply Axiom 0, refl,
    rw replace_formula_with_idem,
    { apply Or_intro_left, apply Axiom 0, refl } 
      <|>
    { apply Or_intro_right, apply Axiom 0, refl }
  },
end

def AllOrOut_R : Γ ▸ ((all n p) or (all n q)) → Γ ▸ (all n (p or q)) := To_Right_Rule AllOrOut_

def AllOrOut_L : Γ ▸ ((all n p) or (all n q)) → ((all n (p or q))::Γ) ▸ r → Γ ▸ r := To_Left_Rule AllOrOut_

def AllAndIn_ : all n (p and q) ▸ ((all n p) and (all n q)) := begin
  apply AndProves, split,
  all_goals { 
    apply All_intro _ _ n, simp,
    rw replace_formula_with_idem,
    apply All_elim n (v n),
      apply Axiom 0, refl,
      rw replace_formula_with_idem,
      { apply And_elim_right_R, apply Axiom 0, refl }
        <|> 
      { apply And_elim_left_R, apply Axiom 0, refl, },
  }
end

def AllAndIn_R : Γ ▸ (all n (p and q)) → (Γ ▸ ((all n p) and (all n q))) := To_Right_Rule AllAndIn_

def AllAndIn_L : Γ ▸ all n (p and q) → (((all n p) and (all n q))::Γ) ▸ r → Γ ▸ r := To_Left_Rule AllAndIn_

def AllAndOut_ : ((all n p) and (all n q)) ▸ (all n (p and q)) := begin
  apply All_intro _ _ n, simp,
  rw replace_formula_with_idem,
  apply And_intro,
  { 
    apply And_elim_left_L, 
    apply Axiom 0, 
    refl,
    apply All_elim n (v n),
      apply Axiom 0, refl,
      rw replace_formula_with_idem,
      apply Axiom 0, refl,
  },
  {
    apply And_elim_right_L, 
    apply Axiom 0, 
    refl,
    apply All_elim n (v n),
      apply Axiom 0, refl,
      rw replace_formula_with_idem,
      apply Axiom 0, refl,
  }
end

def AllAndOut_R : (Γ ▸ ((all n p) and (all n q))) → (Γ ▸ (all n (p and q))) := To_Right_Rule AllAndOut_

def AllAndOut_L : Γ ▸ ((all n p) and (all n q)) → ((all n (p and q))::Γ) ▸ r → Γ ▸ r := To_Left_Rule AllAndOut_

def ExOrIn_ : (exi n (p or q)) ▸ ((exi n p) or (exi n q)) := begin
  apply DeMorganNotAnd_R,
  apply Right_Rule_To_Not_Rule_R AllAndIn_R,
  apply Right_Rule_To_Not_Rule_R (Right_Rule_To_All_Rule_R DeMorganNotOr_R),
  apply Axiom 0, refl,
end

def ExOrIn_R : (Γ ▸ (exi n (p or q))) → (Γ ▸ ((exi n p) or (exi n q))) := To_Right_Rule ExOrIn_

def ExOrIn_L : Γ ▸ (exi n (p or q)) → (((exi n p) or (exi n q))::Γ) ▸ r → Γ ▸ r := To_Left_Rule ExOrIn_

def ExOrOut_ : ((exi n p) or (exi n q)) ▸ (exi n (p or q)) := begin
  apply Right_Rule_To_Not_Rule_R (Right_Rule_To_All_Rule_R DeMorganAnd_R),
  apply Right_Rule_To_Not_Rule_R AllAndOut_R,
  apply DeMorganOr_R,
  apply Axiom 0, refl,
end

def ExOrOut_R : (Γ ▸ ((exi n p) or (exi n q))) → (Γ ▸ (exi n (p or q))) := To_Right_Rule ExOrOut_

def ExOrOut_L : (Γ ▸ ((exi n p) or (exi n q))) → ((exi n (p or q))::Γ) ▸ r → Γ ▸ r := To_Left_Rule ExOrOut_

def ExAndOut_ : ((exi n p) and (exi n q)) ▸ (exi n (p and q))  := begin
  apply Right_Rule_To_Not_Rule_R (Right_Rule_To_All_Rule_R DeMorganOr_R),
  apply Right_Rule_To_Not_Rule_R AllOrOut_R,
  apply DeMorganAnd_R,
  apply Axiom 0, refl,
end

def ExAndOut_R : (Γ ▸ ((exi n p) and (exi n q))) → (Γ ▸ (exi n (p and q))) := To_Right_Rule ExAndOut_

def ExAndOut_L : Γ ▸ ((exi n p) and (exi n q)) → ((exi n (p and q))::Γ) ▸ r → Γ ▸ r := To_Left_Rule ExAndOut_

def SwapAll_ : (all n (all m p)) ▸ (all m (all n p)) := begin
  apply All_intro _ _ m, simp,
    rw replace_formula_with_idem,
  apply All_intro _ _ n, simp,
    rw replace_formula_with_idem,
  apply All_elim n (v n),
    apply Axiom 0, refl,
    rw replace_formula_with_idem,
  apply All_elim m (v m),
    apply Axiom 0, refl,
    rw replace_formula_with_idem,
  apply Axiom 0, refl,
end

def SwapAll_R : (Γ ▸ (all n (all m p))) → (Γ ▸ (all m (all n p))) := To_Right_Rule SwapAll_

def SwapAll_L : Γ ▸ (all n (all m p)) → ((all m (all n p))::Γ) ▸ r → Γ ▸ r := To_Left_Rule SwapAll_

def SwapEx_ : (exi n (exi m p)) ▸ (exi m (exi n p)) := begin
  simp,
  apply Right_Rule_To_Not_Rule_R (Right_Rule_To_All_Rule_R Double_negation_intro_R),
  apply Right_Rule_To_Not_Rule_L (Right_Rule_To_All_Rule_R Double_negation_elim_R),
  apply Axiom 0, refl,
  apply Right_Rule_To_Not_Rule_R SwapAll_R,
  apply Axiom 0, refl,
end

def SwapEx_R : (Γ ▸ (exi n (exi m p))) → (Γ ▸ (exi m (exi n p))) := To_Right_Rule SwapEx_

def SwapEx_L : Γ ▸ (exi n (exi m p)) → ((exi m (exi n p))::Γ) ▸ r → Γ ▸ r := To_Left_Rule SwapEx_

-- def SwapAllEx_R : (Γ ▸ ∼(all n (exi m ∼p))) → (Γ ▸ (exi m (all n p))) := sorry

-- def SwapExAll_R : (Γ ▸ ∼(exi n (all m ∼p))) → (Γ ▸ (all m (exi n p))) := sorry

end prf

end first_order
