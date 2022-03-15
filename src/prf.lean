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
    substitutable_for t n φ → Prf ((replace_formula_with n t φ) :: Γ) ψ → Prf Γ ψ
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
def R_ : (p ▸ q) → (Γ ▸ p → Γ ▸ q) := begin
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


def L_ : (p ▸ q) → Γ ▸ p → (q::Γ) ▸ r → Γ ▸ r := begin
    intros h1 h2 h3,
    apply Cut,
    apply R_,
    apply h1,
    apply h2,
    apply h3,
  end

def L_R_ : (Γ ▸ p → Γ ▸ q) → Γ ▸ p → (q::Γ) ▸ r → Γ ▸ r := begin
  intros h1 h2 h3,
  apply Cut,
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

def R_Not_ : (Γ ▸ p → Γ ▸ q) → (Γ ▸ ∼p → Γ ▸ ∼q) := sorry

def R_Eq_Not_ : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ ∼p ↔ Γ ▸ ∼q) := sorry

def R_Left_Or_ : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (p or r) → Γ ▸ (q or r)) := sorry

def R_Eq_Left_Or_ : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ (p or r) ↔ Γ ▸ (q or r)) := sorry

def R_Right_Or_ : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (r or p) → Γ ▸ (r or q)) := sorry

def R_Eq_Right_Or_ : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ (r or p) ↔ Γ ▸ (r or q)) := sorry

def R_Or_ : (Γ ▸ p₁ → Γ ▸ q₁) → (Γ ▸ p₂ → Γ ▸ q₂) → (Γ ▸ (p₁ or p₂) → (Γ ▸ (q₁ or q₂))) := sorry

def R_Eq_Or_ : (Γ ▸ p₁ ↔ Γ ▸ q₁) → (Γ ▸ p₂ ↔ Γ ▸ q₂) → (Γ ▸ (p₁ or p₂) ↔ (Γ ▸ (q₁ or q₂))) := sorry

def R_Left_And_ : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (p and r) → Γ ▸ (q and r)) := sorry

def R_Eq_Left_And_ : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ (p and r) ↔ Γ ▸ (q and r)) := sorry

def R_Right_And_ : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (r and p) → Γ ▸ (r and q)) := sorry

def R_And_ : (Γ ▸ p₁ → Γ ▸ q₁) → (Γ ▸ p₂ → Γ ▸ q₂) → (Γ ▸ (p₁ and p₂) → (Γ ▸ (q₁ and q₂))) := sorry

def R_Eq_And_ : (Γ ▸ p₁ ↔ Γ ▸ q₁) → (Γ ▸ p₂ ↔ Γ ▸ q₂) → (Γ ▸ (p₁ and p₂) ↔ (Γ ▸ (q₁ and q₂))) := sorry

def R_All_ : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (all n p) → Γ ▸ (all n q)) := sorry

def R_Eq_All_ : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ (all n p) ↔ Γ ▸ (all n q)) := sorry

def R_Ex_ : (Γ ▸ p → Γ ▸ q) → (Γ ▸ (exi n p) → Γ ▸ (exi n q)) := sorry 

def R_Eq_Ex_ : (Γ ▸ p ↔ Γ ▸ q) → (Γ ▸ (exi n p) ↔ Γ ▸ (exi n q)) := sorry 

-- Basic intro and elim ND rules
def Not_intro : (p ⇒ F) ▸ ∼p := begin
    apply Or_elim,
    apply Axiom 0, refl,
    apply Axiom 0, refl,
    apply Bot_elim,
    apply Axiom 0, refl,
  end

def Not_impl : ∼p ▸ (p ⇒ F) := begin
  apply Or_intro_left,
  apply Axiom 0, refl,
end

def Impl_not : (p ⇒ F) ▸ ∼p := begin
  apply Or_elim,
  apply Axiom 0, refl,
  apply Axiom 0, refl,
  apply R_ Not_intro,
  apply Axiom 1, refl,
end

def Double_negation_elim : ∼∼p ▸ p := begin
    apply (By_contradiction p),
    apply Not_elim,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
  end

def Double_negation_intro : p ▸ ∼∼p := begin
    apply R_ Not_intro,
    apply Proves_impl,
    apply Not_elim,
    apply Axiom 0, refl,
    apply Axiom 1, refl,
  end

def Top_intro : p ▸ T := begin
  apply By_contradiction,
  apply R_ Double_negation_elim,
  apply Axiom 0, refl,
end

def Impl_elim : [p, p ⇒ q] ▸ q := begin
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
    apply To_Right_Rule_List _ _ Impl_elim,
  end

def And_intro : [p, q] ▸ (p and q) := begin
    apply R_ Not_intro,
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

def And_intro_R : Γ ▸ p → Γ ▸ q → Γ ▸ (p and q) := begin
    intros h1 h2,
    apply Cut,
    apply h2,
    apply To_Right_Rule_List _ _ And_intro,
    apply h1,
  end

def And_elim_left : (p and q) ▸ p := begin
      apply By_contradiction,
      apply Not_elim,
      apply Axiom 1, refl,
      apply Or_intro_left,
      apply Axiom 0, refl,
    end

def And_elim_right : (p and q) ▸ q := begin
      apply By_contradiction,
      apply Not_elim,
      apply Axiom 1, refl,
      apply Or_intro_right,
      apply Axiom 0, refl,
    end

def NonContradiction : (p and ∼p) ▸ F := begin
    apply Not_elim,
    apply And_elim_right,
    apply And_elim_left,
  end

-- DeMorgan laws
def DeMorganNotAnd : ∼(p and q) ▸ (∼p or ∼q) := begin
    apply By_contradiction,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
  end

def DeMorganNotOr : ∼(p or q) ▸ (∼p and ∼q) := begin
    apply R_ Not_intro,
    apply Proves_impl,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Or_elim,
    apply Axiom 0, refl,
    apply Or_intro_left,
    apply R_ Double_negation_elim,
    apply Axiom 0, refl,
    apply Or_intro_right,
    apply R_ Double_negation_elim,
    apply Axiom 0, refl,
  end

def ExcludedMiddle : p ▸ (q or ∼q) := begin
  apply By_contradiction,
  apply L_ DeMorganNotOr,
  apply Axiom 0, refl,
  apply L_ And_elim_left,
  apply Axiom 0, refl,
  apply Not_elim,
  apply Axiom 2, refl,
  apply Or_intro_right,
  apply Axiom 0, refl,
end

def DeMorganOr : (∼p or ∼q) ▸ ∼(p and q) := begin
    apply R_ Not_intro,
    apply Proves_impl,
    apply Or_elim,
    apply Axiom 1, refl,
    apply Not_elim,
    apply Axiom 0, refl,
    apply L_ And_elim_left,
    apply Axiom 1, refl,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
    apply L_ And_elim_right,
    apply Axiom 1, refl,
    apply Not_elim,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
  end

def DeMorganAnd : (∼p and ∼q) ▸ ∼(p or q) := begin
  apply By_contradiction,
  apply L_ Double_negation_elim,
  apply Axiom 0, refl,
  apply Or_elim,
  apply Axiom 0, refl,
  apply L_ And_elim_left,
  apply Axiom 3, refl,
  apply Not_elim,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
  apply L_ And_elim_right,
  apply Axiom 3, refl,
  apply Not_elim,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
end

-- Distribution of and and or
-- TODO: Right now there are 8 distribution rules, is there any way to simplify this?
def DistributionAndOrInLeft : (r and (p or q)) ▸ ((r and p) or (r and q)) := begin
    apply L_ And_elim_right,
    apply Axiom 0, refl,
    apply L_ And_elim_left,
    apply Axiom 1, refl,
    apply Or_elim,
    apply Axiom 1, refl,
    apply Or_intro_left,
    apply And_intro_R,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
    apply Or_intro_right,
    apply And_intro_R,
    apply Axiom 1, refl,
    apply Axiom 0, refl,
  end

def DistributionAndOrInRight : ((p or q) and r) ▸ ((p and r) or (q and r)) := begin
  apply L_ And_elim_left,
  apply Axiom 0, refl,
  apply L_ And_elim_right,
  apply Axiom 1, refl,
  apply Or_elim,
  apply Axiom 1, refl,
  apply Or_intro_left,
  apply And_intro_R,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
  apply Or_intro_right,
  apply And_intro_R,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
end

def DistributionAndOrOutLeft : ((r and p) or (r and q)) ▸ (r and (p or q)) := begin
  apply And_intro_R,
  apply Or_elim,
  apply Axiom 0, refl,
  any_goals { by {
    apply L_ And_elim_left,
    repeat { apply Axiom 0, refl, }
  } },
  apply Or_elim,
  apply Axiom 0, refl,
  any_goals { by {
    apply L_ And_elim_right,
    apply Axiom 0, refl,
    { apply Or_intro_left, apply Axiom 0, refl } 
      <|>
    { apply Or_intro_right, apply Axiom 0, refl }
  } },
end

def DistributionAndOrOutRight : ((p and r) or (q and r)) ▸ ((p or q) and r) := begin
  apply And_intro_R,
  apply Or_elim,
  apply Axiom 0, refl,
  any_goals { 
    apply L_ And_elim_left,
    apply Axiom 0, refl,
    { apply Or_intro_left, apply Axiom 0, refl }
      <|>
    { apply Or_intro_right, apply Axiom 0, refl }
  },
  apply Or_elim,
  apply Axiom 0, refl,
  all_goals {
    apply L_ And_elim_right,
    repeat { apply Axiom 0, refl },
  },
end

def DistributionOrAndInLeft : (r or (p and q)) ▸ ((r or p) and (r or q)) := begin
    apply Or_elim, 
    apply Axiom 0, refl,
    apply And_intro_R,
    apply Or_intro_left,
    apply Axiom 0, refl,
    apply Or_intro_left,
    apply Axiom 0, refl,
    apply And_intro_R,
    apply L_ And_elim_left,
    apply Axiom 0, refl,
    apply Or_intro_right,
    apply Axiom 0, refl,
    apply L_ And_elim_right,
    apply Axiom 0, refl,
    apply Or_intro_right,
    apply Axiom 0, refl,
  end

def DistributionOrAndOutRight : ((p or r) and (q or r)) ▸ ((p and q) or r) := begin
  apply L_ And_elim_left,
  apply Axiom 0, refl,
  apply L_ And_elim_right,
  apply Axiom 1, refl,
  apply Or_elim,
  apply Axiom 0, refl,
  apply Or_elim,
  apply Axiom 2, refl,
  apply Or_intro_left,
  apply And_intro_R,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
  all_goals {
    apply Or_intro_right,
    apply Axiom 0, refl
  },
end

def DistributionOrAndOutLeft : ((r or p) and (r or q)) ▸ (r or (p and q)) := begin
  apply L_ And_elim_left,
  apply Axiom 0, refl,
  apply L_ And_elim_right,
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
  apply And_intro_R,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
end

def DistributionOrAndInRight : ((p or q) and r) ▸ ((p and r) or (q and r)) := begin
  apply L_ And_elim_left,
  apply Axiom 0, refl,
  apply L_ And_elim_right,
  apply Axiom 1, refl,
  apply Or_elim,
  apply Axiom 1, refl,
  apply Or_intro_left,
  apply And_intro_R,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
  apply Or_intro_right,
  apply And_intro_R,
  apply Axiom 0, refl,
  apply Axiom 1, refl,
end

-- Commutativity rules 
def Or_comm : (p or q) ▸ (q or p) := begin
  apply Or_elim,
  apply Axiom 0, refl,
  apply Or_intro_right,
  apply Axiom 0, refl,
  apply Or_intro_left,
  apply Axiom 0, refl,
end

def And_comm_ : (p and q) ▸ (q and p) := begin
  apply And_intro_R,
  apply L_ And_elim_right,
  apply Axiom 0, refl,
  apply Axiom 0, refl,
  apply L_ And_elim_left,
  apply Axiom 0, refl,
  apply Axiom 0, refl,
end

def AndProves : (Γ ▸ p) ∧ (Γ ▸ q) → (Γ ▸ (p and q)) := begin
    intros h,
    apply And_intro_R,
    apply and.elim_left h,
    apply and.elim_right h,
  end

def Contrapose : (p ⇒ q) ▸ (∼q ⇒ ∼p) := begin
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

def Ex_intro (n : ℕ) (t : term L) (φ : formula L) : 
  substitutable_for t n φ → Γ ▸ (replace_formula_with n t φ) → Γ ▸ (exi n φ) := sorry

def Ex_elim (n : ℕ) (t : term L) (φ : formula L) (ψ : formula L) : 
  var_not_free_in_axioms m Γ → Γ ▸ (exi n φ) → ((replace_formula_with n (term.var m) φ)::Γ) ▸ ψ → Γ ▸ ψ := sorry

def All_To_Ex : (all n p) ▸ ∼(exi n ∼p) := begin
  apply R_ Double_negation_intro,
  apply R_All_ (R_ Double_negation_intro),
  apply Axiom 0, refl,
end

def Ex_To_All : ∼(exi n ∼p) ▸ (all n p) := begin
  apply R_All_ (R_ Double_negation_elim),
  apply R_ Double_negation_elim,
  apply Axiom 0, refl,
end

def NotAll : ∼(all n p) ▸ (exi n ∼p) := begin
  apply R_Not_ (R_All_ (R_ Double_negation_intro)),
  apply Axiom 0, refl,
end

def AllNot : (all n ∼p) ▸ ∼(exi n p) := begin
  apply R_ Double_negation_intro,
  apply Axiom 0, refl,
end

def NotEx : ∼(exi n p) ▸ (all n ∼p) := begin
  apply L_ Double_negation_elim,
  apply Axiom 0, refl,
  apply Axiom 0, refl,
end

def ExNot : (exi n ∼p) ▸ ∼(all n p) := begin
  apply L_R_ (R_Not_ (R_All_ (R_ Double_negation_elim))),
  apply Axiom 0, refl,
  apply Axiom 0, refl,
end

def NotFreeAll : ¬(free n p) → p ▸ (all n p) := begin
  intro h,
  apply All_intro,
  simp, apply h,
  rw replace_formula_with_idem,
  apply Axiom 0, refl,
end

def AddAll : ¬(free n p) → Γ ▸ p → Γ ▸ (all n p) := sorry

def RemoveAll : Γ ▸ (all n p) → Γ ▸ p := sorry

def AddEx : Γ ▸ p → Γ ▸ (exi n p) := sorry

def RemoveEx : ¬(free n p) → Γ ▸ (exi n p) → Γ ▸ p := sorry

def AllOrOut : ((all n p) or (all n q)) ▸ (all n (p or q)) := begin
  apply All_intro _ _ n, simp,
  rw replace_formula_with_idem,
  apply Or_elim, apply Axiom 0, refl,
  all_goals { 
    apply All_elim n (v n),
    apply Axiom 0, refl,
    apply substitutable_for_idem,
    rw replace_formula_with_idem,
    { apply Or_intro_left, apply Axiom 0, refl } 
      <|>
    { apply Or_intro_right, apply Axiom 0, refl }
  },
end

def AllAndIn : all n (p and q) ▸ ((all n p) and (all n q)) := begin
  apply AndProves, split,
  all_goals { 
    apply All_intro _ _ n, simp,
    rw replace_formula_with_idem,
    apply All_elim n (v n),
      apply Axiom 0, refl,
      apply substitutable_for_idem,
      rw replace_formula_with_idem,
      { apply R_ And_elim_right, apply Axiom 0, refl }
        <|> 
      { apply R_ And_elim_left, apply Axiom 0, refl, },
  }
end

def AllAndOut : ((all n p) and (all n q)) ▸ (all n (p and q)) := begin
  apply All_intro _ _ n, simp,
  rw replace_formula_with_idem,
  apply And_intro_R,
  { 
    apply L_ And_elim_left, 
    apply Axiom 0, 
    refl,
    apply All_elim n (v n),
      apply Axiom 0, refl,
      apply substitutable_for_idem,
      rw replace_formula_with_idem,
      apply Axiom 0, refl,
  },
  {
    apply L_ And_elim_right, 
    apply Axiom 0, 
    refl,
    apply All_elim n (v n),
      apply Axiom 0, refl,
      apply substitutable_for_idem,
      rw replace_formula_with_idem,
      apply Axiom 0, refl,
  }
end

def ExOrIn : (exi n (p or q)) ▸ ((exi n p) or (exi n q)) := begin
  apply R_ DeMorganNotAnd,
  apply R_Not_ (R_ AllAndIn),
  apply R_Not_ (R_All_ (R_ DeMorganNotOr)),
  apply Axiom 0, refl,
end

def ExOrOut : ((exi n p) or (exi n q)) ▸ (exi n (p or q)) := begin
  apply R_Not_ (R_All_ (R_ DeMorganAnd)),
  apply R_Not_ (R_ AllAndOut),
  apply R_ DeMorganOr,
  apply Axiom 0, refl,
end

def ExAndOut : ((exi n p) and (exi n q)) ▸ (exi n (p and q))  := begin
  apply R_Not_ (R_All_ (R_ DeMorganOr)),
  apply R_Not_ (R_ AllOrOut),
  apply R_ DeMorganAnd,
  apply Axiom 0, refl,
end

def SwapAll : (all n (all m p)) ▸ (all m (all n p)) := begin
  apply All_intro _ _ m, simp,
    rw replace_formula_with_idem,
  apply All_intro _ _ n, simp,
    rw replace_formula_with_idem,
  apply All_elim n (v n),
    apply Axiom 0, refl,
    apply substitutable_for_idem,
    rw replace_formula_with_idem,
  apply All_elim m (v m),
    apply Axiom 0, refl,
    apply substitutable_for_idem,
    rw replace_formula_with_idem,
  apply Axiom 0, refl,
end

def SwapEx : (exi n (exi m p)) ▸ (exi m (exi n p)) := begin
  simp,
  apply R_Not_ (R_All_ (R_ Double_negation_intro)),
  apply L_R_ (R_Not_ (R_All_ (R_ Double_negation_elim))),
  apply Axiom 0, refl,
  apply R_Not_ (R_ SwapAll),
  apply Axiom 0, refl,
end

-- def SwapAllEx_R : (Γ ▸ ∼(all n (exi m ∼p))) → (Γ ▸ (exi m (all n p))) := sorry

-- def SwapExAll_R : (Γ ▸ ∼(exi n (all m ∼p))) → (Γ ▸ (all m (exi n p))) := sorry

end prf

end first_order
