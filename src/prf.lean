import language
import data.nat.parity

namespace first_order

section prf

variables {L : language} (n : ℕ)

def var_not_free_in_new (n : ℕ) (Γ : ℕ → formula L) : Prop
  := ∀ m : ℕ, ¬(free _ n (Γ m))

/- Shifts a sequence to the right -/
attribute [simp]
def cons { A : Type } (a : A) (f : ℕ → A) : ℕ → A := 
  λ n, if n = 0 then a else (f (n - 1))

/- Append two sequences -/
attribute [simp]
def append { A : Type } (f : ℕ → A) (g : ℕ → A) : ℕ → A :=
  λ n : ℕ, if (even n) then f (n / 2) else g ((n - 1) / 2)

notation a`::`f := cons a f

notation l`++`f := append l f

inductive Prf : (ℕ → (formula L)) → formula L → Prop
| Axiom : ∀ {Γ : ℕ → (formula L)} n φ, Γ n = φ → Prf Γ φ
| Bot_elim : ∀ {Γ : ℕ → (formula L)} φ, Prf Γ F → Prf Γ φ
| Not_elim : ∀ {Γ : ℕ → (formula L)} φ ψ, Prf Γ ∼φ → Prf Γ φ → Prf Γ ψ
| By_contradiction : ∀ {Γ : ℕ → (formula L)} φ, Prf (∼φ::Γ) F → Prf Γ φ
| Or_intro_left : ∀ {Γ : ℕ → (formula L)} φ ψ, Prf Γ φ → Prf Γ (φ or ψ)
| Or_intro_right : ∀ {Γ : ℕ → (formula L)} φ ψ, Prf Γ ψ → Prf Γ (φ or ψ)
| Or_elim : ∀ {Γ : ℕ → (formula L)} φ ψ χ, Prf Γ (φ or ψ) → Prf (φ::Γ) χ → Prf (ψ::Γ) χ → Prf Γ χ
| All_intro : ∀ {Γ : ℕ → (formula L)} φ n m, var_not_free_in_new m Γ → Prf Γ (replace_formula_with _ n (term.var m) φ) → Prf Γ (formula.all n φ)
| All_elim : ∀ {Γ : ℕ → (formula L)} φ n ψ, Prf Γ (formula.all n φ) → Prf Γ (replace_formula_with _ n ψ φ)
| Cut : ∀ {Γ : ℕ → (formula L)} φ ψ, Prf Γ φ → Prf (φ::Γ) ψ → Prf Γ ψ

open Prf

def list_to_func (Γ : list (formula L)) : ℕ → (formula L) :=
λ n, match Γ.nth n with
    | none       := T
    | some a     := a
    end

def Prf_list (Γ : list (formula L)) (φ : formula L) : Prop := 
  Prf (list_to_func Γ) φ

/- Using ⊢ doesn't compile -/
infix ` ▸ ` := Prf

infix ` ▸ ` := Prf_list

notation φ` ▸ `ψ := Prf (λ n, φ) ψ

notation ` ▸ `φ := Prf (λ n, T) φ

variables {p p₁ p₂ q q₁ q₂ r s : formula L}

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

def To_Right_Rule_List : ((h::l) ▸ q) → ∀ Γ : ℕ → (formula L), Γ ▸ h → ((l ++ Γ) ▸ q) := begin
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

/-
def Right_To_ND_Rule : Γ ▸ p → Γ ▸ q → (p ▸ q):= begin
  intro h1,
  have h2 : p ▸ p → p ▸ q := by { intros, },
  have h3 : p ▸ p := begin apply Prf.Axiom 0, refl, end,
  exact (h2 h3),
end
-/

-- def Impl_proves : (Γ ▸ (p ⇒ q)) → (p::Γ) ▸ q := sorry

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

def Top_intro : Γ ▸ T := begin
  apply By_contradiction,
  apply Double_negation_elim_R,
  apply Axiom 0, refl,
end

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

def ExcludedMiddle_ : ▸ (p or ∼p) := begin
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

def ExcludedMiddle : Γ ▸ (p or ∼p) := begin
  apply weakening _ ExcludedMiddle_,
  intros n φ h,
  contradiction,
end

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

-- TODO
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
def DistributionAndOr_ : (p and (q or r)) ▸ ((p and q) or (p and r)) := begin
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

def DistributionAndOr_R : Γ ▸ (p and (q or r)) → Γ ▸ ((p and q) or (p and r)):= To_Right_Rule DistributionAndOr_

def DistributionAndOr_L : Γ ▸ (p and (q or r)) → (((p and q) or (p and r))::Γ) ▸ s → Γ ▸ s := To_Left_Rule DistributionAndOr_

def DistributionOrAnd_ : (p or (q and r)) ▸ ((p or q) and (p or r)) := begin
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

def DistributionOrAnd_R : Γ ▸ (p or (q and r)) → Γ ▸ ((p or q) and (p or r)) := To_Right_Rule DistributionOrAnd_

def DistributionOrAnd_L : Γ ▸ (p or (q and r)) → (((p or q) and (p or r))::Γ) ▸ s → Γ ▸ s := To_Left_Rule DistributionOrAnd_

def DistributionAndDisj_ : (p and (Disj q Q)) ▸ (Disj (p and q) (p and⬝ Q)) := begin
  induction Q,
  repeat { simp },
  apply Axiom 0, refl,
  apply DistributionAndOr_L,
  apply Axiom 0, refl,
  apply Or_elim,
  apply Axiom 0, refl,
  apply Or_intro_left,
  apply Axiom 0, refl,
  apply Or_intro_right,
  apply To_Left_Rule Q_ih,
  apply Axiom 0, refl,
  apply Axiom 0, refl,
end

def DistributionAndDisj_R : Γ ▸ (p and (Disj q Q)) → Γ ▸ (Disj (p and q) (p and⬝ Q)) := To_Right_Rule DistributionAndDisj_

def DistributionAndDisj_L : Γ ▸ (p and (Disj q Q)) → ((Disj (p and q) (p and⬝ Q))::Γ) ▸ r → Γ ▸ r := To_Left_Rule DistributionAndDisj_

def DistributionOrConj_ : (p or (Conj q Q)) ▸ (Conj (p or q) (p or⬝ Q)) := begin
  induction Q,
  repeat { simp },
  apply Axiom 0, refl,
  apply DistributionOrAnd_L,
  apply Axiom 0, refl,
  apply And_intro,
  apply And_elim_left_L,
  apply Axiom 0, refl,
  apply Axiom 0, refl,
  apply To_Right_Rule Q_ih,
  apply And_elim_right_R,
  apply Axiom 0, refl,
end

def DistributionOrConj_R : Γ ▸ (p or (Conj q Q)) → Γ ▸ (Conj (p or q) (p or⬝ Q)) := To_Right_Rule DistributionOrConj_

def DistributionOrConj_L : Γ ▸ (p or (Conj q Q)) → ((Conj (p or q) (p or⬝ Q))::Γ) ▸ r → Γ ▸ r := To_Left_Rule DistributionOrConj_

-- Commutativity rules 
def Or_comm_ : (p or q) ▸ (q or p) := sorry

def Or_comm_R : Γ ▸ (p or q) → Γ ▸ (q or p) := To_Right_Rule Or_comm_

-- Contrapositive and logical operations on proofs
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

def Impl_To_Right_Rule : (Γ ▸ (p ⇒ q)) → (Γ ▸ p → Γ ▸ q) := sorry

def Right_Rule_Impl : ((Γ ▸ p) → (Γ ▸ q)) → ((Γ ▸ (p ⇒ r)) → (Γ ▸ (q ⇒ r))) := sorry

def Impl_Right_Rule : ((Γ ▸ p) → (Γ ▸ q)) → ((Γ ▸ (r ⇒ p)) → (Γ ▸ (r ⇒ q))) := sorry

def Left_And_Impl_Right_Rule : ((Γ ▸ p₁) → (Γ ▸ q)) → ((Γ ▸ ((p₁ and p₂) ⇒ r)) → (Γ ▸ ((q and p₂) ⇒ r))) := sorry

def Right_And_Impl_Right_Rule : ((Γ ▸ p₂) → (Γ ▸ q)) → ((Γ ▸ ((p₁ and p₂) ⇒ r)) → (Γ ▸ ((p₁ and q) ⇒ r))) := sorry

def Left_And_Right_Rule_Impl : ((Γ ▸ p₁) → (Γ ▸ q)) → ((Γ ▸ (r ⇒ (p₁ and p₂))) → (Γ ▸ (r ⇒ (q and p₂)))) := sorry

def Right_And_Right_Rule_Impl : ((Γ ▸ p₂) → (Γ ▸ q)) → ((Γ ▸ (r ⇒ (p₁ and p₂))) → (Γ ▸ (r ⇒ (p₁ and q)))) := sorry

end prf

end first_order
