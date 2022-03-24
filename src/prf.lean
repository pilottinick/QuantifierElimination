import language
import data.nat.parity

namespace first_order

section prf

variables {L : language} {n m : ℕ}

inductive Prf (A : Type) [has_coe A (formula L)] : list (formula L) → formula L → Prop
| Axiom : ∀ {Γ : list (formula L)} a φ, a = φ → Prf Γ φ
| Assumption : ∀ {Γ : list (formula L)} n φ, Γ.nth n = some φ → Prf Γ φ
| Bot_elim : ∀ {Γ : list (formula L)} φ, Prf Γ F → Prf Γ φ
| Not_elim : ∀ {Γ : list (formula L)} φ ψ, Prf Γ ∼φ → Prf Γ φ → Prf Γ ψ
| By_contradiction : ∀ {Γ : list (formula L)} φ, Prf (∼φ::Γ) F → Prf Γ φ
| Or_intro_left : ∀ {Γ : list (formula L)} φ ψ, Prf Γ φ → Prf Γ (φ or ψ)
| Or_intro_right : ∀ {Γ : list (formula L)} φ ψ, Prf Γ ψ → Prf Γ (φ or ψ)
| Or_elim : ∀ {Γ : list (formula L)} φ ψ χ, Prf Γ (φ or ψ) → Prf (φ::Γ) χ → Prf (ψ::Γ) χ → Prf Γ χ
| All_intro : ∀ {Γ : list (formula L)} φ n m, var_not_free_in_axioms_context m A Γ → 
    Prf Γ (replace_formula_with n (term.var m) φ) → Prf Γ (formula.all n φ)
| All_elim : ∀ {Γ : list (formula L)} n t φ ψ, Prf Γ (formula.all n φ) → 
    substitutable_for t n φ → Prf ((replace_formula_with n t φ) :: Γ) ψ → Prf Γ ψ
| Cut : ∀ {Γ : list (formula L)} φ ψ, Prf Γ φ → Prf (φ::Γ) ψ → Prf Γ ψ

open Prf

notation A ` ∣ ` Γ` ⊢ `φ := Prf A Γ φ

notation A` ⊢ `φ := Prf A list.nil φ

variables {p p₁ p₂ q q₁ q₂ r s φ : formula L}

variables {Γ γ : list (formula L)} {P Q : list (formula L)} {A : Type} [has_coe A (formula L)]

-- If a set of Assumptions is consistent
def is_consistent (Γ : list (formula L)) :=  ∀ φ : formula L, ¬((A∣Γ ⊢ φ) ∧ (A∣Γ ⊢ ∼φ))

-- If a set of Assumption is complete
def is_complete (Γ : list (formula L)) := ∀ φ : formula L, (A∣Γ ⊢ φ) ∨ (A∣Γ ⊢ ∼φ)

-- Weakening
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



lemma nth_append_r : ∀ {A : Type} {l1 l2 : list A} n, (l1 ++ l2).nth (n + l1.length) = l2.nth n := begin
  intros A l1 l2 n,
  induction l1,
  simp,
  simp,
  rw ← add_assoc,
  rw ← add_comm,
  rw nat.one_add,
  simp,
  apply l1_ih,
end

def weakening : (forall n x, γ.nth n = some x -> ∃ m, Γ.nth m = some x) →
  (A∣γ ⊢ p) → (A∣Γ ⊢ p) := begin
    intros h γp, revert Γ h,
    induction γp, all_goals { intros Γ h },
      sorry,
      { cases (h _ _ γp_ᾰ), apply Assumption, assumption, },
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

def weakening_append : (A∣γ ⊢ p) → (A∣(γ ++ Γ) ⊢ p) := begin
    apply weakening,
    intros, existsi n,
    apply nth_append_some, assumption,
  end

-- Converting natural deduction rules into sequent calculus rules
def R_ : (A∣[p] ⊢ q) → ((A∣Γ ⊢ p) → (A∣Γ ⊢ q)) := begin
    intros pq Γp,
    apply Cut,
    apply Γp,
    apply weakening _ pq,
    intros n φ pn_eq_φ,
    cases n, simp at pn_eq_φ,
    existsi 0, simp, assumption,
    contradiction,
  end

variables (h : formula L) (l : list (formula L))

def To_Right_Rule_List : (A∣(h::l) ⊢ q) → ∀ Γ : (list (formula L)), (A∣Γ ⊢ h) → (A∣(l ++ Γ) ⊢ q) := begin
    intros h1 Γ h2,
    apply Cut,
    apply weakening _ h2,
    intros n1 h3 h4,
    existsi (n1 + l.length),
    rw nth_append_r,
    apply h4,
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


def L_ : (A∣[p] ⊢ q) → (A∣Γ ⊢ p) → (A∣(q::Γ) ⊢ r) → (A∣Γ ⊢ r) := begin
    intros h1 h2 h3,
    apply Cut,
    apply R_,
    apply h1,
    apply h2,
    apply h3,
  end

def L_R_ : ((A∣Γ ⊢ p) → (A∣Γ ⊢ q)) → (A∣Γ ⊢ p) → (A∣(q::Γ) ⊢ r) → (A∣Γ ⊢ r) := begin
  intros h1 h2 h3,
  apply Cut,
  apply h1,
  apply h2,
  apply h3,
end

def Proves_impl : (A∣(p::Γ) ⊢ q) → (A∣Γ ⊢ (p ⇒ q)) := begin
  intro h, simp,
  apply By_contradiction,
  apply Not_elim,
  apply Assumption 0, refl,
  apply Cut p,
  apply By_contradiction,
  apply Not_elim,
  apply Assumption 1, refl,
  apply Or_intro_left,
  apply Assumption 0, refl,
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

def R_Not_ : ((A∣Γ ⊢ p) → (A∣Γ ⊢ q)) → ((A∣Γ ⊢ ∼p) → (A∣Γ ⊢ ∼q)) := sorry

def R_Eq_Not_ : ((A∣Γ ⊢ p) ↔ (A∣Γ ⊢ q)) → ((A∣Γ ⊢ ∼p) ↔ (A∣Γ ⊢ ∼q)) := sorry

def R_Left_Or_ : ((A∣Γ ⊢ p) → (A∣Γ ⊢ q)) → ((A∣Γ ⊢ (p or r)) → (A∣Γ ⊢ (q or r))) := sorry

def R_Eq_Left_Or_ : ((A∣Γ ⊢ p) ↔ (A∣Γ ⊢ q)) → ((A∣Γ ⊢ (p or r)) ↔ (A∣Γ ⊢ (q or r))) := sorry

def R_Right_Or_ : ((A∣Γ ⊢ p) → (A∣Γ ⊢ q)) → ((A∣Γ ⊢ (r or p)) → (A∣Γ ⊢ (r or q))) := sorry

def R_Eq_Right_Or_ : ((A∣Γ ⊢ p) ↔ (A∣Γ ⊢ q)) → ((A∣Γ ⊢ (r or p)) ↔ (A∣Γ ⊢ (r or q))) := sorry

def R_Or_ : ((A∣Γ ⊢ p₁) → (A∣Γ ⊢ q₁)) → ((A∣Γ ⊢ p₂) → (A∣Γ ⊢ q₂)) → ((A∣Γ ⊢ (p₁ or p₂)) → ((A∣Γ ⊢ (q₁ or q₂)))) := sorry

def R_Eq_Or_ : ((A∣Γ ⊢ p₁) ↔ (A∣Γ ⊢ q₁)) → ((A∣Γ ⊢ p₂) ↔ (A∣Γ ⊢ q₂)) → ((A∣Γ ⊢ (p₁ or p₂)) ↔ ((A∣Γ ⊢ (q₁ or q₂)))) := sorry

def R_Left_And_ : ((A∣Γ ⊢ p) → (A∣Γ ⊢ q)) → ((A∣Γ ⊢ (p and r)) → (A∣Γ ⊢ (q and r))) := sorry

def R_Eq_Left_And_ : ((A∣Γ ⊢ p) ↔ (A∣Γ ⊢ q)) → ((A∣Γ ⊢ (p and r)) ↔ (A∣Γ ⊢ (q and r))) := sorry

def R_Right_And_ : ((A∣Γ ⊢ p) → (A∣Γ ⊢ q)) → ((A∣Γ ⊢ (r and p)) → (A∣Γ ⊢ (r and q))) := sorry

def R_And_ : ((A∣Γ ⊢ p₁) → (A∣Γ ⊢ q₁)) → ((A∣Γ ⊢ p₂) → (A∣Γ ⊢ q₂)) → ((A∣Γ ⊢ (p₁ and p₂)) → ((A∣Γ ⊢ (q₁ and q₂)))) := sorry

def R_Eq_And_ : ((A∣Γ ⊢ p₁) ↔ (A∣Γ ⊢ q₁)) → ((A∣Γ ⊢ p₂) ↔ (A∣Γ ⊢ q₂)) → ((A∣Γ ⊢ (p₁ and p₂)) ↔ ((A∣Γ ⊢ (q₁ and q₂)))) := sorry

def R_All_ : ((A∣Γ ⊢ p) → (A∣Γ ⊢ q)) → ((A∣Γ ⊢ (all n p)) → (A∣Γ ⊢ (all n q))) := sorry

def R_Eq_All_ : ((A∣Γ ⊢ p) ↔ (A∣Γ ⊢ q)) → ((A∣Γ ⊢ (all n p)) ↔ (A∣Γ ⊢ (all n q))) := sorry

def R_Ex_ : ((A∣Γ ⊢ p) → (A∣Γ ⊢ q)) → ((A∣Γ ⊢ (exi n p)) → (A∣Γ ⊢ (exi n q))) := sorry 

def R_Eq_Ex_ : ((A∣Γ ⊢ p) ↔ (A∣Γ ⊢ q)) → ((A∣Γ ⊢ (exi n p)) ↔ (A∣Γ ⊢ (exi n q))) := sorry 

-- Basic intro and elim ND rules
def Not_intro : (A∣[(p ⇒ F)] ⊢ ∼p) := begin
    apply Or_elim,
    apply Assumption 0, refl,
    apply Assumption 0, refl,
    apply Bot_elim,
    apply Assumption 0, refl,
  end

def Not_impl : A∣[∼p] ⊢ (p ⇒ F) := begin
  apply Or_intro_left,
  apply Assumption 0, refl,
end

def Impl_not : A∣[(p ⇒ F)] ⊢ ∼p := begin
  apply Or_elim,
  apply Assumption 0, refl,
  apply Assumption 0, refl,
  apply R_ Not_intro,
  apply Assumption 1, refl,
end

def Double_negation_elim : A∣[∼∼p] ⊢ p := begin
    apply (By_contradiction p),
    apply Not_elim,
    apply Assumption 1, refl,
    apply Assumption 0, refl,
  end

def Double_negation_intro : A∣[p] ⊢ ∼∼p := begin
    apply R_ Not_intro,
    apply Proves_impl,
    apply Not_elim,
    apply Assumption 0, refl,
    apply Assumption 1, refl,
  end

def Top_intro : A∣[p] ⊢ T := begin
  apply By_contradiction,
  apply R_ Double_negation_elim,
  apply Assumption 0, refl,
end

def Impl_elim_ : A∣[p, p ⇒ q] ⊢ q := begin
    apply Or_elim,
    apply Assumption 1, refl,
    apply Not_elim,
    apply Assumption 0, refl,
    apply Assumption 1, refl,
    apply Assumption 0, refl,
  end

def Impl_elim : (A∣Γ ⊢ p) → ((A∣Γ ⊢ (p ⇒ q)) → ((A∣Γ ⊢ q))) := begin
    intros h1 h2,
    apply Cut,
    apply h2,
    apply To_Right_Rule_List _ _ Impl_elim_,
    assumption,
  end

def And_intro : (A∣[p, q] ⊢ (p and q)) := begin
    apply R_ Not_intro,
    apply Proves_impl,
    apply Or_elim,
    apply Assumption 0, refl,
    apply Not_elim,
    apply Assumption 0, refl,
    apply Assumption 2, refl,
    apply Not_elim,
    apply Assumption 0, refl,
    apply Assumption 3, refl,
  end

def And_intro_R : (A∣Γ ⊢ p) → (A∣Γ ⊢ q) → (A∣Γ ⊢ (p and q)) := begin
    intros h1 h2,
    apply Cut,
    apply h2,
    apply To_Right_Rule_List _ _ And_intro,
    apply h1,
  end

def And_elim_left : A∣[(p and q)] ⊢ p := begin
      apply By_contradiction,
      apply Not_elim,
      apply Assumption 1, refl,
      apply Or_intro_left,
      apply Assumption 0, refl,
    end

def And_elim_right : A∣[(p and q)] ⊢ q := begin
      apply By_contradiction,
      apply Not_elim,
      apply Assumption 1, refl,
      apply Or_intro_right,
      apply Assumption 0, refl,
    end

def NonContradiction : A∣[(p and ∼p)] ⊢ F := begin
    apply Not_elim,
    apply And_elim_right,
    apply And_elim_left,
  end

-- DeMorgan laws
def DeMorganNotAnd : A∣[∼(p and q)] ⊢ (∼p or ∼q) := begin
    apply By_contradiction,
    apply Not_elim,
    apply Assumption 1, refl,
    apply Assumption 0, refl,
  end

def DeMorganNotOr : A∣[∼(p or q)] ⊢ (∼p and ∼q) := begin
    apply R_ Not_intro,
    apply Proves_impl,
    apply Not_elim,
    apply Assumption 1, refl,
    apply Or_elim,
    apply Assumption 0, refl,
    apply Or_intro_left,
    apply R_ Double_negation_elim,
    apply Assumption 0, refl,
    apply Or_intro_right,
    apply R_ Double_negation_elim,
    apply Assumption 0, refl,
  end

def ExcludedMiddle : A∣[p] ⊢ (q or ∼q) := begin
  apply By_contradiction,
  apply L_ DeMorganNotOr,
  apply Assumption 0, refl,
  apply L_ And_elim_left,
  apply Assumption 0, refl,
  apply Not_elim,
  apply Assumption 2, refl,
  apply Or_intro_right,
  apply Assumption 0, refl,
end

def DeMorganOr : A∣[(∼p or ∼q)] ⊢ ∼(p and q) := begin
    apply R_ Not_intro,
    apply Proves_impl,
    apply Or_elim,
    apply Assumption 1, refl,
    apply Not_elim,
    apply Assumption 0, refl,
    apply L_ And_elim_left,
    apply Assumption 1, refl,
    apply Not_elim,
    apply Assumption 1, refl,
    apply Assumption 0, refl,
    apply L_ And_elim_right,
    apply Assumption 1, refl,
    apply Not_elim,
    apply Assumption 1, refl,
    apply Assumption 0, refl,
  end

def DeMorganAnd : A∣[(∼p and ∼q)] ⊢ ∼(p or q) := begin
  apply By_contradiction,
  apply L_ Double_negation_elim,
  apply Assumption 0, refl,
  apply Or_elim,
  apply Assumption 0, refl,
  apply L_ And_elim_left,
  apply Assumption 3, refl,
  apply Not_elim,
  apply Assumption 0, refl,
  apply Assumption 1, refl,
  apply L_ And_elim_right,
  apply Assumption 3, refl,
  apply Not_elim,
  apply Assumption 0, refl,
  apply Assumption 1, refl,
end

-- Distribution of and and or
-- TODO: Right now there are 8 distribution rules, is there any way to simplify this?
def DistributionAndOrInLeft : A∣[(r and (p or q))] ⊢ ((r and p) or (r and q)) := begin
    apply L_ And_elim_right,
    apply Assumption 0, refl,
    apply L_ And_elim_left,
    apply Assumption 1, refl,
    apply Or_elim,
    apply Assumption 1, refl,
    apply Or_intro_left,
    apply And_intro_R,
    apply Assumption 1, refl,
    apply Assumption 0, refl,
    apply Or_intro_right,
    apply And_intro_R,
    apply Assumption 1, refl,
    apply Assumption 0, refl,
  end

def DistributionAndOrInRight : A∣[((p or q) and r)] ⊢ ((p and r) or (q and r)) := begin
  apply L_ And_elim_left,
  apply Assumption 0, refl,
  apply L_ And_elim_right,
  apply Assumption 1, refl,
  apply Or_elim,
  apply Assumption 1, refl,
  apply Or_intro_left,
  apply And_intro_R,
  apply Assumption 0, refl,
  apply Assumption 1, refl,
  apply Or_intro_right,
  apply And_intro_R,
  apply Assumption 0, refl,
  apply Assumption 1, refl,
end

def DistributionAndOrOutLeft : A∣[((r and p) or (r and q))] ⊢ (r and (p or q)) := begin
  apply And_intro_R,
  apply Or_elim,
  apply Assumption 0, refl,
  any_goals { by {
    apply L_ And_elim_left,
    repeat { apply Assumption 0, refl, }
  } },
  apply Or_elim,
  apply Assumption 0, refl,
  any_goals { by {
    apply L_ And_elim_right,
    apply Assumption 0, refl,
    { apply Or_intro_left, apply Assumption 0, refl } 
      <|>
    { apply Or_intro_right, apply Assumption 0, refl }
  } },
end

def DistributionAndOrOutRight : A∣[((p and r) or (q and r))] ⊢ ((p or q) and r) := begin
  apply And_intro_R,
  apply Or_elim,
  apply Assumption 0, refl,
  any_goals { 
    apply L_ And_elim_left,
    apply Assumption 0, refl,
    { apply Or_intro_left, apply Assumption 0, refl }
      <|>
    { apply Or_intro_right, apply Assumption 0, refl }
  },
  apply Or_elim,
  apply Assumption 0, refl,
  all_goals {
    apply L_ And_elim_right,
    repeat { apply Assumption 0, refl },
  },
end

def DistributionOrAndInLeft : A∣[(r or (p and q))] ⊢ ((r or p) and (r or q)) := begin
    apply Or_elim, 
    apply Assumption 0, refl,
    apply And_intro_R,
    apply Or_intro_left,
    apply Assumption 0, refl,
    apply Or_intro_left,
    apply Assumption 0, refl,
    apply And_intro_R,
    apply L_ And_elim_left,
    apply Assumption 0, refl,
    apply Or_intro_right,
    apply Assumption 0, refl,
    apply L_ And_elim_right,
    apply Assumption 0, refl,
    apply Or_intro_right,
    apply Assumption 0, refl,
  end

def DistributionOrAndOutRight : A∣[((p or r) and (q or r))] ⊢ ((p and q) or r) := begin
  apply L_ And_elim_left,
  apply Assumption 0, refl,
  apply L_ And_elim_right,
  apply Assumption 1, refl,
  apply Or_elim,
  apply Assumption 0, refl,
  apply Or_elim,
  apply Assumption 2, refl,
  apply Or_intro_left,
  apply And_intro_R,
  apply Assumption 0, refl,
  apply Assumption 1, refl,
  all_goals {
    apply Or_intro_right,
    apply Assumption 0, refl
  },
end

def DistributionOrAndOutLeft : A∣[((r or p) and (r or q))] ⊢ (r or (p and q)) := begin
  apply L_ And_elim_left,
  apply Assumption 0, refl,
  apply L_ And_elim_right,
  apply Assumption 1, refl,
  apply Or_elim,
  apply Assumption 0, refl,
  apply Or_intro_left,
  apply Assumption 0, refl,
  apply Or_elim,
  apply Assumption 2, refl,
  apply Or_intro_left,
  apply Assumption 0, refl,
  apply Or_intro_right,
  apply And_intro_R,
  apply Assumption 0, refl,
  apply Assumption 1, refl,
end

def DistributionOrAndInRight : A∣[((p or q) and r)] ⊢ ((p and r) or (q and r)) := begin
  apply L_ And_elim_left,
  apply Assumption 0, refl,
  apply L_ And_elim_right,
  apply Assumption 1, refl,
  apply Or_elim,
  apply Assumption 1, refl,
  apply Or_intro_left,
  apply And_intro_R,
  apply Assumption 0, refl,
  apply Assumption 1, refl,
  apply Or_intro_right,
  apply And_intro_R,
  apply Assumption 0, refl,
  apply Assumption 1, refl,
end

-- Commutativity rules 
def Or_comm : A∣[(p or q)] ⊢ (q or p) := begin
  apply Or_elim,
  apply Assumption 0, refl,
  apply Or_intro_right,
  apply Assumption 0, refl,
  apply Or_intro_left,
  apply Assumption 0, refl,
end

def And_comm_ : A∣[(p and q)] ⊢ (q and p) := begin
  apply And_intro_R,
  apply L_ And_elim_right,
  apply Assumption 0, refl,
  apply Assumption 0, refl,
  apply L_ And_elim_left,
  apply Assumption 0, refl,
  apply Assumption 0, refl,
end

def AndProves : ((A∣Γ ⊢ p)) ∧ ((A∣Γ ⊢ q)) → ((A∣Γ ⊢ (p and q))) := begin
    intros h,
    apply And_intro_R,
    apply and.elim_left h,
    apply and.elim_right h,
  end

def Contrapose : A∣[(p ⇒ q)] ⊢ (∼q ⇒ ∼p) := begin
  simp,
  apply Or_elim,
  apply Assumption 0, refl,
  apply Or_intro_right,
  apply Assumption 0, refl,
  apply Proves_impl,
  apply Not_elim,
  apply Assumption 0, refl,
  apply Assumption 1, refl,
end

def Ex_intro (n : ℕ) (t : term L) (φ : formula L) : 
  substitutable_for t n φ → (A∣Γ ⊢ (replace_formula_with n t φ)) → (A∣Γ ⊢ (exi n φ)) := sorry

def Ex_elim (n : ℕ) (t : term L) (φ : formula L) (ψ : formula L) : 
  var_not_free_in_axioms_context m A Γ → (A∣Γ ⊢ (exi n φ)) → (A∣(replace_formula_with n (term.var m) φ)::Γ ⊢ ψ) → (A∣Γ ⊢ ψ) := sorry

def All_To_Ex : A∣[(all n p)] ⊢ ∼(exi n ∼p) := begin
  apply R_ Double_negation_intro,
  apply R_All_ (R_ Double_negation_intro),
  apply Assumption 0, refl,
end

def Ex_To_All : A∣[∼(exi n ∼p)] ⊢ (all n p) := begin
  apply R_All_ (R_ Double_negation_elim),
  apply R_ Double_negation_elim,
  apply Assumption 0, refl,
end

def NotAll : A∣[∼(all n p)] ⊢ (exi n ∼p) := begin
  apply R_Not_ (R_All_ (R_ Double_negation_intro)),
  apply Assumption 0, refl,
end

def AllNot : A∣[(all n ∼p)] ⊢ ∼(exi n p) := begin
  apply R_ Double_negation_intro,
  apply Assumption 0, refl,
end

def NotEx : A∣[∼(exi n p)] ⊢ (all n ∼p) := begin
  apply L_ Double_negation_elim,
  apply Assumption 0, refl,
  apply Assumption 0, refl,
end

def ExNot : A∣[(exi n ∼p)] ⊢ ∼(all n p) := begin
  apply L_R_ (R_Not_ (R_All_ (R_ Double_negation_elim))),
  apply Assumption 0, refl,
  apply Assumption 0, refl,
end

def NotFreeAll : ((@var_not_free_in_axioms L n A _) ∧ ¬(free n p)) → (A∣[p] ⊢ (all n p)) := begin
  intro h,
  apply All_intro,
  split, apply h.left,
  intro m, cases m, simp, apply h.right,
  simp, 
  rw replace_formula_with_idem,
  apply Assumption 0, refl,
end

def AddAll : ¬(free n p) → ((A∣Γ ⊢ p) → (A∣Γ ⊢ (all n p))) := sorry

def RemoveAll : (A∣Γ ⊢ (all n p)) → (A∣Γ ⊢ p) := sorry

def AddEx : (A∣Γ ⊢ p) → (A∣Γ ⊢ (exi n p)) := sorry

def RemoveEx : ¬(free n p) → (A∣Γ ⊢ (exi n p)) → (A∣Γ ⊢ p) := sorry

def AllOrOut : (@var_not_free_in_axioms L n A _) → A∣[((all n p) or (all n q))] ⊢ (all n (p or q)) := begin
  intro h,
  apply All_intro _ _ n,
  split, assumption, 
  intro m, cases m, simp, simp,
  rw replace_formula_with_idem,
  apply Or_elim, apply Assumption 0, refl,
  all_goals { 
    apply All_elim n (v n),
    apply Assumption 0, refl,
    apply substitutable_for_idem,
    rw replace_formula_with_idem,
    { apply Or_intro_left, apply Assumption 0, refl } 
      <|>
    { apply Or_intro_right, apply Assumption 0, refl }
  },
end

def AllAndIn : (@var_not_free_in_axioms L n A _) → A∣[all n (p and q)] ⊢ ((all n p) and (all n q)) := begin
  intro h,
  apply AndProves, split,
  all_goals { 
    apply All_intro _ _ n,
    split, assumption, 
    intro m, cases m, simp, simp,
    apply All_elim n (v n),
      apply Assumption 0, refl,
      apply substitutable_for_idem,
      rw replace_formula_with_idem,
      rw replace_formula_with_idem,
      { apply R_ And_elim_right, apply Assumption 0, refl }
        <|> 
      { apply R_ And_elim_left, apply Assumption 0, refl, },
  }
end

def AllAndOut : (@var_not_free_in_axioms L n A _) → A∣[((all n p) and (all n q))] ⊢ (all n (p and q)) := begin
  intro h,
  apply All_intro _ _ n,
  split, assumption, 
  intro m, cases m, simp, simp,
  rw replace_formula_with_idem,
  apply And_intro_R,
  { 
    apply L_ And_elim_left, 
    apply Assumption 0, 
    refl,
    apply All_elim n (v n),
      apply Assumption 0, refl,
      apply substitutable_for_idem,
      rw replace_formula_with_idem,
      apply Assumption 0, refl,
  },
  {
    apply L_ And_elim_right, 
    apply Assumption 0, 
    refl,
    apply All_elim n (v n),
      apply Assumption 0, refl,
      apply substitutable_for_idem,
      rw replace_formula_with_idem,
      apply Assumption 0, refl,
  }
end

def ExOrIn : (@var_not_free_in_axioms L n A _) → A∣[(exi n (p or q))] ⊢ ((exi n p) or (exi n q)) := begin
  intro h,
  apply R_ DeMorganNotAnd,
  apply R_Not_ (R_ (AllAndIn h)),
  apply R_Not_ (R_All_ (R_ DeMorganNotOr)),
  apply Assumption 0, refl,
end

def ExOrOut : (@var_not_free_in_axioms L n A _) → A∣[((exi n p) or (exi n q))] ⊢ (exi n (p or q)) := begin
  intro h,
  apply R_Not_ (R_All_ (R_ DeMorganAnd)),
  apply R_Not_ (R_ (AllAndOut h)),
  apply R_ DeMorganOr,
  apply Assumption 0, refl,
end

def ExAndOut : (@var_not_free_in_axioms L n A _) → A∣[((exi n p) and (exi n q))] ⊢ (exi n (p and q))  := begin
  intro h,
  apply R_Not_ (R_All_ (R_ DeMorganOr)),
  apply R_Not_ (R_ (AllOrOut h)),
  apply R_ DeMorganAnd,
  apply Assumption 0, refl,
end

def SwapAll : (@var_not_free_in_axioms L n A _) → (@var_not_free_in_axioms L m A _) → 
    A∣[(all n (all m p))] ⊢ (all m (all n p)) := begin
  intros h₁ h₂,
  apply All_intro _ _ m,
    split, assumption, 
    intro m, cases m, simp, simp,
    rw replace_formula_with_idem,
  apply All_intro _ _ n, simp,
    split, assumption, 
    intro m, cases m, simp, simp,
    rw replace_formula_with_idem,
  apply All_elim n (v n),
    apply Assumption 0, refl,
    apply substitutable_for_idem,
    rw replace_formula_with_idem,
  apply All_elim m (v m),
    apply Assumption 0, refl,
    apply substitutable_for_idem,
    rw replace_formula_with_idem,
  apply Assumption 0, refl,
end

def SwapEx : (@var_not_free_in_axioms L n A _) → (@var_not_free_in_axioms L m A _) → 
    A∣[(exi n (exi m p))] ⊢ (exi m (exi n p)) := begin
  intros h₁ h₂,
  apply R_Not_ (R_All_ (R_ Double_negation_intro)),
  apply L_R_ (R_Not_ (R_All_ (R_ Double_negation_elim))),
  apply Assumption 0, refl,
  apply R_Not_ (R_ (SwapAll h₁ h₂)),
  apply Assumption 0, refl,
end

-- def SwapAllEx_R : ((A∣Γ ⊢ ∼(all n (exi m ∼p))) → ((A∣Γ ⊢ (exi m (all n p))) := sorry

-- def SwapExAll_R : ((A∣Γ ⊢ ∼(exi n (all m ∼p))) → ((A∣Γ ⊢ (all m (exi n p))) := sorry

end prf

end first_order
