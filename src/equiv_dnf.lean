/- This file contains a proof that all formulas φ in some language L are logically
   equivalent to a formula ψ where ψ is in disjunctive normal form. 
   Outline of the proof:
   We induct on the number of "bad connectives" n, which counts the number of 
   connectives in a formula φ such that the sub-formula covered by that connective
   is not in disjunctive normal form.
    - If there are zero bad connectives, then φ is already is disjunctive normal form
      - See bc_eq_zero_dnf
    - If there is one bad connective, then we induct on the structure of φ
      - If the formula is atomic, it is already in disjunctive normal form
      - If the formula is ∼φ, we induct on the structure of φ
        - Since there is one bad connective, then φ is in dnf
          - See not_bc_eq_one_phi_dnf
        - If φ is atomic then ∼φ is in dnf
        - If φ is ∼∼φ₁, then since ∼φ₁ is in dnf it is either the negation of
          an atomic formula or the conjunction of atomic formulas
          - See neg_dnf_phi_atomic_or_disj_neg_atomic
          - In either case ∼∼φ₁ is equivalent to φ₁ which is in dnf
        - If φ is ∼(φ₁ or φ₂), then since (φ₁ or φ₂) is in dnf then both
          φ₁ and φ₂ are in disjunctive normal form.
          - By Demorgans laws, φ ≃ (∼φ₁ and ∼φ₂)
          - So we reduce to the case where φ = (φ₁ and φ₂) with one bad connective
      - If the formula is (φ₁ and φ₂), then since there is one bad connective
        both φ₁ and φ₂ are in dnf
        - We make use of a theorem characterizing (non-first order) formulas in dnf: a formula 
          is in dnf if and only if it is a disjunction of conjunctions of literals. 
          - See dnf_iff_disj_conj_lit
        - The conjunction of two formulas which are disjunctions of conjunctions of literals is
          a conjunction of disjunctions of literals
          - See conj_disj_conj_lit_equiv_disj_conj_lit
      - If the formula is (φ₁ or φ₂), then since there is one bad connective 
        both φ₁ and φ₂ are in dnf
        - The disjuction of two formulas which are disjunctions of conjunctions of literals is
          a conjunction of disjunctions of literals
          - See disj_disj_conj_lit_disj_conj_lit
      - TODO: If the formula is (all n φ)...
    - If there is more than one bad connective, then by induction the subformulas of the
      top-most connective can be written in disjunctive normal form. Now we have reduced to the case
      where the top-most connective is the only bad connective and we apply the base case                
-/

import prf
import dnf
import dcl

namespace first_order

section formula

variables (L : language) (Γ : list (formula L)) (p q φ φ₁ φ₂ : formula L)

/- If a formula is equivalent to a formula in dnf -/
attribute [simp]
def equiv_dnf (φ : formula L) := ∃ ψ : formula L, (dnf _ ψ) ∧ (Γ ▸ φ ↔ Γ ▸ ψ)

/- Converts any right rule into a equiv_dnf right rule -/
def Right_Rule_equiv_dnf : (Γ ▸ p → Γ ▸ q) → ((equiv_dnf _ Γ p) → (equiv_dnf _ Γ q)) := sorry

/- If a formula is in dnf it is equivalent to a formula in dnf -/
lemma dnf_equiv_dnf : dnf _ φ → equiv_dnf _ Γ φ := begin
  intro φdnf,
  simp,
  existsi φ,
  apply and.intro,
  apply φdnf,
  apply iff.intro,
  intro h, apply h,
  intro h, apply h,
end

/- If a formula is equivalent to a formula which is a disjunction of conjunction of literals -/
attribute [simp]
def equiv_disj_conj_lit (φ : formula L) := ∃ ψ : formula L, (disj_conj_lit _ ψ) ∧ (Γ ▸ φ ↔ Γ ▸ ψ)

/- A formula which is a disjunction of conjunction of literals is equivalent to a disjunction of conjunction of literals -/
def disj_conj_lit_equiv_disj_conj_lit : disj_conj_lit _ φ → equiv_disj_conj_lit _ Γ φ := sorry

/- A formula is equivalent to a formula in dnf if and only if it is equivalent to a formula which is
   a disjunction of conjunctions of literals -/
lemma equiv_dnf_iff_equiv_disj_conj_lit : equiv_dnf _ Γ φ ↔ equiv_disj_conj_lit _ Γ φ := begin
  -- TODO: Figure out how to simplify by applying in paralel
  apply iff.intro,
  intro φdnf,
  apply exists.elim φdnf,
  intros ψ h,
  existsi ψ,
  apply and.intro,
  apply (dnf_iff_disj_conj_lit _ ψ).mp (and.elim_left h),
  apply and.elim_right h,
  intro φdcl,
  apply exists.elim φdcl,
  intros ψ h,
  existsi ψ,
  apply and.intro,
  apply (dnf_iff_disj_conj_lit _ ψ).mpr (and.elim_left h),
  apply and.elim_right h,
end

/- The conjunction of disjunctions of conjunctions of literals is equivalent to a conjunction of disjunctions of literals -/
lemma conj_disj_conj_lit_equiv_disj_conj_lit : disj_conj_lit _ φ₁ → disj_conj_lit _ φ₂ → equiv_disj_conj_lit _  Γ (φ₁ and φ₂) := begin
  intros φ₁dcl φ₂dcl,
  apply exists.elim φ₁dcl,
  intros p₁ h₁',
  apply exists.elim h₁',
  intros P₁ h₁,
  apply exists.elim φ₂dcl,
  intros p₂ h₂',
  apply exists.elim h₂',
  intros P₂ h₂,  
  induction P₁,
  induction P₂,
  simp at h₁ h₂,
  have p₁conj_lit : conj_lit _ p₁ := and.elim_right h₁,
  have p₂conj_lit : conj_lit _ p₂ := and.elim_right h₂,
  apply disj_conj_lit_equiv_disj_conj_lit,
  apply conj_lit_disj_conj_lit,
  apply conj_conj_lit_conj_lit,
  rw and.elim_left h₁,
  assumption,
  rw and.elim_left h₂,
  assumption,
  simp at h₁ h₂,
  admit,
  admit,
end

/- And case of dnf with one bad connective -/
lemma and_bc_eq_one_equiv_dnf : (dnf_bad_connectives _ (φ₁ and φ₂) = 1) → equiv_dnf _ Γ (φ₁ and φ₂) := begin
  intro bc,
  have φ₁φ₂dnf : dnf _ φ₁ ∧ dnf _ φ₂ := and_bc_eq_one_phi_dnf _ _ _ bc,
  have φ₁dcl : disj_conj_lit _ φ₁ := (dnf_iff_disj_conj_lit _ _).mp (and.elim_left φ₁φ₂dnf),
  have φ₂dcl : disj_conj_lit _ φ₂ := (dnf_iff_disj_conj_lit _ _).mp (and.elim_right φ₁φ₂dnf),
  have φ₁aφ₂equiv_dcl : equiv_disj_conj_lit _ Γ (φ₁ and φ₂) := 
    by  { apply conj_disj_conj_lit_equiv_disj_conj_lit, repeat { assumption }, },
  apply (equiv_dnf_iff_equiv_disj_conj_lit _ _ _).mpr,
  assumption,
end

/- Not case of dnf with one bad connective -/
lemma not_bc_eq_one_equiv_dnf : (dnf_bad_connectives _ ∼φ = 1) → equiv_dnf _ Γ ∼φ := begin
  intro bc,
  have φdnf : dnf _ φ := not_bc_eq_one_phi_dnf _ φ bc,
  induction φ,
  any_goals { by { apply dnf_equiv_dnf, simp } },
  rename φ_ᾰ φ,
  have φdnf : dnf _ φ := not_not_bc_eq_one_phi_dnf _ φ bc,
  apply Right_Rule_equiv_dnf _ _ _ _ Double_negation_intro_R,
  apply dnf_equiv_dnf _ Γ φ φdnf,
  rename φ_ᾰ φ₁, rename φ_ᾰ_1 φ₂,
  have φ₁φ₂dnf : dnf _ φ₁ ∧ dnf _ φ₂ := or_dnf_phi_dnf _ φ₁ φ₂ φdnf,
  have φ₁dnf : dnf _ φ₁ := φ₁φ₂dnf.left,
  have φ₂dnf : dnf _ φ₂ := φ₁φ₂dnf.right,
  apply Right_Rule_equiv_dnf,
  apply DeMorganAnd_R,
  have nφ₁dnf_or_bc_eq_one : dnf _ (∼φ₁) ∨ dnf_bad_connectives _ (∼φ₁) = 1 := begin 
      apply dnf_neg_dnf_or_bc_eq_one, apply φ₁dnf 
    end,
  have nφ₂dnf_or_bc_eq_one : dnf _ (∼φ₂) ∨ dnf_bad_connectives _ (∼φ₂) = 1 := begin 
      apply dnf_neg_dnf_or_bc_eq_one, apply φ₂dnf 
    end,
  have nφ₁equiv_dnf : equiv_dnf _ Γ (∼φ₁) := begin
      apply or.elim nφ₁dnf_or_bc_eq_one,
      intro left,
      apply dnf_equiv_dnf _ Γ (∼φ₁) left,
      intro right,
      apply φ_ih_ᾰ right φ₁dnf,
    end,
  have nφ₂equiv_dnf : equiv_dnf _ Γ (∼φ₂) := begin
      apply or.elim nφ₂dnf_or_bc_eq_one,
      intro left,
      apply dnf_equiv_dnf _ Γ (∼φ₂) left,
      intro right,
      apply φ_ih_ᾰ_1 right φ₂dnf,
    end,
    have nφ₁anφ₂bc_eq_one : dnf_bad_connectives _ (∼φ₁ and ∼φ₂) = 1 := sorry,
    apply and_bc_eq_one_equiv_dnf,
    apply nφ₁anφ₂bc_eq_one,
    -- TODO: All case
    admit,
end

/- Or case of dnf with one bad connective -/
lemma or_bc_eq_one_equiv_dnf : dnf_bad_connectives _ (φ₁ or φ₂) = 1 →
                                equiv_dnf _ Γ (φ₁ or φ₂) := begin
  intro bc,
  have φ₁φ₂dnf : dnf _ φ₁ ∧ dnf _ φ₂ := or_bc_eq_one_phi_dnf _ _ _ bc,
  cases φ₁,
  all_goals { cases φ₂ },
  -- TODO
  all_goals { admit },
end

/- All case of dnf with one bad connective -/
lemma all_bc_eq_one_equiv_dnf : ∀ n : ℕ, dnf_bad_connectives _ (formula.all n φ) = 1 → 
    equiv_dnf _ Γ (formula.all n φ) := sorry

/- If φ has one bad connective, then is it equivalent to a formula in dnf -/
theorem bc_eq_one_equiv_dnf : dnf_bad_connectives _ φ = 1 → equiv_dnf _ Γ φ := begin
  intro bc,
  -- Case 2: Exactly one bad connective, induct on φ
  induction φ,
  -- Case 2a : Trivial cases
  any_goals { by { apply dnf_equiv_dnf, simp } },
  -- Case 2b : Not case
  apply not_bc_eq_one_equiv_dnf _ _ _ bc,
  -- Case 2c : Or case
  apply or_bc_eq_one_equiv_dnf _ _ _ _ bc,
  -- Case 2d : All case
  apply all_bc_eq_one_equiv_dnf _ _ _ _ bc,
end

theorem for_all_equiv_dnf : equiv_dnf _ Γ φ := begin
  have h : ∃ n, dnf_bad_connectives _ φ = n := begin existsi dnf_bad_connectives _ φ, refl, end,
  apply exists.elim h,
  intros n bc,
  induction n,
  -- Case 1: No bad connectives
  apply dnf_equiv_dnf _ Γ φ,
  apply bc_eq_zero_dnf _ φ bc,
  induction n_n,
  -- Case 2: Exactly one bad connective
  apply bc_eq_one_equiv_dnf, assumption,
  -- Case 3 : Inductive step: more than one bad connective
  induction φ,
  -- Case 3a : Trivial cases
  any_goals { by { apply dnf_equiv_dnf, simp } },
  -- Case 3b : Not case
  have φequiv_dnf : equiv_dnf _ Γ φ_ᾰ := sorry,
  have bc_eq_one : dnf_bad_connectives _ ∼φ_ᾰ = 1 := sorry,
  apply bc_eq_one_equiv_dnf, assumption,
  -- Case 3c : Or case
  have φ₁equiv_dnf : equiv_dnf _ Γ φ_ᾰ := sorry,
  have φ₂equiv_dnf : equiv_dnf _ Γ φ_ᾰ_1 := sorry,
  have bc_eq_one : dnf_bad_connectives _ (φ_ᾰ or φ_ᾰ_1) = 1 := sorry,
  apply bc_eq_one_equiv_dnf, assumption,
  -- Case 3d : All case
  have φequiv_dnf : equiv_dnf _ Γ φ_ᾰ_1 := sorry,
  have bc_eq_one : dnf_bad_connectives _ (formula.all φ_ᾰ φ_ᾰ_1) = 1 := sorry,
  apply bc_eq_one_equiv_dnf, assumption,
end

end formula

end first_order