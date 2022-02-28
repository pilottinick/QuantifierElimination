/- This file contains a proof of the characterization of propositions in disjunctive normal formula.
   A proposition is in disjunctive normal form if and only if it is a conjunction of disjunctions of literals -/

import language
import dnf

namespace first_order

section formula

variables (L : language) (Γ : list (formula L)) (p q φ φ₁ φ₂ : formula L)

/- Conjunctions of literals are disjunctions of conjunctions of literals -/
lemma conj_lit_disj_conj_lit : conj_lit _ φ → disj_conj_lit _ φ := begin
  intro φconj_lit,
  simp,
  existsi φ,
  existsi list.nil,
  simp,
  assumption,
end

/- Atomic formulas are conjunctions of literals -/
lemma atomic_conj_lit : atomic _ φ → conj_lit _ φ := begin
  intro atom,
  cases φ,
  existsi F,
  existsi list.nil,
  simp,
  existsi φ_ᾰ ≃ φ_ᾰ_1,
  existsi list.nil,
  simp,
  existsi formula.rel φ_ᾰ φ_ᾰ_1,
  existsi list.nil,
  simp,
  repeat { simp at atom, apply false.elim atom },
end

/- Atomic formulas are disjunctions of conjunctions of literals -/
lemma atomic_disj_conj_lit : atomic _ φ → disj_conj_lit _ φ := begin
  intro atom,
  apply conj_lit_disj_conj_lit,
  apply atomic_conj_lit,
  assumption,
end

/- Negations of atomic formulas are conjunctions of literals -/
lemma neg_atomic_conj_lit : neg_atomic _ φ → conj_lit _ φ := begin
  intro atom,
  cases φ,
  existsi F,
  existsi list.nil,
  simp,
  existsi φ_ᾰ ≃ φ_ᾰ_1,
  existsi list.nil,
  simp,
  existsi formula.rel φ_ᾰ φ_ᾰ_1,
  existsi list.nil,
  simp at *,
  existsi ∼φ,
  existsi list.nil,
  simp,
  assumption,
  repeat { simp at atom, apply false.elim atom },
end

/- Negations of atomic formulas are disjunctions of conjunctions of literals -/
lemma neg_atomic_disj_conj_lit : neg_atomic _ φ → disj_conj_lit _ φ := begin
  intro atom,
  apply conj_lit_disj_conj_lit,
  apply neg_atomic_conj_lit,
  assumption,
end

/- Conjunctions of two atomic formulas are conjunctions of literals -/
lemma conj_atomic_conj_lit : atomic _ φ₁ → atomic _ φ₂ → conj_lit _ (φ₁ and φ₂) := begin
  intros atom1 atom2,
  existsi φ₁,
  existsi (φ₂::[]),
  simp,
  repeat { split },
  all_goals { apply atomic_lit, assumption },
end

/- Conjunctions of two atomic formulas are conjugations of literals -/
lemma conj_atomic_disj_conj_lit : atomic _ φ₁ → atomic _ φ₂ → disj_conj_lit _ (φ₁ and φ₂) := begin
  intros atom1 atom2,
  apply conj_lit_disj_conj_lit,
  apply conj_atomic_conj_lit _ _ _ atom1 atom2,
end

/- If ∼φ is a disjunction of conjunction of literals then φ is atomic or a disjunction of two negative atomic formulas -/
lemma neg_disj_conj_lit_phi_atomic_or_disj_neg_atomic : disj_conj_lit _ ∼φ → (atomic _ φ ∨ disj_neg_atomic _ φ) := begin
  intro dcl,
  -- induction φ,
  cases φ,
  repeat { simp },
  -- rename φ_ᾰ φ,
  apply exists.elim dcl,
  intros p ph',
  apply exists.elim ph',
  intros P ph,
  have nnp_disj : ∼∼φ = Disj p P := and.elim_left ph,
  cases P,
  simp at nnp_disj,
  have p_conj_lit : conj_lit _ p := and.elim_left (and.elim_right ph),
  rw ← nnp_disj at p_conj_lit,
  apply exists.elim p_conj_lit,
  intros q qh',
  apply exists.elim qh',
  intros Q qh,
  have nnp_conj : ∼∼φ = Conj q Q := and.elim_left qh,
  cases Q,
  simp at nnp_conj,
  have q_lit : literal _ q := and.elim_left (and.elim_right qh),
  rw ← nnp_conj at q_lit,
  simp at q_lit,
  apply false.elim q_lit,
  simp at nnp_conj,
  apply false.elim nnp_conj,
  simp at nnp_disj,
  apply false.elim nnp_disj,
  rename φ_ᾰ φ₁, rename φ_ᾰ_1 φ₂,
  -- rename φ_ih_ᾰ  φ₁_ih, rename φ_ih_ᾰ_1 φ₂_ih,
  apply exists.elim dcl,
  intros p ph',
  apply exists.elim ph',
  intros P ph,
  have norp_disj : ∼(φ₁ or φ₂) = Disj p P := and.elim_left ph,
  cases P,
  simp at norp_disj,
  have norp_conj_lit : conj_lit _ p := and.elim_left (and.elim_right ph),
  rw ← norp_disj at norp_conj_lit,
  simp at norp_conj_lit,
  apply exists.elim norp_conj_lit,
  intros q qh',
  apply exists.elim qh',
  intros Q qh,
  have norp_conj : ∼(φ₁ or φ₂) = Conj q Q := and.elim_left qh,
  cases Q,
  simp at norp_conj,
  have norp_lit : literal _ q := and.elim_left (and.elim_right qh),
  rw ← norp_conj at norp_lit,
  simp at norp_lit,
  apply false.elim norp_lit,
  simp at norp_conj,
  -- TODO
  admit,
  admit,
  -- TODO: All case
  admit,
end

/- If φ₁ and φ₂ are conjunctions of literals then (φ₁ and φ₂) is conjunction of literals -/
lemma conj_conj_lit_conj_lit : conj_lit _ φ₁ → conj_lit _ φ₂ → conj_lit _ (φ₁ and φ₂) := sorry

/- If (φ₁ or φ₂) is a disjunction of conjunction of literals then φ₁ and φ₂ are disjuctions of conjunctions of literals -/
lemma or_disj_conj_lit_phi_conj_lit : disj_conj_lit _ (φ₁ or φ₂) → disj_conj_lit _ φ₁ ∧ disj_conj_lit _ φ₂ := begin
  intro dcl,
  apply exists.elim dcl,
  intros p hp',
  apply exists.elim hp',
  intros P hp,
  cases P,
  simp at hp,
  -- TODO
  admit,
  admit,
end

/- If φ₁ and φ₂ are disjunctions of conjunctions of literals then (φ₁ or φ₂) is a disjunction of conjunctions of literals -/
lemma disj_disj_conj_lit_disj_conj_lit : disj_conj_lit _ φ₁ → disj_conj_lit _ φ₂ → disj_conj_lit _ (φ₁ or φ₂) := sorry

/- A formula is in dnf if and only if it is a disjunction of conjunctions of literals -/
theorem dnf_iff_disj_conj_lit : dnf _ φ ↔ disj_conj_lit _ φ := begin
  apply iff.intro,
  intro φdnf,
  induction φ,
  any_goals { by { apply atomic_disj_conj_lit, simp } },
  have φ'dnf : (atomic _ φ_ᾰ) ∨ (disj_neg_atomic _ φ_ᾰ) :=
    neg_dnf_phi_atomic_or_disj_neg_atomic _ _ φdnf,
  apply or.elim φ'dnf,
  intro atom,
  apply neg_atomic_disj_conj_lit,
  simp, assumption,
  intro conj,
  apply exists.elim conj,
  intros φ₁ conj',
  apply exists.elim conj',
  intros φ₂ conj'',
  rw (and.elim_left conj''),
  apply conj_atomic_disj_conj_lit,
  apply and.elim_left (and.elim_right conj''),
  apply and.elim_right (and.elim_right conj''),
  unfold disj_conj_lit,
  rename φ_ᾰ φ₁, rename φ_ᾰ_1 φ₂,
  rename φ_ih_ᾰ φ₁_ih, rename φ_ih_ᾰ_1 φ₂_ih,
  have φ₁φ₂dnf : dnf _ φ₁ ∧ dnf _ φ₂ := or_dnf_phi_dnf _ _ _ φdnf,
  have φ₁dnf : dnf _ φ₁ := φ₁φ₂dnf.left,
  have φ₂dnf : dnf _ φ₂ := φ₁φ₂dnf.right,
  have φ₁dcl : disj_conj_lit _ φ₁ := φ₁_ih φ₁dnf,
  have φ₂dcl : disj_conj_lit _ φ₂ := φ₂_ih φ₂dnf,
  apply exists.elim φ₁dcl,
  intros p₁ p₁h',
  apply exists.elim p₁h',
  intros P₁ p₁h,
  apply exists.elim φ₂dcl,
  intros p₂ p₂h',
  apply exists.elim p₂h',
  intros P₂ p₂h,
  existsi p₁,
  existsi (P₁ ++ (p₂::[]) ++ P₂),
  rw disj_append,
  rw ← and.elim_left p₁h,
  rw ← and.elim_left p₂h,
  split,
  simp,
  split,
  apply and.elim_left (and.elim_right p₁h),
  intros p' h,
  have p'h : p' ∈ P₁ ∨ p' ∈ [p₂] ∨ p' ∈ P₂ := sorry,
  apply or.elim p'h,
  intro p'P₁,
  apply (and.elim_right (and.elim_right p₁h) p') p'P₁,
  intro p'P,
  apply or.elim p'P,
  intro p'p₂,
  have p'eqp₂ : p' = p₂ := sorry,
  rw p'eqp₂, 
  apply (and.elim_left (and.elim_right p₂h)),
  intro p'P₂,
  apply (and.elim_right (and.elim_right p₂h) p') p'P₂,
  -- TODO: All case - This isn't part of the theorem so will need to specialize the statement of the result to prop
  admit,

  -- Reverse direction
  intro dcl,
  induction φ,
  any_goals { by { repeat { simp } } },
  rename φ_ᾰ φ,
  have φatom_or_disj_neg_atomic : atomic _ φ ∨ disj_neg_atomic _ φ := 
        neg_disj_conj_lit_phi_atomic_or_disj_neg_atomic _ _ dcl,
  apply or.elim φatom_or_disj_neg_atomic,
  intro φatom,
  apply neg_atomic_dnf _ _ φatom,
  intro φdisj_neg_atomic,
  apply disj_neg_atomic_neg_dnf _ _ φdisj_neg_atomic,
  rename φ_ᾰ φ₁, rename φ_ᾰ_1 φ₂,
  rename φ_ih_ᾰ φ₁_ih, rename φ_ih_ᾰ_1 φ₂_ih,
  have φ₁φ₂dcl : disj_conj_lit _ φ₁ ∧ disj_conj_lit _ φ₂ := or_disj_conj_lit_phi_conj_lit _ _ _ dcl,
  have φ₁dcl : disj_conj_lit _ φ₁ := φ₁φ₂dcl.left,
  have φ₂dcl : disj_conj_lit _ φ₂ := φ₁φ₂dcl.right,
  apply dnf_or_dnf,
  apply φ₁_ih φ₁dcl, 
  apply φ₂_ih φ₂dcl,
  -- TODO: All case - This isn't part of the theorem so will need to specialize the statement of the result to prop
  admit,
end

end formula

end first_order