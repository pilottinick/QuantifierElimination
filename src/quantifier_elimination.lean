import equiv_dnf

namespace first_order

section quantifier_elimination

variables (L : language) (Γ : list (formula L)) (φ ψ : formula L)

/- If a formula φ has has quantifier elimination in a theory -/
@[simp]
def qe_form (φ : formula L) := ∃ ψ, (quantifier_free _ ψ) ∧ (Γ ▸ φ ↔ Γ ▸ ψ)

/- If a theory Γ has quantifier elimination -/
@[simp]
def qe := ∀ (φ : formula L), (qe_form _ Γ φ)

/- If a theory Γ has quantifier elimination on quantified conjugations of literals -/
@[simp]
def qe_quantified_conj_lit := ∀ (φ : formula L), (quantified_conj_lit _ φ) → qe_form _ Γ φ

/- If a theory Γ has quantifier elimination on quantifier free formulas -/
@[simp]
def qe_qf := ∀ (φ : formula L), (quantifier_free _ φ) → qe_form _ Γ φ

/- All theories have quantifier elimination on quantifier free formulas -/
def for_all_qe_qf : qe_qf _ Γ := by { intros φ φqf, existsi φ, split, assumption, simp, }

/- If a theory has quantifer elimination on conjunctions of literals with 
   a single quantifier it has quantifier elimination -/
lemma qe_dnf_qe : (qe_quantified_conj_lit _ Γ) → (qe _ Γ) := sorry

/- Deciable sentences in a theory -/
def decidable_sent (φ : formula L) : Prop := (sentence _ φ) ∧ ((Γ ▸ φ ↔ Γ ▸ F) ∨ (Γ ▸ φ ↔ Γ ▸ T))

end quantifier_elimination

end first_order