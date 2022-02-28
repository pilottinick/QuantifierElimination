import equiv_dnf

namespace first_order

section quantifier_elimination

variables (L : language) (Γ : list (formula L)) (φ ψ : formula L)

/- If a formula has has quantifier elimination in a theory -/
attribute [simp]
def qe_form (φ : formula L) := ∃ ψ, (quantifier_free _ ψ) ∧ (Γ ▸ φ ↔ Γ ▸ ψ)

/- If a theory Γ has quantifier elimination -/
attribute [simp]
def qe := ∀ (φ : formula L), (qe_form _ Γ φ)

/- If a theory Γ has quantifier elimination on DNF formulas -/
attribute [simp]
def qe_dnf := ∀ (φ : formula L), (dnf _ φ) → qe_form _ Γ φ

/- If a theory Γ has quantifier elimination on quantified atomic formulas -/
attribute [simp]
def qe_quantified_atomic := ∀ (φ : formula L), (quantified_atomic _ φ) → qe_form _ Γ φ

/- If a theory Γ has quantifier elimination on quantifier free formulas -/
attribute [simp]
def qe_qf := ∀ (φ : formula L), (quantifier_free _ φ) → qe_form _ Γ φ

/- All theories have quantifier elimination on quantifier free formulas -/
def for_all_qe_qf : qe_qf _ Γ := begin
  intros φ φqf,
  existsi φ,
  split,
  assumption,
  simp,
end

/- If a theory has quantifier elimination on dnf formulas it has quantifier elimination -/
lemma qe_dnf_qe : (qe_dnf _ Γ) → (qe _ Γ) := begin
  intro Γqe_dnf,
  intro φ,
  have φequiv_dnf : equiv_dnf _ Γ φ := for_all_equiv_dnf _ _ _,
  apply exists.elim φequiv_dnf,
  intros ψ ψdnf,
  apply exists.elim (Γqe_dnf ψ (and.elim_left ψdnf)),
  intros ψ₀ ψ₀qf,
  existsi ψ₀,
  split,
  apply and.elim_left ψ₀qf,
  split,
  intro Γφ,
  apply (and.elim_right ψ₀qf).mp ((and.elim_right ψdnf).mp Γφ),
  intro Γψ₀,
  apply (and.elim_right ψdnf).mpr (((and.elim_right ψ₀qf).mpr Γψ₀)),
end

end quantifier_elimination

end first_order