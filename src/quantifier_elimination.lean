import prf

namespace first_order

section quantifier_elimination

variables (L : language) (Γ : list (formula L)) (φ : formula L)

/-- If a theory Γ has quantifier elimination -/
def has_qe := ∀ φ, ∃ ψ, (is_quantifier_free _ ψ) ∧ (Γ ▸ φ ↔ Γ ▸ ψ)

/-- If a theory Γ has quantifier elimination on DNF formulas -/
def has_qe_dnf := ∀ φ : (formula L), (is_dnf _ φ) → ∃ ψ, (is_quantifier_free _ ψ) ∧ (Γ ▸ ψ ↔ Γ ▸ ψ)

lemma has_qe_dnf_implies_has_eq : (has_qe_dnf _ Γ) → (has_qe _ Γ) := sorry

end quantifier_elimination

end first_order