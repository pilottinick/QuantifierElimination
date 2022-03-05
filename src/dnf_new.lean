import prf
import tactic

namespace first_order

section dnf

variables (L : language) (Γ : ℕ → formula L)

def for_all_equiv_dnf : ∀ φ : formula L, ∃ ψ : dnf L, Γ ▸ φ ↔ Γ ▸ ψ := begin
  intro φ,
  induction φ,
  existsi ↑atomic.falsum, 
  simp,
end

end dnf

end first_order