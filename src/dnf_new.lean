import prf

namespace first_order

section dnf

variables (L : language) (Γ : ℕ → formula L)

def for_all_equiv_dnf : ∀ φ : formula L, ∃ ψ : dnf L, Γ ▸ φ ↔ Γ ▸ ψ := begin
  intro φ,
  cases φ,
  existsi ↑atomic.falsum,
  refl,
end

end dnf

end first_order