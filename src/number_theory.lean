import quantifier_elimination
import data.nat.basic

namespace number_theory

open first_order

/- The functions of number theory with successor -/
inductive NT_succ_func : ℕ → Type
| zero : NT_succ_func 0
| succ : NT_succ_func 1

/- The relations of number theory with successor -/
inductive NT_succ_rel : ℕ → Type

/- The language of number theory with successor -/
def NT_succ : language :=
  ⟨NT_succ_func, NT_succ_rel⟩

notation ` zero ` := term.func NT_succ_func.zero ![]
notation ` succ `x := term.func NT_succ_func.succ ![x]

/- The axioms of number theory with successor -/
-- TODO: How to define axiom schemas?
def NT_succ_Γ : list (formula NT_succ) :=
  [((succ v₁) ≃ (succ v₂)) ⇒ (v₁ ≃ v₂), ∼((succ v₃) ≃ zero)]

end number_theory