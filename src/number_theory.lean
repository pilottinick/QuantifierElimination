import quantifier_elimination
import data.nat.basic

namespace number_theory

open first_order

variable {L : language}

section NT_succ

/- The functions of number theory with successor -/
inductive NT_succ_func : ℕ → Type
| zero : NT_succ_func 0
| succ : NT_succ_func 1

/- The relations of number theory with successor -/
inductive NT_succ_rel : ℕ → Type

/- The language of number theory with successor -/
def NT_succ : language :=
  ⟨NT_succ_func, NT_succ_rel⟩

notation ` zero `  := term.func NT_succ_func.zero ![]
notation ` succ `x := term.func NT_succ_func.succ ![x]

@[simp]
def nth_succ (t : term NT_succ) : ℕ → term NT_succ
| 0            := t
| (nat.succ n) := succ (nth_succ n)

/- The axioms of number theory with successor -/
@[simp]
def NT_succ_Γ : ℕ → (formula NT_succ) :=
λ n, match n with
    | 0    := formula.all 0 ∼((succ v₀) ≃ zero)
    | 1    := formula.all 0 (formula.all 1 ((((succ v₀) ≃ (succ v₁)) ⇒ (v₀ ≃ v₁))))
    | n    := formula.all 0 ∼((nth_succ v₀ (n - 1)) ≃ v₀)
    end

variables { φ : formula NT_succ } { t : term NT_succ }

lemma NT_succ_qe_qcl1 : qe_qcl1 NT_succ_Γ := begin
  intro φ,
  induction φ,
  { existsi (φ : qf NT_succ), refl },
  { repeat { cases φ_ᾰ_1 },
    { existsi qf.f,
      split,
      intro h,
      apply Prf.Cut,
      apply h,
      apply Prf.All_elim F φ_ᾰ v₀,
      apply Prf.Axiom 0, refl,
      intro h,
      apply Prf.Cut, 
      apply h,
      apply Prf.All_intro,
    },
  }
end

/- NT_succ has quantifier elimination -/
theorem NT_succ_qe : qe NT_succ_Γ := 
  by { apply qe_qcl1_qe, apply NT_succ_qe_qcl1 }

end NT_succ

end number_theory