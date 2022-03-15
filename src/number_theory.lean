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

lemma var_not_free_in_NT_succ_Γ : ∀ x : ℕ, var_not_free_in_axioms x NT_succ_Γ := sorry

lemma NT_succ_qe_ecl1 : qe_ecl1 NT_succ_Γ := begin
  intro φ,
  induction φ,
  { existsi (φ : qf NT_succ), refl },
  { cases φ_ᾰ_1, cases φ_ᾰ_1, cases φ_ᾰ_1,
    { have h_free : ¬(@free NT_succ φ_ᾰ F) := by { intro, assumption, },
      apply Eq_equiv_qf ⟨AddEx, RemoveEx h_free⟩,
      existsi qf.f, refl,
    },
    { have h_free₁ : 
      (occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ) ∨ ¬(occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ) := 
        by apply em,
      have h_free₂ : (occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ_1) ∨ ¬(occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ_1) := 
        by apply em,
      apply or.elim h_free₁,
      all_goals { apply or.elim h_free₂ },
      repeat { sorry },
    },
    { cases φ_ᾰ_1_ᾰ, },
    cases φ_ᾰ_1,
    { have h_free : ¬(@free NT_succ φ_ᾰ ∼F) := by { intro c, apply c, },
      apply Eq_equiv_qf ⟨AddEx, RemoveEx h_free⟩,
      existsi qf.n qf.f, refl,
    },
    { have h_free₁ : 
      (occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ) ∨ ¬(occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ) := 
        by apply em,
      have h_free₂ : (occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ_1) ∨ ¬(occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ_1) := 
        by apply em,
      apply or.elim h_free₁,
      all_goals { apply or.elim h_free₂ },
      repeat { sorry },
    },
    { cases φ_ᾰ_1_ᾰ, },
    { sorry },
  }
end

/- NT_succ has quantifier elimination -/
theorem NT_succ_qe : qe NT_succ_Γ := 
  by { apply qe_ecl1_qe, apply NT_succ_qe_ecl1 }

end NT_succ

end number_theory