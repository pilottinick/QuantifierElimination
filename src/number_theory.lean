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
inductive NT_succ_Γ
| eq1 : NT_succ_Γ
| eq2 : NT_succ_Γ
| ax1 : NT_succ_Γ
| ax2 : NT_succ_Γ
| ax3 : ℕ → NT_succ_Γ

open NT_succ_Γ

def NT_succ_Γ_to_formula : NT_succ_Γ → formula (NT_succ)
| eq1     := formula.all 0 (v₀ ≃ v₀)
| eq2     := formula.all 0 (formula.all 1 (v₀ ≃ v₁ ⇒ (succ v₀) ≃ (succ v₁)))
| ax1     := formula.all 0 ∼((succ v₀) ≃ zero)
| ax2     := formula.all 0 (formula.all 1 ((((succ v₀) ≃ (succ v₁)) ⇒ (v₀ ≃ v₁))))
| (ax3 n) := formula.all 0 ∼(nth_succ v₀ n ≃ v₀)

instance NT_succ_Γ_to_formula_NT_succ : has_coe NT_succ_Γ (formula NT_succ) := sorry

variables { φ : formula NT_succ } { t : term NT_succ }

lemma var_not_free_in_NT_succ_Γ : ∀ x : ℕ, @var_not_free_in_axioms NT_succ x NT_succ_Γ _ := sorry

lemma NT_succ_qe_ecl1 : @qe_ecl1 NT_succ NT_succ_Γ _ := begin
  intro φ,
  induction φ,
  { existsi (φ : qf NT_succ), refl, },
  { cases φ_ᾰ_1, cases φ_ᾰ_1, cases φ_ᾰ_1,
    { have h_free : ¬(@free NT_succ φ_ᾰ F) := by { intro, assumption, },
      apply Eq_equiv_qf ⟨AddEx, RemoveEx h_free⟩,
      existsi qf.f, refl,
    },
    { rename φ_ᾰ n, rename φ_ᾰ_1_ᾰ t₁, rename φ_ᾰ_1_ᾰ_1 t₂,
      have h_free₁ : 
      (occurs_in_term n t₁) ∨ ¬(occurs_in_term n t₁) := by apply em,
      have h_free₂ : (occurs_in_term n t₂) ∨ ¬(occurs_in_term n t₂) := by apply em,
      apply or.elim h_free₁,
      all_goals { apply or.elim h_free₂ },
      { intros h₂ h₁,
        sorry,
      },
      { intros h₂ h₁,
        sorry,
      },
      { intros h₂ h₁,
        cases t₂,
        simp at h₂,
        rw ← h₂,
        existsi (qf.e t₁ t₁),
        split,
        intro h₃,
        apply Ex_elim n t₁,
        sorry,
        apply h₃,
        apply Prf.Assumption 0,
        -- For some reason I need to rw like this in order to simplify
        have h₄ : replace_formula_with n t₁ (t₁ ≃ (v n)) =  replace_formula_with n t₁ (qf_to_formula NT_succ (dcl_to_qf NT_succ ↑(cl.l (lit.a (atom.e t₁ (v n)))))) := begin
          refl,
        end,
        simp,
        rw ← h₄,
        simp,
        cases t₁,
        simp at h₁,
        simp, refl,
        
      },
      { intros h₂ h₁,
        have free : ¬(free n (t₁ ≃ t₂)) := by { simp, exact not_or h₁ h₂, },
        apply Eq_equiv_qf ⟨AddEx, RemoveEx free⟩,
        existsi (qf.e t₁ t₂), refl,
      }
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
theorem NT_succ_qe : @qe NT_succ NT_succ_Γ _ := sorry

end NT_succ

end number_theory