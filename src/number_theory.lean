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

variables (φ : formula NT_succ) (t : term NT_succ)

lemma var_not_free_in_NT_succ_Γ : ∀ x : ℕ, @var_not_free_in_axioms NT_succ x NT_succ_Γ _ := sorry

lemma replace_eq_with_var_not_in_left (n : ℕ) : ¬(occurs_in_term n t) → replace_formula_with n t (t ≃ (v n)) = t ≃ t := begin
  sorry
end

/- A function that converts a formula of the form t₁ ≃ t₂ to an equivalent quantifier free formula -/
@[simp]
def ex_t₁_eq_t₂_to_qf (n : ℕ) : term NT_succ → term NT_succ → qf NT_succ
-- vᵢ ≃ vⱼ
| (v m₁) (v m₂) := if n = m₁ then qf.n qf.f else (if n = m₂ then qf.n qf.f else qf.e (v m₁) (v m₂))
-- vᵢ ≃ 0
| (v m₁) (term.func NT_succ_func.zero _) := if n = m₁ then qf.n qf.f else qf.e (v m₁) zero
-- 0 ≃ vᵢ
| (term.func NT_succ_func.zero _) (v m₂) := if n = m₂ then qf.n qf.f else qf.e zero (v m₂)
-- vᵢ ≃ succ y
| (v m₁) (term.func NT_succ_func.succ t₂) := if n = m₁ then qf.n qf.f else qf.e (v m₁) (term.func NT_succ_func.succ t₂)
-- succ x ≃ vⱼ
| (term.func NT_succ_func.succ t₁) (v m₂) := qf.f
-- 0 ≃ 0
| (term.func NT_succ_func.zero _) (term.func NT_succ_func.zero _) := qf.n qf.f
-- succ x ≃ 0
| (term.func NT_succ_func.succ t₁) (term.func NT_succ_func.zero _) := qf.f
-- 0 ≃ succ y
| (term.func NT_succ_func.zero _) (term.func NT_succ_func.succ t₂) := qf.f
-- succ x ≃ succ y
| (term.func NT_succ_func.succ t₁) (term.func NT_succ_func.succ t₂) := ex_t₁_eq_t₂_to_qf (t₁ 0) (t₂ 0)

lemma qe_ex_n_n_eq_t₂ (n : ℕ) (t₂ : term NT_succ) : (NT_succ_Γ ∣ [] ⊢ (exi n ((v n) ≃ t₂))) ↔ 
  (@Prf NT_succ NT_succ_Γ _ list.nil T) := begin
  split, intro h,
  sorry, sorry,
end 

lemma qe_ex_n_t₁_eq_n (n : ℕ) (t₁ : term NT_succ) : (NT_succ_Γ ∣ [] ⊢ (exi n (t₁ ≃ (v n)))) ↔ 
  (@Prf NT_succ NT_succ_Γ _ list.nil T) := begin
  split, intro h,
  sorry, sorry,
end 

lemma qe_ex_n_m₁_eq_m₂ (n m₁ m₂ : ℕ) : n ≠ m₁ → n ≠ m₂ → 
  (@Prf NT_succ NT_succ_Γ _ list.nil (exi n ((v m₁) ≃ (v m₂))) ↔ 
   @Prf NT_succ NT_succ_Γ _ list.nil ((v m₁) ≃ (v m₂))) := begin
  sorry,
end

lemma qe_ex_t₁_eq_t₂ (n : ℕ) (t₁ t₂ : term NT_succ) : equiv_qf NT_succ_Γ (exi n (t₁ ≃ t₂)) := begin
  existsi (ex_t₁_eq_t₂_to_qf n t₁ t₂),
  cases t₁, cases t₂,
  { have t₁eq : (n = t₁) ∨ (n ≠ t₁) := by apply em,
    cases t₁eq,
    { rw ← t₁eq, simp,
      apply qe_ex_n_n_eq_t₂
    },
    have t₂eq : (n = t₂) ∨ (n ≠ t₂) := by apply em,
    cases t₂eq,
    { rw t₂eq, simp,
      apply qe_ex_n_t₁_eq_n,
    },
    { -- TODO: How to simplify?
      -- apply (qe_ex_n_m₁_eq_m₂ _ _ _ t₁eq t₂eq),
      sorry
    }
  },
  { cases t₂_n, cases t₂_ᾰ,
    { simp,
      sorry
    },
    cases t₂_ᾰ,
    { simp,
      sorry
    }
  },
  cases t₂,
  { sorry
  },
  { sorry
  }
end

lemma NT_succ_qe_ecl1 : @qe_ecl1 NT_succ NT_succ_Γ _ := begin
  intro φ,
  induction φ,
  { existsi (φ : qf NT_succ), refl, },
  { cases φ_ᾰ_1, cases φ_ᾰ_1, cases φ_ᾰ_1,
    { have h_free : ¬(@free NT_succ φ_ᾰ F) := by { intro, assumption, },
      apply Eq_equiv_qf ⟨AddEx, RemoveEx h_free⟩,
      existsi qf.f, refl,
    },
    { apply qe_ex_t₁_eq_t₂, },
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