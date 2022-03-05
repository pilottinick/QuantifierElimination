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

attribute [simp]
def nth_succ (t : term NT_succ) : ℕ → term NT_succ
| 0            := t
| (nat.succ n) := succ (nth_succ n)


/- The axioms of number theory with successor -/
def NT_succ_Γ : ℕ → (formula NT_succ) :=
λ n, match n with
    | 0    := formula.all 0 ∼((succ v₀) ≃ zero)
    | 1    := formula.all 0 (formula.all 1 ((((succ v₀) ≃ (succ v₁)) ⇒ (v₀ ≃ v₁))))
    | n    := formula.all 0 ∼((nth_succ v₀ (n - 1)) ≃ v₀)
    end

variables { φ : formula NT_succ } { t : term NT_succ }

/- A term is either zero or a variable -/
attribute [simp]
def zero_or_var (t : term NT_succ) : Prop := 
  t = zero ∨ (∃ n : ℕ, t = term.var n)

/- A term is a number of succs on a zero or a variable -/
attribute [simp]
def succ_zero_or_var (t : term NT_succ) : Prop :=
  ∃ s : term NT_succ,
    ((zero_or_var s) ∧ (∃ n, t = nth_succ s n))

/- Characterizing the terms of NT_succ -/
def NT_succ_terms : ∀ (t : term NT_succ), succ_zero_or_var t := begin
  intro t, cases t, 
  simp, existsi term.var t,
  split, simp, existsi 0, simp,
  admit,
end

/- Characterizing the atomic formulas of NT_succ -/
def NT_succ_atomic : atomic _ φ ↔ 
    ((φ = F) ∨ 
    (∃ t s : term NT_succ, succ_zero_or_var t ∧ succ_zero_or_var s ∧ (φ = t ≃ s))) := begin
  split, intro φatomic,
  cases φ, 
  simp, 
  rename φ_ᾰ φ₁ , rename φ_ᾰ_1 φ₂,
  have φ₁succ_zero_or_var : succ_zero_or_var φ₁ := NT_succ_terms φ₁,
  have φ₂succ_zero_or_var : succ_zero_or_var φ₂ := NT_succ_terms φ₂,
  apply or.intro_right, existsi φ₁, existsi φ₂,
  repeat { apply and.intro },
  repeat { assumption }, refl,
  cases φ_ᾰ,
  any_goals { by { simp at φatomic, apply false.elim φatomic } },
  intro h, apply or.elim h,
  intro f, rw f, simp,
  intro t, apply exists.elim t, intros t th, apply exists.elim th, intros s sh,
  rw and.elim_right (and.elim_right sh), simp, 
end

end NT_succ

end number_theory