import language

namespace first_order

section Structure

open term
open formula

variables (L : language) (A : Type*)

/- An L-structure -/
structure Structure :=
(functions : Π {n : ℕ}, L.functions n → (fin n → A) → A)
(relations : Π {n : ℕ}, L.relations n → (fin n → A) → Prop)

variable 𝔸 : Structure L A

/- Variable assignment function into A -/
def var_assign := ℕ → A

/- x-modification of the assignment function s -/
def modification_of (s : var_assign A) (x : ℕ) (a : A) : var_assign A :=
  λ (n : ℕ), if n = x then a else s n

notation s `[`x`|`a`]` := modification_of _ s x a

/-- Term assignment function -/
def term_assign := term L → A

/- The term assignment function induced by the variable assignment function s -/
def term_assign_of_s (s : var_assign A) : term_assign L A
| (v n)                 := s n
| (func fsymb args)     := 𝔸.functions fsymb (λ n, term_assign_of_s (args n))

@[reducible]
instance : has_coe (var_assign A) (term_assign L A) := ⟨term_assign_of_s _ _ 𝔸⟩

notation ` * ` := term_assign_of_s _ _

/- Variable assignments agree on free variables of a term -/
def agree_on_free_variables (s₁ s₂ : var_assign A)(t : term L) : Prop := ∀ n : ℕ, occurs_in_term n t → s₁ n = s₂ n

/- A structure 𝔸 satisfies formula φ with assignment s -/
def satisfies_with_assignment : var_assign A → formula L → Prop
  | s F                   := false
  | s (t₁ ≃ t₂)           := (* 𝔸 s) t₁ = (* 𝔸 s) t₂
  | s (rel rsymb args)    := 𝔸.relations rsymb (λ n, (* 𝔸 s) (args n))
  | s ∼φ₁                 := ¬(satisfies_with_assignment s φ₁)
  | s (φ₁ or φ₂)          := (satisfies_with_assignment s φ₁) ∨ (satisfies_with_assignment s φ₂)
  | s (all n φ₁)          := ∀ a : A, satisfies_with_assignment (s[n|a]) φ₁

notation 𝔸` ⊨ `φ` | `s:= satisfies_with_assignment _ _ 𝔸 s φ

variable s : var_assign A

-- Decidable instances for ⊨
instance eq_decidable [decidable_eq A]: ∀ n m : ℕ, decidable (𝔸 ⊨ (v n  ≃ v m) | s) := begin
intros n m,
rw satisfies_with_assignment,
apply_instance,
end

instance not_decidable {φ : formula L} [decidable (𝔸 ⊨ φ | s)] : decidable (𝔸 ⊨ ∼φ | s) := begin
rw satisfies_with_assignment,
apply_instance,
end

instance or_decidable {φ₁ φ₂ : formula L} [decidable (𝔸 ⊨ φ₁ | s)] [decidable (𝔸 ⊨ φ₂ | s)] : decidable (𝔸 ⊨ (φ₁ or φ₂) | s) := begin
rw satisfies_with_assignment,
apply_instance,
end

/- A structure 𝔸 satisfies a formula i.e. is a model of the formula -/
def satisfies_formula (φ : formula L) : Prop := 
  ∀ s : var_assign A, 𝔸 ⊨ φ | s 

notation 𝔸` ⊨ `φ       := satisfies_formula _ _ 𝔸 φ

/- A structure 𝔸 satisfies a set of formulas -/
def satisfies_set_formula (Γ : set (formula L)) : Prop :=
  ∀ φ ∈ Γ, 𝔸 ⊨ φ

notation 𝔸` ⊨ `Γ          := satisfies_set_formula _ _ 𝔸 Γ

/- Logical implication in a structure -/
def logically_implies (Δ Γ : set (formula L)) : Prop :=
  ∀ (A : Type*) (𝔸 : Structure L A), (𝔸 ⊨ Δ) → (𝔸 ⊨ Γ)

notation Δ` ⊨ `Γ         := logically_implies _ _ Δ Γ

-- A set of formula is valid if it is true in all structures 
-- with every assignment funciton
notation ` ⊨ `Γ          := logically_implies _ _ ∅ Γ

variables (s₁ s₂ : var_assign A) (t : term L) (φ : formula L)

end Structure

end first_order