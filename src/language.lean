import data.matrix.notation
import algebra.group_power

universe variables u v

namespace first_order

section language

/- Definition of a language -/
structure language :=
(functions : ℕ → Type) (relations : ℕ → Type)

/-- The empty language has no symbols. -/
def empty : language := ⟨λ _, pempty, λ _, pempty⟩

instance : inhabited language := ⟨empty⟩

/-- The type of constants in a given language. -/
def const (L : language) := L.functions 0

variable (L : language)

/-- Def 1.3.1. A term of a language-/
inductive term
| var           : ℕ → term
| func {n : ℕ}  : L.functions n → (fin n → term) → term

open term

/- A formula of a language -/
inductive formula
| falsum      : formula
| eq          : term L → term L → formula
| rel {n : ℕ} : L.relations n → (fin n → term L) → formula
| neg         : formula → formula
| or          : formula → formula → formula
| all         : ℕ → formula → formula

notation ` v `    := term.var
notation ` v₀ `   := term.var 0
notation ` v₁ `   := term.var 1
notation ` v₂ `   := term.var 2
notation ` v₃ `   := term.var 3
notation ` v₄ `   := term.var 4
notation ` v₅ `   := term.var 5

notation ` F `        := formula.falsum
notation ` T `        := formula.neg F
infix ` ≃ `:88        := formula.eq
prefix ` ∼ `:100      := formula.neg
infix  ` or `:50      := formula.or
notation φ₁` and `φ₂  := ∼(∼φ₁ or ∼φ₂)
notation φ₁` ⇒ `φ₂    := ∼φ₁ or φ₂
notation φ₁` ⇔ `φ₂   := (φ₁ ⇒ φ₂) and (φ₂ ⇒ φ₁)

open formula

variables (φ φ₁ φ₂ h : formula L) (t Φ₁ Φ₂ : list (formula L)) (n : ℕ) 

section dnf

/- Atomic formulas-/
inductive atomic
| falsum       : atomic
| eq           : term L → term L → atomic 
| rel {n : ℕ}  : L.relations n → (fin n → term L) → atomic

attribute [simp]
def atomic_to_formula : atomic L → formula L 
| atomic.falsum             := formula.falsum
| (atomic.eq t s)           := formula.eq t s
| (atomic.rel rsymb args)   := formula.rel rsymb args

/- Literals -/
inductive literal
| atomic      : atomic L → literal
| neg_atomic  : atomic L → literal

attribute [simp]
def atomic_to_literal : atomic L → literal L
| a := literal.atomic a

attribute [simp]
instance atomic_to_literal_coe (L : language) :
  has_coe (atomic L) (literal L) :=
  ⟨atomic_to_literal L⟩

attribute [simp]
def literal_to_formula : literal L → formula L
| (literal.atomic a)      := atomic_to_formula _ a
| (literal.neg_atomic na) := atomic_to_formula _ na

/- Conjunctions of literals -/
inductive conj_lit
| lit        : literal L → conj_lit 
| conj       : literal L → literal L → conj_lit

attribute [simp]
def lit_to_conj_lit : literal L → conj_lit L
| l := conj_lit.lit l

attribute [simp]
instance lit_to_conj_lit_coe (L : language) :
  has_coe (literal L) (conj_lit L) :=
  ⟨lit_to_conj_lit L⟩

attribute [simp]
def conj_lit_to_formula : conj_lit L → formula L
| (conj_lit.lit l)       := literal_to_formula _ l
| (conj_lit.conj l₁ l₂)  := (literal_to_formula _ l₁) and (literal_to_formula _ l₂)

/- Disjunctions of conjunctions of literals -/
inductive disj_conj_lit
| conj_lit   : conj_lit L → disj_conj_lit
| disj       : conj_lit L → conj_lit L → disj_conj_lit

attribute [simp]
def conj_lit_to_disj_conj_lit : conj_lit L → disj_conj_lit L
| cl := disj_conj_lit.conj_lit cl

attribute [simp]
instance conj_lit_to_disj_conj_lit_coe (L : language) :
  has_coe (conj_lit L) (disj_conj_lit L) :=
  ⟨conj_lit_to_disj_conj_lit L⟩

attribute [simp]
def disj_conj_lit_to_formula : disj_conj_lit L → formula L
| (disj_conj_lit.conj_lit cl)  := conj_lit_to_formula _ cl
| (disj_conj_lit.disj cl₁ cl₂)  := (conj_lit_to_formula _ cl₁) or (conj_lit_to_formula _ cl₂)

/- Disjunctive normal form -/
inductive dnf
| disj_conj_lit   : disj_conj_lit L → dnf
| all             : ℕ → dnf → dnf
| ex              : ℕ → dnf → dnf

attribute [simp]
def dnf_to_formula : dnf L → formula L 
| (dnf.disj_conj_lit dcl) := disj_conj_lit_to_formula _ dcl
| (dnf.all n φ)           := (formula.all n (dnf_to_formula φ))
| (dnf.ex n φ)            := ∼(formula.all n ∼(dnf_to_formula φ))

attribute [simp]
instance dnf_to_formula_coe (L : language) :
  has_coe (dnf L) (formula L) :=
  ⟨dnf_to_formula L⟩

end dnf

/- If a variable occurs in a term -/
def occurs_in_term (n : ℕ) : term L → Prop
| (v m)        := n = m
| (func _ t)   := ∃ i, occurs_in_term (t i)

notation n \ t     := occurs_in_term _ n t

/- Def 1.5.2. If a variable is free in a formula -/
def free (n : ℕ) : formula L → Prop
| F                 := false
| (t₁ ≃ t₂)         := (occurs_in_term L n t₁) ∨ (occurs_in_term L n t₂)
| (rel rsymb args)  := ∃ i, occurs_in_term L n (args i)
| ∼φ                := free φ
| (φ₁ or φ₂)        := free φ₁ ∨ free φ₂
| (all m φ)         := !(n = m) ∧ free φ

def free_dec : decidable (free _ n φ) := sorry

def var_not_free_in (n : ℕ) : list (formula L) → Prop
| list.nil             := true
| (list.cons h t)      := ¬(free _ n h) ∧ (var_not_free_in t)

/-- If a formula is quantifier free-/
def quantifier_free : formula L → Prop
| ∼φ                 := quantifier_free φ
| (φ₁ or φ₂)         := (quantifier_free φ₁) ∧ (quantifier_free φ₂)
| (all n φ)          := false
| _                  := true

/-- Def 1.8.1. The term with the variable x replaced by the term t -/
def replace_term_with (x : ℕ) (t : term L) : term L → term L
| (v n)              := if (n = x) then t else (v n)
| (func fsymb args)  := (func fsymb (λ n, replace_term_with (args n)))

/-- Def 1.8.2. The formula with the variable x replaced the term t -/
def replace_formula_with (x : ℕ) (t : term L) : formula L → formula L
| F                  := falsum
| (t₁ ≃ t₂)          := (replace_term_with _ x t t₁) ≃ (replace_term_with _ x t t₂)
| (rel rsymb args)    := rel rsymb (λ n, replace_term_with _ x t (args n))
| ∼φ                  := ∼(replace_formula_with φ)
| (φ₁ or φ₂)          := (replace_formula_with φ₁) or (replace_formula_with φ₂)
| (all y φ)           := if x = y then (all y φ) else (all y (replace_formula_with φ))

/-- The term t is substitutable for the variable x in formula φ -/
def substitutable_for (x : ℕ) (t : term L) : formula L → Prop
| F                    := true
| (_ ≃ _)              := true
| (rel _ _)            := true
| ∼φ                   := substitutable_for φ
| (φ₁ or φ₂)           := (substitutable_for φ₁) ∧ (substitutable_for φ₂)
| (all y φ)            := ¬(free _ x φ) ∨ (¬(occurs_in_term _ y t) ∧ (substitutable_for φ))

/-- The sentences of a language -/
def sentence : set (formula L) := λ φ, ∀ n : ℕ, ¬(free L n φ)

end language

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

instance : has_coe (var_assign A) (term_assign L A) := ⟨term_assign_of_s _ _ 𝔸⟩

notation ` * ` := term_assign_of_s _ _

/- Variable assignments agree on free variables of a term -/
def agree_on_free_variables (s₁ s₂ : var_assign A)(t : term L) : Prop := ∀ n : ℕ, occurs_in_term _ n t → s₁ n = s₂ n

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

/- Lemma 1.7.6. If variable assignments agree on variables in the term then term assignments agree for that term -/
lemma term_eq_of_var_eq : agree_on_free_variables _ _ s₁ s₂ t → ((* 𝔸 s₁) t) = ((* 𝔸 s₂) t) := sorry

/- Prop 1.7.7. If variable assignment functions agree on free variables in a formula then that formula is satisified 
   by one assignment function if and only if it is satisfied by the other. -/
theorem sat_eq_of_var_eq : agree_on_free_variables _ _ s₁ s₂ t → ((𝔸 ⊨ φ | s₁) ↔ (𝔸 ⊨ φ | s₂)) := sorry

/- Corollary 1.7.8. A sentence either satisfies all assignment functions or none of them -/
theorem sat_of_sentence : φ ∈ sentence L → ((∀ s : var_assign A, 𝔸 ⊨ φ | s) ∨ ¬(∃ s : var_assign A, 𝔸 ⊨ φ | s)) := sorry

end Structure

end first_order