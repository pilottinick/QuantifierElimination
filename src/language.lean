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
| eq          : @term L → @term L → formula
| rel {n : ℕ} : L.relations n → (fin n → @term L) → formula
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
inductive atom
| f           : atom
| e           : term L → term L → atom 
| r {n : ℕ}   : L.relations n → (fin n → term L) → atom

@[simp]
def atom_to_formula : atom L → formula L 
| atom.f               := formula.falsum
| (atom.e t s)         := formula.eq t s
| (atom.r rsymb args)  := formula.rel rsymb args

/- Literals -/
inductive lit
| a      : atom L → lit
| na     : atom L → lit

/- Negate a literal -/
@[simp]
def neg_lit : lit L → lit L
| (lit.a φ)  := lit.na φ
| (lit.na φ) := lit.a φ

@[simp]
def atom_to_lit : atom L → lit L
| a := lit.a a

@[reducible]
instance atom_to_lit_coe (L : language) :
  has_coe (atom L) (lit L) :=
  ⟨atom_to_lit L⟩

@[simp]
def lit_to_formula : lit L → formula L
| (lit.a a)      := atom_to_formula _ a
| (lit.na na) := ∼(atom_to_formula _ na)

/- Conjunctions of literals -/
inductive cl
| l        : lit L → cl 
| c        : cl → cl → cl

@[simp]
def lit_to_cl : lit L → cl L
| l := cl.l l

@[reducible]
instance lit_to_cl_coe (L : language) :
  has_coe (lit L) (cl L) :=
  ⟨lit_to_cl L⟩

@[simp]
def cl_to_formula : cl L → formula L
| (cl.l l)       := lit_to_formula _ l
| (cl.c cl₁ cl₂)  := (cl_to_formula cl₁) and (cl_to_formula cl₂)

/- Disjunctions of conjunctions of literals -/
inductive dcl
| cl : cl L → dcl
| d  : dcl → dcl → dcl

@[simp]
def cl_to_dcl : cl L → dcl L
| cl := dcl.cl cl

@[reducible]
instance cl_to_dcl_coe (L : language) :
  has_coe (cl L) (dcl L) :=
  ⟨cl_to_dcl L⟩

@[simp]
def dcl_to_formula : dcl L → formula L
| (dcl.cl cl)       := cl_to_formula _ cl
| (dcl.d dcl₁ dcl₂) := (dcl_to_formula dcl₁) or (dcl_to_formula dcl₂)

/- Disjunctive normal form -/
inductive dnf
| dcl  : dcl L → dnf
| al   : ℕ → dnf → dnf
| ex   : ℕ → dnf → dnf

@[simp]
def dcl_to_dnf : dcl L → dnf L
| dcl := dnf.dcl dcl

@[reducible]
instance dcl_to_dnf_coe (L : language) :
  has_coe (dcl L) (dnf L) :=
  ⟨dcl_to_dnf L⟩

@[simp]
def dnf_to_formula : dnf L → formula L 
| (dnf.dcl dcl) := dcl_to_formula _ dcl
| (dnf.al n φ)  := (formula.all n (dnf_to_formula φ))
| (dnf.ex n φ)  := ∼(formula.all n ∼(dnf_to_formula φ))

@[reducible]
instance dnf_to_formula_coe (L : language) :
  has_coe (dnf L) (formula L) :=
  ⟨dnf_to_formula L⟩

end dnf

/-- Quantifier free formulas -/
inductive qf
| f           : qf
| e           : term L → term L → qf
| r {n : ℕ}   : L.relations n → (fin n → term L) → qf
| n           : qf → qf
| o           : qf → qf → qf

def qf_to_formula : qf L → formula L 
| qf.f         := formula.falsum
| (qf.e s t)   := formula.eq s t
| (qf.r r a)   := formula.rel r a
| (qf.n φ)     := formula.neg (qf_to_formula φ)
| (qf.o φ₁ φ₂) := formula.or (qf_to_formula φ₁) (qf_to_formula φ₂)

instance qf_to_formula_coe (L : language) :
  has_coe (qf L) (formula L) :=
  ⟨qf_to_formula L⟩

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

@[reducible]
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