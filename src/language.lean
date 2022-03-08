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

/- Quantifier free formulas -/
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
notation ` all `       := formula.all
notation ` exi `       := λ n φ, ∼(formula.all n ∼φ)

open formula

variables (α : language → Type) (φ φ₁ φ₂ h : formula L) (t Φ₁ Φ₂ : list (formula L)) (n : ℕ) 

/- Atomic formulas-/
inductive atom
| f           : atom
| e           : term L → term L → atom 
| r {n : ℕ}   : L.relations n → (fin n → term L) → atom

@[simp]
def atom_to_qf : atom L → qf L
| atom.f               := qf.f
| (atom.e t s)         := qf.e t s
| (atom.r rsymb args)  := qf.r rsymb args

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
def lit_to_qf : lit L → qf L
| (lit.a a)   := atom_to_qf _ a
| (lit.na na) := qf.n (atom_to_qf _ na)

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
def cl_to_qf : cl L → qf L
| (cl.l l)        := lit_to_qf _ l
| (cl.c cl₁ cl₂)  := qf.n (qf.o (qf.n (cl_to_qf cl₁)) (qf.n (cl_to_qf cl₂)))

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
def dcl_to_qf : dcl L → qf L
| (dcl.cl cl)       := cl_to_qf _ cl
| (dcl.d dcl₁ dcl₂) := qf.o (dcl_to_qf dcl₁) (dcl_to_qf dcl₂)

@[reducible]
instance dcl_to_qf_coe (L : language) :
  has_coe (dcl L) (qf L) :=
  ⟨dcl_to_qf L⟩

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
| (dnf.dcl dcl)  := qf_to_formula _ (dcl_to_qf _ dcl)
| (dnf.al n dnf) := all n (dnf_to_formula dnf)
| (dnf.ex n dnf) := exi n (dnf_to_formula dnf)

@[reducible]
instance dnf_to_formula_coe (L : language) :
  has_coe (dnf L) (formula L) :=
  ⟨dnf_to_formula L⟩

/- A single quantifier on a conjunction of literals -/
inductive qcl1
| cl : cl L → qcl1
| al : ℕ → cl L → qcl1
| ex : ℕ → cl L → qcl1

/- A series of quantifiers on a conjunction of literals -/
inductive qcl
| cl : cl L → qcl
| al : ℕ → qcl → qcl
| ex : ℕ → qcl → qcl

@[simp]
def qcl1_to_qcl : qcl1 L → qcl L
| (qcl1.cl cl)   := qcl.cl cl
| (qcl1.al n cl) := qcl.al n (qcl.cl cl)
| (qcl1.ex n cl) := qcl.ex n (qcl.cl cl)

@[reducible]
instance qcl1_to_qcl_coe (L : language) :
  has_coe (qcl1 L) (qcl L) :=
  ⟨qcl1_to_qcl L⟩

@[simp]
def qcl_to_formula : qcl L → formula L
| (qcl.cl cl)    := qf_to_formula _ (cl_to_qf _ cl)
| (qcl.al n qcl) := (all n (qcl_to_formula qcl))
| (qcl.ex n qcl) := (exi n (qcl_to_formula qcl))

/- A disjunction of qcl -/
inductive dqcl
| qcl : qcl L → dqcl
| d   : dqcl → dqcl → dqcl

@[simp]
def qcl_to_dqcl : qcl L → dqcl L 
| qcl := dqcl.qcl qcl

@[reducible]
instance qcl_to_dqcl_coe (L : language) :
  has_coe (qcl L) (dqcl L) :=
  ⟨qcl_to_dqcl L⟩

@[simp]
def dqcl_to_formula : dqcl L → formula L
| (dqcl.qcl qcl)       := qcl_to_formula _ qcl
| (dqcl.d dqcl₁ dqcl₂) := (dqcl_to_formula dqcl₁) or (dqcl_to_formula dqcl₂)

@[reducible]
instance dqcl_to_formula_coe (L : language) :
  has_coe (dqcl L) (formula L) :=
  ⟨dqcl_to_formula L⟩

/- A single quantifier on a disjunction of conjunction of literals -/
inductive qdcl1
| dcl : dcl L → qdcl1
| al  : ℕ → dcl L → qdcl1
| ex  : ℕ → dcl L → qdcl1

@[simp]
def qcl1_to_qdcl1 : qcl1 L → qdcl1 L 
| (qcl1.cl cl)   := qdcl1.dcl (dcl.cl cl)
| (qcl1.al n cl) := qdcl1.al n (dcl.cl cl)
| (qcl1.ex n cl) := qdcl1.ex n (dcl.cl cl)

@[reducible]
instance qcl1_to_qdcl1_coe (L : language) :
  has_coe (qcl1 L) (qdcl1 L) :=
  ⟨qcl1_to_qdcl1 L⟩

@[simp]
def qdcl1_to_dnf : qdcl1 L → dnf L
| (qdcl1.dcl dcl)  := dnf.dcl dcl
| (qdcl1.al n dcl) := dnf.al n (dnf.dcl dcl)
| (qdcl1.ex n dcl) := dnf.ex n (dnf.dcl dcl)

@[reducible]
instance qdcl1_to_dnf_coe (L : language) :
  has_coe (qdcl1 L) (dnf L) :=
  ⟨qdcl1_to_dnf L⟩

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

end Structure

end first_order