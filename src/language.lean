import data.matrix.notation
import algebra.group_power
import data.nat.parity

universe variables u v

namespace first_order

section language

/- Shifts a sequence to the right -/
@[simp]
def cons { A : Type } (a : A) (f : ℕ → A) : ℕ → A := 
  λ n, if n = 0 then a else (f (n - 1))

/- Append two sequences -/
@[simp]
def append { A : Type } (f : ℕ → A) (g : ℕ → A) : ℕ → A :=
  λ n : ℕ, if (even n) then f (n / 2) else g ((n - 1) / 2)

notation a`::`f := cons a f

notation l`++`f := append l f

/- Definition of a language -/
structure language :=
(functions : ℕ → Type) (relations : ℕ → Type)

/-- The empty language has no symbols. -/
def empty : language := ⟨λ _, pempty, λ _, pempty⟩

instance : inhabited language := ⟨empty⟩

/-- The type of constants in a given language. -/
def const (L : language) := L.functions 0

variable (L : language)

/-- A term of a language-/
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
| l : lit L → cl 
| c : cl → cl → cl

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

/- A single existential quantifier on a conjunction of literals -/
inductive ecl1
| cl : cl L → ecl1
| ex : ℕ → cl L → ecl1

/- A single existential quantifier on a disjunction of conjunction of literals -/
inductive edcl1
| dcl : dcl L → edcl1
| ex  : ℕ → dcl L → edcl1

@[simp]
def ecl1_to_edcl1 : ecl1 L → edcl1 L 
| (ecl1.cl cl)  := edcl1.dcl cl
| (ecl1.ex n cl) := edcl1.ex n cl

@[reducible]
instance ecl1_to_edcl1_coe (L : language) :
  has_coe (ecl1 L) (edcl1 L) :=
  ⟨ecl1_to_edcl1 L⟩

/- A single quantifier on a disjunction of conjunction of literals -/
inductive qdcl1
| dcl : dcl L → qdcl1
| al  : ℕ → dcl L → qdcl1
| ex  : ℕ → dcl L → qdcl1

@[simp]
def edcl1_to_qdcl1 : edcl1 L → qdcl1 L 
| (edcl1.dcl dcl)  := qdcl1.dcl dcl
| (edcl1.ex n dcl) := qdcl1.ex n dcl

@[reducible]
instance qcl1_to_qdcl1_coe (L : language) :
  has_coe (edcl1 L) (qdcl1 L) :=
  ⟨edcl1_to_qdcl1 L⟩

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
@[simp]
def occurs_in_term {L : language} (n : ℕ) : term L → Prop
| (v m)        := n = m
| (func _ t)   := ∃ i, occurs_in_term (t i)

instance occurs_in_term_dec (n : ℕ) (t : term L) : decidable (occurs_in_term n t) := sorry

/- The variable vₓ is free -/
@[simp]
def free {L : language} (x : ℕ) : formula L → Prop
| F                 := false
| (t₁ ≃ t₂)         := (occurs_in_term x t₁) ∨ (occurs_in_term x t₂)
| (rel rsymb args)  := ∃ i, occurs_in_term x (args i)
| ∼φ                := free φ
| (φ₁ or φ₂)        := free φ₁ ∨ free φ₂
| (all m φ)         := ¬(m = x) ∧ free φ

/- For all terms, there is a variable which does not occur in the term -/
lemma for_all_term_ex_var_not_in_term : 
  ∀ t : (term L), ∃ m : ℕ, ¬(occurs_in_term m t) :=
begin
  intro t,
  cases t,
  { existsi t + 1, simp },
  { sorry }
end

/- For all formulas, there is a variable which is not free in the formula -/
lemma for_all_formula_ex_var_not_free : 
  ∀ φ : (formula L), ∃ m : ℕ, ¬(free m φ) :=
begin
  intro φ,
  cases φ,
  { simp, },
  repeat { sorry },
end

/- The variable x is not free at position n of Γ -/
@[simp]
def nth_not_free {L : language} (x : ℕ) (n : ℕ) (Γ : list (formula L)) : Prop
  := match Γ.nth n with
     | none   := true
     | some φ := ¬(free x φ)
     end

/- The variable x is not free in axioms A -/
@[simp]
def var_not_free_in_axioms {L : language} (x : ℕ) (α : Type) [has_coe α (formula L)] : Prop := 
  (∀ a : α, ¬(@free L x a))

/- The variable x is not free in the context Γ -/
@[simp]
def var_not_free_in_context {L : language} (x : ℕ) (Γ : list (formula L)) : Prop := 
  (∀ n : ℕ, (nth_not_free x n Γ))

/- The variable x is not free in the context Γ -/
@[simp]
def var_not_free_in_axioms_context {L : language} (x : ℕ) (α : Type) [has_coe α (formula L)] (Γ : list (formula L)) : Prop := 
  (@var_not_free_in_axioms L x α _) ∧ (var_not_free_in_context x Γ)

/-- Replace the variable vₓ with the term t -/
@[simp]
def replace_term_with {L : language} (x : ℕ) (t : term L) : term L → term L
| (v n)              := if (n = x) then t else (v n)
| (func fsymb args)  := (func fsymb (λ n, replace_term_with (args n)))

/-- If vₓ does not occur in the term t, then replacing vₓ in t does nothing -/
def replace_term_with_does_not_occur (x : ℕ) (t' : term L) (t : term L) : 
  ¬(occurs_in_term x t) → replace_term_with x t' t = t := sorry

/-- Replace the variable vₓ with the term t -/
@[simp]
def replace_formula_with {L : language} (x : ℕ) (t : term L) : formula L → formula L
| F                  := falsum
| (t₁ ≃ t₂)          := (replace_term_with x t t₁) ≃ (replace_term_with x t t₂)
| (rel rsymb args)    := rel rsymb (λ n, replace_term_with x t (args n))
| ∼φ                  := ∼(replace_formula_with φ)
| (φ₁ or φ₂)          := (replace_formula_with φ₁) or (replace_formula_with φ₂)
| (all y φ)           := if x = y then (all y φ) else (all y (replace_formula_with φ))

/- Replacing the variable vₓ with vₓ does not change the formula -/
lemma replace_formula_with_idem : ∀ x φ, @replace_formula_with L x (v x) φ = φ := sorry

/-- The term t is substitutable for the variable vₓ -/
@[simp]
def substitutable_for {L : language} (t : term L) (x : ℕ) : formula L → Prop
| F                    := true
| (_ ≃ _)              := true
| (rel _ _)            := true
| ∼φ                   := substitutable_for φ
| (φ₁ or φ₂)           := (substitutable_for φ₁) ∧ (substitutable_for φ₂)
| (all y φ)            := ¬(free x (all y φ)) ∨ (¬(occurs_in_term y t) ∧ (substitutable_for φ))

/- The variable vₓ is always substitutible for the variable vₓ -/
lemma substitutable_for_idem : ∀ x φ, @substitutable_for L (v x) x φ := begin
  intros x φ,
  induction φ,
  any_goals { by { simp  } },
  assumption,
  apply and.intro,
  repeat { assumption },
  unfold substitutable_for,
  have x_eq := em (φ_ᾰ = x),
  apply or.elim x_eq,
  intro h₁,
  apply or.intro_left,
  unfold free,
  intro c,
  apply c.left h₁,
  intro h₂,
  apply or.intro_right,
  apply and.intro,
  repeat { assumption },
end

/- The sentences of a language -/
@[simp]
def sentence (L : language) := {φ : formula L // ∀ n : ℕ, ¬(free n φ)}

end language

end first_order