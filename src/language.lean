import data.matrix.notation
import algebra.group_power

universe variables u v

namespace first_order

section language

/-- Def 1.2.1. -/
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

/-- Def 1.3.3. A formula of a language -/
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

/- If a formula is an atomic formula -/
attribute [simp]
def atomic : formula L → Prop
| F                := true
| (_ ≃ _)         := true
| (rel _ _)       := true
| _               := false

/- If a formula is the negative of an atomic formula -/
attribute [simp]
def neg_atomic : formula L → Prop
| ∼φ              := atomic _ φ
| _               := false

lemma neg_atomic_phi_atomic : neg_atomic _ ∼φ → atomic _ φ := begin
  intro h,
  unfold neg_atomic at h,
  assumption,
end 

/- If a formula is an atomic formula or the negation of an atomic formula -/
attribute [simp]
def literal : formula L → Prop 
| F                  := true
| (t₁ ≃ t₂)          := true
| (rel rsymb args)   := true
| ∼φ                 := atomic _ φ
| _                  := false

/- If a formula is the conjunction of two atomic formulas -/
attribute [simp]
def conj_atomic := ∃ φ₁ φ₂ : formula L, φ = (φ₁ and φ₂)  ∧ atomic _ φ₁ ∧ atomic _ φ₂

/- If a formula is the disjunction of two negative atomic formulas -/
attribute [simp]
def disj_neg_atomic := ∃ φ₁ φ₂ : formula L, φ = (∼φ₁ or ∼φ₂) ∧ atomic _ φ₁ ∧ atomic _ φ₂

/- If a formula is the conjunction of an atomic formula with a negative atomic formulas -/
attribute [simp]
def conj_atomic_neg_atomic := ∃ φ₁ φ₂ : formula L, φ = (φ₁ and ∼φ₂) ∧ atomic _ φ₁ ∧ atomic _ φ₂

/- If a formulas is the conjunction of a negative atomic formulas with an atomic formula -/
attribute [simp]
def conj_neg_atomic_atomic := ∃ φ₁ φ₂ : formula L, φ = (∼φ₁ and φ₂) ∧ atomic _ φ₁ ∧ atomic _ φ₂

/- A literal is either atomic or the negation of an atomic formula -/
lemma lit_atomic_or_neg_atomic :
    literal _ φ ↔ (∃ ψ : formula L, (atomic _ ψ) ∧ (φ = ψ ∨ φ = ∼ψ)) := begin
  split,
  intro lit,
  cases φ,
  existsi F, simp,
  existsi (φ_ᾰ ≃ φ_ᾰ_1), simp,
  existsi rel φ_ᾰ φ_ᾰ_1, simp,
  unfold literal at lit,
  existsi φ,
  apply and.intro,
  assumption,
  simp,
  any_goals { by { unfold literal at lit, apply false.elim lit } },
  intro atom,
  cases φ,
  all_goals { unfold literal },
  apply exists.elim atom,
  intros ψ h,
  have h1 : atomic _ ψ := and.elim_left h,
  have h2 : (∼φ = ψ ∨ ∼φ = ∼ψ)  := and.elim_right h,
  apply or.elim h2,
  intro p,
  rw ← p at h1,
  unfold atomic at h1,
  apply false.elim h1,
  intro np,
  have φeqψ: φ = ψ := begin simp at np, assumption end,
  rw φeqψ,
  assumption,
  have atom' : ¬ (∀ (ψ : formula L), ¬(atomic L ψ ∧ (φ_ᾰ or φ_ᾰ_1 = ψ ∨ φ_ᾰ or φ_ᾰ_1 =  ∼ ψ))) := not_forall_not.mpr atom,
  have natom' : ∀ (ψ : formula L), ¬(atomic L ψ ∧ (φ_ᾰ or φ_ᾰ_1 = ψ ∨ φ_ᾰ or φ_ᾰ_1 =  ∼ ψ)) := begin
    intros ψ f,
    have ψatom : atomic _ ψ := and.elim_left f,
    have ψeq : φ_ᾰ or φ_ᾰ_1 = ψ ∨ φ_ᾰ or φ_ᾰ_1 = ∼ψ := and.elim_right f,
    apply or.elim ψeq,
    intro f1,
    rw ← f1 at ψatom,
    unfold atomic at ψatom,
    assumption,
    intro f2,
    have nf2 : ¬(φ_ᾰ or φ_ᾰ_1 =  ∼ ψ) := begin simp end,
    contradiction,
  end,
  contradiction,
  have atom' : ¬ (∀ (ψ : formula L), ¬(atomic L ψ ∧ (formula.all φ_ᾰ φ_ᾰ_1 = ψ ∨ formula.all φ_ᾰ φ_ᾰ_1 =  ∼ ψ))) := not_forall_not.mpr atom,
  have natom' : ∀ (ψ : formula L), ¬(atomic L ψ ∧ (formula.all φ_ᾰ φ_ᾰ_1 = ψ ∨ formula.all φ_ᾰ φ_ᾰ_1 =  ∼ ψ)) := begin
    intros ψ f,
    have ψatom : atomic _ ψ := and.elim_left f,
    have ψeq : formula.all φ_ᾰ φ_ᾰ_1 = ψ ∨ formula.all φ_ᾰ φ_ᾰ_1 = ∼ψ := and.elim_right f,
    apply or.elim ψeq,
    intro f1,
    rw ← f1 at ψatom,
    unfold atomic at ψatom,
    assumption,
    intro f2,
    have nf2 : ¬(formula.all φ_ᾰ φ_ᾰ_1 =  ∼ ψ) := begin simp end,
    contradiction,
  end,
  contradiction,
end

/- Atomics are literals -/
def atomic_lit : atomic _ φ → literal _ φ := begin
  intros h,
  have lit : (∃ ψ : formula L, (atomic _ ψ) ∧ (φ = ψ ∨ φ = ∼ψ)) := begin
    existsi φ,
    apply and.intro,
    assumption,
    simp,
  end,
  apply (lit_atomic_or_neg_atomic _ φ).mpr lit,
end

/- Negations of atomics are literals -/
def neg_atomic_lit : atomic _ φ → literal _ ∼φ := begin
  intros h,
  have lit : (∃ ψ : formula L, (atomic _ ψ) ∧ (∼φ = ψ ∨ ∼φ = ∼ψ)) := begin
    existsi φ,
    apply and.intro,
    assumption,
    simp,
  end,
  apply (lit_atomic_or_neg_atomic _ ∼φ).mpr lit,
end

/- Take the disjunction of a non-empty list of formulas -/
attribute [simp]
def disjunction (φ : formula L) : list (formula L) → formula L
| list.nil         := φ
| (list.cons h t)  := (disjunction t) or h

notation ` Disj `:120 := disjunction _

attribute [simp]
def disj_nil : (Disj φ []) = φ := begin
  unfold disjunction,
end

attribute [simp]
def disj_cons : (Disj φ (h::t)) = ((Disj φ t) or h) := begin
  unfold disjunction,
end

def disj_append : (Disj φ₁ (Φ₁ ++ (φ₂::[]) ++ Φ₂)) = ((Disj φ₁ Φ₁) or (Disj φ₂ Φ₂)) := sorry

attribute [simp]
def or_list (φ : formula L) : list (formula L) → list (formula L)
| list.nil         := []
| (list.cons h t)  := ((φ or h)::(or_list t))

notation φ` or⬝ `Φ := or_list _ φ Φ

attribute [simp]
def or_list_nil : (φ or⬝ []) = [] := by simp

attribute [simp]
def or_list_cons : (φ or⬝ (h::t)) = ((φ or h)::(φ or⬝ t)) := by simp

/- The conjunction of a non-empty list of formulas -/
attribute [simp]
def conjunction (φ : formula L) : list (formula L) → formula L
| list.nil         := φ
| (list.cons h t)  := (conjunction t) and h

notation ` Conj `:120 := conjunction _

attribute [simp]
def conj_nil : (Conj φ []) = φ := by simp

attribute [simp]
def conj_cons : (Conj φ (h::t)) = ((Conj φ t) and h) := by simp

attribute [simp]
def and_list (φ : formula L) : list (formula L) → list (formula L)
| list.nil         := []
| (list.cons h t)  := ((φ and h)::(and_list t))

notation φ` and⬝ `Φ := and_list _ φ Φ

attribute [simp]
def and_list_nil : (φ and⬝ list.nil) = list.nil := by simp

attribute [simp]
def and_list_cons : (φ and⬝ (list.cons h t)) = ((φ and h)::(φ and⬝ t)) := by simp

/- If a formula is the conjunction of literals -/
attribute [simp]
def conj_lit (φ : formula L) := 
    (∃ q : (formula L), ∃ Q : list (formula L),
     φ = Conj q Q ∧ literal _ q ∧ ∀ q' ∈ Q, literal _ q')

/- If a formula is the disjunction of conjunction of literals -/
attribute [simp]
def disj_conj_lit (φ : formula L) :=
    (∃ p : (formula L), ∃ P : list (formula L), 
      (φ = Disj p P) ∧ 
      (conj_lit _ p) ∧ 
      (∀ p' ∈ P, conj_lit _ p'))

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

/-- If a propositional logic formula is in disjunctive normal form -/
attribute [simp]
def dnf_prop : formula L → Prop
| ∼φ                 := match φ with
                        | F                 := true
                        | (t₁ ≃ t₂)         := true
                        | (rel rsymb args)  := true
                        | ∼φ                := false
                        | (φ₁ or φ₂)        := neg_atomic _ φ₁ ∧ neg_atomic _ φ₂
                        | _                 := false
                        end
| (φ₁ or φ₂)         := dnf_prop φ₁ ∧ dnf_prop φ₂
| (all n φ)          := false
| _                  := true

/-- If a first order logic formula is in disjunctive normal form -/
attribute [simp]
def dnf : formula L → Prop
| (all n φ)         := dnf φ
| φ                 := dnf_prop _ φ

instance decidable_dnf : decidable (dnf _ φ) := sorry

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

/-- Def 1.8.3. The term t is substitutable for the variable x in formula φ -/
def substitutable_for (x : ℕ) (t : term L) : formula L → Prop
| F                    := true
| (_ ≃ _)              := true
| (rel _ _)            := true
| ∼φ                   := substitutable_for φ
| (φ₁ or φ₂)           := (substitutable_for φ₁) ∧ (substitutable_for φ₂)
| (all y φ)            := ¬(free _ x φ) ∨ (¬(occurs_in_term _ y t) ∧ (substitutable_for φ))

/-- Def 1.5.3. The sentences of a language -/
def sentence : set (formula L) := λ φ, ∀ n : ℕ, ¬(free L n φ)

end language

section Structure

open term
open formula

variables (L : language) (A : Type*)

/-- Def 1.6.1. An L-structure -/
structure Structure :=
(functions : Π {n : ℕ}, L.functions n → (fin n → A) → A)
(relations : Π {n : ℕ}, L.relations n → (fin n → A) → Prop)

variable 𝔸 : Structure L A

/-- Def 1.7.1. Variable assignment function into A -/
def var_assign := ℕ → A

/-- Def 1.7.2. x-modification of the assignment function s -/
def modification_of (s : var_assign A) (x : ℕ) (a : A) : var_assign A :=
  λ (n : ℕ), if n = x then a else s n

notation s `[`x`|`a`]` := modification_of _ s x a

/-- Term assignment function -/
def term_assign := term L → A

/-- Def 1.7.3. The term assignment function induced by the variable assignment function s -/
def term_assign_of_s (s : var_assign A) : term_assign L A
| (v n)                 := s n
| (func fsymb args)     := 𝔸.functions fsymb (λ n, term_assign_of_s (args n))

instance : has_coe (var_assign A) (term_assign L A) := ⟨term_assign_of_s _ _ 𝔸⟩

notation ` * ` := term_assign_of_s _ _

/-- Variable assignments agree on free variables of a term -/
def agree_on_free_variables (s₁ s₂ : var_assign A)(t : term L) : Prop := ∀ n : ℕ, occurs_in_term _ n t → s₁ n = s₂ n

/-- Def 1.7.4. A structure 𝔸 satisfies formula φ with assignment s -/
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

/-- A structure 𝔸 satisfies a formula i.e. is a model of the formula -/
def satisfies_formula (φ : formula L) : Prop := 
  ∀ s : var_assign A, 𝔸 ⊨ φ | s 

notation 𝔸` ⊨ `φ       := satisfies_formula _ _ 𝔸 φ

/-- A structure 𝔸 satisfies a set of formulas -/
def satisfies_set_formula (Γ : set (formula L)) : Prop :=
  ∀ φ ∈ Γ, 𝔸 ⊨ φ

notation 𝔸` ⊨ `Γ          := satisfies_set_formula _ _ 𝔸 Γ

/-- Def 1.9.1. Logical implication in a structure -/
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