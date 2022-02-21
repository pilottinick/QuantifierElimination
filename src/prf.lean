import language

namespace first_order

section prf

variable L : language

inductive Prf : list (formula L) → formula L → Prop
| Axiom : forall {Γ : list (formula L)} n φ, Γ.nth n = some φ → Prf Γ φ
| Bot_elim : forall {Γ : list _} n φ, Γ.nth n = some F → Prf Γ φ
| Not_elim : forall {Γ : list _} n (φ ψ : formula _), Γ.nth n = some (formula.neg φ) → Prf Γ φ → Prf Γ ψ
| Or_elim : forall {Γ : list _} n φ ψ χ, Γ.nth n = some (φ or ψ)
  → Prf (φ :: Γ) χ → Prf (ψ :: Γ) χ → Prf Γ χ

/-
| Not_intro : Prf → Prf
| By_contradiction : Prf → Prf
| Or_intro_left : Prf → Prf 
| Or_intro_right : Prf → Prf
-/
open Prf
/-
def Proves : Prf → list (formula L) → formula L → Prop
| (Axiom n) Γ φ := Γ.nth n = (some φ)
| (Bot_elim n) Γ _ := (Γ.nth n) = (some F)
| (Not_elim n π) Γ _ := match Γ.nth n with
                        | some ∼φ  := Proves π Γ φ
                        | _        := false
                        end
| (Not_intro π) Γ ∼φ := Proves π (φ::Γ) F
| (By_contradiction π) Γ φ := Proves π (∼φ::Γ) F
| (Or_intro_left π) Γ (φ or ψ) := Proves π Γ φ
| (Or_intro_right π) Γ (φ or ψ) := Proves π Γ ψ
| (Or_elim n π₁ π₂) Γ χ := match Γ.nth n with
                           | some (φ or ψ) := (Proves π₁ (φ::Γ) χ) ∧ (Proves π₂ (ψ::Γ) χ)
                           | _             := false
                           end
                          
| _ _ _ := false

def proves (Γ : list (formula L)) (φ : formula L) : Prop := 
  ∃ π : Prf, Proves _ π Γ φ

def proves_prop (φ : formula L) (ψ : formula L) : Prop :=
  proves _ (φ::[]) ψ 
-/

/- Using ⊢ doesn't compile -/
infix ` ▸ ` := Prf _

notation ` ▸ `φ := Prf _ list.nil φ

variables p q r : formula L

variables Γ γ : list (formula L)

def Impl_elim_ : [p, p ⇒ q] ▸ q := begin
    apply (Or_elim 1),
    begin
      refl,
    end,
    begin
      simp,
      apply (Not_elim 0),
        refl,
        apply (Axiom 1), refl,
    end,
    begin
      apply (Axiom 0), refl,
    end
  end

def proves_impl : (p ▸ q) → (▸ (p ⇒ q)) := sorry

def Bot_elim_ : F ▸ p := begin
    let π : Prf := Bot_elim 0,
    existsi π,
    unfold Proves, simp,
  end

def Not_elim_ : [p, ∼p] ▸ q := begin
    let π : Prf := Not_elim 1 (Axiom 0),
    existsi π, simp [Proves], 
  end

def Not_intro_ : (p ⇒ F) ▸ ∼p := begin
    let π : Prf := Or_elim 0 (Axiom 0) (Bot_elim 0),
    existsi π, simp [Proves],
  end

def double_negation_elim : ∼∼p ▸ p := begin
    let π := By_contradiction (Not_elim 1 (Axiom 0)),
    existsi π, simp [Proves],
  end

def By_contradiction_ : (∼p ⇒ F) ▸ p := sorry

def Or_intro_left_ : p ▸ (p or q) := begin
    let π := Or_intro_left (Axiom 0),
    existsi π, simp [Proves],
  end

def Or_intro_right_ : q ▸ (p or q) := begin
    let π := Or_intro_right (Axiom 0),
    existsi π, simp [Proves],
  end

def Or_elim_ : [p or q, p ⇒ r, q ⇒ r] ▸ r := sorry

def And_intro_ : [p, q] ▸ (p and q) := begin
    let π : Prf := Not_intro
      (Or_elim 0 
        (Not_elim 0 (Axiom 2)) 
        (Not_elim 0 (Axiom 3))),
    existsi π, simp [Proves],
  end

def And_elim_left_ : (p and q) ▸ p := begin
    let π : Prf := 
      By_contradiction 
        (Not_elim 1 
        (Or_intro_left (Axiom 0))),

    existsi π,
    unfold Proves, simp [Proves],
  end

def And_elim_right_ : (p and q) ▸ q := begin
  let π : Prf :=
    By_contradiction
      (Not_elim 1
      (Or_intro_right (Axiom 0))),

    existsi π,
    unfold Proves, simp [Proves],
  end

def redundency : (γ ▸ p) → ((γ.append Γ) ▸ p) := sorry

def impl_elim : (p ▸ q) → (q ▸ r) → (p ▸ r) := sorry

def not_elim : (Γ ▸ (p and ∼p)) → (Γ ▸ q) := sorry

def not_intro : (Γ ▸ (p ⇒ F)) → (Γ ▸ ∼p) := sorry

def not_not_elim : (Γ ▸ ∼∼p) → (Γ ▸ p) := sorry

def or_intro_left : (Γ ▸ p) → (Γ ▸ (p or q)) := sorry

def or_intro_right : (Γ ▸ q) → (Γ ▸ (p or q)) := sorry

def or_elim : (Γ ▸ (p or q)) → (Γ ▸ (p ⇒ r)) → (Γ ▸ (q ⇒ r)) → (Γ ▸ r) := sorry

def and_intro : (Γ ▸ p) ∧ (Γ ▸ q) → (Γ ▸ (p and q)) := sorry

def excluded_middle : ▸ (p or ∼p) := sorry

end prf

end first_order
