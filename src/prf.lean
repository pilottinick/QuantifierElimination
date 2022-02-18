import language

namespace first_order

section prf

variable L : language

inductive Prf
| Axiom : nat → Prf
| Bot_elim : nat → Prf
| Not_elim : nat → Prf → Prf
| Not_intro : Prf → Prf
| By_contradiction : Prf → Prf
| Or_intro_left : Prf → Prf 
| Or_intro_right : Prf → Prf
| Or_elim : nat → Prf → Prf → Prf

open Prf

def Proves : Prf → list (formula L) → formula L → Prop
| (Axiom n) Γ φ := Γ.nth n = (some φ)
| (Bot_elim n) Γ _ := (Γ.nth n) = (some F)
| (Not_elim n π) Γ _ := match Γ.nth n with
                        | some ∼φ  := Proves π Γ φ
                        | _        := false
                        end
| (Not_intro π) Γ (∼φ) := Proves π (φ::Γ) F
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

/- Using ⊢ doesn't compile -/
infix ` ▸ ` := proves _

notation φ` ▸ `ψ := proves_prop _ φ ψ

notation ` ▸ `φ := proves _ list.nil φ

variables p q r : formula L

variables Γ γ : list (formula L)

def redundency : (γ ▸ p) → ((γ.append Γ) ▸ p) := sorry

def bot_elim : F ▸ p := begin
    let π : Prf := Bot_elim 0,
    existsi π,
    unfold Proves,
    begin
      refl
    end
  end

def And_intro : [p, q] ▸ (p and q) := begin
  let π : Prf := Not_intro
    (Or_elim 0
      (Not_elim 0 (Axiom 2))
      (Not_elim 0 (Axiom 3))),
  existsi π, simp [Proves],
end

def And_elim_left : (p and q) ▸ p := begin
    let π : Prf := 
      By_contradiction 
        (Not_elim 1 
        (Or_intro_left (Axiom 0))),
    
    existsi π,
    unfold Proves, simp [Proves],
  end

def And_elim_right : (p and q) ▸ q := sorry

def impl_proves : (▸ (p ⇒ q)) → (p ▸ q) := sorry

def proves_impl : (p ▸ q) → (▸ (p ⇒ q)) := sorry

def Impl_elim : (p and (p ⇒ q)) ▸ q := sorry



def not_elim : (Γ ▸ (p and ∼p)) → (Γ ▸ q) := sorry

def not_intro : (Γ ▸ (p ⇒ F)) → (Γ ▸ ∼p) := sorry

def not_not_elim : (Γ ▸ ∼∼p) → (Γ ▸ p) := sorry

def or_intro_left : (Γ ▸ p) → (Γ ▸ (p or q)) := sorry

def or_intro_right : (Γ ▸ q) → (Γ ▸ (p or q)) := sorry

def or_elim : (Γ ▸ (p or q)) → (Γ ▸ (p ⇒ r)) → (Γ ▸ (q ⇒ r)) → (Γ ▸ r) := sorry

def and_intro : (Γ ▸ p) ∧ (Γ ▸ q) → (Γ ▸ (p and q)) := sorry

def excluded_middle : ▸ (p or ∼p) := sorry

/-
example : ⊢ ((p or q)::[]), (q or p) := begin
    let π₁ : Prf := Or_intro_right,
    let π₂ : Prf := Or_intro_left,
    let π : Prf := Or_elim π₁ π₂,
    existsi π,
    unfold Proves,
    apply and.intro,
    begin
      apply eq.refl p,
    end,
    begin
      apply eq.refl q,
    end
example : F ▸ p := begin
    let π : Prf := Bot_elim 0,
    existsi π, simp [Proves],
  end

example : (p or q) ▸ (q or p) := begin
    let π : Prf := Or_elim 0
      (Or_intro_right (Axiom 0))
      (Or_intro_left (Axiom 0)),
    existsi π, simp [Proves],
  end


example : (p and q) ▸ (q and p) := begin
    let π : Prf := Not_intro
      (Not_elim 1 (Or_elim 0
        (Or_intro_right (Axiom 0))
        (Or_intro_left (Axiom 0)))),
    existsi π, simp [Proves],
  end
-/

end prf

end first_order
