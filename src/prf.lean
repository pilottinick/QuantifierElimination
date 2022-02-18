import language

namespace first_order

section prf

variable L : language

inductive Prf
| Axiom : nat → Prf
| Bot_elim : nat → Prf
| Not_elim : nat → Prf → Prf
| Not_intro : Prf → Prf
| Not_not_elim : nat → Prf
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
| (Not_not_elim n) Γ φ := match Γ.nth n with
                          | some ∼∼φ  := true
                          | _          := false
                          end
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

variable Γ : list (formula L)

def impl_proves : (▸ (p ⇒ q)) → (p ▸ q) := sorry

def proves_impl : (p ▸ q) → (▸ (p ⇒ q)) := sorry

def bot_elim : F ▸ p := begin
    let π : Prf := Bot_elim 0,
    existsi π,
    unfold Proves,
    begin
      apply eq.refl ([F].nth 0),
    end
  end

def not_elim : (Γ ▸ (p and ∼p)) → (Γ ▸ q) := sorry

def not_intro : (Γ ▸ (p ⇒ F)) → (Γ ▸ ∼p) := sorry

def not_not_elim : (Γ ▸ ∼∼p) → (Γ ▸ p) := sorry

def or_intro_left : (Γ ▸ p) → (Γ ▸ (p or q)) := sorry

def or_intro_right : (Γ ▸ q) → (Γ ▸ (p or q)) := sorry

def or_elim : (Γ ▸ (p or q)) → (Γ ▸ (p ⇒ r)) → (Γ ▸ (q ⇒ r)) → (Γ ▸ r) := sorry

def excluded_middle : [] ▸ (p or ∼p) := sorry

def And_intro : [p, q] ▸ (p and q) := sorry

def And_elim_left : (p and q) ▸ p := begin
    let Γ : list (formula L) := ((p and q)::[]),
    let π₁ : Prf := sorry,
    let π : Prf := Not_intro π₁,
    existsi π,
    admit
  end

def And_elim_right : (p and q) ▸ q := sorry

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
  end


example : ⊢ ((p and q)::[]), (q and p) := begin
    let π₃ : Prf := sorry,
    let π₂ : Prf := sorry,
    let π₁ : Prf := Or_elim π₃ π₂,
    let π : Prf := Not_intro π₁,
    existsi π,
    unfold Proves,
    
  end
-/

end prf

end first_order