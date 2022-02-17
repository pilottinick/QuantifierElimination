import language

namespace first_order

section prf

variable L : language

inductive Prf
| Axiom : nat → Prf
| Bot_elim : nat → Prf
| Not_elim : nat → Prf → Prf
| Not_intro : Prf → Prf
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
| (Or_intro_left π) Γ (φ or ψ) := Proves π Γ φ
| (Or_intro_right π) Γ (φ or ψ) := Proves π Γ ψ
| (Or_elim n π₁ π₂) Γ χ := match Γ.nth n with
                           | some (φ or ψ) := (Proves π₁ (φ::Γ) χ) ∧ (Proves π₂ (ψ::Γ) χ)
                           | _             := false
                           end
                          
| _ _ _ := false

#check Proves

notation ⊢ Φ, φ  := ∃ π : Prf, Proves _ π Φ φ

variables p q r : formula L

example : ⊢ (F::[]), p:= begin
    let π : Prf := Bot_elim 0,
    existsi π,
    unfold Proves,
    
  end

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

end prf

end first_order