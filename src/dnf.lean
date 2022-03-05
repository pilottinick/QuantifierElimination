import prf
import tactic

namespace first_order

section dnf

variables {L : language} (Γ : ℕ → formula L) {p q : formula L}

def equiv_dcl (φ : formula L) : Prop := ∃ ψ : dcl L, Γ ▸ φ ↔ Γ ▸ ψ

def equiv_dnf (φ : formula L) : Prop := ∃ ψ : dnf L, Γ ▸ φ ↔ Γ ▸ ψ

def Right_Rule_To_equiv_dcl_Rule : (Γ ▸ p → Γ ▸ q) → (equiv_dcl Γ p → equiv_dcl Γ q) := sorry

/- The negation of a literal (as a literal) is equivalent to the negation of the literal (as a formula) -/
def neg_lit_equiv_lit : ∀ φ : lit L, Γ ▸ ∼↑φ ↔ Γ ▸ neg_lit _ φ  := begin
  intro φ,
  cases φ,
  refl,
  { simp, apply Double_negation_R }
end

def dcl_and_equiv_dcl : ∀ φ₁ φ₂ : dcl L, equiv_dcl Γ (φ₁ and φ₂) := begin
  intros φ₁ φ₂,
  induction φ₁, induction φ₂,
  { existsi (cl.c φ₁ φ₂ : dcl L), refl },
  { rcases φ₂_ih_ᾰ with ⟨φ₂₁, h₂₁⟩, rcases φ₂_ih_ᾰ_1 with ⟨φ₂₂, h₂₂⟩,
    apply Right_Rule_To_equiv_dcl_Rule Γ DistributionAndOrOutLeft_R,
    apply Right_Rule_To_equiv_dcl_Rule Γ (Right_Rule_To_Left_Or_Rule h₂₁.mpr),
    apply Right_Rule_To_equiv_dcl_Rule Γ (Right_Rule_To_Right_Or_Rule h₂₂.mpr),
    existsi dcl.d φ₂₁ φ₂₂, refl,
  },
  { rcases φ₁_ih_ᾰ with ⟨φ₁₁, h₁₁⟩, rcases φ₁_ih_ᾰ_1 with ⟨φ₁₂, h₁₂⟩,
    apply Right_Rule_To_equiv_dcl_Rule Γ DistributionAndOrOutRight_R,
    apply Right_Rule_To_equiv_dcl_Rule Γ (Right_Rule_To_Left_Or_Rule h₁₁.mpr),
    apply Right_Rule_To_equiv_dcl_Rule Γ (Right_Rule_To_Right_Or_Rule h₁₂.mpr),
    existsi dcl.d φ₁₁ φ₁₂, refl,
  }
end

def dcl_not_equiv_dcl : ∀ φ : dcl L, equiv_dcl Γ ∼φ := begin
  intro φ,
  induction φ, induction φ,
  { existsi (neg_lit L φ : dcl L), apply neg_lit_equiv_lit },
  { rcases φ_ih_ᾰ with ⟨φ₁, h₁⟩, rcases φ_ih_ᾰ_1 with ⟨φ₂, h₂⟩,
    existsi dcl.d φ₁ φ₂, split,
    intro h,
    apply Right_Rule_To_Left_Or_Rule h₁.mp,
    apply Right_Rule_To_Right_Or_Rule h₂.mp,
    apply DeMorganNotAnd_R, apply h,
    intro h,
    apply DeMorganOr_R,
    apply Right_Rule_To_Left_Or_Rule h₁.mpr,
    apply Right_Rule_To_Right_Or_Rule h₂.mpr,
    apply h,
  },
  { rcases φ_ih_ᾰ with ⟨φ₁, h₁⟩, rcases φ_ih_ᾰ_1 with ⟨φ₂, h₂⟩,
    apply Right_Rule_To_equiv_dcl_Rule Γ DeMorganAnd_R,
    apply Right_Rule_To_equiv_dcl_Rule Γ (Right_Rule_To_Left_And_Rule h₁.mpr),
    apply Right_Rule_To_equiv_dcl_Rule Γ (Right_Rule_To_Right_And_Rule h₂.mpr),
    apply dcl_and_equiv_dcl
  }
end

def dcl_or_equiv_dcl : ∀ φ₁ φ₂ : dcl L, equiv_dcl Γ (φ₁ or φ₂) := begin
  intros φ₁ φ₂,
  { existsi (dcl.d φ₁ φ₂ : dcl L), refl },
end

def for_all_qf_equiv_dcl : ∀ φ : qf L, equiv_dcl Γ φ := begin
  intro φ,
  induction φ,
  { existsi (@atom.f L : dcl L), refl },
  { existsi (@atom.e L φ_ᾰ φ_ᾰ_1 : dcl L), refl },
  { existsi (@atom.r L φ_n φ_ᾰ φ_ᾰ_1 : dcl L), refl },
  { rcases φ_ih with ⟨φ, h⟩, 
    apply Right_Rule_To_equiv_dcl_Rule Γ (Right_Rule_To_Not_Rule h.mpr), 
    apply dcl_not_equiv_dcl, },
  { rcases φ_ih_ᾰ with ⟨φ₁, h₁⟩, rcases φ_ih_ᾰ_1 with ⟨φ₂, h₂⟩,
    apply Right_Rule_To_equiv_dcl_Rule Γ (Right_Rule_To_Or_Rule h₁.mpr h₂.mpr),
    apply dcl_or_equiv_dcl },
end

end dnf

end first_order