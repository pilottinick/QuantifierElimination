import prf

namespace first_order

section dnf

variables {L : language} (Γ : ℕ → formula L) {p q : formula L}

-- TODO: Use this
def equiv (α : language → Type) [i : has_coe (α L) (formula L)] : Prop := 
  ∀ φ : formula L, ∃ ψ : α L, Γ ▸ φ ↔ Γ ▸ ψ

-- def equiv_dcl := equiv dcl

-- def equiv_dnf := equiv dnf

def equiv_dcl (φ : formula L) : Prop := ∃ ψ : dcl L, Γ ▸ φ ↔ Γ ▸ ψ

def equiv_dnf (φ : formula L) : Prop := ∃ ψ : dnf L, Γ ▸ φ ↔ Γ ▸ ψ

def Equiv_Rule_To_equiv_dcl_Rule : (Γ ▸ p ↔ Γ ▸ q) → (equiv_dcl Γ p → equiv_dcl Γ q) := begin
   intros h₁ h₂,
   rcases h₂ with ⟨φ₃, h₃⟩,
   existsi φ₃,
   split,
   intro h₄,
   apply h₃.mp (h₁.mpr h₄),
   intro h₄,
   apply h₁.mp (h₃.mpr h₄),
end

def Equiv_Rule_To_equiv_dnf_Rule : (Γ ▸ p ↔ Γ ▸ q) → (equiv_dnf Γ p → equiv_dnf Γ q) := begin
   intros h₁ h₂,
   rcases h₂ with ⟨φ₃, h₃⟩,
   existsi φ₃,
   split,
   intro h₄,
   apply h₃.mp (h₁.mpr h₄),
   intro h₄,
   apply h₁.mp (h₃.mpr h₄),
end

/- The negation of a literal (as a literal) is equivalent to the negation of the literal (as a formula) -/
def neg_lit_equiv_lit : ∀ φ : lit L, Γ ▸ ∼↑φ ↔ Γ ▸ neg_lit _ φ  := begin
  intro φ,
  cases φ,
  refl,
  simp,
  split,
  intro h,
  apply Double_negation_elim_R,
  assumption,
  intro h,
  apply Double_negation_intro_R,
  assumption,
end

def dcl_and_equiv_dcl : ∀ φ₁ φ₂ : dcl L, equiv_dcl Γ (φ₁ and φ₂) := begin
  intros φ₁ φ₂,
  induction φ₁, induction φ₂,
  { existsi (cl.c φ₁ φ₂ : dcl L), refl },
  { rcases φ₂_ih_ᾰ with ⟨φ₂₁, h₂₁⟩, rcases φ₂_ih_ᾰ_1 with ⟨φ₂₂, h₂₂⟩,
    apply Equiv_Rule_To_equiv_dcl_Rule Γ ⟨DistributionAndOrOutLeft_R, DistributionAndOrInLeft_R⟩,
    apply Equiv_Rule_To_equiv_dcl_Rule Γ (Equiv_Rule_To_Or_Rule_R ⟨h₂₁.mpr, h₂₁.mp⟩ ⟨h₂₂.mpr, h₂₂.mp⟩),
    existsi dcl.d φ₂₁ φ₂₂, refl,
  },
  { rcases φ₁_ih_ᾰ with ⟨φ₁₁, h₁₁⟩, rcases φ₁_ih_ᾰ_1 with ⟨φ₁₂, h₁₂⟩,
    apply Equiv_Rule_To_equiv_dcl_Rule Γ ⟨DistributionAndOrOutRight_R, DistributionAndOrInRight_R⟩,
    apply Equiv_Rule_To_equiv_dcl_Rule Γ (Equiv_Rule_To_Or_Rule_R ⟨h₁₁.mpr, h₁₁.mp⟩ ⟨h₁₂.mpr, h₁₂.mp⟩),
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
    apply Rule_To_Left_Or_Rule_R h₁.mp,
    apply Rule_To_Right_Or_Rule_R h₂.mp,
    apply DeMorganNotAnd_R, apply h,
    intro h,
    apply DeMorganOr_R,
    apply Rule_To_Left_Or_Rule_R h₁.mpr,
    apply Rule_To_Right_Or_Rule_R h₂.mpr,
    apply h,
  },
  { rcases φ_ih_ᾰ with ⟨φ₁, h₁⟩, rcases φ_ih_ᾰ_1 with ⟨φ₂, h₂⟩,
    apply Equiv_Rule_To_equiv_dcl_Rule Γ ⟨DeMorganAnd_R, DeMorganNotOr_R⟩,
    apply Equiv_Rule_To_equiv_dcl_Rule Γ (Equiv_Rule_To_And_Rule_R ⟨h₁.mpr, h₁.mp⟩ ⟨h₂.mpr, h₂.mp⟩),
    apply dcl_and_equiv_dcl
  }
end

def dcl_or_equiv_dcl : ∀ φ₁ φ₂ : dcl L, equiv_dcl Γ (φ₁ or φ₂) := begin
  intros φ₁ φ₂,
  { existsi (dcl.d φ₁ φ₂ : dcl L), refl },
end

def qf_equiv_dcl : ∀ φ : qf L, equiv_dcl Γ φ := begin
  intro φ,
  induction φ,
  { existsi (@atom.f L : dcl L), refl, },
  { existsi (@atom.e L φ_ᾰ φ_ᾰ_1 : dcl L), refl },
  { existsi (@atom.r L φ_n φ_ᾰ φ_ᾰ_1 : dcl L), refl },
  { rcases φ_ih with ⟨φ, h⟩, 
    apply Equiv_Rule_To_equiv_dcl_Rule Γ (Equiv_Rule_To_Not_Rule_R ⟨h.mpr, h.mp⟩), 
    apply dcl_not_equiv_dcl, },
  { rcases φ_ih_ᾰ with ⟨φ₁, h₁⟩, rcases φ_ih_ᾰ_1 with ⟨φ₂, h₂⟩,
    apply Equiv_Rule_To_equiv_dcl_Rule Γ (Equiv_Rule_To_Or_Rule_R ⟨h₁.mpr, h₁.mp⟩ ⟨h₂.mpr, h₂.mp⟩),
    apply dcl_or_equiv_dcl },
end

def equiv_dcl_equiv_dnf : ∀ φ : formula L, equiv_dcl Γ φ →  equiv_dnf Γ φ := begin
  intros φ₁ h₁,
  rcases h₁ with ⟨φ₂, h₂⟩,
  existsi (dnf.dcl φ₂),
  apply h₂,
end

def dnf_not_equiv_dnf : ∀ φ : dnf L, equiv_dnf Γ ∼φ := begin
  intro φ,
  induction φ,
  { apply equiv_dcl_equiv_dnf, apply dcl_not_equiv_dcl },
  { apply Equiv_Rule_To_equiv_dnf_Rule Γ ⟨ExNot_R, NotAll_R⟩, 
    rcases φ_ih with ⟨φ, h⟩,
    apply Equiv_Rule_To_equiv_dnf_Rule Γ (Equiv_Rule_To_Ex_Rule_R ⟨h.mpr, h.mp⟩), simp,
    existsi dnf.ex φ_ᾰ φ, refl
  },
  { apply Equiv_Rule_To_equiv_dnf_Rule Γ ⟨AllNot_R, NotEx_R⟩,
    rcases φ_ih with ⟨φ, h⟩,
    apply Equiv_Rule_To_equiv_dnf_Rule Γ (Equiv_Rule_To_All_Rule_R ⟨h.mpr, h.mp⟩),
    existsi dnf.al φ_ᾰ φ, refl
  }
end

def dnf_or_equiv_dnf : ∀ φ₁ φ₂ : dnf L, equiv_dnf Γ (φ₁ or φ₂) := begin
  intros φ₁ φ₂,
  induction φ₁, induction φ₂,
  { apply equiv_dcl_equiv_dnf, apply dcl_or_equiv_dcl },
  repeat { sorry },
end

def dnf_all_equiv_dnf : ∀ n : ℕ, ∀ φ : dnf L, equiv_dnf Γ (formula.all n φ) := begin
  intros n φ,
  induction φ,
  { existsi (dnf.al n (dnf.dcl φ)), refl },
  repeat { sorry },
end

/- All formulas are logical equivalent to a formula in dnf -/
def for_all_equiv_dnf : ∀ φ : formula L, equiv_dnf Γ φ := begin
  intro φ,
  induction φ,
  { existsi (@atom.f L : dnf L), refl, },
  { existsi (@atom.e L φ_ᾰ φ_ᾰ_1 : dnf L), refl },
  { existsi (@atom.r L φ_n φ_ᾰ φ_ᾰ_1 : dnf L), refl },
  { rcases φ_ih with ⟨φ, h⟩, 
    apply Equiv_Rule_To_equiv_dnf_Rule Γ (Equiv_Rule_To_Not_Rule_R ⟨h.mpr, h.mp⟩), 
    apply dnf_not_equiv_dnf, },
  { rcases φ_ih_ᾰ with ⟨φ₁, h₁⟩, rcases φ_ih_ᾰ_1 with ⟨φ₂, h₂⟩,
    apply Equiv_Rule_To_equiv_dnf_Rule Γ (Equiv_Rule_To_Or_Rule_R ⟨h₁.mpr, h₁.mp⟩ ⟨h₂.mpr, h₂.mp⟩),
    apply dnf_or_equiv_dnf },
  { rcases φ_ih with ⟨φ, h⟩, 
    apply Equiv_Rule_To_equiv_dnf_Rule Γ (Equiv_Rule_To_All_Rule_R ⟨h.mpr, h.mp⟩),
    apply dnf_all_equiv_dnf }
end

end dnf

end first_order