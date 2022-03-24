import prf

namespace first_order

section dnf

variables (A : Type)
variables {L : language} (Γ : list (formula L)) {p q : formula L} [has_coe A (formula L)]

-- TODO: Use this
def equiv (α : Type) [has_coe α (formula L)]: Prop := 
  ∀ φ : formula L, ∃ ψ : α, (A∣Γ ⊢ φ) ↔ (A∣Γ ⊢ ψ)

-- def equiv_dcl := equiv dcl

-- def equiv_dnf := equiv dnf

def equiv_dcl (φ : formula L) : Prop := ∃ ψ : dcl L, (A∣Γ ⊢ φ) ↔ (A∣Γ ⊢ ψ)

def equiv_dnf (φ : formula L) : Prop := ∃ ψ : dnf L, (A∣Γ ⊢ φ) ↔ (A∣Γ ⊢ ψ)

def Eq_equiv_dcl : ((A∣Γ ⊢ p) ↔ (A∣Γ ⊢ q)) → (equiv_dcl A Γ p → equiv_dcl A Γ q) := begin
   intros h₁ h₂,
   rcases h₂ with ⟨φ₃, h₃⟩,
   existsi φ₃,
   split,
   intro h₄,
   apply h₃.mp (h₁.mpr h₄),
   intro h₄,
   apply h₁.mp (h₃.mpr h₄),
end

def Eq_equiv_dnf : ((A∣Γ ⊢ p) ↔ (A∣Γ ⊢ q)) → (equiv_dnf A Γ p → equiv_dnf A Γ q) := begin
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
def neg_lit_equiv_lit : ∀ φ : lit L, (A∣Γ ⊢ ∼↑φ) ↔ (A∣Γ ⊢ neg_lit _ φ) := begin
  intro φ,
  cases φ,
  refl,
  simp,
  split,
  intro h,
  apply R_ Double_negation_elim,
  assumption,
  intro h,
  apply R_ Double_negation_intro,
  assumption,
end

def dcl_and_equiv_dcl : ∀ φ₁ φ₂ : dcl L, equiv_dcl A Γ (φ₁ and φ₂) := begin
  intros φ₁ φ₂,
  induction φ₁, induction φ₂,
  { existsi (cl.c φ₁ φ₂ : dcl L), refl },
  { rcases φ₂_ih_ᾰ with ⟨φ₂₁, h₂₁⟩, rcases φ₂_ih_ᾰ_1 with ⟨φ₂₂, h₂₂⟩,
    apply Eq_equiv_dcl A Γ ⟨R_ DistributionAndOrOutLeft, R_ DistributionAndOrInLeft⟩,
    apply Eq_equiv_dcl A Γ (R_Eq_Or_ ⟨h₂₁.mpr, h₂₁.mp⟩ ⟨h₂₂.mpr, h₂₂.mp⟩),
    existsi dcl.d φ₂₁ φ₂₂, refl,
  },
  { rcases φ₁_ih_ᾰ with ⟨φ₁₁, h₁₁⟩, rcases φ₁_ih_ᾰ_1 with ⟨φ₁₂, h₁₂⟩,
    apply Eq_equiv_dcl A Γ ⟨R_ DistributionAndOrOutRight, R_ DistributionAndOrInRight⟩,
    apply Eq_equiv_dcl A Γ (R_Eq_Or_ ⟨h₁₁.mpr, h₁₁.mp⟩ ⟨h₁₂.mpr, h₁₂.mp⟩),
    existsi dcl.d φ₁₁ φ₁₂, refl,
  }
end

def dcl_not_equiv_dcl : ∀ φ : dcl L, equiv_dcl A Γ ∼φ := begin
  intro φ,
  induction φ, induction φ,
  { existsi (neg_lit L φ : dcl L), apply neg_lit_equiv_lit },
  { rcases φ_ih_ᾰ with ⟨φ₁, h₁⟩, rcases φ_ih_ᾰ_1 with ⟨φ₂, h₂⟩,
    existsi dcl.d φ₁ φ₂, split,
    intro h,
    apply R_Or_ h₁.mp h₂.mp,
    apply R_ DeMorganNotAnd, apply h,
    intro h,
    apply R_ DeMorganOr,
    apply R_Or_ h₁.mpr h₂.mpr,
    apply h,
  },
  { rcases φ_ih_ᾰ with ⟨φ₁, h₁⟩, rcases φ_ih_ᾰ_1 with ⟨φ₂, h₂⟩,
    apply Eq_equiv_dcl A Γ ⟨R_ DeMorganAnd, R_ DeMorganNotOr⟩,
    apply Eq_equiv_dcl A Γ (R_Eq_And_ ⟨h₁.mpr, h₁.mp⟩ ⟨h₂.mpr, h₂.mp⟩),
    apply dcl_and_equiv_dcl
  }
end

def dcl_or_equiv_dcl : ∀ φ₁ φ₂ : dcl L, equiv_dcl A Γ (φ₁ or φ₂) := begin
  intros φ₁ φ₂,
  { existsi (dcl.d φ₁ φ₂ : dcl L), refl },
end

def qf_equiv_dcl : ∀ φ : qf L, equiv_dcl A Γ φ := begin
  intro φ,
  induction φ,
  { existsi (@atom.f L : dcl L), refl, },
  { existsi (@atom.e L φ_ᾰ φ_ᾰ_1 : dcl L), refl },
  { existsi (@atom.r L φ_n φ_ᾰ φ_ᾰ_1 : dcl L), refl },
  { rcases φ_ih with ⟨φ, h⟩, 
    apply Eq_equiv_dcl  A Γ (R_Eq_Not_ ⟨h.mpr, h.mp⟩), 
    apply dcl_not_equiv_dcl, },
  { rcases φ_ih_ᾰ with ⟨φ₁, h₁⟩, rcases φ_ih_ᾰ_1 with ⟨φ₂, h₂⟩,
    apply Eq_equiv_dcl A Γ (R_Eq_Or_ ⟨h₁.mpr, h₁.mp⟩ ⟨h₂.mpr, h₂.mp⟩),
    apply dcl_or_equiv_dcl },
end

def equiv_dcl_equiv_dnf : ∀ φ : formula L, equiv_dcl A Γ φ →  equiv_dnf A Γ φ := begin
  intros φ₁ h₁,
  rcases h₁ with ⟨φ₂, h₂⟩,
  existsi (dnf.dcl φ₂),
  apply h₂,
end

def dnf_not_equiv_dnf : ∀ φ : dnf L, equiv_dnf A Γ ∼φ := begin
  intro φ,
  induction φ,
  { apply equiv_dcl_equiv_dnf, apply dcl_not_equiv_dcl },
  { apply Eq_equiv_dnf A Γ ⟨R_ ExNot, R_ NotAll⟩, 
    rcases φ_ih with ⟨φ, h⟩,
    apply Eq_equiv_dnf A Γ (R_Eq_Ex_ ⟨h.mpr, h.mp⟩), simp,
    existsi dnf.ex φ_ᾰ φ, refl
  },
  { apply Eq_equiv_dnf A Γ ⟨R_ AllNot, R_ NotEx⟩,
    rcases φ_ih with ⟨φ, h⟩,
    apply Eq_equiv_dnf A Γ (R_Eq_All_ ⟨h.mpr, h.mp⟩),
    existsi dnf.al φ_ᾰ φ, refl
  }
end

def dnf_or_equiv_dnf : ∀ φ₁ φ₂ : dnf L, equiv_dnf A Γ (φ₁ or φ₂) := begin
  intros φ₁ φ₂,
  induction φ₁, induction φ₂,
  { apply equiv_dcl_equiv_dnf, apply dcl_or_equiv_dcl },
  repeat { sorry },
end

def dnf_all_equiv_dnf : ∀ n : ℕ, ∀ φ : dnf L, equiv_dnf A Γ (formula.all n φ) := begin
  intros n φ,
  induction φ,
  { existsi (dnf.al n (dnf.dcl φ)), refl },
  repeat { sorry },
end

/- All formulas are logical equivalent to a formula in dnf -/
def for_all_equiv_dnf : ∀ φ : formula L, equiv_dnf A Γ φ := begin
  intro φ,
  induction φ,
  { existsi (@atom.f L : dnf L), refl, },
  { existsi (@atom.e L φ_ᾰ φ_ᾰ_1 : dnf L), refl },
  { existsi (@atom.r L φ_n φ_ᾰ φ_ᾰ_1 : dnf L), refl },
  { rcases φ_ih with ⟨φ, h⟩, 
    apply Eq_equiv_dnf A Γ (R_Eq_Not_ ⟨h.mpr, h.mp⟩), 
    apply dnf_not_equiv_dnf, },
  { rcases φ_ih_ᾰ with ⟨φ₁, h₁⟩, rcases φ_ih_ᾰ_1 with ⟨φ₂, h₂⟩,
    apply Eq_equiv_dnf A Γ (R_Eq_Or_ ⟨h₁.mpr, h₁.mp⟩ ⟨h₂.mpr, h₂.mp⟩),
    apply dnf_or_equiv_dnf },
  { rcases φ_ih with ⟨φ, h⟩, 
    apply Eq_equiv_dnf A Γ (R_Eq_All_ ⟨h.mpr, h.mp⟩),
    apply dnf_all_equiv_dnf }
end

end dnf

end first_order