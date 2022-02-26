import prf

namespace first_order

section formula

variables (L : language) (Γ : list (formula L))

def has_equiv_dnf (φ : formula L) := 
        ∃ ψ : formula L, (is_dnf _ ψ) ∧ (Γ ▸ (φ ⇒ ψ)) ∧ (Γ ▸ (ψ ⇒ φ))

lemma is_dnf_equiv_dnf : ∀ φ : formula L, is_dnf _ φ → has_equiv_dnf _ Γ φ := sorry

lemma is_dnf_and_dnf : ∀ φ ψ : formula L, is_dnf _ φ → is_dnf _ ψ → is_dnf _ (φ and ψ) := sorry

-- If the negation of a formula can be written in dnf so can the formula
lemma is_not_equiv_dnf_equiv_dnf : ∀ φ : formula L, 
                                  has_equiv_dnf _ Γ ∼φ → has_equiv_dnf _ Γ φ := sorry

-- Not case of dnf
lemma is_not_equiv_dnf : ∀ φ : formula L, has_equiv_dnf _ Γ ∼φ := begin
  intro φ,
  induction φ,
  apply is_dnf_equiv_dnf,
  unfold is_dnf,
  apply is_dnf_equiv_dnf,
  unfold is_dnf,
  apply is_dnf_equiv_dnf,
  unfold is_dnf,
  -- Not case
  apply is_not_equiv_dnf_equiv_dnf,
  apply exists.elim φ_ih,
  intro ψ, simp, intros ψdnf1 ψdnf2 ψdnf3,
  existsi ψ,
  apply and.intro,
  apply ψdnf1,
  apply and.intro,
  apply Right_Rule_Impl Double_negation_intro_R, simp,
  apply ψdnf2,
  apply Impl_Right_Rule Double_negation_intro_R, simp,
  apply ψdnf3,
  -- Or case
  rename φ_ih_ᾰ ψ₁_ih, rename φ_ih_ᾰ_1 ψ₂_ih,
  apply exists.elim ψ₁_ih,
  intro ψ₁, simp, intros ψ₁dnf1 ψ₁dnf2 ψ₁dnf3,
  apply exists.elim ψ₂_ih,
  intros ψ₂, simp, intros ψ₂dnf1 ψ₂dnf2 ψ₂dnf3,
  existsi (ψ₁ and ψ₂),
  apply and.intro,
  apply is_dnf_and_dnf _ _ _ ψ₁dnf1 ψ₂dnf1,
  apply and.intro, simp,
  apply Right_Rule_Impl DeMorganAnd_R, simp,
  have ψ₁dnf2_R : Γ ▸  ∼ φ_ᾰ → Γ ▸ ψ₁ := sorry,
  apply Left_And_Right_Rule_Impl ψ₁dnf2_R, simp,
  have ψ₂dnf2_R : Γ ▸  ∼ φ_ᾰ_1 → Γ ▸ ψ₂ := sorry,
  apply Right_And_Right_Rule_Impl ψ₂dnf2_R, simp,
  apply Or_comm_R ExcludedMiddle, simp,
  apply Impl_Right_Rule DeMorganAnd_R, simp,
  have ψ₁dnf3_R : Γ ▸  ∼ φ_ᾰ → Γ ▸ ψ₁ := sorry,
  apply Left_And_Impl_Right_Rule ψ₁dnf3_R, simp,
  have ψ₂dnf3_R : Γ ▸  ∼ φ_ᾰ_1 → Γ ▸ ψ₂ := sorry,
  apply Right_And_Impl_Right_Rule ψ₂dnf3_R, simp,
  apply Or_comm_R ExcludedMiddle,
  -- TODO: All case
  admit,
end

-- Or case of dnf
lemma is_or_equiv_dnf : ∀ φ ψ : formula L, has_equiv_dnf _ Γ (φ or ψ) := sorry

-- All case of dnf
lemma is_all_equiv_dnf : ∀ φ : formula L, ∀ n : ℕ, has_equiv_dnf _ Γ (formula.all n φ) := sorry

theorem dnf :  ∀ φ : formula L, has_equiv_dnf _ Γ φ := begin
  intro φ,
  cases φ,
  -- The first three cases are the same
  -- Is there any way in lean to use repeat a fixed number of times?
  -- I don't want it to apply this to all goals, just the first three
  apply is_dnf_equiv_dnf,
  unfold is_dnf,
  apply is_dnf_equiv_dnf,
  unfold is_dnf,
  apply is_dnf_equiv_dnf,
  unfold is_dnf,
  apply is_not_equiv_dnf,
  apply is_or_equiv_dnf,
  apply is_all_equiv_dnf,
end

end formula

end first_order