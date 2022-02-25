import prf

namespace first_order

section formula

variables (L : language) (Γ : list (formula L))

lemma if_neg_neg_dnf_impl_false : ∀ φ : formula L,
                                  (is_dnf _ ∼∼φ → false) := sorry

lemma if_neg_or_dnf_impl_false : ∀ φ ψ : formula L,
                                (is_dnf _ ∼(φ or ψ) → false) := sorry

lemma if_neg_all_dnf_impl_false : ∀ φ : formula L, ∀ n : ℕ,
                                  (is_dnf _ ∼(formula.all n φ) → false) := sorry

lemma if_neg_dnf_impl_dnf : ∀ φ : formula L, 
                            (is_dnf _ ∼φ → is_dnf _ φ) := begin
  intros φ h,
  cases φ,
  unfold is_dnf,
  unfold is_dnf,
  unfold is_dnf,
  apply false.elim (if_neg_neg_dnf_impl_false _ φ h),
  apply false.elim (if_neg_or_dnf_impl_false _ φ_ᾰ φ_ᾰ_1 h),
  apply false.elim (if_neg_all_dnf_impl_false _ φ_ᾰ_1 φ_ᾰ h),
end

lemma if_or_dnf_impl_dnf_left : ∀ φ ψ : formula L,
                                (is_dnf _ (φ or ψ) → is_dnf _ φ) := sorry

lemma if_or_dnf_impl_dnf_right : ∀ φ ψ : formula L,
                                (is_dnf _ (φ or ψ) → is_dnf _ ψ) := sorry

lemma dnf_and : ∀ φ₁ φ₂ : formula L, 
                (∃ ψ₁ : formula L, is_dnf _ ψ₁ ∧ (Γ ▸ φ₁ ↔ Γ ▸ ψ₁)) 
              → (∃ ψ₂ : formula L, is_dnf _ ψ₂ ∧ (Γ ▸ φ₂ ↔ Γ ▸ ψ₂))
              → (∃ ψ  : formula L, is_dnf _ ψ  ∧ (Γ ▸ (φ₁ and φ₂) ↔ Γ ▸ ψ)):= sorry

lemma dnf_neg_neg : ∀ φ : formula L,
                    (∃ ψ₁ : formula L, is_dnf _ ψ₁ ∧ (Γ ▸ ∼φ ↔ Γ ▸ ψ₁)) →
                    (∃ ψ₂ : formula L, is_dnf _ ψ₂ ∧ (Γ ▸ φ  ↔ Γ ▸ ψ₂)) := begin
  intros φ h1,
  apply exists.elim h1,
  intro a, simp, intros h2 h3,
  induction a,
  existsi ∼F,
  apply and.intro,
  unfold is_dnf,
  apply NegEquiv.mp h3,
  existsi ∼(a_ᾰ ≃ a_ᾰ_1),
  apply and.intro,
  unfold is_dnf,
  apply NegEquiv.mp h3,
  existsi ∼(formula.rel a_ᾰ a_ᾰ_1),
  apply and.intro,
  unfold is_dnf,
  apply NegEquiv.mp h3,
  existsi a_ᾰ,
  apply and.intro,
  apply if_neg_dnf_impl_dnf _ a_ᾰ h2,
  apply NegNegEquiv.mpr,
  apply h3,
  have h4 : is_dnf L a_ᾰ := begin apply if_or_dnf_impl_dnf_left _ a_ᾰ a_ᾰ_1 h2 end,
  have h5 : is_dnf L a_ᾰ_1 := begin apply if_or_dnf_impl_dnf_right _ a_ᾰ a_ᾰ_1 h2 end,
  have h6 : (Γ ▸  ∼ φ ↔ Γ ▸ a_ᾰ) ∨ (Γ ▸ ∼φ ↔ Γ ▸ a_ᾰ_1) := begin apply OrEquiv.mp h3 end, 
  apply or.elim h6,
  intro h7,
  apply a_ih_ᾰ h4 h7,
  intro h8,
  apply a_ih_ᾰ_1 h5 h8,
  -- TODO: All case
  admit,
end

lemma dnf_neg : ∀ φ : formula L, ∃ ψ : formula L, 
                (is_dnf _ ψ) ∧ (Γ ▸ ∼φ ↔ Γ ▸ ψ) := begin
  intros φ,
  induction φ,
  existsi ∼F,
  simp,
  existsi ∼(φ_ᾰ ≃ φ_ᾰ_1),
  simp,
  existsi ∼formula.rel φ_ᾰ φ_ᾰ_1,
  simp,
  have π₁ : ∃ ψ : formula L, is_dnf _ ψ ∧ (Γ ▸ φ_ᾰ  ↔ Γ ▸ ψ) := dnf_neg_neg _ Γ φ_ᾰ φ_ih,
  apply exists.elim π₁,
  intro a, simp, intros h1 h2,
  existsi a,
  apply and.intro,
  apply h1,
  apply iff.intro,
  intro h3,
  apply h2.mp,
  apply Double_negation_elim_L,
  apply h3,
  apply Prf.Axiom 0, refl,
  intro h3,
  apply Double_negation_intro_R,
  apply h2.mpr h3,
  apply exists.elim φ_ih_ᾰ,
  intro a1, simp, intros h1 h2,
  apply exists.elim φ_ih_ᾰ_1,
  intro a2, simp, intros h3 h4,
  have π₁ : ∃ ψ : formula L, is_dnf _ ψ ∧ (Γ ▸ (∼φ_ᾰ and ∼φ_ᾰ_1) ↔ Γ ▸ ψ) := sorry,
  apply exists.elim π₁,
  intro a, simp, intros h1 h2,
  existsi a,
  apply and.intro,
  apply h1,
  apply iff.intro,
  intro h5,
  apply h2.mp,
  apply DeMorganNotOr_R,
  apply h5,
  intro h6,
  apply DeMorganAnd_R,
  apply h2.mpr h6,
  -- TODO: All case
  admit,
end

lemma dnf_or : ∀ φ₁ φ₂ : formula L, ∃ ψ : formula L,
              (is_dnf _ ψ) ∧ (Γ ▸ (φ₁ or φ₂) ↔ Γ ▸ ψ) := sorry            

lemma dnf_all : ∀ φ : formula L, ∀ n : ℕ, ∃ ψ : formula L,
                (is_dnf _ ψ) ∧ (Γ ▸ (formula.all n φ) ↔ Γ ▸ ψ) := sorry

theorem dnf :  ∀ φ : formula L, ∃ ψ : formula L, 
            (is_dnf _ ψ) ∧ (Γ ▸ φ ↔ Γ ▸ ψ) := begin
  intros φ,
  cases φ,
  existsi F,
  simp,
  existsi φ_ᾰ ≃ φ_ᾰ_1,
  simp,
  existsi formula.rel φ_ᾰ φ_ᾰ_1,
  simp,
  apply dnf_neg,
  apply dnf_or,
  apply dnf_all,
end

end formula

end first_order