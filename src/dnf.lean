import prf

namespace first_order

section formula

variables (L : language) (Γ : list (formula L))

lemma dnf_and : ∀ φ₁ φ₂ : formula L, is_dnf _ φ₁ → is_dnf _ φ₂ → is_dnf _ (φ₁ and φ₂) := sorry

lemma dnf_neg_neg : ∀ φ : formula L,
                    (∃ ψ₁ : formula L, is_dnf _ ψ₁ ∧ (Γ ▸ ∼φ ↔ Γ ▸ ψ₁)) →
                    (∃ ψ₂ : formula L, is_dnf _ ψ₂ ∧ (Γ ▸ φ  ↔ Γ ▸ ψ₂))

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
  existsi (a1 and a2),
  apply and.intro,
  apply dnf_and,
  apply h1,
  apply h3,
  apply iff.intro,
  intro h5,
  apply DeMorganAnd_R,
  have h6 : Γ ▸ (∼φ_ᾰ and ∼φ_ᾰ_1) := begin apply DeMorganNotOr_R h5 end,
  apply And_intro,
  apply Double_negation_intro_R,
  have h7 : Γ ▸ ∼φ_ᾰ := begin apply And_elim_left_R h6 end,
  apply (h2.mp h7),
  apply Double_negation_intro_R,
  have h8 : Γ ▸ ∼φ_ᾰ_1 := begin apply And_elim_right_R h6 end,
  apply (h4.mp h8),
  intro h5,
  apply DeMorganAnd_R,
  apply And_intro,
  have h6 : Γ ▸ a1 := begin apply And_elim_left_R h5 end,
  apply (h2.mpr h6),
  have h7 : Γ ▸ a2 := begin apply And_elim_right_R h5 end,
  apply (h4.mpr h7),
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