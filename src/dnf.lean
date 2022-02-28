import language

namespace first_order

section formula

variables (L : language) (Γ : list (formula L)) (p q φ φ₁ φ₂ : formula L)

/- A dnf_prop is in dnf -/
def dnf_prop_dnf : dnf_prop _ φ  → dnf _ φ := begin
  intro φdnf_prop,
  cases φ,
  repeat { simp },
  repeat { assumption },
  simp at φdnf_prop,
  apply false.elim φdnf_prop,
end

/- An atomic formula is in dnf_prop -/
def atomic_dnf_prop : atomic _ φ → dnf_prop _ φ := begin
  intro atom,
  cases φ,
  any_goals { by { simp } },
  any_goals { by { simp at atom, apply false.elim atom } },
end

/- An atomic formula is dnf -/
def atomic_dnf : atomic _ φ → dnf _ φ := begin
  intro atom,
  have φdnf_prop : dnf_prop _ φ := atomic_dnf_prop _ _ atom,
  apply dnf_prop_dnf _ _ φdnf_prop,
end

/- The negation of an atomic formula is in dnf_prop -/
def neg_atomic_dnf_prop : atomic _ φ → dnf_prop _ ∼φ := begin
  intro natom,
  cases φ,
  any_goals { by { simp } },
  any_goals { by { simp at natom, apply false.elim natom } },
end

/- The negation of an atomic formula is dnf -/
def neg_atomic_dnf : atomic _ φ → dnf _ ∼φ := begin
  intro natom,
  have φdnf_prop : dnf_prop _ ∼φ := neg_atomic_dnf_prop _ _ natom,
  apply dnf_prop_dnf _ _ φdnf_prop,
end

/- A conjunction of two atomic formulas is in dnf -/
def conj_atomic_dnf : conj_atomic _ φ → dnf _ φ := begin
  intro φconj_atomic,
  apply exists.elim φconj_atomic,
  intros φ₁ h',
  apply exists.elim h',
  intros φ₂ h,
  rw and.elim_left h,
  simp,
  apply and.elim_right h,
end

/- The negative of a disjunction of two negative atomic formulas is in dnf -/
def disj_neg_atomic_neg_dnf : disj_neg_atomic _ φ → dnf _ ∼φ := begin
  intro φdisj_neg_atomic,
  apply exists.elim φdisj_neg_atomic,
  intros φ₁ h',
  apply exists.elim h',
  intros φ₂ h,
  rw and.elim_left h,
  simp,
  apply and.elim_right h,
end

/- A literal is in dnf -/
def literal_dnf_prop : literal _ φ → dnf_prop _ φ := begin
  intro lit,
  have h1 : ∃ ψ : formula L, (atomic _ ψ) ∧ (φ = ψ ∨ φ = ∼ψ) := 
    (lit_atomic_or_neg_atomic _ φ).mp lit,
  apply exists.elim h1,
  intros ψ h2,
  have h3 : atomic _ ψ := and.elim_left h2,
  have h4 : φ = ψ ∨ φ = ∼ψ := and.elim_right h2,
    apply or.elim h4,
  all_goals {
    intro p,
    rw p,
  },
  apply atomic_dnf_prop,
  assumption,
  simp,
  cases ψ,
  repeat { simp at * },
  repeat { apply false.elim h3 },
end

/- The number of connectives in the formula that break dnf rules -/
attribute [simp]
def dnf_bad_connectives : formula L → ℕ
| F                         := 0
| (t₁ ≃ t₂)                 := 0
| (formula.rel rsymb args)  := 0
| ∼φ                        := (dnf_bad_connectives φ) +
                               (if (dnf _ ∼φ) then 0 else 1)
| (φ₁ or φ₂)                 := (dnf_bad_connectives φ₁) + (dnf_bad_connectives φ₂) +
                                (if (dnf _ (φ₁ or φ₂)) then 0 else 1)
| (formula.all m φ)          := (dnf_bad_connectives φ) +
                                (if (dnf _ (formula.all m φ)) then 0 else 1)

/- If a formula has no bad connectives then the formula is already in dnf -/
def bc_eq_zero_dnf : dnf_bad_connectives _ φ = 0 → dnf _ φ := begin
  contrapose,
  induction φ,
  any_goals { by { intro h, simp, apply h true.intro } },
  intro nφdnf,
  unfold dnf_bad_connectives,
  simp,
  intro h,
  simp at nφdnf, 
  contradiction,
  simp,
  intros h1 h2 h3 h4,
  apply h1 h4,
  simp,
  intros h1 h2,
  let h := φ_ih h1,
  contradiction,
end

/- If a formula is not in dnf, it has at least one bad connective -/
def ndnf_bc_ge_one : ¬(dnf _ φ) → (dnf_bad_connectives _ φ) > 0 := begin
  intro ndnf,
  have h1 : ¬(dnf _ φ) → ¬(dnf_bad_connectives _ φ) = 0 := begin contrapose!, apply bc_eq_zero_dnf end,
  have h2 : ¬(dnf_bad_connectives _ φ) = 0 := h1 ndnf,
  exact pos_iff_ne_zero.mpr (h1 ndnf),
end

/- If a formula ∼φ is in dnf then φ is atomic or disjunction of two negative atomics -/
lemma neg_dnf_phi_atomic_or_disj_neg_atomic : dnf _ (∼φ) → ((atomic _ φ) ∨ disj_neg_atomic _ φ) := begin
  intro φdnf,
  simp at φdnf,
  cases φ,
  any_goals { by { apply or.intro_left, simp } },
  any_goals { by { simp at φdnf, contradiction } },
  cases φ_ᾰ,
  all_goals { cases φ_ᾰ_1 },
  any_goals { 
    by { 
      unfold dnf_prop at φdnf, 
      unfold neg_atomic at φdnf, 
      apply false.elim (and.elim_left φdnf)
      <|>
      apply false.elim (and.elim_right φdnf)
    } 
  },
  apply or.intro_right,
  existsi φ_ᾰ, existsi φ_ᾰ_1,
  repeat { split },
  repeat { unfold dnf_prop at φdnf },
  apply and.elim_left φdnf,
  apply and.elim_right φdnf,
end

/- If a formula ∼φ is in dnf then φ is in dnf -/
lemma neg_dnf_phi_dnf : dnf _ ∼φ → dnf _ φ := begin
  intro φdnf,
  have atom_or_disj : (atomic _ φ) ∨ disj_neg_atomic _ φ := begin
      simp at φdnf,
      apply neg_dnf_phi_atomic_or_disj_neg_atomic _ _ φdnf, 
    end,
  cases φ,
  any_goals { simp },
  any_goals { by { repeat { simp }, apply false.elim φdnf, } },
  apply or.elim atom_or_disj,
  intro atom,
  simp at atom,
  apply false.elim atom,
  intro conj,
  apply exists.elim conj,
  intro φ',
  intro conj',
  apply exists.elim conj,
  intro φ₁,
  intro conj'',
  apply exists.elim conj'',
  intro φ₂,
  intro conj''',
  have eq_conj''' : (φ_ᾰ or φ_ᾰ_1) = (∼φ₁ or ∼φ₂) := and.elim_left conj''',
  have φ₁eq : φ_ᾰ = ∼φ₁ := begin 
    simp at eq_conj''',
    apply and.elim_left eq_conj''',
  end,
  have φ₂eq : φ_ᾰ_1 = ∼φ₂ := begin
    simp at eq_conj''',
    apply and.elim_right eq_conj''',
  end,
  rw φ₁eq,
  rw φ₂eq,
  have φ₁_atom : atomic _ φ₁ := and.elim_left (and.elim_right conj'''),
  have φ₂_atom : atomic _ φ₂ := and.elim_right (and.elim_right conj'''),
  have nφ₁_dnf : dnf_prop _ ∼φ₁ := neg_atomic_dnf_prop _ _ φ₁_atom,
  have nφ₂_dnf : dnf_prop _ ∼φ₂ := neg_atomic_dnf_prop _ _ φ₂_atom,
  simp at *,
  apply and.intro nφ₁_dnf nφ₂_dnf,
end

/- If a formula ∼φ has one bad connective then φ is in dnf -/
lemma not_bc_eq_one_phi_dnf : dnf_bad_connectives _ ∼φ = 1 → dnf _ φ := begin
  intro bc,
  have h1 : ¬dnf L φ → ¬dnf L ( ∼ φ) := begin contrapose!, apply neg_dnf_phi_dnf end,
  apply by_contra,
  intro nφdnf,
  simp at bc,
  have φbc : dnf_bad_connectives _ φ > 0 := by apply ndnf_bc_ge_one _ _ nφdnf,
  have nφdnf : ¬(dnf _ ∼φ) := h1 nφdnf,
  have ite_h : ite (dnf L ( ∼ φ)) 0 1 = 1 := begin
    simp,
    intro h,
    contradiction,
  end,
  linarith,
end

/- If a formula ∼∼φ has one bad connective then φ is in dnf -/
lemma not_not_bc_eq_one_phi_dnf : ∀ φ : formula L, (dnf_bad_connectives _ ∼∼φ = 1) →
                                      dnf _ φ := begin
  intros φ bc,
  have nφdnf : dnf _ ∼φ := not_bc_eq_one_phi_dnf _ (∼φ) bc,
  apply neg_dnf_phi_dnf _ φ nφdnf,
end

/- If a formula (φ₁ and φ₂) is in dnf then φ₁ φ₂ are in dnf -/
lemma and_dnf_phi_dnf : (dnf _ (φ₁ and φ₂)) → (dnf _ φ₁) ∧ (dnf _ φ₂) := begin
  intro φ₁aφ₂dnf,
  simp at φ₁aφ₂dnf,
  have φ₁atom : atomic _ φ₁ := neg_atomic_phi_atomic _ _ (and.elim_left φ₁aφ₂dnf),
  have φ₂atom : atomic _ φ₂ := neg_atomic_phi_atomic _ _ (and.elim_right φ₁aφ₂dnf),
  apply and.intro (atomic_dnf _ _ φ₁atom) (atomic_dnf _ _ φ₂atom),
end

/- If a formula (φ₁ and φ₂) has one bad connective then φ₁ φ₂ are in dnf -/
lemma and_bc_eq_one_phi_dnf : (dnf_bad_connectives _ (φ₁ and φ₂) = 1) → (dnf _ φ₁) ∧ (dnf _ φ₂) := begin
  intro bc,
  have φ₁em : dnf _ φ₁ ∨ ¬(dnf _ φ₁) := by apply em,
  have φ₂em : dnf _ φ₂ ∨ ¬(dnf _ φ₂) := by apply em,
  apply or.elim φ₁em,
  apply or.elim φ₂em,
  intros φ₂dnf φ₁dnf,
  apply and.intro φ₁dnf φ₂dnf,
  intros nφ₂dnf φ₁dnf,
  split,
  assumption,
  have : dnf_bad_connectives L (φ₁ and φ₂) > 1 := sorry,
  linarith,
  intro nφ₁dnf,
  have : dnf_bad_connectives L (φ₁ and φ₂) > 1 := sorry,
  linarith,
end                      

/- If a formula (φ₁ or φ₂) is in dnf then φ₁ φ₂ are in dnf -/
lemma or_dnf_phi_dnf : (dnf _ (φ₁ or φ₂)) → (dnf _ φ₁) ∧ (dnf _ φ₂) := begin
  intro φ₁oφ₂dnf,
  simp at φ₁oφ₂dnf,
  have φ₁dnf_prop : dnf_prop _ φ₁ := and.elim_left φ₁oφ₂dnf,
  have φ₂dnf_prop : dnf_prop _ φ₂ := and.elim_right φ₁oφ₂dnf,
  apply and.intro (dnf_prop_dnf _ _ φ₁dnf_prop) (dnf_prop_dnf _ _ φ₂dnf_prop),
end

/- If a formula (φ₁ or φ₂) has one bad connective then φ₁ φ₂ are in dnf -/
lemma or_bc_eq_one_phi_dnf : (dnf_bad_connectives _ (φ₁ or φ₂) = 1) →
                              (dnf _ φ₁) ∧ (dnf _ φ₂) := begin
  intro bc,
  have φ₁em : dnf _ φ₁ ∨ ¬(dnf _ φ₁) := by apply em,
  have φ₂em : dnf _ φ₂ ∨ ¬(dnf _ φ₂) := by apply em,
  apply or.elim φ₁em,
  apply or.elim φ₂em,
  intros φ₂dnf φ₁dnf,
  apply and.intro φ₁dnf φ₂dnf,
  intros nφ₂dnf φ₁dnf,
  split,
  assumption,
  have : dnf_bad_connectives L (φ₁ or φ₂) > 1 := sorry,
  linarith,
  intro nφ₁dnf,
  have : dnf_bad_connectives L (φ₁ or φ₂) > 1 := sorry,
  linarith,
end 

/- If a formula (all n φ) is in dnf then φ is in dnf -/
lemma all_dnf_phi_dnf : ∀ n : ℕ, (dnf _ (formula.all n φ)) → (dnf _ φ) := sorry

/- If a formula (all n φ) has one bad connective then φ is in dnf -/
lemma all_bc_eq_one_phi_dnf : ∀ n : ℕ, (dnf_bad_connectives _ (formula.all n φ)) = 1 → (dnf _ φ) := sorry

/- If a formula is in dnf it has no bad connectives -/
lemma dnf_bc_eq_zero : dnf _ φ → dnf_bad_connectives _ φ = 0 := begin
  intros φdnf,
  induction φ,
  any_goals { simp },
  apply and.intro,
  have h : dnf _ φ_ᾰ := neg_dnf_phi_dnf _ _ φdnf,
  apply φ_ih h,
  intro h, contradiction,
  apply and.intro,
  have h : dnf _ φ_ᾰ ∧ dnf _ φ_ᾰ_1 := or_dnf_phi_dnf _ _ _ φdnf,
  apply and.intro,
  have h1 : dnf _ φ_ᾰ := h.left,
  apply φ_ih_ᾰ h1,
  have h2 : dnf _ φ_ᾰ_1 := h.right,
  apply φ_ih_ᾰ_1 h2,
  intro h,
  simp at φdnf,
  apply absurd (and.elim_right φdnf) (h (and.elim_left φdnf)),
  apply and.intro,
  have h : dnf L φ_ᾰ_1 := all_dnf_phi_dnf _ _ _ φdnf,
  apply φ_ih h,
  intro h, contradiction,
end

/- If a formula φ is in dnf then ∼φ is in dnf or has one bad connective -/
lemma dnf_neg_dnf_or_bc_eq_one : dnf _ φ → ((dnf _ ∼φ) ∨ (dnf_bad_connectives _ ∼φ) = 1) := begin
  intro h, 
  have dnf_or_ndnf : (dnf _ (∼φ)) ∨ ¬(dnf _ (∼φ)) := by apply em,
  apply or.elim dnf_or_ndnf,
  intro dnf,
  apply or.intro_left,
  apply dnf,
  intro dnf,
  apply or.intro_right,
  simp,
  unfold ite,
  have bc : dnf_bad_connectives L φ = 0 := dnf_bc_eq_zero _ _ h,
  rw bc,
  admit,
end

/- If formulas φ₁ φ₂ are in dnf then (φ₁ and φ₂) is in dnf or has one bad connective -/
lemma dnf_and_dnf_phi_dnf_or_bc_eq_one : dnf _ φ₁ → dnf _ φ₂ → 
    ((dnf _ (φ₁ and φ₂)) ∨ (dnf_bad_connectives _ (φ₁ and φ₂) = 1)) := sorry

/- If formulas φ₁ φ₂ are in dnf then (φ₁ or φ₂) is in dnf -/
lemma dnf_or_dnf : dnf _ φ₁ → dnf _ φ₂ → (dnf _ (φ₁ or φ₂)) := sorry

/- If a formula φ is in dnf then (all n φ) is in dnf or has one bad connective -/
lemma dnf_all_dnf_phi_dnf_or_bc_eq_one : ∀ n : ℕ, dnf _ φ →
    ((dnf _ (formula.all n φ)) ∨ (dnf_bad_connectives _ (formula.all n φ) = 1)) := sorry

end formula

end first_order