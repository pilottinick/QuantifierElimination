import prf

namespace first_order

section formula

variables (L : language) (Γ : list (formula L)) (p q : formula L)

/- A formula is in dnf if and only if it is a disjunction of conjunctions of literals -/
-- def dnf_iff_disj_conj_lit : ∀ φ : formula L, dnf _ φ ↔ 

/- If a formula is equivalent to a formula in dnf -/
def equiv_dnf (φ : formula L) :=
        ∃ ψ : formula L, (dnf _ ψ) ∧ (Γ ▸ φ ↔ Γ ▸ ψ)

/- Converts any right rule into a equiv_dnf right rule -/
def Right_Rule_equiv_dnf : (Γ ▸ p → Γ ▸ q) → ((equiv_dnf _ Γ p) → (equiv_dnf _ Γ q)) := sorry

/- The number of connectives in the formula that break dnf rules -/
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

/- A dnf_prop is in dnf -/
def dnf_prop_dnf : ∀ φ : formula L, dnf_prop _ φ  → dnf _ φ := begin
  intros φ φdnf_prop,
  cases φ,
  repeat { unfold dnf },
  repeat { assumption },
  unfold dnf_prop at φdnf_prop,
  apply false.elim φdnf_prop,
end

/- An atomic formula is in dnf_prop -/
def atomic_dnf_prop : ∀ φ : formula L, atomic _ φ → dnf_prop _ φ := begin
  intros φ atom,
  cases φ,
  any_goals { by { unfold dnf_prop } },
  any_goals { by { unfold atomic at atom, apply false.elim atom } },
end

/- An atomic formula is dnf -/
def atomic_dnf : ∀ φ : formula L, atomic _ φ → dnf _ φ := begin
  intros φ atom,
  have φdnf_prop : dnf_prop _ φ := atomic_dnf_prop _ _ atom,
  apply dnf_prop_dnf _ _ φdnf_prop,
end

/- The negation of an atomic formula is in dnf_prop -/
def neg_atomic_dnf_prop : ∀ φ : formula L, atomic _ φ → dnf_prop _ ∼φ := begin
  intros φ natom,
  cases φ,
  any_goals { by { unfold dnf_prop } },
  any_goals { by { unfold atomic at natom, apply false.elim natom } },
end

/- The negation of an atomic formula is dnf -/
def neg_atomic_dnf : ∀ φ : formula L, atomic _ φ → dnf _ φ := begin
  intros φ natom,
  have φdnf_prop : dnf_prop _ φ := atomic_dnf_prop _ _ natom,
  apply dnf_prop_dnf _ _ φdnf_prop,
end

/- A literal is in dnf -/
def literal_dnf_prop : ∀ φ : formula L, literal _ φ → dnf_prop _ φ := begin
  intros φ lit,
  have h1 : ∃ ψ : formula L, (atomic _ ψ) ∧ (φ = ψ ∨ φ = ∼ψ) := 
    (literal_atomic_or_neg_atomic _ φ).mp lit,
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
  unfold dnf_prop,
  cases ψ,
  any_goals { by { unfold dnf_prop } },
  any_goals { by { unfold atomic at h3, apply false.elim h3 } },
end

/- If a formula has no bad connectives then the formula is already in dnf -/
def bc_eq_zero_dnf : ∀ (φ : formula L), (dnf_bad_connectives _ φ) = 0 → dnf _ φ := begin
  intro φ,
  contrapose,
  induction φ,
  intro h, unfold dnf_bad_connectives, simp, unfold dnf at h, unfold dnf_prop at h, apply h true.intro,
  intro h, unfold dnf_bad_connectives, simp, unfold dnf at h, unfold dnf_prop at h, apply h true.intro,
  intro h, unfold dnf_bad_connectives, simp, unfold dnf at h, unfold dnf_prop at h, apply h true.intro,
  have lem : ∀ x, ¬(x + 1) = 0 := nat.succ_ne_zero,
  repeat {  
    intros h1 h2,
    unfold dnf_bad_connectives at h2,
  },
  have c : dnf_bad_connectives L φ_ᾰ + 1 = 0 := sorry,
  contradiction,
  have c : dnf_bad_connectives L φ_ᾰ + dnf_bad_connectives L φ_ᾰ_1 + 1 = 0 := sorry,
  contradiction,
  have c : dnf_bad_connectives L φ_ᾰ_1 + 1 = 0 := sorry,
  contradiction,
end

/- If a formula is not in dnf, it has at least one connective -/
def ndnf_bc_ge_one : ∀ (φ : formula L), ¬(dnf _ φ) → (dnf_bad_connectives _ φ) > 0 := begin
  intros φ ndnf,
  have h1 : ¬(dnf _ φ) → ¬(dnf_bad_connectives _ φ) = 0 := begin contrapose!, apply bc_eq_zero_dnf end,
  have h2 : ¬(dnf_bad_connectives _ φ) = 0 := h1 ndnf,
  exact pos_iff_ne_zero.mpr (h1 ndnf),
end


/- If a formula is in dnf it is equivalent to a formula in dnf -/
lemma dnf_equiv_dnf : ∀ φ : formula L, dnf _ φ → equiv_dnf _ Γ φ := begin
  intros φ φdnf,
  unfold equiv_dnf,
  existsi φ,
  apply and.intro,
  apply φdnf,
  apply iff.intro,
  intro h, apply h,
  intro h, apply h,
end

/- If a formula ∼φ is in dnf then φ is atomic or disjunction of two negations of atomics -/
lemma not_dnf_phi_atomic_or_disj_of_neg_atomic : ∀ φ : formula L, dnf _ (∼φ) → 
                                    ((atomic _ φ) ∨ 
                                     (∃ φ₁ φ₂ : formula L, φ = (∼φ₁ or ∼φ₂) ∧ 
                                                           atomic _ φ₁ ∧ 
                                                           atomic _ φ₂)) := begin
  intros φ φdnf,
  unfold dnf at φdnf,
  cases φ,
  any_goals { by { apply or.intro_left, unfold atomic } },
  any_goals { by { unfold dnf_prop at φdnf, contradiction } },
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
lemma not_dnf_phi_dnf : ∀ φ : formula L, dnf _ ∼φ → dnf _ φ := begin
  intros φ φdnf,
  have atom_or_conj : (atomic _ φ) ∨
                      (∃ φ₁ φ₂ : formula L, φ = (∼φ₁ or ∼φ₂) ∧ 
                                                atomic _ φ₁ ∧ 
                                                atomic _ φ₂) := begin
      unfold dnf at φdnf,
      apply not_dnf_phi_atomic_or_disj_of_neg_atomic _ _ φdnf, 
    end,
  cases φ,
  any_goals { unfold first_order.dnf },
  any_goals { by { 
    unfold dnf at φdnf,
    unfold dnf_prop at φdnf,
    apply false.elim φdnf, 
    }
  },
  apply or.elim atom_or_conj,
  intro atom,
  unfold atomic at atom,
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
  unfold dnf_prop,
  unfold dnf_prop at nφ₁_dnf,
  unfold dnf_prop at nφ₂_dnf,
  apply and.intro nφ₁_dnf nφ₂_dnf,
end

/- If a formula ∼φ has one bad connective then φ is in dnf -/
lemma not_bc_eq_one_phi_dnf : ∀ φ : formula L, (dnf_bad_connectives _ ∼φ = 1) →
                                    dnf _ φ := begin
  intros φ bc,
  have h1 : ¬dnf L φ → ¬dnf L ( ∼ φ) := begin contrapose!, apply not_dnf_phi_dnf end,
  apply by_contra,
  intro ndnf,
  unfold dnf_bad_connectives at bc,
  have φbc : dnf_bad_connectives _ φ > 0 := by apply ndnf_bc_ge_one _ _ ndnf,
  have nφdnf : ¬(dnf _ ∼φ) := h1 ndnf,
  -- TODO: show contradiction on bc
  admit,
end

/- If a formula ∼∼φ has one bad connective then φ is in dnf -/
lemma not_not_bc_eq_one_phi_dnf : ∀ φ : formula L, (dnf_bad_connectives _ ∼∼φ = 1) →
                                      dnf _ φ := begin
  intros φ bc,
  have nφdnf : dnf _ ∼φ := not_bc_eq_one_phi_dnf _ (∼φ) bc,
  apply not_dnf_phi_dnf _ φ nφdnf,
end

/- If a formula (φ₁ and φ₂) is in dnf then φ₁ φ₂ are in dnf -/
lemma and_dnf_phi_dnf : ∀ φ₁ φ₂ : formula L, (dnf _ (φ₁ and φ₂)) →
                          (dnf _ φ₁) ∧ (dnf _ φ₂) := begin
  intros φ₁ φ₂ φ₁aφ₂dnf,
  unfold dnf at φ₁aφ₂dnf,
  unfold dnf_prop at φ₁aφ₂dnf,
  have φ₁atom : atomic _ φ₁ := neg_atomic_phi_atomic _ _ (and.elim_left φ₁aφ₂dnf),
  have φ₂atom : atomic _ φ₂ := neg_atomic_phi_atomic _ _ (and.elim_right φ₁aφ₂dnf),
  apply and.intro (atomic_dnf _ _ φ₁atom) (atomic_dnf _ _ φ₂atom),
end

/- If a formula (φ₁ and φ₂) has one bad connective then φ₁ φ₂ are in dnf -/
lemma and_bc_eq_one_phi_dnf : ∀ φ₁ φ₂ : formula L, (dnf_bad_connectives _ (φ₁ and φ₂) = 1) →
                              (dnf _ φ₁) ∧ (dnf _ φ₂) := begin
  intros φ₁ φ₂ bc,
  have φ₁em : dnf _ φ₁ ∨ ¬(dnf _ φ₁) := by apply em,
  have φ₂em : dnf _ φ₂ ∨ ¬(dnf _ φ₂) := by apply em,
  apply or.elim φ₁em,
  apply or.elim φ₂em,
  intros φ₂dnf φ₁dnf,
  apply and.intro φ₁dnf φ₂dnf,
  all_goals { 
    repeat {
      apply or.elimφ₂em
      <|>
      apply and.intro φ₁dnf φ₂dnf,
      intros φ₂dnf φ₁dnf,
      unfold dnf_bad_connectives at bc
      -- TODO: show contradiction on bc 
    } 
  },
  repeat { admit },
end                      

/- If a formula (φ₁ or φ₂) is in dnf then φ₁ φ₂ are in dnf -/
lemma or_dnf_phi_dnf : ∀ φ₁ φ₂ : formula L, (dnf _ (φ₁ or φ₂)) →
                        (dnf _ φ₁) ∧ (dnf _ φ₂) := begin
  intros φ₁ φ₂ φ₁oφ₂dnf,
  unfold dnf at φ₁oφ₂dnf,
  unfold dnf_prop at φ₁oφ₂dnf,
  have φ₁dnf_prop : dnf_prop _ φ₁ := and.elim_left φ₁oφ₂dnf,
  have φ₂dnf_prop : dnf_prop _ φ₂ := and.elim_right φ₁oφ₂dnf,
  apply and.intro (dnf_prop_dnf _ _ φ₁dnf_prop) (dnf_prop_dnf _ _ φ₂dnf_prop),
end

/- If a formula (φ₁ or φ₂) has one bad connective then φ₁ φ₂ are in dnf -/
lemma or_bc_eq_one_phi_dnf : ∀ φ₁ φ₂ : formula L, (dnf_bad_connectives _ (φ₁ or φ₂) = 1) →
                              (dnf _ φ₁) ∧ (dnf _ φ₂) := begin
  intros φ₁ φ₂ bc,
  have φ₁em : dnf _ φ₁ ∨ ¬(dnf _ φ₁) := by apply em,
  have φ₂em : dnf _ φ₂ ∨ ¬(dnf _ φ₂) := by apply em,
  apply or.elim φ₁em,
  apply or.elim φ₂em,
  intros φ₂dnf φ₁dnf,
  apply and.intro φ₁dnf φ₂dnf,
  all_goals { 
    repeat {
      apply or.elimφ₂em
      <|>
      apply and.intro φ₁dnf φ₂dnf,
      intros φ₂dnf φ₁dnf,
      unfold dnf_bad_connectives at bc
      -- TODO: show contradiction on bc 
    } 
  },
  repeat { admit },
end 

/- If a formula (all n φ) is in dnf then φ is in dnf -/
lemma all_dnf_phi_dnf : ∀ φ : formula L, ∀ n : ℕ, (dnf _ (formula.all n φ)) → (dnf _ φ) := sorry

/- If a formula (all n φ) has one bad connective then φ is in dnf -/
lemma all_bc_eq_one_phi_dnf : ∀ φ : formula L, ∀ n : ℕ, (dnf_bad_connectives _ (formula.all n φ)) = 1 → 
                                (dnf _ φ) := sorry

/- If a formula is in dnf it has no bad connectives -/
lemma dnf_bc_eq_zero : ∀ φ : formula L, dnf _ φ → dnf_bad_connectives _ φ = 0 := begin
  intros φ φdnf,
  induction φ,
  any_goals { unfold dnf_bad_connectives },
  simp,
  apply and.intro,
  have h : dnf _ φ_ᾰ := not_dnf_phi_dnf _ _ φdnf,
  apply φ_ih h,
  intro h, contradiction,
  simp,
  apply and.intro,
  have h : dnf _ φ_ᾰ ∧ dnf _ φ_ᾰ_1 := or_dnf_phi_dnf _ _ _ φdnf,
  apply and.intro,
  have h1 : dnf _ φ_ᾰ := h.left,
  apply φ_ih_ᾰ h1,
  have h2 : dnf _ φ_ᾰ_1 := h.right,
  apply φ_ih_ᾰ_1 h2,
  intro h, contradiction,
  simp,
  apply and.intro,
  have h : dnf L φ_ᾰ_1 := all_dnf_phi_dnf _ _ _ φdnf,
  apply φ_ih h,
  intro h, contradiction,
end

/- If a formula φ is in dnf then ∼φ is in dnf or has one bad connective -/
lemma dnf_not_dnf_or_bc_eq_one : ∀ φ : formula L, dnf _ φ → ((dnf _ ∼φ) ∨ (dnf_bad_connectives _ ∼φ) = 1) := begin
  intros φ h, 
  have dnf_or_ndnf : (dnf _ (∼φ)) ∨ ¬(dnf _ (∼φ)) := by apply em,
  apply or.elim dnf_or_ndnf,
  intro dnf,
  apply or.intro_left,
  apply dnf,
  intro dnf,
  apply or.intro_right,
  unfold dnf_bad_connectives,
  unfold ite,
  have bc : dnf_bad_connectives L φ = 0 := dnf_bc_eq_zero _ _ h,
  rw bc,
  ring_nf,
  -- TODO: How do I apply dnf to simplify decidable.rec?
  admit,
end

/- If formulas φ₁ φ₂ are in dnf then (φ₁ and φ₂) is in dnf or has one bad connective -/
lemma dnf_and_dnf_or_bc_eq_one : ∀ φ₁ φ₂ : formula L, dnf _ φ₁ → dnf _ φ₂ →
                                  ((dnf _ (φ₁ and φ₂)) ∨ (dnf_bad_connectives _ (φ₁ and φ₂) = 1)) := sorry

/- If formulas φ₁ φ₂ are in dnf then (φ₁ or φ₂) is in dnf or has one bad connective -/
lemma dnf_or_dnf_or_bc_eq_one : ∀ φ₁ φ₂ : formula L, dnf _ φ₁ → dnf _ φ₂ →
                                  ((dnf _ (φ₁ or φ₂)) ∨ (dnf_bad_connectives _ (φ₁ or φ₂) = 1)) := sorry

/- If a formula φ is in dnf then (all n φ) is in dnf or has one bad connective -/
lemma dnf_all_dnf_or_bc_eq_one : ∀ φ : formula L, ∀ n : ℕ, dnf _ φ →
                                  ((dnf _ (formula.all n φ)) ∨ (dnf_bad_connectives _ (formula.all n φ) = 1)) := sorry

/- And case of dnf with one bad connective -/
lemma and_bc_eq_one_equiv_dnf : ∀ φ₁ φ₂ : formula L, (dnf_bad_connectives _ (φ₁ and φ₂) = 1) →
                                  equiv_dnf _ Γ (φ₁ and φ₂) := begin
  intros φ₁ φ₂ bc,
  have φ₁φ₂dnf : dnf _ φ₁ ∧ dnf _ φ₂ := and_bc_eq_one_phi_dnf _ φ₁ φ₂ bc,
  have φ₁dnf : dnf _ φ₁ := φ₁φ₂dnf.left,
  have φ₂dnf : dnf _ φ₂ := φ₁φ₂dnf.right,
  induction φ₁,
  all_goals { induction φ₂ },
  any_goals { 
    by { 
      apply dnf_equiv_dnf, 
      unfold dnf, 
      unfold dnf_prop, 
      unfold neg_atomic, 
      unfold atomic, 
      simp } 
  },
  
end

/- Not case of dnf with one bad connective -/
lemma not_bc_eq_one_equiv_dnf : ∀ φ : formula L, (dnf_bad_connectives _ ∼φ = 1) →
                                equiv_dnf _ Γ ∼φ := begin
  intros φ bc,
  have φdnf : dnf _ φ := not_bc_eq_one_phi_dnf _ φ bc,
  induction φ,
  any_goals { by { apply dnf_equiv_dnf, unfold dnf } },
  rename φ_ᾰ φ,
  have φdnf : dnf _ φ := not_not_bc_eq_one_phi_dnf _ φ bc,
  apply Right_Rule_equiv_dnf _ _ _ _ Double_negation_intro_R,
  apply dnf_equiv_dnf _ Γ φ φdnf,
  rename φ_ᾰ φ₁, rename φ_ᾰ_1 φ₂,
  have φ₁φ₂dnf : dnf _ φ₁ ∧ dnf _ φ₂ := or_dnf_phi_dnf _ φ₁ φ₂ φdnf,
  have φ₁dnf : dnf _ φ₁ := φ₁φ₂dnf.left,
  have φ₂dnf : dnf _ φ₂ := φ₁φ₂dnf.right,
  apply Right_Rule_equiv_dnf,
  apply DeMorganAnd_R,
  have nφ₁dnf_or_bc_eq_one : dnf _ (∼φ₁) ∨ dnf_bad_connectives _ (∼φ₁) = 1 := begin 
      apply dnf_not_dnf_or_bc_eq_one, apply φ₁dnf 
    end,
  have nφ₂dnf_or_bc_eq_one : dnf _ (∼φ₂) ∨ dnf_bad_connectives _ (∼φ₂) = 1 := begin 
      apply dnf_not_dnf_or_bc_eq_one, apply φ₂dnf 
    end,
  have nφ₁equiv_dnf : equiv_dnf _ Γ (∼φ₁) := begin
      apply or.elim nφ₁dnf_or_bc_eq_one,
      intro left,
      apply dnf_equiv_dnf _ Γ (∼φ₁) left,
      intro right,
      apply φ_ih_ᾰ right φ₁dnf,
    end,
  have nφ₂equiv_dnf : equiv_dnf _ Γ (∼φ₂) := begin
      apply or.elim nφ₂dnf_or_bc_eq_one,
      intro left,
      apply dnf_equiv_dnf _ Γ (∼φ₂) left,
      intro right,
      apply φ_ih_ᾰ_1 right φ₂dnf,
    end,
    have nφ₁anφ₂bc_eq_one : dnf_bad_connectives _ (∼φ₁ and ∼φ₂) = 1 := sorry,
    apply and_bc_eq_one_equiv_dnf,
    apply nφ₁anφ₂bc_eq_one,
    -- TODO: All case
    admit,
end

/- Or case of dnf with one bad connective -/
lemma or_bc_eq_one_equiv_dnf : ∀ φ₁ φ₂ : formula L, dnf_bad_connectives _ (φ₁ or φ₂) = 1 →
                                equiv_dnf _ Γ (φ₁ or φ₂) := begin
  intros φ₁ φ₂ bc,
  have φ₁φ₂dnf : dnf _ φ₁ ∧ dnf _ φ₂ := or_bc_eq_one_phi_dnf _ _ _ bc,
  cases φ₁,
  all_goals { cases φ₂ },
  repeat {
    apply dnf_equiv_dnf,
    unfold dnf,
    unfold dnf_prop,
    apply φ₁φ₂dnf,
  },
  -- TODO: All cases
  all_goals { admit },
end

/- All case of dnf with one bad connective -/
lemma all_bc_eq_one_equiv_dnf : ∀ φ : formula L, ∀ n : ℕ, dnf_bad_connectives _ (formula.all n φ) = 1 →
                                  equiv_dnf _ Γ (formula.all n φ) := sorry

theorem for_all_equiv_dnf :  ∀ φ : formula L, equiv_dnf _ Γ φ := begin
  intro φ,
  have h : ∃ n, dnf_bad_connectives _ φ = n := begin existsi dnf_bad_connectives _ φ, refl, end,
  apply exists.elim h,
  intros n nh,
  induction n,
  -- Case 1: No bad connectives
  apply dnf_equiv_dnf _ Γ φ,
  apply bc_eq_zero_dnf _ φ nh,
  induction n_n,
  -- Case 2: Exactly one bad connective, induct on φ
  induction φ,
  -- The first three cases are the same
  -- Case 2a : Trivial cases
  any_goals { by { apply dnf_equiv_dnf, unfold dnf } },
  -- Case 2b : Not case
  apply not_bc_eq_one_equiv_dnf, apply nh,
  -- Case 2c : Or case
  apply or_bc_eq_one_equiv_dnf, apply nh,
  -- Case 2d : All case
  apply all_bc_eq_one_equiv_dnf, apply nh,
  -- Case 3 : Inductive step: more than one bad connective
  induction φ,
  -- Case 3a : Trivial cases
  any_goals { by { apply dnf_equiv_dnf, unfold dnf } },
  -- Case 3b : Not case
  admit,
  -- Case 3c : Or case
  admit,
  -- Case 3d : All case
  admit,
end

end formula

end first_order