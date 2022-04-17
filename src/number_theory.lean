import quantifier_elimination
import data.nat.basic

namespace number_theory

open first_order

variable {L : language}

section NT_succ

/- The functions of number theory with successor -/
inductive NT_succ_func : ℕ → Type
| zero : NT_succ_func 0
| succ : NT_succ_func 1

/- The relations of number theory with successor -/
inductive NT_succ_rel : ℕ → Type

/- The language of number theory with successor -/
def NT_succ : language :=
  ⟨NT_succ_func, NT_succ_rel⟩

notation ` zero `  := @term.func NT_succ _ NT_succ_func.zero ![]
notation ` zero' `x := @term.func NT_succ _ NT_succ_func.zero x
notation ` succ `x := @term.func NT_succ _ NT_succ_func.succ ![x]
notation ` succ' `x := @term.func NT_succ _ NT_succ_func.succ x

@[simp]
def nth_succ (t : term NT_succ) : ℕ → term NT_succ
| 0            := t
| (nat.succ n) := succ' (λ _, nth_succ n)

/- The axioms of number theory with successor -/
inductive NT_succ_Γ
| eq1 : NT_succ_Γ
| eq2 : NT_succ_Γ
| ax1 : NT_succ_Γ
| ax2 : NT_succ_Γ
| ax3 : ℕ → NT_succ_Γ

open NT_succ_Γ

def NT_succ_Γ_to_formula : NT_succ_Γ → formula (NT_succ)
-- Equality is reflexive
| eq1     := formula.all 0 (v₀ ≃ v₀)
-- Functional extensionality
| eq2     := formula.all 0 (formula.all 1 (v₀ ≃ v₁ ⇒ (succ v₀) ≃ (succ v₁)))
-- Zero does not have a predecessor
| ax1     := formula.all 0 ∼((succ v₀) ≃ zero)
-- Successor is injective
| ax2     := formula.all 0 (formula.all 1 ((((succ v₀) ≃ (succ v₁)) ⇒ (v₀ ≃ v₁))))
-- There are no loops
| (ax3 n) := formula.all 0 ∼(nth_succ v₀ n ≃ v₀)

instance NT_succ_Γ_to_formula_NT_succ : has_coe NT_succ_Γ (formula NT_succ) := ⟨NT_succ_Γ_to_formula⟩

variables (φ : formula NT_succ) (t : term NT_succ)

lemma var_not_free_in_NT_succ_Γ : ∀ x : ℕ, @var_not_free_in_axioms NT_succ x NT_succ_Γ _ := sorry

-- Helpful lemmas
lemma rw_ite_P {α : Type*} (a b : α) (P : Prop) [decidable P] : P → ite P a b = a := sorry

lemma rw_ite_nP {α : Type*} (a b : α) (P : Prop) [decidable P]: ¬P → ite P a b = b := sorry

lemma fin_0_eq {α : Type*} (f g : fin 0 → α) : f = g := begin
  apply funext, intro x, rcases x with ⟨y, hy⟩, apply absurd hy (nat.not_lt_zero y),
end

lemma reflexive (Γ : list (formula NT_succ)) : ∀ t : term NT_succ, NT_succ_Γ ∣ Γ ⊢ t ≃ t := sorry

lemma symmetric (Γ : list (formula NT_succ)) : ∀ t₁ t₂ : term NT_succ, 
  (NT_succ_Γ ∣ Γ ⊢ (t₁ ≃ t₂)) → (NT_succ_Γ ∣ Γ ⊢ (t₂ ≃ t₁)) := sorry

lemma ax1 (Γ : list (formula NT_succ)) (arg1 : fin 1 → term NT_succ) (arg2 : fin 0 → term NT_succ) : 
  NT_succ_Γ ∣ Γ ⊢ ∼((succ' arg1) ≃ (zero' arg2)) := sorry

lemma ax2 (Γ : list (formula NT_succ)) (t₁ t₂ : term NT_succ) : 
  NT_succ_Γ ∣ Γ ⊢ ((succ t₁) ≃ (succ t₂)) ⇒ (t₁ ≃ t₂) := sorry

lemma ax3 (Γ : list (formula NT_succ)) (t : term NT_succ) (n : ℕ) :
  NT_succ_Γ ∣ Γ ⊢ ∼(nth_succ t n ≃ t) := sorry

/- A function that converts a formula of the form t₁ ≃ t₂ to an equivalent quantifier free formula -/
@[simp]
def ex_t₁_eq_t₂_to_qf (n : ℕ) : term NT_succ → term NT_succ → qf NT_succ
-- vᵢ ≃ vⱼ
| (v m₁) (v m₂) := if n = m₁ then qf.n qf.f else (if n = m₂ then qf.n qf.f else qf.e (v m₁) (v m₂))
-- vᵢ ≃ 0
| (v m₁) (term.func NT_succ_func.zero arg) := if n = m₁ then qf.n qf.f else qf.e (v m₁) (zero' arg)
-- 0 ≃ vᵢ
| (term.func NT_succ_func.zero arg) (v m₂) := if n = m₂ then qf.n qf.f else qf.e (zero' arg) (v m₂)
/- ... -/
-- vᵢ ≃ succ y
| (v m₁) (term.func NT_succ_func.succ t₂) := 
  if n = m₁ then 
    (if occurs_in_term n (@term.func NT_succ _ NT_succ_func.succ t₂) then qf.f else qf.n qf.f) else
    (if occurs_in_term n (@term.func NT_succ _ NT_succ_func.succ t₂) then qf.f else qf.e (v m₁) (@term.func NT_succ _ NT_succ_func.succ t₂))
-- succ x ≃ vⱼ
| (term.func NT_succ_func.succ t₁) (v m₂) := qf.f
-- 0 ≃ 0
| (term.func NT_succ_func.zero _) (term.func NT_succ_func.zero _) := qf.n qf.f
-- succ x ≃ 0
| (term.func NT_succ_func.succ t₁) (term.func NT_succ_func.zero _) := qf.f
-- 0 ≃ succ y
| (term.func NT_succ_func.zero _) (term.func NT_succ_func.succ t₂) := qf.f
-- succ x ≃ succ y
| (term.func NT_succ_func.succ t₁) (term.func NT_succ_func.succ t₂) := ex_t₁_eq_t₂_to_qf (t₁ 0) (t₂ 0)

def not_occurs_in_zero (n : ℕ) (args : fin 0 → term NT_succ) : ¬(@occurs_in_term NT_succ n (term.func NT_succ_func.zero args)) := begin
  simp, intro x, rcases x with ⟨n, hn⟩,
  apply false.elim (nat.not_lt_zero n hn)
end

lemma qe_ex_n_n_eq_t₂ (n : ℕ) (t₂ : term NT_succ) : ¬(occurs_in_term n t₂) →
  ((NT_succ_Γ ∣ [] ⊢ (exi n ((v n) ≃ t₂))) ↔ (@Prf NT_succ NT_succ_Γ _ list.nil T)) := begin
  intro h1, split,
  { intro h2, apply Top_intro },
  { simp, intro h2,
    apply Ex_intro n t₂ _,
    simp,
    rw replace_term_with_does_not_occur _ _ _ _ h1,
    apply reflexive,
  }
end 

lemma qe_ex_n_t₁_eq_n (n : ℕ) (t₁ : term NT_succ) : ¬(occurs_in_term n t₁) →
  ((NT_succ_Γ ∣ [] ⊢ (exi n (t₁ ≃ (v n)))) ↔ (@Prf NT_succ NT_succ_Γ _ list.nil T)) := begin
  intro h1, split,
  { intro h2, apply Top_intro },
  { simp, intro h2,
    apply Ex_intro n t₁ _,
    simp,
    rw replace_term_with_does_not_occur _ _ _ _ h1,
    apply reflexive,
  }
end

lemma qe_ex_n_t₁_eq_t₂ (n : ℕ) (t₁ t₂ : term NT_succ) : ¬(occurs_in_term n t₁) → ¬(occurs_in_term n t₂) → 
  (@Prf NT_succ NT_succ_Γ _ list.nil (exi n (t₁ ≃ t₂)) ↔ @Prf NT_succ NT_succ_Γ _ list.nil (t₁ ≃ t₂)) := begin
  intros ht₁ ht₂,
  split,
  { intro h1,
    apply Ex_elim n v₀ _ (t₁ ≃ t₂), 
    have h2 : substitutable_for v₀ n (t₁ ≃ t₂) := sorry,
    apply h2,
    apply h1,
    unfold replace_formula_with,
    rw replace_term_with_does_not_occur _ n _ t₂ ht₂,
    apply Prf.Assumption 0, simp,
    apply replace_term_with_does_not_occur,
    apply ht₁,
  },
  { intro h1,
    apply Ex_intro n v₀,
    unfold replace_formula_with,
    rw replace_term_with_does_not_occur _ n _ t₁ ht₁,
    rw replace_term_with_does_not_occur _ n _ t₂ ht₂,
    assumption,
  }
end

lemma qe_ex_n_vi_eq_succ (n m : ℕ) (x : fin 1 → term NT_succ) : 
  (NT_succ_Γ ∣ [] ⊢ exi n ((v m) ≃ succ' x)) ↔
  (@Prf NT_succ NT_succ_Γ _ list.nil ↑(ex_t₁_eq_t₂_to_qf n (v m) (succ' x))) := begin
  have x' := x 0,
  have h : (succ' x) = (succ x') := sorry,
  unfold ex_t₁_eq_t₂_to_qf,
  have h_occurs : (occurs_in_term n (succ' x)) ∨ ¬(occurs_in_term n (succ' x)) := by apply em,
  have m_eq : (m = n) ∨ (m ≠ n) := by apply em,
  apply or.elim h_occurs,
  all_goals { apply or.elim m_eq },
  all_goals { intro t₁eq', intro h_occurs' },
  { rw rw_ite_P _ _ _ (h_occurs'),
    rw t₁eq', simp,
    rw h,
    cases x',
    have x'eq : (x' = n) ∨ (x' ≠ n) := by apply em,
    apply or.elim x'eq,
    intro x'eq', rw x'eq',
    split,
    { intro h1,
      apply Ex_elim n (v n) _ F,
      have h2 : substitutable_for (v n) n (v n ≃ @term.func NT_succ _ NT_succ_func.succ ![v n]) := sorry,
      apply h2, apply h1,
      simp,
      apply Absurd,
      apply Prf.Assumption 0, refl,
      apply R_Not_ (symmetric _ _ _),
      apply ax3 _ (v n) 1,
    },
    { apply Prf.Bot_elim, },
    intro x'eq,
    have : ¬(occurs_in_term n (@term.func NT_succ _ NT_succ_func.succ x)) := sorry,
    contradiction,
    cases x'_ᾰ,
    {
      sorry
    },
    {
      sorry
    }
  },
  { rw rw_ite_P _ _ _ (h_occurs'),
    rw rw_ite_nP _ _ _ (ne.symm t₁eq'),
    sorry,
  },
  { rw rw_ite_nP _ _ _ (h_occurs'),
    rw t₁eq', simp,
    apply qe_ex_n_n_eq_t₂,
    assumption,
  },
  { rw rw_ite_nP _ _ _ (ne.symm t₁eq'),
    rw rw_ite_nP _ _ _ (h_occurs'),
    apply qe_ex_n_t₁_eq_t₂,
    simp, exact ne.symm t₁eq',
    assumption,
  }
end

lemma qe_ex_n_succ_eq_vj (n m : ℕ) (x : fin 1 → term NT_succ) : 
  (NT_succ_Γ ∣ [] ⊢ exi n ((succ' x) ≃ (v m))) ↔
  (@Prf NT_succ NT_succ_Γ _ list.nil ↑(ex_t₁_eq_t₂_to_qf n (succ' x) (v m))) := sorry

lemma qe_ex_t₁_eq_t₂ (n : ℕ) (t₁ t₂ : term NT_succ) : equiv_qf NT_succ_Γ (exi n (t₁ ≃ t₂)) := begin
  existsi (ex_t₁_eq_t₂_to_qf n t₁ t₂),
  induction t₁, cases t₂,
  -- Case: vᵢ ≃ vⱼ
  { have t₁eq : (n = t₁) ∨ (n ≠ t₁) := by apply em,
    have t₂eq : (n = t₂) ∨ (n ≠ t₂) := by apply em,
    cases t₁eq,
    all_goals { cases t₂eq },
    -- n = t₁, n = t₂
    { rw ← t₁eq, rw ← t₂eq,
      split,
      intro h1, simp, apply Top_intro,
      intro h1, simp, apply Ex_intro n (v 0) _, simp, apply reflexive,
    },
    -- n = t₁, n ≠ t₂ 
    { rw ← t₁eq, simp,
      apply qe_ex_n_n_eq_t₂,
      simp, assumption,
    },
    -- n ≠ t₁, n = t₂
    { rw ← t₂eq, simp,
      apply qe_ex_n_t₁_eq_n,
      simp, assumption,
    },
    -- n ≠ t₁, n ≠ t₂
    { have h : (v t₁ ≃ v t₂) = ((ex_t₁_eq_t₂_to_qf n (v t₁) (v t₂)) : formula NT_succ) := begin
        simp, repeat { rw rw_ite_nP _ _ _ }, refl, repeat { assumption },
      end, rw ← h,
      apply qe_ex_n_t₁_eq_t₂,
      repeat { simp, assumption },
    },
  },
  { cases t₂_n, cases t₂_ᾰ,
    -- Case: vᵢ ≃ zero
    { simp,
      have t₁eq : (t₁ = n) ∨ (t₁ ≠ n) := by apply em,
      apply or.elim t₁eq,
      intro t₁eq', rw t₁eq', simp,
      apply qe_ex_n_n_eq_t₂,
      apply not_occurs_in_zero,
      intro t₁eq', rw rw_ite_nP _ _ _ (ne.symm t₁eq'),
      apply qe_ex_n_t₁_eq_t₂,
      simp, apply (ne.symm t₁eq'),
      apply not_occurs_in_zero,
    },
    cases t₂_ᾰ,
    -- Case: vᵢ ≃ succ x
    { apply qe_ex_n_vi_eq_succ }
  },
  cases t₁_ᾰ, 
  all_goals { cases t₂ }, 
  any_goals { cases t₂_ᾰ },
  -- Case: zero ≃ vⱼ
  { simp,
    have t₂eq : (t₂ = n) ∨ (t₂ ≠ n) := by apply em,
    apply or.elim t₂eq,
    intro t₂eq', rw t₂eq', simp,
    apply qe_ex_n_t₁_eq_n,
    apply not_occurs_in_zero,
    intro t₂eq', rw rw_ite_nP _ _ _ (ne.symm t₂eq'),
    apply qe_ex_n_t₁_eq_t₂,
    apply not_occurs_in_zero, 
    simp, apply (ne.symm t₂eq'),
  },
  -- Case: zero ≃ zero
  { simp, split,
    { intro h1, apply Top_intro },
    { intro h1, apply Ex_intro _ v₀,
      unfold replace_formula_with, 
      repeat { rw replace_term_with_does_not_occur },
      rw fin_0_eq t₁_ᾰ_1 t₂_ᾰ_1,
      apply reflexive,
      repeat { apply not_occurs_in_zero _ _ },
    }
  },
  -- Case: zero ≃ succ y
  { simp, split,
    { intro h1,
      have h2 : ∃ m : ℕ, ¬(free m ((zero' t₁_ᾰ_1) ≃ (succ' t₂_ᾰ_1))) := by apply for_all_formula_ex_var_not_free,
      rcases h2 with ⟨m, hm⟩,
      unfold free at hm, 
      have hm' : ¬(occurs_in_term m (zero' t₁_ᾰ_1)) ∧ ¬(occurs_in_term m (succ' t₂_ᾰ_1)) := not_or_distrib.mp hm,
      apply Ex_elim m (v 0) ((zero' t₁_ᾰ_1) ≃ (succ' t₂_ᾰ_1)),
      simp, apply (Ex_rename n m _ h1),
      apply Absurd,
      apply Prf.Assumption 0, refl,
      unfold replace_formula_with,
      repeat { rw replace_term_with_does_not_occur },
      apply R_Not_ (symmetric _ _ _),
      apply ax1,
      apply hm'.right, apply hm'.left,
    },
    { apply Prf.Bot_elim, }
  },
  -- Case: succ x ≃ vⱼ
  { apply qe_ex_n_succ_eq_vj },
  -- Case: succ x ≃ zero
  { simp, split,
    { intro h1,
      have h2 : ∃ m : ℕ, ¬(free m ((succ' t₁_ᾰ_1) ≃ (zero' t₂_ᾰ_1))) := by apply for_all_formula_ex_var_not_free,
      rcases h2 with ⟨m, hm⟩,
      unfold free at hm, 
      have hm' : ¬(occurs_in_term m (succ' t₁_ᾰ_1)) ∧ ¬(occurs_in_term m (zero' t₂_ᾰ_1)) := not_or_distrib.mp hm,
      apply Ex_elim m (v 0) ((succ' t₁_ᾰ_1) ≃ (zero' t₂_ᾰ_1)),
      simp, apply (Ex_rename n m _ h1),
      apply Absurd,
      apply Prf.Assumption 0, refl,
      unfold replace_formula_with,
      repeat { rw replace_term_with_does_not_occur },
      apply ax1,
      apply hm'.right, apply hm'.left,
    },
    { apply Prf.Bot_elim, } 
  },
  -- Case succ x ≃ succ y
  { sorry, },
end

lemma NT_succ_qe_ecl1 : @qe_ecl1 NT_succ NT_succ_Γ _ := begin
  intro φ,
  induction φ,
  { existsi (φ : qf NT_succ), refl, },
  { cases φ_ᾰ_1, cases φ_ᾰ_1, cases φ_ᾰ_1,
    { have h_free : ¬(@free NT_succ φ_ᾰ F) := by { intro, assumption, },
      apply Eq_equiv_qf ⟨AddEx, RemoveEx h_free⟩,
      existsi qf.f, refl,
    },
    { apply qe_ex_t₁_eq_t₂, },
    { cases φ_ᾰ_1_ᾰ, },
    cases φ_ᾰ_1,
    { have h_free : ¬(@free NT_succ φ_ᾰ ∼F) := by { intro c, apply c, },
      apply Eq_equiv_qf ⟨AddEx, RemoveEx h_free⟩,
      existsi qf.n qf.f, refl,
    },
    { have h_free₁ : 
      (occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ) ∨ ¬(occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ) := 
        by apply em,
      have h_free₂ : (occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ_1) ∨ ¬(occurs_in_term φ_ᾰ φ_ᾰ_1_ᾰ_1) := 
        by apply em,
      apply or.elim h_free₁,
      all_goals { apply or.elim h_free₂ },
      repeat { sorry },
    },
    { cases φ_ᾰ_1_ᾰ, },
    { sorry },
  }
end

/- NT_succ has quantifier elimination -/
theorem NT_succ_qe : @qe NT_succ NT_succ_Γ _ := sorry

end NT_succ

end number_theory