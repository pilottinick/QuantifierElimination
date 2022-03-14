import dnf

namespace first_order

section quantifier_elimination

variables {L : language} (Γ : ℕ → (formula L)) {φ φ₁ φ₂ ψ : formula L} {p q : formula L}

/- If a formula φ has has quantifier elimination in a theory -/
@[simp]
def equiv_qf (φ : formula L) := ∃ ψ : qf L, Γ ▸ φ ↔ Γ ▸ ψ

def Equiv_Rule_To_equiv_qf_Rule {Γ : ℕ → (formula L)} : (Γ ▸ p ↔ Γ ▸ q) → (equiv_qf Γ p → equiv_qf Γ q) := begin
   intros h₁ h₂,
   rcases h₂ with ⟨φ₃, h₃⟩,
   existsi φ₃,
   split,
   intro h₄,
   apply h₃.mp (h₁.mpr h₄),
   intro h₄,
   apply h₁.mp (h₃.mpr h₄),
end

/- If a theory Γ has quantifier elimination -/
@[simp]
def qe := ∀ (φ : formula L), equiv_qf Γ φ

/- If a theory Γ has quantifier elimination on conjunctions of literals with
   with a single existential quantifier -/
def qe_ecl1 := ∀ (φ : ecl1 L), equiv_qf Γ φ

/- If a theory Γ has quantifier elimination on disjunctions of conjunctions
   of literals with a single existential quantifier -/
def qe_edcl1 := ∀ (φ : edcl1 L), equiv_qf Γ φ

/- If a theory Γ has quantifier elimination on disjunctions of conjugations 
   of literals with a single quantifier -/
@[simp]
def qe_qdcl1 := ∀ (φ : qdcl1 L), equiv_qf Γ φ

@[simp]
def qe_dnf := ∀ (φ : dnf L), equiv_qf Γ φ

/- If a theory Γ has quantifier elimination on quantifier free formulas -/
@[simp]
def qe_qf := ∀ (φ : qf L), equiv_qf Γ φ

/- All theories have quantifier elimination on quantifier free formulas -/
def for_all_qe_qf : qe_qf Γ := by { intros φ, existsi φ, refl }

/- If a theory has quantifier elimination on φ₁ φ₂ then it has quantifier 
   elimination on (φ₁ or φ₂) -/
lemma equiv_qf_or_equiv_qf : equiv_qf Γ φ₁ → equiv_qf Γ φ₂ → equiv_qf Γ (φ₁ or φ₂) := begin
   intros h_φ₁ h_φ₂,
   rcases h_φ₁ with ⟨φ₁', h₁⟩,
   rcases h_φ₂ with ⟨φ₂', h₂⟩,
   apply Equiv_Rule_To_equiv_qf_Rule (Equiv_Rule_To_Or_Rule_R ⟨h₁.mpr, h₁.mp⟩ ⟨h₂.mpr, h₂.mp⟩),
   existsi (qf.o φ₁' φ₂'), refl,
end

lemma qe_ecl1_qe_edcl1 : (qe_ecl1 Γ) → (qe_edcl1 Γ) := begin
   intros h₁ φ,
   cases φ,
   {  existsi (φ : qf L), refl, },
   {  induction φ_ᾰ_1,
      rcases (h₁ (ecl1.ex φ_ᾰ φ_ᾰ_1)) with ⟨φ₂, h₂⟩,
      apply Equiv_Rule_To_equiv_qf_Rule ⟨h₂.mpr, h₂.mp⟩,
      existsi φ₂, refl,
      rcases φ_ᾰ_1_ih_ᾰ with ⟨φ₂, h₂⟩,
      rcases φ_ᾰ_1_ih_ᾰ_1 with ⟨φ₃, h₃⟩,
      apply Equiv_Rule_To_equiv_qf_Rule ⟨ExOrOut_R, ExOrIn_R⟩,
      apply Equiv_Rule_To_equiv_qf_Rule (Equiv_Rule_To_Or_Rule_R ⟨h₂.mpr, h₂.mp⟩ ⟨h₃.mpr, h₃.mp⟩),
      existsi qf.o φ₂ φ₃, refl,
   },
end

lemma qe_edcl1_qe_qdcl1 : (qe_edcl1 Γ) → (qe_qdcl1 Γ) := begin
   intros h₁ φ,
   induction φ,
   {  existsi (φ : qf L), refl, },
   { 
      rcases (qf_equiv_dcl Γ (qf.n φ_ᾰ_1)) with ⟨φ₂, h₂⟩,
      apply Equiv_Rule_To_equiv_qf_Rule ⟨Ex_To_All_R, All_To_Ex_R⟩,
      apply Equiv_Rule_To_equiv_qf_Rule 
         (Equiv_Rule_To_Not_Rule_R (Equiv_Rule_To_Ex_Rule_R ⟨h₂.mpr, h₂.mp⟩)),
      rcases (h₁ (edcl1.ex φ_ᾰ φ₂)) with ⟨φ₃, h₃⟩,
      apply Equiv_Rule_To_equiv_qf_Rule (Equiv_Rule_To_Not_Rule_R ⟨h₃.mpr, h₃.mp⟩),
      existsi (qf.n φ₃), refl,
   },
   {  rcases (h₁ (edcl1.ex φ_ᾰ φ_ᾰ_1)) with ⟨φ₂, h₂⟩,
      apply Equiv_Rule_To_equiv_qf_Rule ⟨h₂.mpr, h₂.mp⟩,
      existsi φ₂, refl,
   }
end

lemma qe_qdcl1_qe_dnf : (qe_qdcl1 Γ) → (qe_dnf Γ) := begin
   intros h₁ φ₁,
   induction φ₁,
   {  existsi (φ₁ : qf L), refl, },
   {  cases φ₁_ᾰ_1,
      {  rcases (h₁ (qdcl1.al φ₁_ᾰ φ₁_ᾰ_1)) with ⟨φ₂, h₂⟩,
         apply Equiv_Rule_To_equiv_qf_Rule ⟨h₂.mpr, h₂.mp⟩,
         existsi φ₂, refl, },
      all_goals {  rcases φ₁_ih with ⟨φ₂, h₂⟩,
         apply Equiv_Rule_To_equiv_qf_Rule (Equiv_Rule_To_All_Rule_R ⟨h₂.mpr, h₂.mp⟩),
         rcases (qf_equiv_dcl Γ φ₂) with ⟨φ₃, h₃⟩,
         apply Equiv_Rule_To_equiv_qf_Rule (Equiv_Rule_To_All_Rule_R ⟨h₃.mpr, h₃.mp⟩),
         rcases (h₁ (qdcl1.al φ₁_ᾰ φ₃)) with ⟨φ₄, h₄⟩,
         apply Equiv_Rule_To_equiv_qf_Rule ⟨h₄.mpr, h₄.mp⟩,
         existsi φ₄, refl,
      },
   },
   {  induction φ₁_ᾰ_1,
      {  rcases (h₁ (qdcl1.ex φ₁_ᾰ φ₁_ᾰ_1)) with ⟨φ₂, h₂⟩,
         apply Equiv_Rule_To_equiv_qf_Rule ⟨h₂.mpr, h₂.mp⟩,
         existsi φ₂, refl, },
      all_goals {  rcases φ₁_ih with ⟨φ₂, h₂⟩,
         apply Equiv_Rule_To_equiv_qf_Rule (Equiv_Rule_To_Ex_Rule_R ⟨h₂.mpr, h₂.mp⟩),
         rcases (qf_equiv_dcl Γ φ₂) with ⟨φ₃, h₃⟩,
         apply Equiv_Rule_To_equiv_qf_Rule (Equiv_Rule_To_Ex_Rule_R ⟨h₃.mpr, h₃.mp⟩),
         rcases (h₁ (qdcl1.ex φ₁_ᾰ φ₃)) with ⟨φ₄, h₄⟩,
         apply Equiv_Rule_To_equiv_qf_Rule ⟨h₄.mpr, h₄.mp⟩,
         existsi φ₄, refl,
      },
   }
end

/- If a theory has quantifer elimination on conjunctions of literals with 
   a single existential quantifier, it has quantifier elimination -/
lemma qe_ecl1_qe : (qe_ecl1 Γ) → (qe Γ) := begin
   intro h,
   have h_dnf : qe_dnf Γ := 
      by { apply qe_qdcl1_qe_dnf, apply qe_edcl1_qe_qdcl1, apply qe_ecl1_qe_edcl1, assumption },
   intro φ₁,
   rcases (for_all_equiv_dnf Γ φ₁) with ⟨φ₂, h₂⟩,
   apply Equiv_Rule_To_equiv_qf_Rule ⟨h₂.mpr, h₂.mp⟩,
   rcases (h_dnf φ₂) with ⟨φ₃, h₃⟩,
   apply Equiv_Rule_To_equiv_qf_Rule ⟨h₃.mpr, h₃.mp⟩,
   existsi φ₃, refl,
end

/- Deciable sentences in a theory -/
def decidable_sent (φ : sentence L) : Prop := (Γ ▸ φ ↔ Γ ▸ F) ∨ (Γ ▸ φ ↔ Γ ▸ T)

end quantifier_elimination

end first_order