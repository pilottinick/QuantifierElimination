import dnf

namespace first_order

section quantifier_elimination

variables {L : language} (A : Type) (Γ : list (formula L)) {φ φ₁ φ₂ ψ : formula L} {p q : formula L}
variable [has_coe A (formula L)]

/- If a formula φ has has quantifier elimination in a theory -/
@[simp]
def equiv_qf (φ : formula L) := ∃ ψ : qf L, (A∣[] ⊢ φ) ↔ (A∣[] ⊢ (ψ : formula L))

def Eq_equiv_qf {A : Type} [has_coe A (formula L)] : ((A∣[] ⊢ p) ↔ (A∣[] ⊢ q)) → (equiv_qf A p → equiv_qf A q) := begin
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
def qe := ∀ (φ : formula L), equiv_qf A φ

/- If a theory Γ has quantifier elimination on conjunctions of literals with
   with a single existential quantifier -/
def qe_ecl1 := ∀ (φ : ecl1 L), equiv_qf A (φ : formula L)

/- If a theory Γ has quantifier elimination on disjunctions of conjunctions
   of literals with a single existential quantifier -/
def qe_edcl1 := ∀ (φ : edcl1 L), equiv_qf A (φ : formula L)

/- If a theory Γ has quantifier elimination on disjunctions of conjugations 
   of literals with a single quantifier -/
@[simp]
def qe_qdcl1 := ∀ (φ : qdcl1 L), equiv_qf A (φ : formula L)

@[simp]
def qe_dnf := ∀ (φ : dnf L), equiv_qf A (φ : formula L)

/- If a theory Γ has quantifier elimination on quantifier free formulas -/
@[simp]
def qe_qf := ∀ (φ : qf L), equiv_qf A (φ : formula L)

/- All theories have quantifier elimination on quantifier free formulas -/
def for_all_qe_qf : @qe_qf L A _ := by { intros φ, existsi φ, refl }

/- If a theory has quantifier elimination on φ₁ φ₂ then it has quantifier 
   elimination on (φ₁ or φ₂) -/
lemma equiv_qf_or_equiv_qf : equiv_qf A φ₁ → equiv_qf A φ₂ → equiv_qf A (φ₁ or φ₂) := begin
   intros h_φ₁ h_φ₂,
   rcases h_φ₁ with ⟨φ₁', h₁⟩,
   rcases h_φ₂ with ⟨φ₂', h₂⟩,
   apply Eq_equiv_qf (R_Eq_Or_ ⟨h₁.mpr, h₁.mp⟩ ⟨h₂.mpr, h₂.mp⟩),
   existsi (qf.o φ₁' φ₂'), refl,
end

lemma qe_ecl1_qe_edcl1 : (∀ x : ℕ, @var_not_free_in_axioms L x A _) → ((@qe_ecl1 L A _) → (@qe_edcl1 L A _)) := begin
   intros h h₁ φ,
   cases φ,
   {  existsi (φ : qf L), refl, },
   {  induction φ_ᾰ_1,
      rcases (h₁ (ecl1.ex φ_ᾰ φ_ᾰ_1)) with ⟨φ₂, h₂⟩,
      apply Eq_equiv_qf ⟨h₂.mpr, h₂.mp⟩,
      existsi φ₂, refl,
      rcases φ_ᾰ_1_ih_ᾰ with ⟨φ₂, h₂⟩,
      rcases φ_ᾰ_1_ih_ᾰ_1 with ⟨φ₃, h₃⟩,
      apply Eq_equiv_qf ⟨R_ (ExOrOut (h φ_ᾰ)), R_ (ExOrIn (h φ_ᾰ))⟩,
      apply Eq_equiv_qf (R_Eq_Or_ ⟨h₂.mpr, h₂.mp⟩ ⟨h₃.mpr, h₃.mp⟩),
      existsi qf.o φ₂ φ₃, refl,
   },
end

lemma qe_edcl1_qe_qdcl1 : (@qe_edcl1 L A _) → (@qe_qdcl1 L A _) := begin
   intros h₁ φ,
   induction φ,
   {  existsi (φ : qf L), refl, },
   { 
      rcases (qf_equiv_dcl A (qf.n ↑φ_ᾰ_1)) with ⟨φ₂, h₂⟩,
      apply Eq_equiv_qf ⟨R_ Ex_To_All, R_ All_To_Ex⟩,
      apply Eq_equiv_qf
         (R_Eq_Not_ (R_Eq_Ex_ ⟨h₂.mpr, h₂.mp⟩)),
      rcases (h₁ (edcl1.ex φ_ᾰ φ₂)) with ⟨φ₃, h₃⟩,
      apply Eq_equiv_qf (R_Eq_Not_ ⟨h₃.mpr, h₃.mp⟩),
      existsi (qf.n φ₃), refl,
   },
   {  rcases (h₁ (edcl1.ex φ_ᾰ φ_ᾰ_1)) with ⟨φ₂, h₂⟩,
      apply Eq_equiv_qf ⟨h₂.mpr, h₂.mp⟩,
      existsi φ₂, refl,
   }
end

lemma qe_qdcl1_qe_dnf : (@qe_qdcl1 L A _) → (@qe_dnf L A _) := begin
   intros h₁ φ₁,
   induction φ₁,
   {  existsi (φ₁ : qf L), refl, },
   {  cases φ₁_ᾰ_1,
      {  rcases (h₁ (qdcl1.al φ₁_ᾰ φ₁_ᾰ_1)) with ⟨φ₂, h₂⟩,
         apply Eq_equiv_qf ⟨h₂.mpr, h₂.mp⟩,
         existsi φ₂, refl, },
      all_goals {  rcases φ₁_ih with ⟨φ₂, h₂⟩,
         apply Eq_equiv_qf (R_Eq_All_ ⟨h₂.mpr, h₂.mp⟩),
         rcases (qf_equiv_dcl A φ₂) with ⟨φ₃, h₃⟩,
         apply Eq_equiv_qf (R_Eq_All_ ⟨h₃.mpr, h₃.mp⟩),
         rcases (h₁ (qdcl1.al φ₁_ᾰ φ₃)) with ⟨φ₄, h₄⟩,
         apply Eq_equiv_qf ⟨h₄.mpr, h₄.mp⟩,
         existsi φ₄, refl,
      },
   },
   {  induction φ₁_ᾰ_1,
      {  rcases (h₁ (qdcl1.ex φ₁_ᾰ φ₁_ᾰ_1)) with ⟨φ₂, h₂⟩,
         apply Eq_equiv_qf ⟨h₂.mpr, h₂.mp⟩,
         existsi φ₂, refl, },
      all_goals {  rcases φ₁_ih with ⟨φ₂, h₂⟩,
         apply Eq_equiv_qf (R_Eq_Ex_ ⟨h₂.mpr, h₂.mp⟩),
         rcases (qf_equiv_dcl A φ₂) with ⟨φ₃, h₃⟩,
         apply Eq_equiv_qf (R_Eq_Ex_ ⟨h₃.mpr, h₃.mp⟩),
         rcases (h₁ (qdcl1.ex φ₁_ᾰ φ₃)) with ⟨φ₄, h₄⟩,
         apply Eq_equiv_qf ⟨h₄.mpr, h₄.mp⟩,
         existsi φ₄, refl,
      },
   }
end

/- If a theory has quantifer elimination on conjunctions of literals with 
   a single existential quantifier, it has quantifier elimination -/
lemma qe_ecl1_qe : (∀ x : ℕ, @var_not_free_in_axioms L x A _) → ((@qe_ecl1 L A _) → (@qe L A _)) := begin
   intros h₁ h₂,
   have h_dnf : qe_dnf A := 
      by { apply qe_qdcl1_qe_dnf, apply qe_edcl1_qe_qdcl1,
           apply qe_ecl1_qe_edcl1 A h₁, assumption },
   intro φ₁,
   rcases (for_all_equiv_dnf A φ₁) with ⟨φ₂, h₂⟩,
   apply Eq_equiv_qf ⟨h₂.mpr, h₂.mp⟩,
   rcases (h_dnf φ₂) with ⟨φ₃, h₃⟩,
   apply Eq_equiv_qf ⟨h₃.mpr, h₃.mp⟩,
   existsi φ₃, refl,
end

/- Deciable sentences in a theory -/
--def decidable_sent (φ : sentence L) : Prop 
--   := ((A∣[] ⊢ (φ : formula L)) ↔ (A∣Γ ⊢ F)) ∨ ((A∣[] ⊢ φ) ↔ (A∣Γ ⊢ T))

end quantifier_elimination

end first_order