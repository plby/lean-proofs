/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTReweightedEventMass
import ErdosProblems.Erdos4b.FGKMTConditionedState

/-! # Expected loss on bad normalizers, including the conditioned-state cost -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ] [DecidableEq α]

def badNormalizerMass (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (τ : ℝ) (i : I) : ℝ :=
  ∑ s, if |F.reweightNormalizer P (W s) i - 1| ≤ τ then 0 else ρ s

theorem badNormalizerMass_le_tail (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (τ : ℝ) (i : I) (hρ : ∀ s, 0 ≤ ρ s) :
    F.badNormalizerMass P ρ W τ i ≤
      ∑ s, if τ ≤ |F.reweightNormalizer P (W s) i - 1| then ρ s else 0 := by
  apply Finset.sum_le_sum
  intro s _hs
  by_cases hgood : |F.reweightNormalizer P (W s) i - 1| ≤ τ
  · rw [if_pos hgood]
    split_ifs
    · exact hρ s
    · exact le_rfl
  · rw [if_neg hgood, if_pos (le_of_lt (lt_of_not_ge hgood))]

theorem badNormalizerMass_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ b η τ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (hρ0 : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (i : I) (hb : 0 ≤ b) (hη : 0 ≤ η) (hτ : 0 < τ)
    (hcap : ∀ v ∈ F.vertices, F.vertexMass i v ≤ b)
    (hfirst : ∀ w, |containmentMass ρ W (F.edge i w) - survivalProduct P (F.edge i w)| ≤
      η * survivalProduct P (F.edge i w))
    (hsecond : ∀ w z, containmentMass ρ W (F.edge i w ∪ F.edge i z) ≤
      (1 + η) * survivalProduct P (F.edge i w ∪ F.edge i z)) :
    F.badNormalizerMass P ρ W τ i ≤
      (3 * η + (1 + η) * (1 / κ ^ F.rank) * ((F.rank : ℝ) * b)) / τ ^ 2 :=
  (F.badNormalizerMass_le_tail P ρ W τ i hρ0).trans
    (F.reweightNormalizer_tail_le hκ0 hκ1 hP ρ W hρ0 hρsum i hb hη hτ hcap hfirst hsecond)

theorem reweightedEventMass_error_mean (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (hρ0 : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (i : I) (T : Finset Ω) :
    (∑ s, ρ s * |F.reweightedEventMass P (W s) τ i T - F.rawEventMass P (W s) i T|) ≤
      (F.badNormalizerMass P ρ W τ i + 2 * τ) *
        ((1 / κ ^ F.rank) * ∑ w ∈ T, F.mass i w) := by
  calc
    _ ≤ ∑ s, ρ s *
        (((if |F.reweightNormalizer P (W s) i - 1| ≤ τ then 0 else 1) + 2 * τ) *
          ((1 / κ ^ F.rank) * ∑ w ∈ T, F.mass i w)) :=
      Finset.sum_le_sum fun s _hs => mul_le_mul_of_nonneg_left
        (F.reweightedEventMass_error hκ0 hκ1 hP (W s) hτ0 hτ i T) (hρ0 s)
    _ = _ := by
      have hsum : (∑ s, ρ s *
          ((if |F.reweightNormalizer P (W s) i - 1| ≤ τ then 0 else 1) + 2 * τ)) =
          F.badNormalizerMass P ρ W τ i + 2 * τ := by
        simp only [badNormalizerMass, mul_add, mul_ite, mul_zero, mul_one,
          Finset.sum_add_distrib, ← Finset.sum_mul, hρsum, one_mul]
      calc
        _ = (∑ s, ρ s *
            ((if |F.reweightNormalizer P (W s) i - 1| ≤ τ then 0 else 1) + 2 * τ)) *
            ((1 / κ ^ F.rank) * ∑ w ∈ T, F.mass i w) := by
          simp only [Finset.sum_mul, mul_assoc]
        _ = _ := by rw [hsum]

theorem reweightedEventMass_error_mean_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ β : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (hρ0 : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (i : I) (T : Finset Ω)
    (hbad : F.badNormalizerMass P ρ W τ i ≤ β) :
    (∑ s, ρ s * |F.reweightedEventMass P (W s) τ i T - F.rawEventMass P (W s) i T|) ≤
      (β + 2 * τ) * ((1 / κ ^ F.rank) * ∑ w ∈ T, F.mass i w) :=
  (F.reweightedEventMass_error_mean hκ0 hκ1 hP ρ W hρ0 hρsum hτ0 hτ i T).trans
    (mul_le_mul_of_nonneg_right (add_le_add hbad le_rfl)
      (mul_nonneg (one_div_nonneg.mpr (pow_pos hκ0 F.rank).le)
        (Finset.sum_nonneg fun w _hw => F.mass_nonneg i w)))

theorem reweightedEventMass_error_sum_mean_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ β : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (hρ0 : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (T : I → Finset Ω)
    (hbad : ∀ i, F.badNormalizerMass P ρ W τ i ≤ β) :
    (∑ s, ρ s * ∑ i,
      |F.reweightedEventMass P (W s) τ i (T i) - F.rawEventMass P (W s) i (T i)|) ≤
      (β + 2 * τ) * ((1 / κ ^ F.rank) * ∑ i, ∑ w ∈ T i, F.mass i w) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _hi
  simpa only [Finset.mul_sum] using
    F.reweightedEventMass_error_mean_le hκ0 hκ1 hP ρ W hρ0 hρsum hτ0 hτ i (T i) (hbad i)

theorem reweightedEventMass_error_conditioned_tail_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ β t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (hρ0 : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (T : I → Finset Ω)
    (hbad : ∀ i, F.badNormalizerMass P ρ W τ i ≤ β)
    (e : Finset α) (hq : 0 < containmentMass ρ W e) (ht : 0 < t) :
    (∑ s, if t ≤ ∑ i,
        |F.reweightedEventMass P (W s) τ i (T i) - F.rawEventMass P (W s) i (T i)|
      then conditionedStateMass ρ W e s else 0) ≤
      ((β + 2 * τ) * ((1 / κ ^ F.rank) * ∑ i, ∑ w ∈ T i, F.mass i w)) /
        (containmentMass ρ W e * t) := by
  exact (conditionedState_tail_le hρ0
    (fun s => Finset.sum_nonneg fun i _hi => abs_nonneg _) hq ht).trans
    (div_le_div_of_nonneg_right
      (F.reweightedEventMass_error_sum_mean_le hκ0 hκ1 hP ρ W hρ0 hρsum hτ0 hτ T hbad)
      (mul_pos hq ht).le)

end

end Erdos4b.FGKMT.FiniteEdgeFamily
