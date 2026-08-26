import ErdosProblems.Erdos67b.MRAuxiliaryMissingEnergy

/-! # Complete finite auxiliary energy with all three arithmetic errors -/

open MeasureTheory
open scoped BigOperators Interval

namespace Erdos67b

noncomputable section

theorem mrTypicalDyadic_auxiliary_energy_le
    {ι : Type*} (V : Finset ι) (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ)
    (K : ι → ℕ × ℕ) (D : ι → Finset ℕ)
    (hpartition : Set.PairwiseDisjoint (↑V) D) (hcover : V.biUnion D = primesInBlock I)
    (hK : ∀ v ∈ V, 0 < (K v).1)
    (hDK : ∀ v ∈ V, ∀ p ∈ D v, (K v).1 ≤ p ∧ p ≤ (K v).2)
    (hdisj : ∀ B ∈ blocks, B ≠ I → Disjoint (primesInBlock I) (primesInBlock B))
    (hI : 0 < I.1) {X : ℕ} (hX : 0 < X)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hwidth : ∀ v ∈ V, ((K v).2 : ℝ) ≤ (1 + epsilon) * (K v).1)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, E.indicator (fun t ↦ ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2) t) ≤
      8 * (V.card : ℝ) * (∑ v ∈ V, ∫ t in -T..T, E.indicator
        (fun t ↦ ‖logarithmicDirichletPolynomial (D v) (mrFinitePrimeLineCoefficient f) t *
          logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I (K v) X)
            (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2) t) +
      256 * (1 + Real.pi) * (T / X + 1) * (3 * epsilon + 1 / X + 1 / I.1) +
      2 * ∫ t in -T..T, ‖mrAuxiliaryMissingPolynomial blocks I f X t‖ ^ 2 := by
  classical
  let Q : ι → ℝ → ℂ := fun v t ↦
    logarithmicDirichletPolynomial (D v) (mrFinitePrimeLineCoefficient f) t *
      logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I (K v) X)
        (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t
  let B : ℝ → ℂ := fun t ↦
    ∑ v ∈ V, mrTypicalRamareBoundaryPolynomial blocks I (K v) (D v) f X t
  let F : ℝ → ℂ := fun t ↦ (∑ v ∈ V, Q v t) - B t
  let S := mrPrimeSquareErrorPolynomial (insert I blocks) I f X
  let M := mrAuxiliaryMissingPolynomial blocks I f X
  have hQ : ∀ v ∈ V, Continuous (Q v) := fun _ _ ↦
    (continuous_logarithmicDirichletPolynomial _ _).mul
      (continuous_logarithmicDirichletPolynomial _ _)
  have hB : Continuous B := continuous_finsetSum V (fun _ _ ↦
    continuous_logarithmicDirichletPolynomial _ _)
  have hF : Continuous F := (continuous_finsetSum V hQ).sub hB
  have hS : Continuous S := continuous_logarithmicDirichletPolynomial _ _
  have hM : Continuous M := continuous_logarithmicDirichletPolynomial _ _
  have hfactor (t : ℝ) : mrTypicalDyadicPolynomial blocks f X t = (F t + S t) + M t := by
    have hh := mrTypicalDyadicPolynomial_eq_auxiliary_products_add_errors
      hpartition hcover hK hDK hdisj f X t
    simpa only [Finset.sum_sub_distrib] using hh
  have houter := intervalIntegral_indicator_add_le (hF.add hS) hM hE hT
  simp only [Pi.add_apply] at houter
  have hmiddle := intervalIntegral_indicator_add_le hF hS hE hT
  have hbase := intervalIntegral_indicator_sum_sub_le V Q B hQ hB hE hT
  have hDP : ∀ v ∈ V, D v ⊆ primesInBlock I := by
    intro v hv p hp
    rw [← hcover]
    exact Finset.mem_biUnion.mpr ⟨v, hv, hp⟩
  have hboundary := intervalIntegral_sum_mrTypicalRamareBoundaryPolynomial_le
    V blocks I K D hbound hX hepsilon hepsilonHalf hK hwidth hDK hDP hpartition hT
  have hsquare := intervalIntegral_mrPrimeSquareError_le (Z := 2 * X)
    (Finset.mem_insert_self I blocks) hI hX hmul hbound hT
  have heq : 256 * (1 + Real.pi) * (T / X + 1) * (3 * epsilon + 1 / X + 1 / I.1) =
      8 * (32 * (1 + Real.pi) * (T / X + 1) * (3 * epsilon + 1 / X)) +
      4 * (64 * (1 + Real.pi) * (T / X + 1) / I.1) := by ring
  simp_rw [hfactor]
  change (∫ t in -T..T, E.indicator (fun t ↦ ‖(F t + S t) + M t‖ ^ 2) t) ≤
    8 * (V.card : ℝ) * (∑ v ∈ V, ∫ t in -T..T, E.indicator (fun t ↦ ‖Q v t‖ ^ 2) t) +
      256 * (1 + Real.pi) * (T / X + 1) * (3 * epsilon + 1 / X + 1 / I.1) +
      2 * ∫ t in -T..T, ‖M t‖ ^ 2
  rw [heq]
  change (∫ t in -T..T, ‖B t‖ ^ 2) ≤ _ at hboundary
  change (∫ t in -T..T, ‖S t‖ ^ 2) ≤ _ at hsquare
  change (∫ t in -T..T, E.indicator (fun t ↦ ‖F t‖ ^ 2) t) ≤ _ at hbase
  linarith

end

end Erdos67b
