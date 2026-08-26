import ErdosProblems.Erdos67b.MRCofactorComplementaryPrefixes
import ErdosProblems.Erdos67b.MRCofactorSelectedPrefixBound

/-!
# Actual selected-cofactor prefixes from ambient nonpretentiousness

Every small selected factor leaves a complementary prefix above the common
lower scale. This discharges its cancellation hypothesis simultaneously.
No selected-prime cutoff is imposed on the analytic contour.
-/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrExists_ambient_selected_cofactor_prefix_bound
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ M₀ Y₀ : ℕ, 0 < M₀ ∧ 2 ≤ Y₀ ∧
      ∀ {M X Y : ℕ}, M₀ ≤ M → Y₀ ≤ Y → Y ≤ X →
        Real.log (X : ℝ) ≤ 2 * Real.log (Y : ℝ) →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ (J : Finset ℕ) (B : ℕ → Finset ℕ),
        (∀ j ∈ J, 1 ≤ j) → (∀ j ∈ J, B j ⊆ primesUpTo Y) →
        Set.PairwiseDisjoint (↑J : Set ℕ) B →
        (∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (Y : ℝ) / 16) →
        (∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ)) →
        (∀ j ∈ J, ∀ p ∈ B j, p ≤ mrCofactorPowerCutoff delta Y) →
        (∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p) →
        (∀ j ∈ J, Disjoint A (B j)) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| + Real.log (X : ℝ) ^ 2 ≤ X →
      ∀ {Z K : ℕ}, Z ≤ X → 0 < K → K * Y ≤ Z →
      ∀ {sigma : ℝ}, 0 < sigma → sigma ≤ 1 →
        ‖gsTwistedPositivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) t Z‖ /
          (Z : ℝ) ≤ epsilon * (∏ p ∈ A, (1 - (p : ℝ)⁻¹)⁻¹) +
            (K : ℝ) ^ (sigma - 1) * ∏ p ∈ A, (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  obtain ⟨delta, hdelta, hdeltaOne, M₀, Y₀, hM₀, hY₀, hprefix⟩ :=
    mrExists_uniform_small_complementary_typical_prefixes hepsilon
  refine ⟨delta, hdelta, hdeltaOne, M₀, Y₀, hM₀, hY₀, ?_⟩
  intro M X Y hM hY hYX hlogXY A hA J B hJ hB hdisj hsmall hmass hBy hlarge hAB
    f hmul hbound hnonpret t hwindow Z K hZX hK hKY sigma hsigma hsigmaOne
  have hYpos : 0 < Y := by have := hY₀.trans hY; omega
  have hZpos : 0 < Z := (Nat.mul_pos hK hYpos).trans_le hKY
  have hgbound : ∀ n, 0 < n → ‖archimedeanUntwist f t n‖ ≤ 1 := by
    intro n hn
    rw [mrNorm_archimedeanUntwist_of_pos f t hn]
    exact hbound n hn
  have hboundPrefix := mrNorm_typicalCofactor_prefix_div_le_euler_rankin A hA J B
    (fun j hj p hp ↦ (mem_primesUpTo.mp (hB j hj hp)).1) hAB
    (archimedeanUntwist_isMultiplicative hmul t) hgbound hepsilon.le hsigma hsigmaOne hZpos hK
    (by
      intro d hd hdK _hdSupported
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hlower : Y ≤ Z / d := by
        apply (Nat.le_div_iff_mul_le hdpos).2
        calc
          Y * d ≤ Y * K := Nat.mul_le_mul_left Y hdK
          _ = K * Y := Nat.mul_comm _ _
          _ ≤ Z := hKY
      have hupper : Z / d ≤ X := (Nat.div_le_self Z d).trans hZX
      have hp := hprefix hM hY hYX hlogXY (fun p ↦ p ∈ A) J B hJ hB hdisj
        hsmall hmass hBy hlarge hmul hbound hnonpret t hwindow (Z / d)
        (Finset.mem_Icc.mpr ⟨hlower, hupper⟩)
      have hquotPos : (0 : ℝ) < (Z / d : ℕ) := by
        exact_mod_cast hYpos.trans_le hlower
      exact (div_le_iff₀ hquotPos).1 hp)
  rw [mrPositivePrefix_typicalCofactor_untwist_eq] at hboundPrefix
  exact hboundPrefix

end

end Erdos67b
