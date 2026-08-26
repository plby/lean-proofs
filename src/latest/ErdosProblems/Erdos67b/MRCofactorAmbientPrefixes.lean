import ErdosProblems.Erdos67b.MRTypicalCofactorRestoredSmallMean
import ErdosProblems.Erdos67b.MRCofactorTwistedPrefix

/-!
# Uniform ambient-to-prefix transfer over a general cofactor interval

All structural conditions are imposed at the lower endpoint and propagated
to every prefix. The upper endpoint and shifted frequency window remain
explicit, so this applies to the rounded Ramaré rectangle.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrExists_uniform_small_ambient_cofactor_prefixes
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ M₀ Y₀ : ℕ, 0 < M₀ ∧ 2 ≤ Y₀ ∧
      ∀ {M X Y U : ℕ}, M₀ ≤ M → Y₀ ≤ Y → Y ≤ U → U ≤ X →
        Real.log (X : ℝ) ≤ 2 * Real.log (Y : ℝ) →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ (J : Finset ℕ) (B : ℕ → Finset ℕ),
        (∀ j ∈ J, 1 ≤ j) → (∀ j ∈ J, B j ⊆ primesUpTo Y) →
        Set.PairwiseDisjoint (↑J : Set ℕ) B →
        (∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (Y : ℝ) / 16) →
        (∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ)) →
        (∀ p ∈ A, p ≤ mrCofactorPowerCutoff delta Y) →
        (∀ j ∈ J, ∀ p ∈ B j, p ≤ mrCofactorPowerCutoff delta Y) →
        (∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| + (U : ℝ) ≤ X → ∀ Z ∈ Finset.Icc Y U,
        ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B (archimedeanUntwist f t)) Z‖ /
          (Z : ℝ) ≤ epsilon := by
  obtain ⟨delta, hdelta, hdeltaOne, N₀, Z₀, hN₀, hmean⟩ :=
    mrExists_uniform_small_mean_restoredTypicalCofactor hepsilon
  let M₀ := N₀ + ⌈mrCofactorDistanceLoss⌉₊
  let Y₀ := max Z₀ 2
  have hM₀ : 0 < M₀ := hN₀.trans_le (Nat.le_add_right _ _)
  refine ⟨delta, hdelta, hdeltaOne, M₀, Y₀, hM₀, le_max_right _ _, ?_⟩
  intro M X Y U hM hY _hYU hUX hlogXY A hA J B hJ hB hdisj hsmall hmass hAy hBy hlarge
    f hmul hbound hnonpret t hwindow Z hZ
  have hYtwo : 2 ≤ Y := (le_max_right Z₀ 2).trans hY
  have hYpos : 0 < Y := by omega
  have hYZ₀ : Z₀ ≤ Y := (le_max_left Z₀ 2).trans hY
  have hNM : (N₀ : ℝ) + mrCofactorDistanceLoss ≤ M := by
    have hceil : mrCofactorDistanceLoss ≤ (⌈mrCofactorDistanceLoss⌉₊ : ℝ) := Nat.le_ceil _
    have hMreal : (N₀ : ℝ) + (⌈mrCofactorDistanceLoss⌉₊ : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hYZ := (Finset.mem_Icc.1 hZ).1
  have hZup := (Finset.mem_Icc.1 hZ).2
  have hZtwo : 2 ≤ Z := hYtwo.trans hYZ
  have hlogYZ : Real.log (Y : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log (by exact_mod_cast hYpos) (by exact_mod_cast hYZ)
  have hwindowZ : |t| + (Z : ℝ) ≤ X := by
    have hcast : (Z : ℝ) ≤ U := by exact_mod_cast hZup
    linarith
  have hdist : MRArchimedeanNonpretentious (archimedeanUntwist f t) N₀ Z :=
    mrArchimedeanNonpretentious_untwist_lower_scale hbound hNM hZtwo (hZup.trans hUX)
      (by linarith) hwindowZ hnonpret
  have hcutoff := mrCofactorPowerCutoff_mono hdelta.le hYpos hYZ
  apply hmean le_rfl (hYZ₀.trans hYZ) A hA J B hJ
  · intro j hj
    exact (hB j hj).trans (primesUpTo_mono hYZ)
  · exact hdisj
  · intro j hj p hp
    exact (hsmall j hj p hp).trans (div_le_div_of_nonneg_right hlogYZ (by norm_num))
  · exact hmass
  · intro p hp
    exact (hAy p hp).trans hcutoff
  · intro j hj p hp
    exact (hBy j hj p hp).trans hcutoff
  · exact hlarge
  · exact archimedeanUntwist_isMultiplicative hmul t
  · intro n hn
    rw [mrNorm_archimedeanUntwist_of_pos f t hn]
    exact hbound n hn
  · exact hdist

end

end Erdos67b
