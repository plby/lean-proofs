import ErdosProblems.Erdos67b.MRGSCentralAmplitude

/-!
# Complementary typical prefixes with unrestricted deleted primes

The deleted prime set is not a denominator set. Consequently its primes
need not lie below the contour splitting cutoff. Deletion costs at most
half the local distance, and lowering the prime cutoff costs a fixed
Mertens allowance.
-/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrDeletedUntwist_localDistance_lower_scale
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q] {N M Z X : ℕ}
    (hNM : 2 * (N : ℝ) + mrCofactorDistanceLoss ≤ M)
    (hZ : 2 ≤ Z) (hZX : Z ≤ X) (hlog : Real.log (X : ℝ) ≤ 2 * Real.log (Z : ℝ))
    {t : ℝ} (hwindow : |t| + Real.log (X : ℝ) ^ 2 ≤ X)
    (hnonpret : MRArchimedeanNonpretentious f M X) :
    ∀ u : ℝ, |u| ≤ Real.log (Z : ℝ) ^ 2 →
      (N : ℝ) ≤ pretentiousDistSq
        (gsDeletePrimeBand (archimedeanUntwist f t) Q) (archimedeanTwist u) Z := by
  intro u hu
  have hlogZ : 0 ≤ Real.log (Z : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Z by omega))
  have hlogZX : Real.log (Z : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < Z by omega)) (by exact_mod_cast hZX)
  have hheight := pow_le_pow_left₀ hlogZ hlogZX 2
  have hfreq : |t + u| ≤ (X : ℝ) := (abs_add_le t u).trans (by linarith)
  have hupper := hnonpret (t + u) hfreq
  have htail := mrPretentiousDistSq_tail_le_cofactorLoss hZ hZX hlog
    (fun p hp ↦ hbound p hp.pos) (fun p hp ↦ (norm_archimedeanTwist hp.pos (t + u)).le)
  have hhalf := half_pretentiousDistSq_le_deletePrimeBand
    (f := archimedeanUntwist f t) (g := archimedeanTwist u)
    (fun p hp ↦ by rw [mrNorm_archimedeanUntwist_of_pos f t hp.pos]; exact hbound p hp.pos)
    (fun p hp ↦ (norm_archimedeanTwist hp.pos u).le) Q Z
  rw [mrPretentiousDistSq_archimedeanUntwist] at hhalf
  linarith

theorem mrExists_uniform_small_complementary_typical_prefixes
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ M₀ Y₀ : ℕ, 0 < M₀ ∧ 2 ≤ Y₀ ∧
      ∀ {M X Y : ℕ}, M₀ ≤ M → Y₀ ≤ Y → Y ≤ X →
        Real.log (X : ℝ) ≤ 2 * Real.log (Y : ℝ) →
      ∀ (Q : ℕ → Prop) [DecidablePred Q],
      ∀ (J : Finset ℕ) (B : ℕ → Finset ℕ),
        (∀ j ∈ J, 1 ≤ j) → (∀ j ∈ J, B j ⊆ primesUpTo Y) →
        Set.PairwiseDisjoint (↑J : Set ℕ) B →
        (∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (Y : ℝ) / 16) →
        (∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ)) →
        (∀ j ∈ J, ∀ p ∈ B j, p ≤ mrCofactorPowerCutoff delta Y) →
        (∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| + Real.log (X : ℝ) ^ 2 ≤ X → ∀ Z ∈ Finset.Icc Y X,
        ‖positivePrefixSum (mrIndexedTypicalCoefficient J B
          (gsDeletePrimeBand (archimedeanUntwist f t) Q)) Z‖ / (Z : ℝ) ≤ epsilon := by
  obtain ⟨delta, hdelta, hdeltaOne, N₀, Z₀, hN₀, hmean⟩ :=
    mrExists_uniform_small_mean_restoredTypicalCofactor_of_localDistance hepsilon
  let M₀ := 2 * N₀ + ⌈mrCofactorDistanceLoss⌉₊
  let Y₀ := max Z₀ 2
  have hM₀ : 0 < M₀ := by dsimp only [M₀]; omega
  refine ⟨delta, hdelta, hdeltaOne, M₀, Y₀, hM₀, le_max_right _ _, ?_⟩
  intro M X Y hM hY _hYX hlogXY Q instQ J B hJ hB hdisj hsmall hmass hBy hlarge
    f hmul hbound hnonpret t hwindow Z hZ
  have hYtwo : 2 ≤ Y := (le_max_right Z₀ 2).trans hY
  have hYZ := (Finset.mem_Icc.mp hZ).1
  have hZX := (Finset.mem_Icc.mp hZ).2
  have hZtwo : 2 ≤ Z := hYtwo.trans hYZ
  have hlogYZ : Real.log (Y : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < Y by omega)) (by exact_mod_cast hYZ)
  have hNM : 2 * (N₀ : ℝ) + mrCofactorDistanceLoss ≤ M := by
    have hceil := Nat.le_ceil mrCofactorDistanceLoss
    have hcast : 2 * (N₀ : ℝ) + (⌈mrCofactorDistanceLoss⌉₊ : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hcutoff := mrCofactorPowerCutoff_mono hdelta.le (show 0 < Y by omega) hYZ
  have hg : IsMultiplicativeOnPositiveNat (gsDeletePrimeBand (archimedeanUntwist f t) Q) :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat (archimedeanUntwist_isMultiplicative hmul t) Q
  have hgbound : ∀ n, 0 < n → ‖gsDeletePrimeBand (archimedeanUntwist f t) Q n‖ ≤ 1 :=
    fun n hn ↦ norm_gsDeletePrimeBand_le_one
      (fun m hm ↦ by rw [mrNorm_archimedeanUntwist_of_pos f t hm]; exact hbound m hm) Q hn
  have hdistance := mrDeletedUntwist_localDistance_lower_scale hbound Q hNM hZtwo hZX
    (by linarith) hwindow hnonpret
  have hprefix := hmean (N := N₀) (X := Z) le_rfl
    (((le_max_left Z₀ 2).trans hY).trans hYZ) ∅ (by simp) J B hJ
    (fun j hj ↦ (hB j hj).trans (primesUpTo_mono hYZ)) hdisj
    (fun j hj p hp ↦ (hsmall j hj p hp).trans
      (div_le_div_of_nonneg_right hlogYZ (by norm_num))) hmass (by simp)
    (fun j hj p hp ↦ (hBy j hj p hp).trans hcutoff) hlarge hg hgbound hdistance
  simpa only [mrIndexedTypicalCofactorCoefficient_empty] using hprefix

end

end Erdos67b
