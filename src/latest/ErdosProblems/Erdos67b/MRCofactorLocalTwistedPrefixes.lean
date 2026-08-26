import ErdosProblems.Erdos67b.MRTypicalCofactorRestoredSmallMean
import ErdosProblems.Erdos67b.MRCofactorTwistedPrefix

/-!
# Twisted cofactor prefixes from an ambient local frequency window

At prefix scales above the ambient scale, monotonicity loses no distance.
The contour window, not the prefix endpoint, is added to the twist height.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrPretentiousDistSq_untwist_upper_scale_local
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {M X Z : ℕ}
    (hXZ : X ≤ Z) (hnonpret : MRArchimedeanNonpretentious f M X)
    {t R : ℝ} (hwindow : |t| + R ≤ X) {u : ℝ} (hu : |u| ≤ R) :
    (M : ℝ) ≤ pretentiousDistSq (archimedeanUntwist f t) (archimedeanTwist u) Z := by
  rw [mrPretentiousDistSq_archimedeanUntwist]
  have hfreq : |t + u| ≤ (X : ℝ) := (abs_add_le t u).trans (by linarith)
  exact (hnonpret (t + u) hfreq).trans (pretentiousDistSq_mono hXZ
    (fun p hp ↦ hbound p hp.pos)
    (fun p hp ↦ (norm_archimedeanTwist hp.pos (t + u)).le))

theorem mrExists_uniform_small_local_twisted_cofactor_prefixes
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 2 ≤ X₀ ∧
      ∀ {M X U : ℕ}, M₀ ≤ M → X₀ ≤ X → X ≤ U →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ (J : Finset ℕ) (B : ℕ → Finset ℕ),
        (∀ j ∈ J, 1 ≤ j) → (∀ j ∈ J, B j ⊆ primesUpTo X) →
        Set.PairwiseDisjoint (↑J : Set ℕ) B →
        (∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16) →
        (∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ)) →
        (∀ p ∈ A, p ≤ mrCofactorPowerCutoff delta X) →
        (∀ j ∈ J, ∀ p ∈ B j, p ≤ mrCofactorPowerCutoff delta X) →
        (∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| + Real.log (U : ℝ) ^ 2 ≤ X → ∀ Z ∈ Finset.Icc X U,
        ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B
          (archimedeanUntwist f t)) Z‖ / (Z : ℝ) ≤ epsilon := by
  obtain ⟨delta, hdelta, hdeltaOne, M₀, Y₀, hM₀, hmean⟩ :=
    mrExists_uniform_small_mean_restoredTypicalCofactor_of_localDistance hepsilon
  refine ⟨delta, hdelta, hdeltaOne, M₀, max Y₀ 2, hM₀, le_max_right _ _, ?_⟩
  intro M X U hM hX hXU A hA J B hJ hB hdisj hsmall hmass hAy hBy hlarge
    f hmul hbound hnonpret t hwindow Z hZ
  have hXtwo : 2 ≤ X := (le_max_right Y₀ 2).trans hX
  have hXpos : 0 < X := by omega
  have hXZ := (Finset.mem_Icc.1 hZ).1
  have hZU := (Finset.mem_Icc.1 hZ).2
  have hlogXZ : Real.log (X : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log (by exact_mod_cast hXpos) (by exact_mod_cast hXZ)
  have hlogZU : Real.log (Z : ℝ) ≤ Real.log (U : ℝ) :=
    Real.log_le_log (by exact_mod_cast hXpos.trans_le hXZ) (by exact_mod_cast hZU)
  have hlogZ : 0 ≤ Real.log (Z : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Z by omega))
  have hheight : Real.log (Z : ℝ) ^ 2 ≤ Real.log (U : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlogZ hlogZU 2
  have hcutoff := mrCofactorPowerCutoff_mono hdelta.le hXpos hXZ
  apply hmean hM (((le_max_left Y₀ 2).trans hX).trans hXZ) A hA J B hJ
  · intro j hj
    exact (hB j hj).trans (primesUpTo_mono hXZ)
  · exact hdisj
  · intro j hj p hp
    exact (hsmall j hj p hp).trans (div_le_div_of_nonneg_right hlogXZ (by norm_num))
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
  · intro u hu
    exact mrPretentiousDistSq_untwist_upper_scale_local hbound hXZ hnonpret
      hwindow (hu.trans hheight)

end

end Erdos67b
