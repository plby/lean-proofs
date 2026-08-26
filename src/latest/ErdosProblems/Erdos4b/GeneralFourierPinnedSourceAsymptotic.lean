/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierJointSourceCutoff
import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightedAsymptotic
import ErdosProblems.Erdos4b.GeneralFourierPinnedMainConstant

/-!
# The literal pinned source coefficient in the totient graph asymptotic

The finite bilinear kernel uses the reduced source coefficient, with
its pinning amplitudes. It is stable at every joint source cutoff.
Its prime-progression interpretation is not assumed or asserted here.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem pinnedSourceSelbergCoefficient_eq_weighted_tensors_of_flat
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (LD LE : ℝ) (v : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℕ) :
    pinnedSourceSelbergCoefficient S F G h LD LE (fun i ↦ v (.inl i)) (fun i ↦ v (.inr i)) =
      ∑ j ∈ S, pinnedSourceProfileAmplitude F G h j *
        selbergTensorCoefficient (pinnedSourceProfileFamily F G h j)
          (twoFamilySelbergScales LD LE) v := by
  unfold pinnedSourceSelbergCoefficient
  have hv : Sum.elim (fun i ↦ v (.inl i)) (fun i ↦ v (.inr i)) = v := by
    funext i
    cases i <;> rfl
  rw [hv]

def pinnedSourceTotientGraphKernel {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (w m p₀ Y B : ℕ) (LD LE : ℝ) : ℂ :=
  cutoffTotientSelbergBilinearSum
    (selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes B))
    (roughPinnedFourierEdges h w m p₀ Y) (truncatedPinnedFourierCompanion m Y)
    (fun v ↦ pinnedSourceSelbergCoefficient S F G h LD LE
      (fun i ↦ v (.inl i)) (fun i ↦ v (.inr i)))
    (fun v ↦ pinnedSourceSelbergCoefficient S F G h LD LE
      (fun i ↦ v (.inl i)) (fun i ↦ v (.inr i)))

theorem pinnedSourceTotientGraphKernel_eq_compact
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (w m p₀ Y B : ℕ) (LD LE : ℝ) (hLD : 0 < LD) (hLE : 0 < LE)
    (hF : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i)) (hG : HasCompactSupport G)
    (hB : pinnedSourceCommonPrimeBound S F G h LD LE ≤ B) :
    pinnedSourceTotientGraphKernel S F G h w m p₀ Y B LD LE =
      compactWeightedTotientSelbergTensorSquareSum (fun p ↦ decide (w < p))
        (roughPinnedFourierEdges h w m p₀ Y) (truncatedPinnedFourierCompanion m Y)
        S (pinnedSourceProfileAmplitude F G h) (pinnedSourceProfileFamily F G h)
        (twoFamilySelbergScales LD LE) := by
  unfold pinnedSourceTotientGraphKernel
  simp_rw [pinnedSourceSelbergCoefficient_eq_weighted_tensors_of_flat]
  symm
  apply compactWeightedTotientSelbergTensorSquareSum_eq_cutoff_of_common_le
    _ _ _ S _ _
    (fun j hj ↦ hasCompactSupport_pinnedSourceProfileFamily F G h j (hF j hj) hG)
    _ _ hB
  intro i
  cases i
  · exact hLD
  · exact hLE

theorem pinnedFiniteFourierNormalization_twoFamily
    {K : ℕ} (h : Fin K) (w m p₀ Y : ℕ) (LD LE : ℝ) :
    pinnedFiniteFourierNormalization h w m p₀ Y (twoFamilySelbergScales LD LE) =
      ((LD ^ (K - 1) * LE ^ (K - 1) : ℝ) : ℂ) / (pinnedSingularSeries h w m p₀ Y : ℂ) := by
  simp only [pinnedFiniteFourierNormalization, twoFamilySelbergScales,
    Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_const,
    Finset.card_univ, card_pinnedShiftIndex, Complex.ofReal_mul, Complex.ofReal_pow]

theorem tendsto_pinnedSourceTotientGraphKernel_normalized
    {α J : Type*} {l : Filter α} [l.IsCountablyGenerated] {K : ℕ}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (hFcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hFsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (w m p₀ Y B : α → ℕ) (V : α → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop) (hY : Tendsto Y l atTop)
    (hm : ∀ᶠ a in l, 0 < m a) (hp₀ : ∀ᶠ a in l, (p₀ a).Prime)
    (hwY : ∀ᶠ a in l, w a ≤ Y a) (hYp₀ : ∀ᶠ a in l, Y a < p₀ a)
    (hcop : ∀ᶠ a in l, (m a * p₀ a - 1).Coprime (primorial (Y a)))
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    (hmV : ∀ᶠ a in l, Real.log (m a) ≤ V a)
    (hp₀V : ∀ᶠ a in l, Real.log (p₀ a) ≤ 2 * V a)
    (hLElower : ∀ᶠ a in l, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ Real.log (Y a))
    (hLEupper : ∀ᶠ a in l, Real.log (Y a) ≤ V a)
    (hB : ∀ᶠ a in l, jointSourceCommonPrimeBound S F G (V a) (Real.log (Y a)) ≤ B a) :
    Tendsto (fun a ↦
      (((V a ^ (K - 1) * Real.log (Y a) ^ (K - 1) : ℝ) : ℂ) /
        (pinnedSingularSeries h (w a) (m a) (p₀ a) (Y a) : ℂ)) *
      pinnedSourceTotientGraphKernel S F G h (w a) (m a) (p₀ a) (Y a) (B a)
        (V a) (Real.log (Y a))) l
      (𝓝 ((sourcePinnedFirstVariationalIntegral S F h *
        sourcePinnedCompanionVariationalIntegral K G : ℝ) : ℂ)) := by
  let L (a : α) : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℝ :=
    twoFamilySelbergScales (V a) (Real.log (Y a))
  have hLlower : ∀ᶠ a in l, ∀ i, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ L a i := by
    filter_upwards [hLElower, hLEupper] with a hla hua
    intro i
    cases i
    · exact hla.trans hua
    · exact hla
  have hLupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a := by
    filter_upwards [hLEupper] with a hua
    intro i
    cases i
    · exact le_rfl
    · exact hua
  have hlim := tendsto_compactPinnedWeightedTotientTensorSquareSum_finite_normalized
    h w m p₀ Y V L hw hV hY hm hp₀ hwY hYp₀ hcop hcutoff hmV hp₀V hLlower hLupper
    S (pinnedSourceProfileAmplitude F G h) (pinnedSourceProfileFamily F G h)
    (fun j hj ↦ hasCompactSupport_pinnedSourceProfileFamily F G h j (hFcompact j hj) hGcompact)
    (fun j hj ↦ contDiff_pinnedSourceProfileFamily F G h j (hFsmooth j hj) hGsmooth)
  rw [weightedSelbergTensorSquareMainConstant_pinnedSource S F G h
    hFcompact hFsmooth hGsmooth] at hlim
  apply hlim.congr'
  filter_upwards [hB, hV.eventually_gt_atTop 0, hY.eventually_gt_atTop 1]
    with a hBa hVa hYa
  have hlogY : 0 < Real.log (Y a) := Real.log_pos (by exact_mod_cast hYa)
  rw [pinnedSourceTotientGraphKernel_eq_compact S F G h _ _ _ _ _ _ _ hVa hlogY
    hFcompact hGcompact ((pinnedSourceCommonPrimeBound_le_joint S F G h _ _).trans hBa)]
  rw [pinnedFiniteFourierNormalization_twoFamily]

end

end Erdos4b
