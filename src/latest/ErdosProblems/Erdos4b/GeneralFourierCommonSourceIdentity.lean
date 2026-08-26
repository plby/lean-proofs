/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCommonFamilyCutoff
import ErdosProblems.Erdos4b.GeneralFourierSourceNormalization

/-!
# Physical source normalization at an enlarged common cutoff

Any cutoff above the common coordinate bound gives the same Fourier
main term. Its actual CRT endpoint error is retained explicitly.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def sourceAnalyticCommonPrimeBound {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ) (LD LE : ℝ) : ℕ :=
  selbergTensorFamilyCommonBound S (fun j ↦ twoFamilySelbergProfiles (F j) G)
    (twoFamilySelbergScales LD LE)

theorem sourceAnalyticPreSievedWeightSum_normalized_identity_of_common_bound
    {K w m q T B : ℕ} {J : Type*} (hK : 0 < K) (hw : 2 ≤ w) (hKw : K ≤ w)
    (hm : 0 < m) (hmeven : Even m) (hq : q.Prime) (hT : 0 < T)
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (LD LE : ℝ)
    (hLD : 0 < LD) (hLE : 0 < LE)
    (hFcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i)) (hGcompact : HasCompactSupport G)
    (hB : sourceAnalyticCommonPrimeBound S F G LD LE ≤ B)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (hDq : LD / 10 < Real.log q) (hEq : LE < Real.log q) :
    let P := selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes B)
    let Fw := fun j h ↦ F j ((preSievedShiftEquiv K w).symm h)
    fullAffineFourierNormalization K w m q (twoFamilySelbergScales LD LE) *
        (sourceAnalyticPreSievedWeightSum (preSievedShifts K w) P S Fw G LD LE w m q T : ℂ) /
          (T : ℂ) =
      actualAffineFourierNormalization K w m q (twoFamilySelbergScales LD LE) *
        compactSelbergTensorSquareSum (fun p ↦ decide (w < p))
          (indexedPreSievedFourierEdges K w m q) (affineFourierCompanionSwitch m) S
          (fun j ↦ twoFamilySelbergProfiles (F j) G) (twoFamilySelbergScales LD LE) +
      fullAffineFourierNormalization K w m q (twoFamilySelbergScales LD LE) *
        (doubledSelbergGeneralNormalizationError (preSievedShifts K w)
          (cutoffDivisorTupleSupport (preSievedShifts K w) P)
          (cutoffCompanionDivisorTupleSupport (preSievedShifts K w) P m)
          (sourceAnalyticSelbergCoefficient S Fw G LD LE) (primorial w) m q T : ℂ) /
          (T : ℂ) := by
  dsimp only
  let P := selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes B)
  let Fw := fun j h ↦ F j ((preSievedShiftEquiv K w).symm h)
  have hP : ∀ p ∈ P, p.Prime := selectedFourierPrimeCutoff_prime _ _
  have hrough : ∀ p ∈ P, w < p := fun p hp ↦ rough_of_mem_selectedFourierPrimeCutoff w _ hp
  have hmain := preSievedCutoffDoubledWeightSum_eq_lcmKernel_add_error
    (preSievedShifts K w) P hP w m q T hw hm hrough
    (sourceAnalyticSelbergCoefficient S Fw G LD LE)
  have hceil := twoFamily_source_profile_support_ceiling S Fw G
    (fun j hj i t ht hne ↦ hFsupport j hj _ t ht hne) hGsupport
  have hAq : ∀ i : preSievedShifts K w ⊕ preSievedShifts K w,
      twoFamilySelbergScales (1 / 10) 1 i * twoFamilySelbergScales LD LE i < Real.log q := by
    intro i
    cases i
    · change (1 / 10 : ℝ) * LD < _
      linarith
    · simpa only [twoFamilySelbergScales, Sum.elim_inr, one_mul] using hEq
  have hkernel := indexed_cutoffTensorSquare_eq_sourceCoordinateKernel P hP hrough hm hq hKw
    S F G LD LE (twoFamilySelbergScales (1 / 10) 1) hLD hLE hceil hAq
  have hL : ∀ i : Fin K ⊕ Fin K, 0 < twoFamilySelbergScales LD LE i := by
    intro i
    cases i
    · exact hLD
    · exact hLE
  have hcommon := compactSelbergTensorSquareSum_eq_cutoff_of_common_le
    (fun p ↦ decide (w < p)) (indexedPreSievedFourierEdges K w m q)
    (affineFourierCompanionSwitch m) S (fun j ↦ twoFamilySelbergProfiles (F j) G)
    (fun j hj ↦ hasCompactSupport_twoFamilySelbergProfiles (F j) G (hFcompact j hj) hGcompact)
    (twoFamilySelbergScales LD LE) hL hB
  have hfull := fullAffineFourierNormalization_mul_preSieveDensity (w := w) (q := q)
    (twoFamilySelbergScales LD LE) hK hmeven
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  change fullAffineFourierNormalization K w m q (twoFamilySelbergScales LD LE) *
      ((∑ n ∈ Finset.Icc 0 T, if largeGapPreSieved w m n then
        doubledSelbergWeight (preSievedShifts K w)
          (cutoffDivisorTupleSupport (preSievedShifts K w) P)
          (cutoffCompanionDivisorTupleSupport (preSievedShifts K w) P m)
          (sourceAnalyticSelbergCoefficient S Fw G LD LE) m q n else 0 : ℝ) : ℂ) /
      (T : ℂ) = _
  rw [hmain]
  push_cast
  rw [← hkernel, hcommon, mul_add, add_div]
  congr 1
  rw [← hfull]
  dsimp only [P]
  field_simp

end

end Erdos4b
