/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSourceTransport
import ErdosProblems.Erdos4b.GeneralFourierSourceEndpointLimit

/-!
# Exact normalized source weight identity

At the common profile cutoff, the original nonnegative weight sum,
normalized by the full literal singular product, is exactly the
normalized fixed-index tensor square plus the normalized CRT error.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def sourceAnalyticPreSievedWeightSum {J : Type*}
    (H P : Finset ℕ) (S : Finset J) (F : J → H → ℝ → ℝ) (G : ℝ → ℝ)
    (LD LE : ℝ) (w m q T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 T, if largeGapPreSieved w m n then
    doubledSelbergWeight H (cutoffDivisorTupleSupport H P)
      (cutoffCompanionDivisorTupleSupport H P m)
      (sourceAnalyticSelbergCoefficient S F G LD LE) m q n else 0

def sourceAnalyticPrimeCutoff {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ) (w : ℕ) (LD LE : ℝ) : Finset ℕ :=
  selectedFourierPrimeCutoff (fun p ↦ decide (w < p))
    (boundedFourierPrimes (selbergTensorFamilyPrimeBound S
      (fun j ↦ twoFamilySelbergProfiles (F j) G) (twoFamilySelbergScales LD LE)))

theorem sourceAnalyticPreSievedWeightSum_normalized_identity
    {K w m q T : ℕ} {J : Type*} (hK : 0 < K) (hw : 2 ≤ w) (hKw : K ≤ w)
    (hm : 0 < m) (hmeven : Even m) (hq : q.Prime) (hT : 0 < T)
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (LD LE : ℝ)
    (hLD : 0 < LD) (hLE : 0 < LE)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (hDq : LD / 10 < Real.log q) (hEq : LE < Real.log q) :
    let P := sourceAnalyticPrimeCutoff S F G w LD LE
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
  let P := sourceAnalyticPrimeCutoff S F G w LD LE
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
  rw [← hkernel]
  rw [mul_add, add_div]
  congr 1
  calc
    _ = (fullAffineFourierNormalization K w m q (twoFamilySelbergScales LD LE) *
        (preSieveDensity w m : ℂ)) *
        compactSelbergTensorSquareSum (fun p ↦ decide (w < p))
          (indexedPreSievedFourierEdges K w m q) (affineFourierCompanionSwitch m) S
          (fun j ↦ twoFamilySelbergProfiles (F j) G) (twoFamilySelbergScales LD LE) := by
      change _ = _ * cutoffSelbergBilinearSum P _ _ _ _
      field_simp
    _ = _ := by rw [hfull]

end

end Erdos4b
