import ErdosProblems.Erdos1002.GaussHeterogeneousMovingScaleAggregate
import ErdosProblems.Erdos1002.GaussPrefixAnnularTupleDensity
import ErdosProblems.Erdos1002.GaussRoofMean

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The tagged annular zero Fourier mode

This file specializes the aggregate moving-scale theorem to the actual
canonical annular depth boxes.  It verifies the sign/parity orientation
coordinate by coordinate and proves permutation invariance of the
one-point signed-window product.  Consequently only the already proved
aggregate total and short-gap densities are used; no density is asserted
for an individual canonical order class.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 800000

def annularOccurrenceSignedDensity
    (ε A : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) : ℝ :=
  ∏ z : GaussPrefixMixedOccurrence k,
    (intervalGridPoint
          (signedGridLower ε A z.1.sign)
          (signedGridUpper ε A z.1.sign)
          grid (z.1.signed.1 + 1) -
      intervalGridPoint
          (signedGridLower ε A z.1.sign)
          (signedGridUpper ε A z.1.sign)
          grid z.1.signed.1) / Real.log 2

theorem flattenedAnnular_oriented_lower_of_sign_true
    (ε A : ℝ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k))
    (hs : (e j).1.sign = true) :
    gaussPrescribedParityOrientedLower
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j =
      flattenedAnnularSignedLower ε A e j := by
  simp [gaussPrescribedParityOrientedLower,
    flattenedAnnularParity, annularGridDepthParity, hs,
    gaussParityOrientedLower]

theorem flattenedAnnular_oriented_lower_of_sign_false
    (ε A : ℝ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k))
    (hs : (e j).1.sign = false) :
    gaussPrescribedParityOrientedLower
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j =
      -flattenedAnnularSignedUpper ε A e j := by
  simp [gaussPrescribedParityOrientedLower,
    flattenedAnnularParity, annularGridDepthParity, hs,
    gaussParityOrientedLower]

theorem flattenedAnnular_oriented_upper_of_sign_true
    (ε A : ℝ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k))
    (hs : (e j).1.sign = true) :
    gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j =
      flattenedAnnularSignedUpper ε A e j := by
  simp [gaussPrescribedParityOrientedUpper,
    flattenedAnnularParity, annularGridDepthParity, hs,
    gaussParityOrientedUpper]

theorem flattenedAnnular_oriented_upper_of_sign_false
    (ε A : ℝ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k))
    (hs : (e j).1.sign = false) :
    gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j =
      -flattenedAnnularSignedLower ε A e j := by
  simp [gaussPrescribedParityOrientedUpper,
    flattenedAnnularParity, annularGridDepthParity, hs,
    gaussParityOrientedUpper]

theorem flattenedAnnular_oriented_width
    (ε A : ℝ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) :
    gaussPrescribedParityOrientedUpper
          (flattenedAnnularParity e)
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e) j -
        gaussPrescribedParityOrientedLower
          (flattenedAnnularParity e)
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e) j =
      flattenedAnnularSignedUpper ε A e j -
        flattenedAnnularSignedLower ε A e j := by
  cases hs : (e j).1.sign
  · rw [flattenedAnnular_oriented_lower_of_sign_false
      ε A e j hs,
      flattenedAnnular_oriented_upper_of_sign_false
        ε A e j hs]
    ring
  · rw [flattenedAnnular_oriented_lower_of_sign_true
      ε A e j hs,
      flattenedAnnular_oriented_upper_of_sign_true
        ε A e j hs]

theorem flattenedAnnular_oriented_lower_pos
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) :
    0 <
      gaussPrescribedParityOrientedLower
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j := by
  have hactive : 0 < k (e j).1 := by
    have hj := (e j).2.isLt
    omega
  have hidx : (e j).1.signed.1 + 1 ≤ grid :=
    Nat.succ_le_iff.mpr (hsigned (e j).1 hactive)
  have hlowerIcc :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA (e j).1.sign).le
      hgrid (Nat.le_of_lt (hsigned (e j).1 hactive))
  have hupperIcc :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA (e j).1.sign).le
      hgrid hidx
  cases hs : (e j).1.sign
  · rw [flattenedAnnular_oriented_lower_of_sign_false
      ε A e j hs]
    unfold flattenedAnnularSignedUpper
    simp [signedGridLower, signedGridUpper, hs] at hupperIcc ⊢
    linarith
  · rw [flattenedAnnular_oriented_lower_of_sign_true
      ε A e j hs]
    unfold flattenedAnnularSignedLower
    simp [signedGridLower, signedGridUpper, hs] at hlowerIcc ⊢
    linarith

theorem flattenedAnnular_oriented_lower_lt_upper
    {ε A : ℝ} (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) :
    gaussPrescribedParityOrientedLower
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j <
      gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j := by
  have hstep :=
    intervalGridPoint_strictMono_step
      (signedGridLower_lt_upper hεA (e j).1.sign)
      hgrid (k := (e j).1.signed.1)
  cases hs : (e j).1.sign
  · rw [flattenedAnnular_oriented_lower_of_sign_false
      ε A e j hs,
      flattenedAnnular_oriented_upper_of_sign_false
        ε A e j hs]
    unfold flattenedAnnularSignedLower flattenedAnnularSignedUpper
    simpa [hs] using! (neg_lt_neg hstep)
  · rw [flattenedAnnular_oriented_lower_of_sign_true
      ε A e j hs,
      flattenedAnnular_oriented_upper_of_sign_true
        ε A e j hs]
    unfold flattenedAnnularSignedLower flattenedAnnularSignedUpper
    simpa [hs] using! hstep

theorem flattenedAnnular_oriented_upper_le
    {ε A : ℝ} (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) :
    gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j ≤ A := by
  have hactive : 0 < k (e j).1 := by
    have hj := (e j).2.isLt
    omega
  have hidx : (e j).1.signed.1 + 1 ≤ grid :=
    Nat.succ_le_iff.mpr (hsigned (e j).1 hactive)
  have hlowerIcc :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA (e j).1.sign).le
      hgrid (Nat.le_of_lt (hsigned (e j).1 hactive))
  have hupperIcc :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA (e j).1.sign).le
      hgrid hidx
  cases hs : (e j).1.sign
  · rw [flattenedAnnular_oriented_upper_of_sign_false
      ε A e j hs]
    unfold flattenedAnnularSignedLower
    simp [signedGridLower, signedGridUpper, hs] at hlowerIcc ⊢
    linarith
  · rw [flattenedAnnular_oriented_upper_of_sign_true
      ε A e j hs]
    unfold flattenedAnnularSignedUpper
    simp only [ge_iff_le] at hupperIcc ⊢
    exact hupperIcc.2

theorem flattenedAnnular_oriented_product_eq
    (ε A : ℝ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    (∏ j,
      (gaussPrescribedParityOrientedUpper
            (flattenedAnnularParity e)
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e) j -
        gaussPrescribedParityOrientedLower
            (flattenedAnnularParity e)
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e) j) /
          Real.log 2) =
      annularOccurrenceSignedDensity ε A k := by
  simp_rw [flattenedAnnular_oriented_width]
  exact e.prod_comp (fun z : GaussPrefixMixedOccurrence k ↦
    (intervalGridPoint
          (signedGridLower ε A z.1.sign)
          (signedGridUpper ε A z.1.sign)
          grid (z.1.signed.1 + 1) -
      intervalGridPoint
          (signedGridLower ε A z.1.sign)
          (signedGridUpper ε A z.1.sign)
          grid z.1.signed.1) / Real.log 2)

theorem tendsto_annularCanonicalGaussZeroMode
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid) :
    Tendsto
      (fun N ↦
        aggregateGaussMovingSignedMarkedFourierTupleSum
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          N (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun _e _j ↦ 0)
          (fun e ↦ canonicalAnnularGridTupleFamily N k e))
      atTop
      (nhds (((annularOccurrenceTimeDensity k *
        annularOccurrenceSignedDensity ε A k : ℝ)) : ℂ)) := by
  refine
    tendsto_aggregateGaussMovingSignedMarkedFourierTupleSum_zero
      (β := Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (A := A)
      (density := annularOccurrenceTimeDensity k)
      (common := annularOccurrenceSignedDensity ε A k)
      hr (fun N ↦ N) (fun N ↦ Real.log (N : ℝ))
        tendsto_log_natCast_atTop
      (fun e ↦ flattenedAnnularSignedLower ε A e)
      (fun e ↦ flattenedAnnularSignedUpper ε A e)
      (fun e ↦ flattenedAnnularParity e)
      (hε.le.trans hεA.le)
      ?_ ?_ ?_ ?_
      annularSeparationGap
      tendsto_annularSeparationGap_atTop
      ?_
      (fun N e ↦ canonicalAnnularGridTupleFamily N k e)
      ?_ ?_ ?_ ?_
  · exact fun e j ↦
      flattenedAnnular_oriented_lower_pos
        hε hεA hgrid hsigned e j
  · exact fun e j ↦
      flattenedAnnular_oriented_lower_lt_upper
        hεA hgrid e j
  · exact fun e j ↦
      flattenedAnnular_oriented_upper_le
        hεA hgrid hsigned e j
  · exact flattenedAnnular_oriented_product_eq ε A
  · filter_upwards
      [tendsto_annularSeparationGap_atTop.eventually_gt_atTop 0] with
      N hN
    exact hN
  · exact fun N e t ht ↦
      canonicalAnnularGridTupleFamily_chronological N k e t ht
  · exact fun N e t ht j ↦
      canonicalAnnularGridTupleFamily_parity N k e t ht j
  · simpa only [aggregateTupleFamilyCard] using!
      tendsto_totalCanonicalAnnularGridTupleCard_density
        hgrid k hr htime
  · simpa only [aggregateShortTupleFamilyCard] using!
      tendsto_totalShortCanonicalAnnularGridTupleCard_sqrt_density_zero
        hgrid k hr htime

end

end Erdos1002
