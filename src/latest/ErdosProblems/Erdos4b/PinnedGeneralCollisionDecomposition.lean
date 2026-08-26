/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCollisionDecomposition

/-!
# Leading tensor term and corrections in the pinned kernel

This is the pinned counterpart of `GeneralCollisionDecomposition`.  The
ordinary restricted `S₂` tensor is separated from the compatible
`g(p)=p-2` cross-collision amplification and from the tensor terms deleted
by an incompatible affine CRT system.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

noncomputable local instance erdos4PinnedCollisionDecompositionDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Pinned coordinates are one and both divisor-pair families have the
ordinary within-family cross-coordinate compatibility. -/
def PinnedWithinFamilyRestricted
    {H : Finset ℕ} (h : H) (d e d' e' : H → ℕ) : Prop :=
  d h = 1 ∧ d' h = 1 ∧ e h = 1 ∧ e' h = 1 ∧
    WithinFamilyCrossCoordinateCoprime d e d' e'

/-- A genuinely contributing pinned quadruple belongs to the pinned tensor
base. -/
theorem pinnedWithinFamilyRestricted_of_pinnedGeneralRestricted
    {H : Finset ℕ} {RD RE W m p Y : ℕ} (h : H)
    {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p)
    (hrest : PinnedGeneralRestricted W m p h d e d' e') :
    PinnedWithinFamilyRestricted h d e d' e' := by
  obtain ⟨hDD, hEE⟩ :=
    withinFamilyLcm_pairwise_of_pinnedGeneralRestricted h hd hd' he he'
      hcover hp hRDp hREY hpre hrest
  refine ⟨hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1, ?_⟩
  constructor
  · intro a b hab
    exact ⟨
      Nat.Coprime.of_dvd (Nat.dvd_lcm_left (d a) (d' a))
        (Nat.dvd_lcm_right (d b) (d' b)) (hDD hab),
      Nat.Coprime.of_dvd (Nat.dvd_lcm_right (d a) (d' a))
        (Nat.dvd_lcm_left (d b) (d' b)) (hDD hab)⟩
  · intro a b hab
    exact ⟨
      Nat.Coprime.of_dvd (Nat.dvd_lcm_left (e a) (e' a))
        (Nat.dvd_lcm_right (e b) (e' b)) (hEE hab),
      Nat.Coprime.of_dvd (Nat.dvd_lcm_right (e a) (e' a))
        (Nat.dvd_lcm_left (e b) (e' b)) (hEE hab)⟩

/-- Pinned tensor-base kernel before evaluating its two restricted faces. -/
noncomputable def pinnedGeneralTensorBaseKernel
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) : ℝ :=
  ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if PinnedWithinFamilyRestricted h d e d' e' then
      lambda d e * lambda d' e' /
        ((Nat.totient (firstLcmProduct H d d') : ℝ) *
          Nat.totient (companionLcmProduct H e e'))
    else 0

/-- Compatible pinned amplification beyond the unit cross-collision term. -/
noncomputable def pinnedGeneralCompatibleAmplificationCorrection
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m p : ℕ) : ℝ :=
  ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if PinnedGeneralRestricted W m p h d e d' e' then
      lambda d e * lambda d' e' *
        (crossCoordinateS2GAggregate H d e d' e' - 1) /
          ((Nat.totient (firstLcmProduct H d d') : ℝ) *
            Nat.totient (companionLcmProduct H e e'))
    else 0

/-- Pinned tensor-base mass deleted by affine CRT incompatibility. -/
noncomputable def pinnedGeneralIncompatibleRemovalCorrection
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m p : ℕ) : ℝ :=
  ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if PinnedWithinFamilyRestricted h d e d' e' ∧
        ¬PinnedGeneralRestricted W m p h d e d' e' then
      lambda d e * lambda d' e' /
        ((Nat.totient (firstLcmProduct H d d') : ℝ) *
          Nat.totient (companionLcmProduct H e e'))
    else 0

/-- Exact pinned-kernel split on the two standard supports. -/
theorem pinnedGeneralS2GCollisionKernel_eq_tensorBase_add_corrections_standard
    (H : Finset ℕ) (RD RE W m p Y : ℕ)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p) :
    pinnedGeneralS2GCollisionKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        lambda W m p =
      pinnedGeneralTensorBaseKernel H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          lambda +
        pinnedGeneralCompatibleAmplificationCorrection H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          lambda W m p -
        pinnedGeneralIncompatibleRemovalCorrection H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          lambda W m p := by
  classical
  unfold pinnedGeneralS2GCollisionKernel pinnedGeneralTensorBaseKernel
    pinnedGeneralCompatibleAmplificationCorrection
    pinnedGeneralIncompatibleRemovalCorrection
  simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hdMem
  apply Finset.sum_congr rfl
  intro e heMem
  apply Finset.sum_congr rfl
  intro d' hd'Mem
  apply Finset.sum_congr rfl
  intro e' he'Mem
  let hd := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdMem
  let hd' := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd'Mem
  let he := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support heMem
  let he' := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'Mem
  by_cases hr : PinnedGeneralRestricted W m p h d e d' e'
  · have hbase := pinnedWithinFamilyRestricted_of_pinnedGeneralRestricted
      h hd hd' he he' hcover hp hRDp hREY hpre hr
    simp [hr, hbase]
    ring
  · by_cases hbase : PinnedWithinFamilyRestricted h d e d' e'
    · simp [hr, hbase]
    · simp [hr, hbase]

/-- On Maynard support, the totient of the product of the coordinatewise
LCMs factors coordinatewise.  This is the only arithmetic input needed to
identify the pinned tensor base with the two ordinary restricted `S₂`
faces. -/
theorem totient_coordinateLcmProduct_eq_product
    {H : Finset ℕ} {R W : ℕ} {d d' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d')
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d') :
    Nat.totient (∏ h : H, Nat.lcm (d h) (d' h)) =
      ∏ h : H, Nat.totient
        (BoundedGaps.Maynard.divisorTupleLcm H d d' h) := by
  classical
  apply BoundedGaps.Maynard.totient_finsetProd_of_pairwise_coprime
  intro a ha b hb hab
  exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
    (hd.coordinates_coprime hab) (hcross hab).1
    (hcross hab).2 (hd'.coordinates_coprime hab)

/-- The first-family aggregate totient is its coordinatewise product. -/
theorem totient_firstLcmProduct_eq_product
    {H : Finset ℕ} {R W : ℕ} {d d' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d')
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d') :
    Nat.totient (firstLcmProduct H d d') =
      ∏ h : H, Nat.totient
        (BoundedGaps.Maynard.divisorTupleLcm H d d' h) := by
  simpa [firstLcmProduct] using
    totient_coordinateLcmProduct_eq_product hd hd' hcross

/-- The companion-family aggregate totient is its coordinatewise product. -/
theorem totient_companionLcmProduct_eq_product
    {H : Finset ℕ} {R W : ℕ} {e e' : H → ℕ}
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e')
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e') :
    Nat.totient (companionLcmProduct H e e') =
      ∏ h : H, Nat.totient
        (BoundedGaps.Maynard.divisorTupleLcm H e e' h) := by
  simpa [companionLcmProduct] using
    totient_coordinateLcmProduct_eq_product he he' hcross

/-- For tensor coefficients, the pinned tensor base is exactly the sum of
products of the two ordinary restricted pinned kernels. -/
theorem pinnedGeneralTensorBaseKernel_tensor
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m : ℕ}
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (a b : (H → ℕ) → ℝ) :
    pinnedGeneralTensorBaseKernel H D E (fun d e => a d * b e) =
      ∑ h : H,
        rawPinnedPairTotientKernel D a h *
          rawPinnedPairTotientKernel E b h := by
  classical
  unfold pinnedGeneralTensorBaseKernel rawPinnedPairTotientKernel
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d hdMem
  apply Finset.sum_congr rfl
  intro e heMem
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d' hd'Mem
  apply Finset.sum_congr rfl
  intro e' he'Mem
  by_cases hbase : PinnedWithinFamilyRestricted h d e d' e'
  · rw [if_pos hbase]
    have hDpred : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' ∧
        d h = 1 ∧ d' h = 1 :=
      ⟨hbase.2.2.2.2.1, hbase.1, hbase.2.1⟩
    have hEpred : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' ∧
        e h = 1 ∧ e' h = 1 :=
      ⟨hbase.2.2.2.2.2, hbase.2.2.1, hbase.2.2.2.1⟩
    rw [if_pos hDpred, if_pos hEpred]
    have htotD := totient_firstLcmProduct_eq_product
      (hD d hdMem) (hD d' hd'Mem) hDpred.1
    have htotE := totient_companionLcmProduct_eq_product
      (hE e heMem) (hE e' he'Mem) hEpred.1
    have htotDR : (Nat.totient (firstLcmProduct H d d') : ℝ) =
        ∏ j : H, (Nat.totient
          (BoundedGaps.Maynard.divisorTupleLcm H d d' j) : ℝ) := by
      exact_mod_cast htotD
    have htotER : (Nat.totient (companionLcmProduct H e e') : ℝ) =
        ∏ j : H, (Nat.totient
          (BoundedGaps.Maynard.divisorTupleLcm H e e' j) : ℝ) := by
      exact_mod_cast htotE
    rw [htotDR, htotER]
    ring
  · rw [if_neg hbase]
    by_cases hDpred :
        BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' ∧
          d h = 1 ∧ d' h = 1
    · by_cases hEpred :
          BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' ∧
            e h = 1 ∧ e' h = 1
      · exfalso
        apply hbase
        exact ⟨hDpred.2.1, hDpred.2.2, hEpred.2.1, hEpred.2.2,
          hDpred.1, hEpred.1⟩
      · simp [hDpred, hEpred]
    · simp [hDpred]

/-- End-to-end exact decomposition of the genuine pinned arithmetic kernel.
This theorem is deliberately stated before any asymptotic estimate: it shows
that the only difference from the two ordinary restricted Maynard faces is
the compatible affine amplification and the incompatible-removal term. -/
theorem pinnedGeneralArithmeticKernel_eq_tensorBase_add_corrections_standard
    (H : Finset ℕ) (RD RE W m p Y : ℕ)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p) :
    pinnedGeneralArithmeticKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        lambda W m p =
      pinnedGeneralTensorBaseKernel H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          lambda +
        pinnedGeneralCompatibleAmplificationCorrection H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          lambda W m p -
        pinnedGeneralIncompatibleRemovalCorrection H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          lambda W m p := by
  rw [pinnedGeneralArithmeticKernel_eq_s2GCollisionKernel_standard
    H RD RE W m p Y lambda hcover hp hRDp hREY hpre]
  exact pinnedGeneralS2GCollisionKernel_eq_tensorBase_add_corrections_standard
    H RD RE W m p Y lambda hcover hp hRDp hREY hpre

/-- Tensor-coefficient form of the preceding decomposition.  The leading
term is now literally a sum of products of the two ordinary pinned faces;
no doubled Euler-product assertion is hidden in this identity. -/
theorem pinnedGeneralArithmeticKernel_tensor_eq_faces_add_corrections_standard
    (H : Finset ℕ) (RD RE W m p Y : ℕ)
    (a b : (H → ℕ) → ℝ)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p) :
    pinnedGeneralArithmeticKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        (fun d e ↦ a d * b e) W m p =
      (∑ h : H,
        rawPinnedPairTotientKernel
            (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W) a h *
          rawPinnedPairTotientKernel
            (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m)) b h) +
        pinnedGeneralCompatibleAmplificationCorrection H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          (fun d e ↦ a d * b e) W m p -
        pinnedGeneralIncompatibleRemovalCorrection H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          (fun d e ↦ a d * b e) W m p := by
  rw [pinnedGeneralArithmeticKernel_eq_tensorBase_add_corrections_standard
    H RD RE W m p Y (fun d e ↦ a d * b e) hcover hp hRDp hREY hpre]
  rw [pinnedGeneralTensorBaseKernel_tensor
    (fun d hd ↦ BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd)
    (fun e he ↦ BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he)
    a b]

end

end Erdos4b
