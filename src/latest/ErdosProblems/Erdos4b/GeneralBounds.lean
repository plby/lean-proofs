/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralDiscrepancy

/-!
# Size bounds for general lcm moduli

The generalized CRT period is an lcm, hence it divides the product of the
four underlying divisor-tuple products.  In particular its size is bounded
by `RD^2 RE^2`, independently of the number of coordinates.  This supplies
the modulus-cutoff side of the Bombieri--Vinogradov interface.
-/

namespace Erdos4b

open scoped BigOperators

noncomputable section

/-- The lcm period of the complete pinned coordinate system divides the
product of the four tuple products. -/
theorem pinnedGeneralCrtModulus_dvd_divisorTupleProducts
    {H : Finset ℕ} (d e d' e' : H → ℕ) :
    pinnedGeneralCrtModulus H d e d' e' ∣
      BoundedGaps.Maynard.divisorTupleProduct H d *
        BoundedGaps.Maynard.divisorTupleProduct H d' *
        BoundedGaps.Maynard.divisorTupleProduct H e *
        BoundedGaps.Maynard.divisorTupleProduct H e' := by
  let modulus : PinnedGeneralCrtIndex H → ℕ :=
    pinnedGeneralCrtCoordinateModulus H d e d' e'
  have hlcm : (Finset.univ : Finset (PinnedGeneralCrtIndex H)).lcm modulus ∣
      ∏ i : PinnedGeneralCrtIndex H, modulus i :=
    Finset.lcm_dvd_prod Finset.univ modulus
  have hD : (∏ h : H, Nat.lcm (d h) (d' h)) ∣
      BoundedGaps.Maynard.divisorTupleProduct H d *
        BoundedGaps.Maynard.divisorTupleProduct H d' := by
    have hpoint : (∏ h : H, Nat.lcm (d h) (d' h)) ∣
        ∏ h : H, d h * d' h := by
      apply Finset.prod_dvd_prod_of_dvd
      intro h hh
      exact Nat.lcm_dvd_mul _ _
    simpa [BoundedGaps.Maynard.divisorTupleProduct,
      Finset.prod_mul_distrib] using hpoint
  have hE : (∏ h : H, Nat.lcm (e h) (e' h)) ∣
      BoundedGaps.Maynard.divisorTupleProduct H e *
        BoundedGaps.Maynard.divisorTupleProduct H e' := by
    have hpoint : (∏ h : H, Nat.lcm (e h) (e' h)) ∣
        ∏ h : H, e h * e' h := by
      apply Finset.prod_dvd_prod_of_dvd
      intro h hh
      exact Nat.lcm_dvd_mul _ _
    simpa [BoundedGaps.Maynard.divisorTupleProduct,
      Finset.prod_mul_distrib] using hpoint
  have hcoordinates : (∏ i : PinnedGeneralCrtIndex H, modulus i) ∣
      BoundedGaps.Maynard.divisorTupleProduct H d *
        BoundedGaps.Maynard.divisorTupleProduct H d' *
        BoundedGaps.Maynard.divisorTupleProduct H e *
        BoundedGaps.Maynard.divisorTupleProduct H e' := by
    rw [Fintype.prod_sum_type]
    have hmul := Nat.mul_dvd_mul hD hE
    simpa only [modulus, pinnedGeneralCrtCoordinateModulus,
      largeGapCrtModulus, mul_assoc] using hmul
  exact hlcm.trans hcoordinates

/-- Radius-only upper bound for every general pinned lcm modulus. -/
theorem pinnedGeneralCrtModulus_le_radius_product
    {H : Finset ℕ} {RD RE W m : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e') :
    pinnedGeneralCrtModulus H d e d' e' ≤ RD * RD * RE * RE := by
  let Pd := BoundedGaps.Maynard.divisorTupleProduct H d
  let Pd' := BoundedGaps.Maynard.divisorTupleProduct H d'
  let Pe := BoundedGaps.Maynard.divisorTupleProduct H e
  let Pe' := BoundedGaps.Maynard.divisorTupleProduct H e'
  have hPd : 0 < Pd := Nat.pos_of_ne_zero hd.2.2.ne_zero
  have hPd' : 0 < Pd' := Nat.pos_of_ne_zero hd'.2.2.ne_zero
  have hPe : 0 < Pe := Nat.pos_of_ne_zero he.2.2.ne_zero
  have hPe' : 0 < Pe' := Nat.pos_of_ne_zero he'.2.2.ne_zero
  have hdiv : pinnedGeneralCrtModulus H d e d' e' ∣ Pd * Pd' * Pe * Pe' := by
    simpa [Pd, Pd', Pe, Pe'] using
      pinnedGeneralCrtModulus_dvd_divisorTupleProducts d e d' e'
  have hle : pinnedGeneralCrtModulus H d e d' e' ≤ Pd * Pd' * Pe * Pe' :=
    Nat.le_of_dvd (by positivity) hdiv
  have hDD : Pd * Pd' ≤ RD * RD :=
    Nat.mul_le_mul hd.1.le hd'.1.le
  have hEE : Pe * Pe' ≤ RE * RE :=
    Nat.mul_le_mul he.1.le he'.1.le
  calc
    pinnedGeneralCrtModulus H d e d' e' ≤ Pd * Pd' * Pe * Pe' := hle
    _ = (Pd * Pd') * (Pe * Pe') := by ring
    _ ≤ (RD * RD) * (RE * RE) := Nat.mul_le_mul hDD hEE
    _ = RD * RD * RE * RE := by ring

/-- Every modulus occurring in the finite quadruple support inherits the
same radius-product bound. -/
theorem pinnedGeneralModulusSet_subset_Icc_radiusProduct
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m : ℕ}
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e) :
    pinnedGeneralModulusSet D E ⊆ Finset.Icc 1 (RD * RD * RE * RE) := by
  intro M hM
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hM
  have hiData := Finset.mem_product.mp hi
  have hiTail := Finset.mem_product.mp hiData.2
  have hiTail' := Finset.mem_product.mp hiTail.2
  have hpos : 0 < pinnedGeneralIndexModulus i := by
    apply pinnedGeneralCrtModulus_pos
    · intro h
      exact BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard
        (hD i.1 hiData.1) (hD i.2.2.1 hiTail'.1) h
    · intro h
      exact BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard
        (hE i.2.1 hiTail.1) (hE i.2.2.2 hiTail'.2) h
  apply Finset.mem_Icc.mpr
  refine ⟨hpos, ?_⟩
  exact pinnedGeneralCrtModulus_le_radius_product
    (hD i.1 hiData.1) (hD i.2.2.1 hiTail'.1)
    (hE i.2.1 hiTail.1) (hE i.2.2.2 hiTail'.2)

theorem pinnedGeneralModulusSet_subset_modulusCutoff
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m x : ℕ}
    {theta : ℝ}
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (hcut : RD * RD * RE * RE ≤
      BoundedGaps.Maynard.modulusCutoff theta x) :
    pinnedGeneralModulusSet D E ⊆
      Finset.Icc 1 (BoundedGaps.Maynard.modulusCutoff theta x) := by
  intro M hM
  have hbounds := Finset.mem_Icc.mp
    (pinnedGeneralModulusSet_subset_Icc_radiusProduct hD hE hM)
  exact Finset.mem_Icc.mpr ⟨hbounds.1, hbounds.2.trans hcut⟩

end

end Erdos4b
