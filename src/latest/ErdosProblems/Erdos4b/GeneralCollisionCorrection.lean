/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.PinnedGeneralCollisionDecomposition

/-!
# Auxiliary-matrix form of the compatible collision correction

The exact decompositions in `GeneralCollisionDecomposition` isolate the
gain produced by a compatible cross-family gcd.  Here that gain is rewritten
as the finite sum over the nontrivial auxiliary matrices.  This is the form
consumed by the rough reciprocal-square tail estimates.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

noncomputable local instance erdos4GeneralCollisionCorrectionDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- For a compatible standard quadruple, the collision factor minus its
all-one contribution is precisely the sum over nontrivial affine-compatible
auxiliary matrices. -/
theorem crossCoordinateTotientSumProduct_sub_one_eq_auxiliaryTail
    {H : Finset ℕ} {RD RE W m q : ℕ} {d e d' e' : H → ℕ}
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e') :
    crossCoordinateTotientSumProduct H d e d' e' - 1 =
      ∑ a ∈
          ((Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')).erase
            (oneCrossAuxiliaryDivisors
              (fun h ↦ Nat.lcm_pos
                (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)
                (Nat.pos_of_ne_zero (hd'.coordinate_squarefree h).ne_zero))
              (fun h ↦ Nat.lcm_pos
                (Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero)
                (Nat.pos_of_ne_zero (he'.coordinate_squarefree h).ne_zero))))
            |>.filter (CrossAuxiliaryAffineCompatible m q),
        crossAuxiliaryTotientWeight a := by
  classical
  have hwithin :=
    withinFamilyCrossCoordinateCoprime_of_coordinateCompatible
      hm hq hRDq hREq hcover hd hd' he he' hcompat
  have hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)) := by
    intro a b hab
    exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
      (hd.coordinates_coprime hab) (hwithin.1 hab).1
      (hwithin.1 hab).2 (hd'.coordinates_coprime hab)
  have hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b)) := by
    intro a b hab
    exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
      (he.coordinates_coprime hab) (hwithin.2 hab).1
      (hwithin.2 hab).2 (he'.coordinates_coprime hab)
  let hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h) := fun h ↦
    Nat.lcm_pos
      (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (hd'.coordinate_squarefree h).ne_zero)
  let hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h) := fun h ↦
    Nat.lcm_pos
      (Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero)
      (Nat.pos_of_ne_zero (he'.coordinate_squarefree h).ne_zero)
  have hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)) := by
    intro h
    apply Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (e h) (e' h))
    exact (Nat.Coprime.of_dvd_right
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e h)
      (Nat.Coprime.of_dvd_left (dvd_mul_left m W) he.2.1.symm)).mul_right
      (Nat.Coprime.of_dvd_right
        (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product e' h)
        (Nat.Coprime.of_dvd_left (dvd_mul_left m W) he'.2.1.symm))
  let one := oneCrossAuxiliaryDivisors hDpos hEpos
  let S := (Finset.univ :
    Finset (CrossAuxiliaryDivisors H d e d' e')).erase one
  have hall : ∀ a : CrossAuxiliaryDivisors H d e d' e',
      CrossAuxiliaryAffineCompatible m q a := by
    intro a
    exact crossAuxiliaryAffineCompatible_of_coordinateCompatible
      hDpos hEpos hmE hDD hEE hcompat a
  have hfilter : S.filter (CrossAuxiliaryAffineCompatible m q) = S := by
    exact Finset.filter_eq_self.mpr (fun a ha ↦ hall a)
  have honeMem : one ∈
      (Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')) :=
    Finset.mem_univ one
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')))
    (f := crossAuxiliaryTotientWeight) honeMem
  rw [crossCoordinateTotientSumProduct_eq_auxiliarySum]
  change _ = ∑ a ∈ S.filter (CrossAuxiliaryAffineCompatible m q), _
  rw [hfilter]
  have honeWeight : crossAuxiliaryTotientWeight one = 1 := by
    exact crossAuxiliaryTotientWeight_one hDpos hEpos
  rw [honeWeight] at hsplit
  linarith

/-- The canonical auxiliary-prime residue of a compatible pinned system
makes every cross auxiliary divisor satisfy the same affine congruence as
in the normalization kernel.  The actual shift parameter is `W * r`. -/
theorem crossAuxiliaryAffineCompatible_of_pinnedGeneralRestricted
    {H : Finset ℕ} {RD RE W m p : ℕ} (h : H)
    {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hm : 0 < m) (hp : p.Prime)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hrest : PinnedGeneralRestricted W m p h d e d' e')
    (a : CrossAuxiliaryDivisors H d e d' e') :
    CrossAuxiliaryAffineCompatible m
      (W * pinnedGeneralCrtResidue H p W m h d e d' e'
        hrest.2.2.2.2) a := by
  let hc : PinnedGeneralCrtCompatible H p W m h d e d' e' :=
    hrest.2.2.2.2
  let r := pinnedGeneralCrtResidue H p W m h d e d' e' hc
  have hcoverWM :
      BoundedGaps.Maynard.CoversShiftDifferencePrimes H (W * m) :=
    coversShiftDifferencePrimes_of_dvd (dvd_mul_right W m) hcover
  intro ba
  let s := (a ba).1
  let D := Nat.lcm (d ba.2) (d' ba.2)
  let E := Nat.lcm (e ba.1) (e' ba.1)
  change m * (ba.2.1 * (W * r)) + 1 ≡
    m * (ba.1.1 * (W * r)) [MOD s]
  have hsGcd : s ∣ Nat.gcd D E := by
    exact (Nat.mem_divisors.mp (a ba).2).1
  have hsD : s ∣ D := hsGcd.trans (Nat.gcd_dvd_left D E)
  have hsE : s ∣ E := hsGcd.trans (Nat.gcd_dvd_right D E)
  by_cases hfirstPinned : ba.2 = h
  · have hDone : D = 1 := by
      dsimp only [D]
      rw [hfirstPinned, hrest.1, hrest.2.1]
      simp
    have hsOne : s = 1 := Nat.dvd_one.mp (hDone ▸ hsD)
    rw [hsOne]
    exact Nat.modEq_one
  by_cases hcompPinned : ba.1 = h
  · have hEone : E = 1 := by
      dsimp only [E]
      rw [hcompPinned, hrest.2.2.1, hrest.2.2.2.1]
      simp
    have hsOne : s = 1 := Nat.dvd_one.mp (hEone ▸ hsE)
    rw [hsOne]
    exact Nat.modEq_one
  have hrD : r ≡ pinnedCoordinateResidue p W h.1 ba.2.1 D [MOD D] := by
    simpa [r, hc, pinnedGeneralCrtResidue,
      pinnedGeneralCrtCoordinateModulus,
      pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
      BoundedGaps.Maynard.divisorTupleLcm, D, hfirstPinned] using
      (generalCrtResidue_spec Finset.univ
        (pinnedGeneralCrtCoordinateModulus H d e d' e')
        (pinnedGeneralCrtCoordinateResidue H p W m h d e d' e') hc
        (Sum.inl ba.2) (by simp))
  have hrE : r ≡
      pinnedCoordinateResidue (m * p - 1) (W * m) h.1 ba.1.1 E
        [MOD E] := by
    simpa [r, hc, pinnedGeneralCrtResidue,
      pinnedGeneralCrtCoordinateModulus,
      pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
      BoundedGaps.Maynard.divisorTupleLcm, E, hcompPinned] using
      (generalCrtResidue_spec Finset.univ
        (pinnedGeneralCrtCoordinateModulus H d e d' e')
        (pinnedGeneralCrtCoordinateResidue H p W m h d e d' e') hc
        (Sum.inr ba.1) (by simp))
  have hfirst :=
    (modEq_pinnedCoordinateResidue_iff_affine hd hd' hcover
      hfirstPinned).mp hrD
  have hcomp :=
    (modEq_pinnedCoordinateResidue_iff_affine he he' hcoverWM
      hcompPinned).mp hrE
  have hfirstS := (hfirst.of_dvd hsD).mul_left m
  have hcompS := hcomp.of_dvd hsE
  have hmp : 1 ≤ m * p := by
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero hm.ne' hp.ne_zero)
  have hcombined :
      (m * p - 1) + (m * (ba.2.1 * (W * r)) + 1) ≡
        (m * p - 1) + m * (ba.1.1 * (W * r)) [MOD s] := by
    calc
      (m * p - 1) + (m * (ba.2.1 * (W * r)) + 1) =
          m * (p + ba.2.1 * (W * r)) := by
            rw [Nat.mul_add]
            omega
      _ ≡ m * (h.1 * (W * r)) [MOD s] := by
            simpa [D] using hfirstS
      _ = h.1 * ((W * m) * r) := by ring
      _ ≡ (m * p - 1) + ba.1.1 * ((W * m) * r) [MOD s] := by
            simpa [E] using hcompS.symm
      _ = (m * p - 1) + m * (ba.1.1 * (W * r)) := by ring
  exact Nat.ModEq.add_left_cancel' (m * p - 1) hcombined

/-- Pinned counterpart of
`crossCoordinateTotientSumProduct_sub_one_eq_auxiliaryTail`. -/
theorem crossCoordinateS2GAggregate_sub_one_eq_auxiliaryTail
    {H : Finset ℕ} {RD RE W m p Y : ℕ} (h : H)
    {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p)
    (hrest : PinnedGeneralRestricted W m p h d e d' e') :
    crossCoordinateS2GAggregate H d e d' e' - 1 =
      let hDpos : ∀ j : H, 0 < Nat.lcm (d j) (d' j) := fun j ↦
        Nat.lcm_pos
          (Nat.pos_of_ne_zero (hd.coordinate_squarefree j).ne_zero)
          (Nat.pos_of_ne_zero (hd'.coordinate_squarefree j).ne_zero)
      let hEpos : ∀ j : H, 0 < Nat.lcm (e j) (e' j) := fun j ↦
        Nat.lcm_pos
          (Nat.pos_of_ne_zero (he.coordinate_squarefree j).ne_zero)
          (Nat.pos_of_ne_zero (he'.coordinate_squarefree j).ne_zero)
      let r := pinnedGeneralCrtResidue H p W m h d e d' e'
        hrest.2.2.2.2
      ∑ a ∈
          ((Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')).erase
            (oneCrossAuxiliaryDivisors hDpos hEpos)).filter
              (CrossAuxiliaryAffineCompatible m (W * r)),
        crossAuxiliaryS2GWeight a := by
  classical
  let hDpos : ∀ j : H, 0 < Nat.lcm (d j) (d' j) := fun j ↦
    Nat.lcm_pos
      (Nat.pos_of_ne_zero (hd.coordinate_squarefree j).ne_zero)
      (Nat.pos_of_ne_zero (hd'.coordinate_squarefree j).ne_zero)
  let hEpos : ∀ j : H, 0 < Nat.lcm (e j) (e' j) := fun j ↦
    Nat.lcm_pos
      (Nat.pos_of_ne_zero (he.coordinate_squarefree j).ne_zero)
      (Nat.pos_of_ne_zero (he'.coordinate_squarefree j).ne_zero)
  let r := pinnedGeneralCrtResidue H p W m h d e d' e'
    hrest.2.2.2.2
  obtain ⟨hDD, hEE⟩ :=
    withinFamilyLcm_pairwise_of_pinnedGeneralRestricted h hd hd' he he'
      hcover hp hRDp hREY hpre hrest
  have hDsq : ∀ j : H, Squarefree (Nat.lcm (d j) (d' j)) := fun j ↦
    BoundedGaps.Maynard.squarefree_lcm
      (hd.coordinate_squarefree j) (hd'.coordinate_squarefree j)
  have hEsq : ∀ j : H, Squarefree (Nat.lcm (e j) (e' j)) := fun j ↦
    BoundedGaps.Maynard.squarefree_lcm
      (he.coordinate_squarefree j) (he'.coordinate_squarefree j)
  let one := oneCrossAuxiliaryDivisors hDpos hEpos
  let S := (Finset.univ :
    Finset (CrossAuxiliaryDivisors H d e d' e')).erase one
  have hall : ∀ a : CrossAuxiliaryDivisors H d e d' e',
      CrossAuxiliaryAffineCompatible m (W * r) a := by
    intro a
    simpa [r] using
      (crossAuxiliaryAffineCompatible_of_pinnedGeneralRestricted h
        hd hd' he he' hm hp hcover hrest a)
  have hfilter : S.filter (CrossAuxiliaryAffineCompatible m (W * r)) = S := by
    exact Finset.filter_eq_self.mpr (fun a ha ↦ hall a)
  have honeMem : one ∈
      (Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')) :=
    Finset.mem_univ one
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')))
    (f := crossAuxiliaryS2GWeight) honeMem
  rw [crossCoordinateS2GAggregate_eq_product hDsq hEsq hDD hEE,
    crossCoordinateS2GSumProduct_eq_auxiliarySum]
  change _ = ∑ a ∈ S.filter (CrossAuxiliaryAffineCompatible m (W * r)), _
  rw [hfilter]
  have honeWeight : crossAuxiliaryS2GWeight one = 1 := by
    exact crossAuxiliaryS2GWeight_one hDpos hEpos
  rw [honeWeight] at hsplit
  linarith

end

end Erdos4b
