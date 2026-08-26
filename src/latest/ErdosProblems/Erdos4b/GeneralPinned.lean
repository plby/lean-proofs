/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCrt
import ErdosProblems.Erdos4b.FullPinned

/-!
# General pinned CRT systems for Erdős Problem 4

This is the prime-variable counterpart of `GeneralCrt.lean`.  It retains
shared factors between first and companion divisor coordinates and therefore
uses an lcm period instead of the product modulus from the separated-support
development.
-/

namespace Erdos4b

open scoped BigOperators

noncomputable section

noncomputable local instance generalPinnedPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

abbrev PinnedGeneralCrtIndex (H : Finset ℕ) := Sum H H

def pinnedGeneralCrtCoordinateModulus (H : Finset ℕ)
    (d e d' e' : H → ℕ) : PinnedGeneralCrtIndex H → ℕ :=
  largeGapCrtModulus H d e d' e'

noncomputable def pinnedGeneralCrtCoordinateResidue
    (H : Finset ℕ) (p W m : ℕ) (h : H)
    (d e d' e' : H → ℕ) : PinnedGeneralCrtIndex H → ℕ
  | Sum.inl j =>
      if j = h then 0 else
        pinnedCoordinateResidue p W h.1 j.1
          (BoundedGaps.Maynard.divisorTupleLcm H d d' j)
  | Sum.inr j =>
      if j = h then 0 else
        pinnedCoordinateResidue (m * p - 1) (W * m) h.1 j.1
          (BoundedGaps.Maynard.divisorTupleLcm H e e' j)

def PinnedGeneralCrtCompatible (H : Finset ℕ)
    (p W m : ℕ) (h : H) (d e d' e' : H → ℕ) : Prop :=
  GeneralCrtCompatible Finset.univ
    (pinnedGeneralCrtCoordinateModulus H d e d' e')
    (pinnedGeneralCrtCoordinateResidue H p W m h d e d' e')

def pinnedGeneralCrtModulus (H : Finset ℕ)
    (d e d' e' : H → ℕ) : ℕ :=
  generalCrtModulus Finset.univ
    (pinnedGeneralCrtCoordinateModulus H d e d' e')

noncomputable def pinnedGeneralCrtResidue
    (H : Finset ℕ) (p W m : ℕ) (h : H)
    (d e d' e' : H → ℕ)
    (hcompat : PinnedGeneralCrtCompatible H p W m h d e d' e') : ℕ :=
  generalCrtResidue Finset.univ
    (pinnedGeneralCrtCoordinateModulus H d e d' e')
    (pinnedGeneralCrtCoordinateResidue H p W m h d e d' e') hcompat

theorem pinnedGeneralCrtModulus_pos
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ j : H, 0 < Nat.lcm (d j) (d' j))
    (hEpos : ∀ j : H, 0 < Nat.lcm (e j) (e' j)) :
    0 < pinnedGeneralCrtModulus H d e d' e' := by
  apply generalCrtModulus_pos
  intro i hi
  cases i with
  | inl j => exact hDpos j
  | inr j => exact hEpos j

theorem pinnedGeneralCrtCompatible_iff_pairwise
    {H : Finset ℕ} (p W m : ℕ) (h : H)
    (d e d' e' : H → ℕ)
    (hDpos : ∀ j : H, 0 < Nat.lcm (d j) (d' j))
    (hEpos : ∀ j : H, 0 < Nat.lcm (e j) (e' j)) :
    PinnedGeneralCrtCompatible H p W m h d e d' e' ↔
      GeneralCrtPairwiseCompatible Finset.univ
        (pinnedGeneralCrtCoordinateModulus H d e d' e')
        (pinnedGeneralCrtCoordinateResidue H p W m h d e d' e') := by
  apply generalCrtCompatible_iff_pairwise
  intro i hi
  cases i with
  | inl j => exact hDpos j
  | inr j => exact hEpos j

/-- The canonical residue of a compatible pinned lcm system is reduced.
This is the general-overlap analogue of
`fullPinnedCrtResidue_coprime_modulus`: no coprimality between the two
divisor families is assumed. -/
theorem pinnedGeneralCrtResidue_coprime_modulus
    {H : Finset ℕ} {RD RE W m p Y : ℕ} (h : H)
    {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hdh : d h = 1) (hd'h : d' h = 1)
    (heh : e h = 1) (he'h : e' h = 1)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p)
    (hcompat : PinnedGeneralCrtCompatible H p W m h d e d' e') :
    (pinnedGeneralCrtResidue H p W m h d e d' e' hcompat).Coprime
      (pinnedGeneralCrtModulus H d e d' e') := by
  change
    (generalCrtResidue Finset.univ
      (pinnedGeneralCrtCoordinateModulus H d e d' e')
      (pinnedGeneralCrtCoordinateResidue H p W m h d e d' e')
      hcompat).Coprime
        (generalCrtModulus Finset.univ
          (pinnedGeneralCrtCoordinateModulus H d e d' e'))
  apply generalCrtResidue_coprime_modulus
  intro i hi
  cases i with
  | inl j =>
      by_cases hj : j = h
      · subst j
        simp [pinnedGeneralCrtCoordinateModulus,
          pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
          hdh, hd'h]
      · simpa [pinnedGeneralCrtCoordinateModulus,
          pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
          BoundedGaps.Maynard.divisorTupleLcm, hj] using
          (pinnedCoordinateResidue_coprime_lcm hd hd' hcover hp hRDp hj)
  | inr j =>
      by_cases hj : j = h
      · subst j
        simp [pinnedGeneralCrtCoordinateModulus,
          pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
          heh, he'h]
      · have hcoverWM :
            BoundedGaps.Maynard.CoversShiftDifferencePrimes H (W * m) :=
          coversShiftDifferencePrimes_of_dvd (dvd_mul_right W m) hcover
        simpa [pinnedGeneralCrtCoordinateModulus,
          pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
          BoundedGaps.Maynard.divisorTupleLcm, hj] using
          (pinnedCoordinateResidue_coprime_lcm_of_target he he' hcoverWM hj
            (companionTarget_coprime_lcm he he' hREY hpre j))

/-- Exact description of all auxiliary integers `q` for which a pinned
divisor quadruple contributes. -/
theorem modEq_pinnedGeneralCrtResidue_iff
    {H : Finset ℕ} {RD RE W m p q : ℕ}
    (h : H) {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hdh : d h = 1) (hd'h : d' h = 1)
    (heh : e h = 1) (he'h : e' h = 1)
    (hmargin : h.1 * (W * q) < p)
    (hcompat : PinnedGeneralCrtCompatible H p W m h d e d' e') :
    q ≡ pinnedGeneralCrtResidue H p W m h d e d' e' hcompat
          [MOD pinnedGeneralCrtModulus H d e d' e'] ↔
      largeGapDivisorCondition H m (W * q)
          (p - h.1 * (W * q)) d e ∧
        largeGapDivisorCondition H m (W * q)
          (p - h.1 * (W * q)) d' e' := by
  change GeneralCrtCompatible Finset.univ
    (pinnedGeneralCrtCoordinateModulus H d e d' e')
    (pinnedGeneralCrtCoordinateResidue H p W m h d e d' e') at hcompat
  change
    (q ≡ generalCrtResidue Finset.univ
        (pinnedGeneralCrtCoordinateModulus H d e d' e')
        (pinnedGeneralCrtCoordinateResidue H p W m h d e d' e') hcompat
      [MOD generalCrtModulus Finset.univ
        (pinnedGeneralCrtCoordinateModulus H d e d' e')]) ↔ _
  rw [modEq_generalCrtResidue_iff,
    largeGapDivisorCondition_pair_iff_lcm]
  constructor
  · intro hall j
    constructor
    · by_cases hj : j = h
      · subst j
        simp [hdh, hd'h]
      · exact (modEq_pinnedCoordinateResidue_iff hd hd' hcover hj
          hmargin.le).mp (by
            simpa [pinnedGeneralCrtCoordinateModulus,
              pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
              BoundedGaps.Maynard.divisorTupleLcm, hj] using
              hall (Sum.inl j) (Finset.mem_univ _))
    · by_cases hj : j = h
      · subst j
        simp [heh, he'h]
      · exact (modEq_companionPinnedCoordinateResidue_iff hm he he' hcover
          hj hmargin).mp (by
            simpa [pinnedGeneralCrtCoordinateModulus,
              pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
              BoundedGaps.Maynard.divisorTupleLcm, hj] using
              hall (Sum.inr j) (Finset.mem_univ _))
  · intro hdiv i hi
    cases i with
    | inl j =>
        by_cases hj : j = h
        · subst j
          simpa [pinnedGeneralCrtCoordinateModulus,
            pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
            hdh, hd'h] using (Nat.modEq_one (a := q) (b := 0))
        · simpa [pinnedGeneralCrtCoordinateModulus,
            pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
            BoundedGaps.Maynard.divisorTupleLcm, hj] using
            (modEq_pinnedCoordinateResidue_iff hd hd' hcover hj
              hmargin.le).mpr (hdiv j).1
    | inr j =>
        by_cases hj : j = h
        · subst j
          simpa [pinnedGeneralCrtCoordinateModulus,
            pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
            heh, he'h] using (Nat.modEq_one (a := q) (b := 0))
        · simpa [pinnedGeneralCrtCoordinateModulus,
            pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
            BoundedGaps.Maynard.divisorTupleLcm, hj] using
            (modEq_companionPinnedCoordinateResidue_iff hm he he' hcover
              hj hmargin).mpr (hdiv j).2

/-- A contributing auxiliary integer itself witnesses compatibility of the
pinned general CRT system. -/
theorem pinnedGeneralCrtCompatible_of_conditions
    {H : Finset ℕ} {RD RE W m p q : ℕ}
    (h : H) {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hdh : d h = 1) (hd'h : d' h = 1)
    (heh : e h = 1) (he'h : e' h = 1)
    (hmargin : h.1 * (W * q) < p)
    (hcond : largeGapDivisorCondition H m (W * q)
        (p - h.1 * (W * q)) d e ∧
      largeGapDivisorCondition H m (W * q)
        (p - h.1 * (W * q)) d' e') :
    PinnedGeneralCrtCompatible H p W m h d e d' e' := by
  rw [largeGapDivisorCondition_pair_iff_lcm] at hcond
  refine ⟨q, ?_⟩
  intro i hi
  cases i with
  | inl j =>
      by_cases hj : j = h
      · subst j
        simpa [pinnedGeneralCrtCoordinateModulus,
          pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
          hdh, hd'h] using (Nat.modEq_one (a := q) (b := 0))
      · simpa [pinnedGeneralCrtCoordinateModulus,
          pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
          BoundedGaps.Maynard.divisorTupleLcm, hj] using
          (modEq_pinnedCoordinateResidue_iff hd hd' hcover hj
            hmargin.le).mpr (hcond j).1
  | inr j =>
      by_cases hj : j = h
      · subst j
        simpa [pinnedGeneralCrtCoordinateModulus,
          pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
          heh, he'h] using (Nat.modEq_one (a := q) (b := 0))
      · simpa [pinnedGeneralCrtCoordinateModulus,
          pinnedGeneralCrtCoordinateResidue, largeGapCrtModulus,
          BoundedGaps.Maynard.divisorTupleLcm, hj] using
          (modEq_companionPinnedCoordinateResidue_iff hm he he' hcover
            hj hmargin).mpr (hcond j).2

/-- Literal count of auxiliary integers for one pinned divisor quadruple. -/
noncomputable def pinnedGeneralDivisorQCount
    (H : Finset ℕ) (W m p : ℕ) (h : H) (Q : Finset ℕ)
    (d e d' e' : H → ℕ) : ℕ :=
  (Q.filter fun q =>
    largeGapDivisorCondition H m (W * q)
        (p - h.1 * (W * q)) d e ∧
      largeGapDivisorCondition H m (W * q)
        (p - h.1 * (W * q)) d' e').card

/-- Totalized single-class count for the pinned general CRT. -/
noncomputable def pinnedGeneralCrtClassCount
    (H : Finset ℕ) (W m p : ℕ) (h : H) (Q : Finset ℕ)
    (d e d' e' : H → ℕ) : ℕ :=
  if hcompat : PinnedGeneralCrtCompatible H p W m h d e d' e' then
    (Q.filter fun q =>
      q ≡ pinnedGeneralCrtResidue H p W m h d e d' e' hcompat
        [MOD pinnedGeneralCrtModulus H d e d' e']).card
  else 0

theorem pinnedGeneralDivisorQCount_eq_crtClassCount
    {H : Finset ℕ} {RD RE W m p : ℕ}
    (h : H) (Q : Finset ℕ) {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hdh : d h = 1) (hd'h : d' h = 1)
    (heh : e h = 1) (he'h : e' h = 1)
    (hmargin : ∀ q ∈ Q, h.1 * (W * q) < p) :
    pinnedGeneralDivisorQCount H W m p h Q d e d' e' =
      pinnedGeneralCrtClassCount H W m p h Q d e d' e' := by
  classical
  by_cases hcompat : PinnedGeneralCrtCompatible H p W m h d e d' e'
  · rw [pinnedGeneralCrtClassCount, dif_pos hcompat]
    unfold pinnedGeneralDivisorQCount
    apply congrArg Finset.card
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hq, hcond⟩
      exact ⟨hq, (modEq_pinnedGeneralCrtResidue_iff h hd hd' he he' hm
        hcover hdh hd'h heh he'h (hmargin q hq) hcompat).mpr hcond⟩
    · rintro ⟨hq, hmod⟩
      exact ⟨hq, (modEq_pinnedGeneralCrtResidue_iff h hd hd' he he' hm
        hcover hdh hd'h heh he'h (hmargin q hq) hcompat).mp hmod⟩
  · rw [pinnedGeneralCrtClassCount, dif_neg hcompat]
    apply Finset.card_eq_zero.mpr
    rw [Finset.filter_eq_empty_iff]
    intro q hq hcond
    exact hcompat (pinnedGeneralCrtCompatible_of_conditions h hd hd' he he'
      hm hcover hdh hd'h heh he'h (hmargin q hq) hcond)

/-- For a prime interval, the pinned count is either the corresponding
reduced progression count or zero, according to compatibility. -/
theorem pinnedGeneralDivisorQCount_primeInterval_eq
    {H : Finset ℕ} {RD RE W m p A B : ℕ}
    (h : H) {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hdh : d h = 1) (hd'h : d' h = 1)
    (heh : e h = 1) (he'h : e' h = 1)
    (hmargin : ∀ q ∈ Finset.Ico A B, h.1 * (W * q) < p) :
    pinnedGeneralDivisorQCount H W m p h (auxiliaryPrimeInterval A B)
        d e d' e' =
      if hcompat : PinnedGeneralCrtCompatible H p W m h d e d' e' then
        BoundedGaps.Maynard.primeVariableProgressionCount A B
          (pinnedGeneralCrtModulus H d e d' e')
          (pinnedGeneralCrtResidue H p W m h d e d' e' hcompat)
      else 0 := by
  rw [pinnedGeneralDivisorQCount_eq_crtClassCount h
    (auxiliaryPrimeInterval A B) hd hd' he he' hm hcover
    hdh hd'h heh he'h (fun q hq => hmargin q (by
      exact Finset.mem_Ico.mpr
        ⟨(mem_auxiliaryPrimeInterval.mp hq).1,
          (mem_auxiliaryPrimeInterval.mp hq).2.1⟩))]
  unfold pinnedGeneralCrtClassCount
  by_cases hcompat : PinnedGeneralCrtCompatible H p W m h d e d' e'
  · rw [dif_pos hcompat, dif_pos hcompat]
    unfold auxiliaryPrimeInterval
      BoundedGaps.Maynard.primeVariableProgressionCount
    apply congrArg Finset.card
    ext q
    simp [and_assoc]
  · rw [dif_neg hcompat, dif_neg hcompat]

/-! ### Uniform prime main term and discrepancy -/

/-- A divisor quadruple contributes a genuine pinned prime main term exactly
when all four pinned coordinates are one and the remaining (possibly
overlapping) congruences are compatible. -/
def PinnedGeneralRestricted {H : Finset ℕ} (W m p : ℕ) (h : H)
    (d e d' e' : H → ℕ) : Prop :=
  d h = 1 ∧ d' h = 1 ∧ e h = 1 ∧ e' h = 1 ∧
    PinnedGeneralCrtCompatible H p W m h d e d' e'

/-- Every actually contributing arbitrary-overlap quadruple has all four
pinned coordinates equal to one, and the contributing `q` witnesses CRT
compatibility. -/
theorem pinnedGeneral_conditions_restricted
    {H : Finset ℕ} {RD RE W m p q Y : ℕ} (h : H)
    {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hmargin : h.1 * (W * q) < p)
    (hpre : largeGapPreSieved Y m p)
    (hcond :
      largeGapDivisorCondition H m (W * q)
          (p - h.1 * (W * q)) d e ∧
        largeGapDivisorCondition H m (W * q)
          (p - h.1 * (W * q)) d' e') :
    PinnedGeneralRestricted W m p h d e d' e' := by
  let n := p - h.1 * (W * q)
  have hnadd : n + h.1 * (W * q) = p :=
    Nat.sub_add_cancel hmargin.le
  have hdhdiv : d h ∣ p := by
    rw [← hnadd]
    exact (hcond.1 h).1
  have hd'hdiv : d' h ∣ p := by
    rw [← hnadd]
    exact (hcond.2 h).1
  have hehdiv : e h ∣ m * p - 1 := by
    rw [← hnadd]
    exact (hcond.1 h).2
  have he'hdiv : e' h ∣ m * p - 1 := by
    rw [← hnadd]
    exact (hcond.2 h).2
  have hcompCop : (m * p - 1).Coprime (primorial Y) := by
    unfold largeGapPreSieved at hpre
    exact Nat.Coprime.coprime_dvd_left (dvd_mul_left (m * p - 1) p) hpre
  have hdh : d h = 1 :=
    maynard_coordinate_eq_one_of_dvd_prime h hd hp hRDp hdhdiv
  have hd'h : d' h = 1 :=
    maynard_coordinate_eq_one_of_dvd_prime h hd' hp hRDp hd'hdiv
  have heh : e h = 1 :=
    maynard_coordinate_eq_one_of_dvd_and_coprime_primorial h he hREY
      hehdiv hcompCop
  have he'h : e' h = 1 :=
    maynard_coordinate_eq_one_of_dvd_and_coprime_primorial h he' hREY
      he'hdiv hcompCop
  have hcompat := pinnedGeneralCrtCompatible_of_conditions h hd hd' he he'
    hm hcover hdh hd'h heh he'h hmargin hcond
  exact ⟨hdh, hd'h, heh, he'h, hcompat⟩

/-- A quadruple outside the restricted compatible set contributes no
auxiliary integer at all. -/
theorem pinnedGeneralDivisorQCount_eq_zero_of_not_restricted
    {H : Finset ℕ} {RD RE W m p Y : ℕ} (h : H) (Q : Finset ℕ)
    {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hmargin : ∀ q ∈ Q, h.1 * (W * q) < p)
    (hpre : largeGapPreSieved Y m p)
    (hnot : ¬PinnedGeneralRestricted W m p h d e d' e') :
    pinnedGeneralDivisorQCount H W m p h Q d e d' e' = 0 := by
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro q hq hcond
  exact hnot (pinnedGeneral_conditions_restricted h hd hd' he he' hm
    hcover hp hRDp hREY (hmargin q hq) hpre hcond)

/-- The reduced-residue prime main term for one general pinned divisor
quadruple, totalized by zero when the coordinate congruences are
incompatible. -/
noncomputable def pinnedGeneralExpectedCount
    {H : Finset ℕ} (W m p : ℕ) (h : H) (Q : Finset ℕ)
    (d e d' e' : H → ℕ) : ℝ :=
  if PinnedGeneralRestricted W m p h d e d' e' then
    (Q.card : ℝ) /
      Nat.totient (pinnedGeneralCrtModulus H d e d' e')
  else 0

/-- Literal error of a general pinned quadruple from its uniform prime
main term. -/
noncomputable def pinnedGeneralCountError
    {H : Finset ℕ} (W m p : ℕ) (h : H) (Q : Finset ℕ)
    (d e d' e' : H → ℕ) : ℝ :=
  (pinnedGeneralDivisorQCount H W m p h Q d e d' e' : ℝ) -
    pinnedGeneralExpectedCount W m p h Q d e d' e'

theorem pinnedGeneralDivisorQCount_eq_pinnedQuadrupleQCount
    (H : Finset ℕ) (w m p : ℕ) (h : H) (Q : Finset ℕ)
    (d e d' e' : H → ℕ) :
    pinnedGeneralDivisorQCount H (primorial w) m p h Q d e d' e' =
      pinnedQuadrupleQCount H w m p h Q d e d' e' := by
  rfl

/-- The full pinned lcm/totient kernel, including exactly the divisor
quadruples whose possibly overlapping coordinate system is compatible. -/
noncomputable def pinnedGeneralArithmeticKernel
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m p : ℕ) : ℝ :=
  ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if PinnedGeneralRestricted W m p h d e d' e' then
      lambda d e * lambda d' e' /
        Nat.totient (pinnedGeneralCrtModulus H d e d' e')
    else 0

/-- Coefficient-weighted sum of all general pinned progression errors. -/
noncomputable def pinnedGeneralErrorSum
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (W m p : ℕ) (Q : Finset ℕ) : ℝ :=
  ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    lambda d e * lambda d' e' *
      pinnedGeneralCountError W m p h Q d e d' e'

/-- Exact decomposition of the complete, unseparated pinned Selberg sum
into its lcm/totient main kernel and literal prime-progression errors. -/
theorem sum_pinned_scaledDoubledPointWeights_eq_generalMain_add_error
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m p : ℕ) (Q : Finset ℕ) :
    (∑ q ∈ Q, ∑ h : H,
      scaledDoubledPointWeight H D E lambda w m q
        (p - h.1 * (primorial w * q))) =
      (Q.card : ℝ) *
          pinnedGeneralArithmeticKernel H D E lambda (primorial w) m p +
        pinnedGeneralErrorSum H D E lambda (primorial w) m p Q := by
  classical
  rw [sum_pinned_scaledDoubledPointWeights_eq_quadrupleCounts]
  unfold pinnedGeneralArithmeticKernel pinnedGeneralErrorSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e' he'
  rw [← pinnedGeneralDivisorQCount_eq_pinnedQuadrupleQCount]
  unfold pinnedGeneralCountError pinnedGeneralExpectedCount
  by_cases hrest :
      PinnedGeneralRestricted (primorial w) m p h d e d' e'
  · simp only [if_pos hrest]
    ring
  · simp only [if_neg hrest]
    ring

/-- One arbitrary-overlap pinned quadruple is controlled by the maximal
reduced-residue progression discrepancies at the two interval endpoints.
This is the exact Bombieri--Vinogradov interface required by the
`a_{i,j}` collision expansion in Maynard's proof. -/
theorem abs_pinnedGeneralCountError_primeInterval_le_max
    {H : Finset ℕ} {RD RE W m p Y A B : ℕ} (h : H)
    {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hdh : d h = 1) (hd'h : d' h = 1)
    (heh : e h = 1) (he'h : e' h = 1)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p)
    (hmargin : ∀ q ∈ Finset.Ico A B, h.1 * (W * q) < p)
    (hA : 0 < A) (hAB : A ≤ B) :
    |pinnedGeneralCountError W m p h (auxiliaryPrimeInterval A B)
        d e d' e'| ≤
      BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1)
          (pinnedGeneralCrtModulus H d e d' e') +
        BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1)
          (pinnedGeneralCrtModulus H d e d' e') := by
  classical
  by_cases hcompat : PinnedGeneralCrtCompatible H p W m h d e d' e'
  · have hrest : PinnedGeneralRestricted W m p h d e d' e' :=
      ⟨hdh, hd'h, heh, he'h, hcompat⟩
    let M := pinnedGeneralCrtModulus H d e d' e'
    let r := pinnedGeneralCrtResidue H p W m h d e d' e' hcompat
    have hDpos : ∀ j : H, 0 < Nat.lcm (d j) (d' j) := fun j => by
      simpa [BoundedGaps.Maynard.divisorTupleLcm] using
        (BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard hd hd' j)
    have hEpos : ∀ j : H, 0 < Nat.lcm (e j) (e' j) := fun j => by
      simpa [BoundedGaps.Maynard.divisorTupleLcm] using
        (BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard he he' j)
    have hM : 0 < M := pinnedGeneralCrtModulus_pos hDpos hEpos
    have hrcop : r.Coprime M :=
      pinnedGeneralCrtResidue_coprime_modulus h hd hd' he he' hcover
        hdh hd'h heh he'h hp hRDp hREY hpre hcompat
    have hrlt : r < M := by
      exact generalCrtResidue_lt_modulus Finset.univ
        (pinnedGeneralCrtCoordinateModulus H d e d' e')
        (pinnedGeneralCrtCoordinateResidue H p W m h d e d' e') hcompat
        (by
          intro i hi
          cases i with
          | inl j => exact hDpos j
          | inr j => exact hEpos j)
    have hrmem : r ∈ BoundedGaps.Maynard.coprimeResidues M :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrlt, hrcop⟩
    have hcount := pinnedGeneralDivisorQCount_primeInterval_eq h hd hd'
      he he' hm hcover hdh hd'h heh he'h hmargin
    have hcard := cast_auxiliaryPrimeInterval_card hA hAB
    have hglobal :=
      BoundedGaps.Maynard.primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
        (q := M) (r := r) hA hAB
    unfold pinnedGeneralCountError pinnedGeneralExpectedCount
    rw [hcount, dif_pos hcompat, if_pos hrest, hcard]
    calc
      _ ≤ BoundedGaps.Maynard.progressionDiscrepancy (B - 1) M r +
          BoundedGaps.Maynard.progressionDiscrepancy (A - 1) M r := by
        simpa [M, r] using hglobal
      _ ≤ _ := add_le_add
        (BoundedGaps.Maynard.progressionDiscrepancy_le_max hM hrmem)
        (BoundedGaps.Maynard.progressionDiscrepancy_le_max hM hrmem)
  · have hcount := pinnedGeneralDivisorQCount_primeInterval_eq h hd hd'
      he he' hm hcover hdh hd'h heh he'h hmargin
    have hrest : ¬PinnedGeneralRestricted W m p h d e d' e' :=
      fun hr => hcompat hr.2.2.2.2
    unfold pinnedGeneralCountError pinnedGeneralExpectedCount
    simp only [hcount, dif_neg hcompat, if_neg hrest, Nat.cast_zero,
      sub_zero, abs_zero]
    exact add_nonneg
      (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
      (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)

/-- Totalized form of the preceding estimate.  Quadruples with a nontrivial
pinned coordinate have literal count and expected main term both equal to
zero, so the same discrepancy bound holds without a restrictedness
assumption. -/
theorem abs_pinnedGeneralCountError_primeInterval_le_max_total
    {H : Finset ℕ} {RD RE W m p Y A B : ℕ} (h : H)
    {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p)
    (hmargin : ∀ q ∈ Finset.Ico A B, h.1 * (W * q) < p)
    (hA : 0 < A) (hAB : A ≤ B) :
    |pinnedGeneralCountError W m p h (auxiliaryPrimeInterval A B)
        d e d' e'| ≤
      BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1)
          (pinnedGeneralCrtModulus H d e d' e') +
        BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1)
          (pinnedGeneralCrtModulus H d e d' e') := by
  classical
  by_cases hrest : PinnedGeneralRestricted W m p h d e d' e'
  · exact abs_pinnedGeneralCountError_primeInterval_le_max h hd hd'
      he he' hm hcover hrest.1 hrest.2.1 hrest.2.2.1
      hrest.2.2.2.1 hp hRDp hREY hpre hmargin hA hAB
  · have hzero := pinnedGeneralDivisorQCount_eq_zero_of_not_restricted
      h (auxiliaryPrimeInterval A B) hd hd' he he' hm hcover hp hRDp
      hREY (fun q hq => hmargin q (by
        exact Finset.mem_Ico.mpr
          ⟨(mem_auxiliaryPrimeInterval.mp hq).1,
            (mem_auxiliaryPrimeInterval.mp hq).2.1⟩)) hpre hrest
    unfold pinnedGeneralCountError pinnedGeneralExpectedCount
    rw [hzero, if_neg hrest]
    simp only [Nat.cast_zero, sub_zero, abs_zero]
    exact add_nonneg
      (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
      (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)

end

end Erdos4b
