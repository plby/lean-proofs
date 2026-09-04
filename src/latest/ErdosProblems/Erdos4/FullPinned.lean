import ErdosProblems.Erdos4.Base

namespace Erdos4

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Interval
noncomputable section

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem maynard_coordinate_dvd_primorial_of_radius_le
    {H : Finset ℕ} {R W Y : ℕ} {d : H → ℕ} (h : H)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hRY : R ≤ Y) :
    d h ∣ primorial Y := by
  have hprodpos : 0 < BoundedGaps.Maynard.divisorTupleProduct H d :=
    Nat.pos_of_ne_zero hd.2.2.ne_zero
  have hcoordle : d h ≤ BoundedGaps.Maynard.divisorTupleProduct H d :=
    Nat.le_of_dvd hprodpos
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d h)
  have hcoordY : d h ≤ Y := hcoordle.trans (hd.1.le.trans hRY)
  exact dvd_trans (hd.coordinate_squarefree h).dvd_primorial
    (primorial_dvd_primorial hcoordY)

theorem maynard_coordinate_eq_one_of_dvd_and_coprime_primorial
    {H : Finset ℕ} {R W Y x : ℕ} {d : H → ℕ} (h : H)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hRY : R ≤ Y) (hdx : d h ∣ x)
    (hcop : x.Coprime (primorial Y)) :
    d h = 1 := by
  exact Nat.eq_one_of_dvd_coprimes hcop hdx
    (maynard_coordinate_dvd_primorial_of_radius_le h hd hRY)

/-- Generic doubled point weight with covering shifts scaled by the small
pre-sieve modulus. -/
noncomputable def scaledDoubledPointWeight
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m q n : ℕ) : ℝ :=
  doubledSelbergWeight H D E lambda m (primorial w * q) n

theorem scaledDoubledPointWeight_nonneg
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m q n : ℕ) :
    0 ≤ scaledDoubledPointWeight H D E lambda w m q n :=
  doubledSelbergWeight_nonneg _ _ _ _ _ _ _

/-- Number of auxiliary primes for which a fixed doubled divisor quadruple
contributes after pinning coordinate `h` at the target prime `p`. -/
noncomputable def pinnedQuadrupleQCount
    (H : Finset ℕ) (w m p : ℕ) (h : H) (Q : Finset ℕ)
    (d e d' e' : H → ℕ) : ℕ :=
  (Q.filter fun q =>
    let n := p - h.1 * (primorial w * q)
    largeGapDivisorCondition H m (primorial w * q) n d e ∧
      largeGapDivisorCondition H m (primorial w * q) n d' e').card

/-- Exact finite expansion of all pinned coordinate preimages into divisor
quadruple counts. -/
theorem sum_pinned_scaledDoubledPointWeights_eq_quadrupleCounts
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m p : ℕ) (Q : Finset ℕ) :
    (∑ q ∈ Q, ∑ h : H,
      scaledDoubledPointWeight H D E lambda w m q
        (p - h.1 * (primorial w * q))) =
      ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
        lambda d e * lambda d' e' *
          (pinnedQuadrupleQCount H w m p h Q d e d' e' : ℝ) := by
  classical
  simp_rw [scaledDoubledPointWeight,
    doubledSelbergWeight_eq_quadrupleSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e' he'
  simpa [pinnedQuadrupleQCount] using
    (sum_indicator_eq_mul_card Q
      (fun q =>
        largeGapDivisorCondition H m (primorial w * q)
            (p - h.1 * (primorial w * q)) d e ∧
          largeGapDivisorCondition H m (primorial w * q)
            (p - h.1 * (primorial w * q)) d' e')
      (lambda d e * lambda d' e'))

/-- Every contributing full-companion quadruple is compatible and all four
coordinates pinned at the target prime are one. -/
theorem pinnedQuadruple_conditions_restricted
    {H : Finset ℕ} {RD RE w Y m p q : ℕ}
    (h : H) {d e d' e' : H → ℕ}
    (hdmem : d ∈ separatedFirstSupport H RD Y)
    (hd'mem : d' ∈ separatedFirstSupport H RD Y)
    (hemem : e ∈ fullySeparatedCompanionSupport H RE (primorial w) m)
    (he'mem : e' ∈ fullySeparatedCompanionSupport H RE (primorial w) m)
    (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hm : 0 < m) (hp : p.Prime) (hq : q.Prime)
    (hRDp : RD ≤ p) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hREY : RE ≤ Y)
    (hmargin : h.1 * (primorial w * q) < p)
    (hpre : largeGapPreSieved Y m p)
    (hcond :
      largeGapDivisorCondition H m (primorial w * q)
          (p - h.1 * (primorial w * q)) d e ∧
        largeGapDivisorCondition H m (primorial w * q)
          (p - h.1 * (primorial w * q)) d' e') :
    BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' ∧
      BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' ∧
      d h = 1 ∧ d' h = 1 ∧ e h = 1 ∧ e' h = 1 := by
  let W := primorial w
  let n := p - h.1 * (W * q)
  let support := fullySeparatedScaledSupportConditions
    (H := H) (RD := RD) (RE := RE) (w := w) (Y := Y)
    (m := m) (q := q) hm hq hwY hcover hRDq hREq hREY
  have hnpos : 0 < n := by
    dsimp [n, W]
    omega
  have hnadd : n + h.1 * (W * q) = p := by
    exact Nat.sub_add_cancel hmargin.le
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
    maynard_coordinate_eq_one_of_dvd_prime h
      (support.first_tuple d hdmem) hp hRDp hdhdiv
  have hd'h : d' h = 1 :=
    maynard_coordinate_eq_one_of_dvd_prime h
      (support.first_tuple d' hd'mem) hp hRDp hd'hdiv
  have heh : e h = 1 :=
    maynard_coordinate_eq_one_of_dvd_and_coprime_primorial h
      (support.companion_tuple e hemem) hREY hehdiv hcompCop
  have he'h : e' h = 1 :=
    maynard_coordinate_eq_one_of_dvd_and_coprime_primorial h
      (support.companion_tuple e' he'mem) hREY he'hdiv hcompCop
  have hDD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' :=
    firstForms_crossCoordinateCoprime_of_conditions
      (hd := support.first_tuple d hdmem)
      (hd' := support.first_tuple d' hd'mem)
      (hcoverage := support.covers_shift_differences)
      (hqD := support.q_first_coprime d hdmem)
      (hqD' := support.q_first_coprime d' hd'mem)
      (hcond := hcond.1) (hcond' := hcond.2)
  have hEE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' :=
    companionForms_crossCoordinateCoprime_of_conditions
      (hm := support.m_pos) (hn := hnpos) (hq := support.q_pos)
      (he := support.companion_tuple e hemem)
      (he' := support.companion_tuple e' he'mem)
      (hcoverage := support.covers_shift_differences)
      (hmE := support.m_companion_coprime e hemem)
      (hmE' := support.m_companion_coprime e' he'mem)
      (hqE := support.q_companion_coprime e hemem)
      (hqE' := support.q_companion_coprime e' he'mem)
      (hcond := hcond.1) (hcond' := hcond.2)
  exact ⟨hDD, hEE, hdh, hd'h, heh, he'h⟩

def FullPinnedRestricted
    {H : Finset ℕ} (h : H) (d e d' e' : H → ℕ) : Prop :=
  BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' ∧
    BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' ∧
    d h = 1 ∧ d' h = 1 ∧ e h = 1 ∧ e' h = 1

instance {H : Finset ℕ} (h : H) (d e d' e' : H → ℕ) :
    Decidable (FullPinnedRestricted h d e d' e') := by
  unfold FullPinnedRestricted
  infer_instance

theorem pinnedQuadrupleQCount_eq_zero_of_not_restricted
    {H : Finset ℕ} {RD RE w Y m p : ℕ}
    (h : H) (Q : Finset ℕ) {d e d' e' : H → ℕ}
    (hdmem : d ∈ separatedFirstSupport H RD Y)
    (hd'mem : d' ∈ separatedFirstSupport H RD Y)
    (hemem : e ∈ fullySeparatedCompanionSupport H RE (primorial w) m)
    (he'mem : e' ∈ fullySeparatedCompanionSupport H RE (primorial w) m)
    (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hm : 0 < m) (hp : p.Prime)
    (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hRDq : ∀ q ∈ Q, RD ≤ q)
    (hREq : ∀ q ∈ Q, RE ≤ q)
    (hmargin : ∀ q ∈ Q, h.1 * (primorial w * q) < p)
    (hpre : largeGapPreSieved Y m p)
    (hnot : ¬ FullPinnedRestricted h d e d' e') :
    pinnedQuadrupleQCount H w m p h Q d e d' e' = 0 := by
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro q hqQ hcond
  exact hnot (pinnedQuadruple_conditions_restricted h hdmem hd'mem hemem
    he'mem hwY hcover hm hp (hQprime q hqQ) hRDp (hRDq q hqQ)
    (hREq q hqQ) hREY (hmargin q hqQ) hpre hcond)

noncomputable def fullPinnedRestrictedSum
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m p : ℕ) (Q : Finset ℕ) : ℝ :=
  ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if FullPinnedRestricted h d e d' e' then
      lambda d e * lambda d' e' *
        (pinnedQuadrupleQCount H w m p h Q d e d' e' : ℝ)
    else 0

theorem sum_pinned_scaledDoubledPointWeights_eq_restrictedSum
    {H : Finset ℕ} {RD RE w Y m p : ℕ}
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (Q : Finset ℕ)
    (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hm : 0 < m) (hp : p.Prime)
    (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hQprime : ∀ q ∈ Q, q.Prime)
    (hRDq : ∀ q ∈ Q, RD ≤ q)
    (hREq : ∀ q ∈ Q, RE ≤ q)
    (hmargin : ∀ q ∈ Q, ∀ h : H,
      h.1 * (primorial w * q) < p)
    (hpre : largeGapPreSieved Y m p) :
    (∑ q ∈ Q, ∑ h : H,
      scaledDoubledPointWeight H
        (separatedFirstSupport H RD Y)
        (fullySeparatedCompanionSupport H RE (primorial w) m)
        lambda w m q (p - h.1 * (primorial w * q))) =
      fullPinnedRestrictedSum H
        (separatedFirstSupport H RD Y)
        (fullySeparatedCompanionSupport H RE (primorial w) m)
        lambda w m p Q := by
  rw [sum_pinned_scaledDoubledPointWeights_eq_quadrupleCounts]
  unfold fullPinnedRestrictedSum
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro d' hd'
  apply Finset.sum_congr rfl
  intro e' he'
  by_cases hr : FullPinnedRestricted h d e d' e'
  · rw [if_pos hr]
  · rw [if_neg hr]
    rw [pinnedQuadrupleQCount_eq_zero_of_not_restricted h Q hd hd' he he'
      hwY hcover hm hp hRDp hREY hQprime hRDq hREq
      (fun q hq => hmargin q hq h) hpre hr]
    norm_num

theorem coversShiftDifferencePrimes_of_dvd
    {H : Finset ℕ} {W W' : ℕ} (hWW' : W ∣ W')
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W) :
    BoundedGaps.Maynard.CoversShiftDifferencePrimes H W' := by
  intro a b hab p hp hpd
  exact dvd_trans (hcover hab p hp hpd) hWW'

/-- The companion affine form is governed by the same off-coordinate residue
constructor as the first form, with target `m*p-1` and coefficient modulus
`W*m`. -/
theorem modEq_companionPinnedCoordinateResidue_iff
    {H : Finset ℕ} {RE W m p q : ℕ} {e e' : H → ℕ}
    (hm : 0 < m)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    {h j : H} (hj : j ≠ h)
    (hmargin : h.1 * (W * q) < p) :
    q ≡ pinnedCoordinateResidue (m * p - 1) (W * m) h.1 j.1
          (BoundedGaps.Maynard.divisorTupleLcm H e e' j)
        [MOD BoundedGaps.Maynard.divisorTupleLcm H e e' j] ↔
      BoundedGaps.Maynard.divisorTupleLcm H e e' j ∣
        m * (p - h.1 * (W * q) + j.1 * (W * q)) - 1 := by
  have hcover' : BoundedGaps.Maynard.CoversShiftDifferencePrimes H (W * m) :=
    coversShiftDifferencePrimes_of_dvd (dvd_mul_right W m) hcover
  have hscale : h.1 * ((W * m) * q) = m * (h.1 * (W * q)) := by ring
  have hjscale : j.1 * ((W * m) * q) = m * (j.1 * (W * q)) := by ring
  have hmulLt : m * (h.1 * (W * q)) < m * p :=
    (Nat.mul_lt_mul_left hm).2 hmargin
  have hmargin' : h.1 * ((W * m) * q) ≤ m * p - 1 := by
    rw [hscale]
    omega
  have hgeneric := modEq_pinnedCoordinateResidue_iff he he' hcover' hj hmargin'
  rw [hgeneric]
  have hle : h.1 * (W * q) ≤ p := hmargin.le
  have hright :
      m * (p - h.1 * (W * q) + j.1 * (W * q)) - 1 =
        (m * p - m * (h.1 * (W * q)) + m * (j.1 * (W * q))) - 1 := by
    rw [Nat.mul_add, Nat.mul_sub_left_distrib]
  have hleft :
      (m * p - 1) - m * (h.1 * (W * q)) + m * (j.1 * (W * q)) =
        (m * p - m * (h.1 * (W * q)) + m * (j.1 * (W * q))) - 1 := by
    omega
  rw [hscale, hjscale, hleft, hright]

def fullPinnedOffModulus
    (H : Finset ℕ) (h : H) (d e d' e' : H → ℕ) : ℕ :=
  pinnedPairOffModulus H h d d' * pinnedPairOffModulus H h e e'

theorem fullPinnedOffModuli_coprime
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q)
    {h : H} {d d' : H → ℕ} (hd : d ∈ D) (hd' : d' ∈ D)
    {e e' : H → ℕ} (he : e ∈ E) (he' : e' ∈ E) :
    (pinnedPairOffModulus H h d d').Coprime
      (pinnedPairOffModulus H h e e') := by
  unfold pinnedPairOffModulus
  rw [Nat.coprime_prod_left_iff]
  intro a ha
  rw [Nat.coprime_prod_right_iff]
  intro b hb
  exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
    (support.cross_family d hd e he a b)
    (support.cross_family d hd e' he' a b)
    (support.cross_family d' hd' e he a b)
    (support.cross_family d' hd' e' he' a b)

noncomputable def pairedCrtResidue
    (M N r s : ℕ) (hcop : M.Coprime N) : ℕ :=
  (Nat.chineseRemainder hcop r s).1

theorem pairedCrtResidue_mod_left
    {M N r s : ℕ} (hcop : M.Coprime N) :
    pairedCrtResidue M N r s hcop ≡ r [MOD M] :=
  (Nat.chineseRemainder hcop r s).2.1

theorem pairedCrtResidue_mod_right
    {M N r s : ℕ} (hcop : M.Coprime N) :
    pairedCrtResidue M N r s hcop ≡ s [MOD N] :=
  (Nat.chineseRemainder hcop r s).2.2

theorem modEq_pairedCrtResidue_iff
    {M N r s q : ℕ} (hcop : M.Coprime N) :
    q ≡ pairedCrtResidue M N r s hcop [MOD M * N] ↔
      q ≡ r [MOD M] ∧ q ≡ s [MOD N] := by
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  constructor
  · rintro ⟨hM, hN⟩
    exact ⟨hM.trans (pairedCrtResidue_mod_left hcop),
      hN.trans (pairedCrtResidue_mod_right hcop)⟩
  · rintro ⟨hM, hN⟩
    exact ⟨hM.trans (pairedCrtResidue_mod_left hcop).symm,
      hN.trans (pairedCrtResidue_mod_right hcop).symm⟩

theorem companionPinnedForm_eq
    {H : Finset ℕ} {W m p q : ℕ} (hm : 0 < m) (h j : H)
    (hmargin : h.1 * (W * q) < p) :
    (m * p - 1) - h.1 * ((W * m) * q) + j.1 * ((W * m) * q) =
      m * (p - h.1 * (W * q) + j.1 * (W * q)) - 1 := by
  have hscale : h.1 * ((W * m) * q) = m * (h.1 * (W * q)) := by ring
  have hjscale : j.1 * ((W * m) * q) = m * (j.1 * (W * q)) := by ring
  have hmulLt : m * (h.1 * (W * q)) < m * p :=
    (Nat.mul_lt_mul_left hm).2 hmargin
  have hright :
      m * (p - h.1 * (W * q) + j.1 * (W * q)) - 1 =
        (m * p - m * (h.1 * (W * q)) + m * (j.1 * (W * q))) - 1 := by
    rw [Nat.mul_add, Nat.mul_sub_left_distrib]
  rw [hscale, hjscale, hright]
  omega

/-- CRT residue for the two pinned divisor-pair systems. -/
noncomputable def fullPinnedCrtResidue
    {H : Finset ℕ} {RD RE W m : ℕ}
    (p : ℕ) (h : H) (d e d' e' : H → ℕ)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hDD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d')
    (hEE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e')
    (hcop : (pinnedPairOffModulus H h d d').Coprime
      (pinnedPairOffModulus H h e e')) : ℕ :=
  pairedCrtResidue
    (pinnedPairOffModulus H h d d')
    (pinnedPairOffModulus H h e e')
    (pinnedPairCrtResidue p h d d' hd hd' hDD)
    (pinnedPairCrtResidue (m * p - 1) h e e' he he' hEE)
    hcop

theorem modEq_fullPinnedCrtResidue_iff
    {H : Finset ℕ} {RD RE W m p q : ℕ}
    (hm : 0 < m) (h : H) {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hDD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d')
    (hEE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e')
    (hcop : (pinnedPairOffModulus H h d d').Coprime
      (pinnedPairOffModulus H h e e'))
    (hdh : d h = 1) (hd'h : d' h = 1)
    (heh : e h = 1) (he'h : e' h = 1)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hmargin : h.1 * (W * q) < p) :
    q ≡ fullPinnedCrtResidue p h d e d' e' hd hd' he he' hDD hEE hcop
        [MOD fullPinnedOffModulus H h d e d' e'] ↔
      largeGapDivisorCondition H m (W * q)
          (p - h.1 * (W * q)) d e ∧
        largeGapDivisorCondition H m (W * q)
          (p - h.1 * (W * q)) d' e' := by
  have hcoverWM : BoundedGaps.Maynard.CoversShiftDifferencePrimes H (W * m) :=
    coversShiftDifferencePrimes_of_dvd (dvd_mul_right W m) hcover
  have hmulLt : m * (h.1 * (W * q)) < m * p :=
    (Nat.mul_lt_mul_left hm).2 hmargin
  have hmarginComp : h.1 * ((W * m) * q) ≤ m * p - 1 := by
    have hscale : h.1 * ((W * m) * q) = m * (h.1 * (W * q)) := by ring
    rw [hscale]
    omega
  simp only [fullPinnedCrtResidue, fullPinnedOffModulus]
  rw [modEq_pairedCrtResidue_iff hcop]
  rw [modEq_pinnedPairCrtResidue_iff hd hd' hDD hdh hd'h hcover
    hmargin.le]
  rw [modEq_pinnedPairCrtResidue_iff he he' hEE heh he'h hcoverWM
    hmarginComp]
  unfold largeGapDivisorCondition
  constructor
  · rintro ⟨⟨hD, hD'⟩, hE, hE'⟩
    constructor
    · intro j
      exact ⟨hD j, by simpa [companionPinnedForm_eq hm h j hmargin] using hE j⟩
    · intro j
      exact ⟨hD' j, by simpa [companionPinnedForm_eq hm h j hmargin] using hE' j⟩
  · rintro ⟨hDE, hD'E'⟩
    exact ⟨⟨fun j => (hDE j).1, fun j => (hD'E' j).1⟩,
      fun j => by simpa [companionPinnedForm_eq hm h j hmargin] using (hDE j).2,
      fun j => by simpa [companionPinnedForm_eq hm h j hmargin] using (hD'E' j).2⟩

theorem residue_coprime_of_mul_modEq_coprime
    {c r x l : ℕ} (hxl : x.Coprime l)
    (hmod : c * r ≡ x [MOD l]) : r.Coprime l := by
  have hcr : (c * r).Coprime l :=
    (coprime_modulus_iff_of_modEq hmod).mpr hxl
  exact Nat.Coprime.coprime_dvd_left (dvd_mul_left r c) hcr

theorem residue_coprime_of_mul_add_modEq_zero_coprime
    {c r x l : ℕ} (hxl : x.Coprime l)
    (hmod : c * r + x ≡ 0 [MOD l]) : r.Coprime l := by
  by_contra hnot
  obtain ⟨s, hs, hsr, hsl⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hscr : s ∣ c * r := dvd_mul_of_dvd_right hsr c
  have hlsum : l ∣ c * r + x := Nat.modEq_zero_iff_dvd.mp hmod
  have hssum : s ∣ c * r + x := hsl.trans hlsum
  have hsx : s ∣ x := (Nat.dvd_add_iff_right hscr).mpr hssum
  exact hs.ne_one (Nat.eq_one_of_dvd_coprimes hxl hsx hsl)

theorem pinnedCoordinateResidue_coprime_lcm_of_target
    {H : Finset ℕ} {R W x : ℕ} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    {h j : H} (hj : j ≠ h)
    (hxl : x.Coprime (BoundedGaps.Maynard.divisorTupleLcm H d e j)) :
    (pinnedCoordinateResidue x W h.1 j.1
      (BoundedGaps.Maynard.divisorTupleLcm H d e j)).Coprime
        (BoundedGaps.Maynard.divisorTupleLcm H d e j) := by
  let l := BoundedGaps.Maynard.divisorTupleLcm H d e j
  have hl : 0 < l :=
    BoundedGaps.Maynard.divisorTupleLcm_pos_of_isMaynard hd he j
  by_cases hhj : h.1 ≤ j.1
  · rw [pinnedCoordinateResidue, if_pos hhj]
    have hdist : Nat.dist j.1 h.1 = j.1 - h.1 := by
      rw [Nat.dist_comm]
      exact Nat.dist_eq_sub_of_le hhj
    exact residue_coprime_of_mul_add_modEq_zero_coprime hxl
      (negativeLinearResidue_spec hl (by
        simpa [hdist] using
          (pinned_coefficient_coprime_lcm hd he hcover hj)))
  · rw [pinnedCoordinateResidue, if_neg hhj]
    have hjh : j.1 < h.1 := lt_of_not_ge hhj
    have hdist : Nat.dist j.1 h.1 = h.1 - j.1 :=
      Nat.dist_eq_sub_of_le hjh.le
    exact residue_coprime_of_mul_modEq_coprime hxl
      (positiveLinearResidue_spec hl (by
        simpa [hdist] using
          (pinned_coefficient_coprime_lcm hd he hcover hj)))

theorem pinnedPairCrtResidue_coprime_modulus_of_target
    {H : Finset ℕ} {R W x : ℕ} {h : H} {d e : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d e)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hx : ∀ j : H,
      x.Coprime (BoundedGaps.Maynard.divisorTupleLcm H d e j)) :
    (pinnedPairCrtResidue x h d e hd he hcross).Coprime
      (pinnedPairOffModulus H h d e) := by
  unfold pinnedPairOffModulus
  apply Nat.Coprime.prod_right
  intro j hj
  exact (coprime_modulus_iff_of_modEq
    (pinnedPairCrtResidue_mod hd he hcross hj)).mpr
      (pinnedCoordinateResidue_coprime_lcm_of_target hd he hcover
        (by simpa using hj) (hx j))

theorem companionTarget_coprime_lcm
    {H : Finset ℕ} {RE W m p Y : ℕ} {e e' : H → ℕ}
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hREY : RE ≤ Y) (hpre : largeGapPreSieved Y m p) (j : H) :
    (m * p - 1).Coprime
      (BoundedGaps.Maynard.divisorTupleLcm H e e' j) := by
  have htarget : (m * p - 1).Coprime (primorial Y) := by
    unfold largeGapPreSieved at hpre
    exact Nat.Coprime.coprime_dvd_left (dvd_mul_left (m * p - 1) p) hpre
  have hediv : e j ∣ primorial Y :=
    maynard_coordinate_dvd_primorial_of_radius_le j he hREY
  have he'div : e' j ∣ primorial Y :=
    maynard_coordinate_dvd_primorial_of_radius_le j he' hREY
  have hce : (m * p - 1).Coprime (e j) :=
    Nat.Coprime.coprime_dvd_right hediv htarget
  have hce' : (m * p - 1).Coprime (e' j) :=
    Nat.Coprime.coprime_dvd_right he'div htarget
  exact Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (e j) (e' j))
    (hce.mul_right hce')

theorem fullPinnedCrtResidue_coprime_modulus
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q p Y : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q)
    (h : H) {d d' : H → ℕ} (hdmem : d ∈ D) (hd'mem : d' ∈ D)
    {e e' : H → ℕ} (hemem : e ∈ E) (he'mem : e' ∈ E)
    (heWM : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he'WM : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hDD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d')
    (hEE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e')
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p) :
    (fullPinnedCrtResidue p h d e d' e'
      (support.first_tuple d hdmem) (support.first_tuple d' hd'mem)
      heWM he'WM hDD hEE
      (fullPinnedOffModuli_coprime (h := h) support hdmem hd'mem hemem he'mem)).Coprime
      (fullPinnedOffModulus H h d e d' e') := by
  let hd := support.first_tuple d hdmem
  let hd' := support.first_tuple d' hd'mem
  let hcop := fullPinnedOffModuli_coprime (h := h) support hdmem hd'mem hemem he'mem
  let rD := pinnedPairCrtResidue p h d d' hd hd' hDD
  let rE := pinnedPairCrtResidue (m * p - 1) h e e' heWM he'WM hEE
  have hrD : rD.Coprime (pinnedPairOffModulus H h d d') :=
    pinnedPairCrtResidue_coprime_modulus hd hd' hDD
      support.covers_shift_differences hp hRDp
  have hcoverWM : BoundedGaps.Maynard.CoversShiftDifferencePrimes H (W * m) :=
    coversShiftDifferencePrimes_of_dvd (dvd_mul_right W m)
      support.covers_shift_differences
  have hrE : rE.Coprime (pinnedPairOffModulus H h e e') :=
    pinnedPairCrtResidue_coprime_modulus_of_target heWM he'WM hEE hcoverWM
      (fun j => companionTarget_coprime_lcm heWM he'WM hREY hpre j)
  have hrD' :
      (pairedCrtResidue (pinnedPairOffModulus H h d d')
        (pinnedPairOffModulus H h e e') rD rE hcop).Coprime
          (pinnedPairOffModulus H h d d') :=
    (coprime_modulus_iff_of_modEq
      (pairedCrtResidue_mod_left hcop)).mpr hrD
  have hrE' :
      (pairedCrtResidue (pinnedPairOffModulus H h d d')
        (pinnedPairOffModulus H h e e') rD rE hcop).Coprime
          (pinnedPairOffModulus H h e e') :=
    (coprime_modulus_iff_of_modEq
      (pairedCrtResidue_mod_right hcop)).mpr hrE
  simpa [fullPinnedCrtResidue, fullPinnedOffModulus, hd, hd', hcop, rD, rE]
    using hrD'.mul_right hrE'

theorem pinnedQuadrupleQCount_primeInterval_eq_progressionCount
    {H : Finset ℕ} {RD RE w Y m p A B : ℕ}
    (h : H) {d e d' e' : H → ℕ}
    (hdmem : d ∈ separatedFirstSupport H RD Y)
    (hd'mem : d' ∈ separatedFirstSupport H RD Y)
    (hemem : e ∈ fullySeparatedCompanionSupport H RE (primorial w) m)
    (he'mem : e' ∈ fullySeparatedCompanionSupport H RE (primorial w) m)
    (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hm : 0 < m) (hp : p.Prime)
    (hRDp : RD ≤ p) (hREp : RE ≤ p) (hREY : RE ≤ Y)
    (hrest : FullPinnedRestricted h d e d' e')
    (hmargin : ∀ q ∈ Finset.Ico A B,
      h.1 * (primorial w * q) < p) :
    pinnedQuadrupleQCount H w m p h (auxiliaryPrimeInterval A B)
        d e d' e' =
      BoundedGaps.Maynard.primeVariableProgressionCount A B
        (fullPinnedOffModulus H h d e d' e')
        (fullPinnedCrtResidue p h d e d' e'
          ((fullySeparatedSupportConditions hm hp
            (primorial_dvd_primorial hwY) hcover hRDp hREp hREY).first_tuple
              d hdmem)
          ((fullySeparatedSupportConditions hm hp
            (primorial_dvd_primorial hwY) hcover hRDp hREp hREY).first_tuple
              d' hd'mem)
          (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem)
          (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'mem)
          hrest.1 hrest.2.1
          (fullPinnedOffModuli_coprime (h := h)
            (fullySeparatedSupportConditions hm hp
              (primorial_dvd_primorial hwY) hcover hRDp hREp hREY)
            hdmem hd'mem hemem he'mem)) := by
  let support := fullySeparatedSupportConditions hm hp
    (primorial_dvd_primorial hwY) hcover hRDp hREp hREY
  let hd := support.first_tuple d hdmem
  let hd' := support.first_tuple d' hd'mem
  let he := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem
  let he' := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'mem
  let hcop := fullPinnedOffModuli_coprime (h := h) support
    hdmem hd'mem hemem he'mem
  unfold pinnedQuadrupleQCount auxiliaryPrimeInterval
    BoundedGaps.Maynard.primeVariableProgressionCount
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hqI, hqprime⟩, hcond⟩
    refine ⟨hqI, hqprime, ?_⟩
    exact (modEq_fullPinnedCrtResidue_iff hm h hd hd' he he'
      hrest.1 hrest.2.1 hcop hrest.2.2.1 hrest.2.2.2.1
      hrest.2.2.2.2.1 hrest.2.2.2.2.2 hcover
      (hmargin q (by simpa only [Finset.mem_Ico] using hqI))).mpr hcond
  · rintro ⟨hqI, hqprime, hmod⟩
    refine ⟨⟨hqI, hqprime⟩, ?_⟩
    exact (modEq_fullPinnedCrtResidue_iff hm h hd hd' he he'
      hrest.1 hrest.2.1 hcop hrest.2.2.1 hrest.2.2.2.1
      hrest.2.2.2.2.1 hrest.2.2.2.2.2 hcover
      (hmargin q (by simpa only [Finset.mem_Ico] using hqI))).mp hmod

/-! ### Exact main-term/error algebra for the full pinned tensor -/

/-- The uniform reduced-residue main term attached to one full pinned
quadruple. -/
noncomputable def fullPinnedExpectedCount
    {H : Finset ℕ} (Q : Finset ℕ) (h : H)
    (d e d' e' : H → ℕ) : ℝ :=
  (Q.card : ℝ) /
    Nat.totient (fullPinnedOffModulus H h d e d' e')

/-- Literal discrepancy of one full pinned quadruple from its uniform
reduced-residue main term. -/
noncomputable def fullPinnedCountError
    {H : Finset ℕ} (w m p : ℕ) (Q : Finset ℕ) (h : H)
    (d e d' e' : H → ℕ) : ℝ :=
  (pinnedQuadrupleQCount H w m p h Q d e d' e' : ℝ) -
    fullPinnedExpectedCount Q h d e d' e'

/-- The arithmetic kernel left by the full pinned prime count after its
uniform prime-density factor has been removed. -/
noncomputable def fullPinnedRestrictedArithmeticKernel
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) : ℝ :=
  ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if FullPinnedRestricted h d e d' e' then
      lambda d e * lambda d' e' /
        Nat.totient (fullPinnedOffModulus H h d e d' e')
    else 0

/-- Coefficient-weighted aggregate of the literal quadruple
discrepancies. -/
noncomputable def fullPinnedRestrictedErrorSum
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m p : ℕ) (Q : Finset ℕ) : ℝ :=
  ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if FullPinnedRestricted h d e d' e' then
      lambda d e * lambda d' e' *
        fullPinnedCountError w m p Q h d e d' e'
    else 0

/-- Exact finite decomposition of the full pinned sum into the uniform
prime-count main term and the aggregate progression error. -/
theorem fullPinnedRestrictedSum_eq_main_add_error
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (w m p : ℕ) (Q : Finset ℕ) :
    fullPinnedRestrictedSum H D E lambda w m p Q =
      (Q.card : ℝ) *
          fullPinnedRestrictedArithmeticKernel H D E lambda +
        fullPinnedRestrictedErrorSum H D E lambda w m p Q := by
  classical
  unfold fullPinnedRestrictedSum fullPinnedRestrictedArithmeticKernel
    fullPinnedRestrictedErrorSum
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
  by_cases hr : FullPinnedRestricted h d e d' e'
  · simp only [mul_ite, mul_zero]
    unfold fullPinnedCountError fullPinnedExpectedCount
    ring
  · simp [hr]

/-- Raw restricted totient kernel for one divisor family and one pinned
coordinate. -/
noncomputable def rawPinnedPairTotientKernel
    {H : Finset ℕ} (D : Finset (H → ℕ))
    (a : (H → ℕ) → ℝ) (h : H) : ℝ :=
  ∑ d ∈ D, ∑ d' ∈ D,
    if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' ∧
        d h = 1 ∧ d' h = 1 then
      a d * a d' /
        ∏ j : H, (Nat.totient
          (BoundedGaps.Maynard.divisorTupleLcm H d d' j) : ℝ)
    else 0

/-- The totient of the combined off-coordinate modulus factors into the
two coordinatewise totient products. -/
theorem totient_fullPinnedOffModulus
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q)
    {h : H} {d d' : H → ℕ} (hd : d ∈ D) (hd' : d' ∈ D)
    {e e' : H → ℕ} (he : e ∈ E) (he' : e' ∈ E)
    (hrest : FullPinnedRestricted h d e d' e') :
    Nat.totient (fullPinnedOffModulus H h d e d' e') =
      (∏ j : H, Nat.totient
          (BoundedGaps.Maynard.divisorTupleLcm H d d' j)) *
        ∏ j : H, Nat.totient
          (BoundedGaps.Maynard.divisorTupleLcm H e e' j) := by
  let hdT := support.first_tuple d hd
  let hd'T := support.first_tuple d' hd'
  let heT := support.companion_tuple e he
  let he'T := support.companion_tuple e' he'
  rw [fullPinnedOffModulus, Nat.totient_mul
    (fullPinnedOffModuli_coprime support hd hd' he he')]
  rw [totient_pinnedPairOffModulus hdT hd'T hrest.1
    hrest.2.2.1 hrest.2.2.2.1]
  rw [totient_pinnedPairOffModulus heT he'T hrest.2.1
    hrest.2.2.2.2.1 hrest.2.2.2.2.2]

/-- For tensor coefficients, the full pinned arithmetic kernel factors at
each distinguished coordinate into the two ordinary restricted kernels. -/
theorem fullPinnedRestrictedArithmeticKernel_tensor
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m q : ℕ}
    (support : DoubledMaynardSupportConditions H D E RD RE W m q)
    (a b : (H → ℕ) → ℝ) :
    fullPinnedRestrictedArithmeticKernel H D E
        (fun d e => a d * b e) =
      ∑ h : H,
        rawPinnedPairTotientKernel D a h *
          rawPinnedPairTotientKernel E b h := by
  classical
  unfold fullPinnedRestrictedArithmeticKernel rawPinnedPairTotientKernel
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d' hd'
  apply Finset.sum_congr rfl
  intro e' he'
  by_cases hr : FullPinnedRestricted h d e d' e'
  · rw [if_pos hr]
    have hD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' ∧
        d h = 1 ∧ d' h = 1 := ⟨hr.1, hr.2.2.1, hr.2.2.2.1⟩
    have hE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' ∧
        e h = 1 ∧ e' h = 1 :=
      ⟨hr.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩
    rw [if_pos hD, if_pos hE]
    have htot := totient_fullPinnedOffModulus support hd hd' he he' hr
    have htotR :
        (Nat.totient (fullPinnedOffModulus H h d e d' e') : ℝ) =
          (∏ j : H, (Nat.totient
              (BoundedGaps.Maynard.divisorTupleLcm H d d' j) : ℝ)) *
            ∏ j : H, (Nat.totient
              (BoundedGaps.Maynard.divisorTupleLcm H e e' j) : ℝ) := by
      exact_mod_cast htot
    rw [htotR]
    ring
  · rw [if_neg hr]
    by_cases hD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' ∧
        d h = 1 ∧ d' h = 1
    · by_cases hE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e' ∧
          e h = 1 ∧ e' h = 1
      · exact (hr ⟨hD.1, hE.1, hD.2.1, hD.2.2,
          hE.2.1, hE.2.2⟩).elim
      · simp [hD, hE]
    · simp [hD]

/-! ### Bombieri--Vinogradov interface for the full pinned counts -/

theorem fullPinnedOffModulus_pos
    {H : Finset ℕ} {RD RE W m : ℕ} {h : H}
    {d d' e e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e') :
    0 < fullPinnedOffModulus H h d e d' e' := by
  unfold fullPinnedOffModulus
  exact Nat.mul_pos (pinnedPairOffModulus_pos hd hd')
    (pinnedPairOffModulus_pos he he')

/-- The discrepancy of one compatible full pinned quadruple is bounded by
the two endpoint progression discrepancies. -/
theorem abs_fullPinnedCountError_primeInterval_le_global_sum
    {H : Finset ℕ} {RD RE w Y m p A B : ℕ}
    (h : H) {d e d' e' : H → ℕ}
    (hdmem : d ∈ separatedFirstSupport H RD Y)
    (hd'mem : d' ∈ separatedFirstSupport H RD Y)
    (hemem : e ∈ fullySeparatedCompanionSupport H RE (primorial w) m)
    (he'mem : e' ∈ fullySeparatedCompanionSupport H RE (primorial w) m)
    (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hm : 0 < m) (hp : p.Prime)
    (hRDp : RD ≤ p) (hREp : RE ≤ p) (hREY : RE ≤ Y)
    (hrest : FullPinnedRestricted h d e d' e')
    (hmargin : ∀ q ∈ Finset.Ico A B,
      h.1 * (primorial w * q) < p)
    (hA : 0 < A) (hAB : A ≤ B) :
    |fullPinnedCountError w m p (auxiliaryPrimeInterval A B)
        h d e d' e'| ≤
      BoundedGaps.Maynard.progressionDiscrepancy (B - 1)
          (fullPinnedOffModulus H h d e d' e')
          (fullPinnedCrtResidue p h d e d' e'
            ((fullySeparatedSupportConditions hm hp
              (primorial_dvd_primorial hwY) hcover hRDp hREp hREY).first_tuple
                d hdmem)
            ((fullySeparatedSupportConditions hm hp
              (primorial_dvd_primorial hwY) hcover hRDp hREp hREY).first_tuple
                d' hd'mem)
            (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem)
            (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'mem)
            hrest.1 hrest.2.1
            (fullPinnedOffModuli_coprime (h := h)
              (fullySeparatedSupportConditions hm hp
                (primorial_dvd_primorial hwY) hcover hRDp hREp hREY)
              hdmem hd'mem hemem he'mem)) +
        BoundedGaps.Maynard.progressionDiscrepancy (A - 1)
          (fullPinnedOffModulus H h d e d' e')
          (fullPinnedCrtResidue p h d e d' e'
            ((fullySeparatedSupportConditions hm hp
              (primorial_dvd_primorial hwY) hcover hRDp hREp hREY).first_tuple
                d hdmem)
            ((fullySeparatedSupportConditions hm hp
              (primorial_dvd_primorial hwY) hcover hRDp hREp hREY).first_tuple
                d' hd'mem)
            (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem)
            (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'mem)
            hrest.1 hrest.2.1
            (fullPinnedOffModuli_coprime (h := h)
              (fullySeparatedSupportConditions hm hp
                (primorial_dvd_primorial hwY) hcover hRDp hREp hREY)
              hdmem hd'mem hemem he'mem)) := by
  let support := fullySeparatedSupportConditions hm hp
    (primorial_dvd_primorial hwY) hcover hRDp hREp hREY
  let hd := support.first_tuple d hdmem
  let hd' := support.first_tuple d' hd'mem
  let he := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem
  let he' := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'mem
  let hcop := fullPinnedOffModuli_coprime (h := h) support
    hdmem hd'mem hemem he'mem
  let M := fullPinnedOffModulus H h d e d' e'
  let r := fullPinnedCrtResidue p h d e d' e' hd hd' he he'
    hrest.1 hrest.2.1 hcop
  have htot := totient_fullPinnedOffModulus support hdmem hd'mem
    hemem he'mem hrest
  have htotR : (Nat.totient M : ℝ) =
      (∏ j : H, (Nat.totient
          (BoundedGaps.Maynard.divisorTupleLcm H d d' j) : ℝ)) *
        ∏ j : H, (Nat.totient
          (BoundedGaps.Maynard.divisorTupleLcm H e e' j) : ℝ) := by
    exact_mod_cast htot
  have hcount := pinnedQuadrupleQCount_primeInterval_eq_progressionCount
    h hdmem hd'mem hemem he'mem hwY hcover hm hp hRDp hREp hREY hrest
    hmargin
  have hcard := cast_auxiliaryPrimeInterval_card hA hAB
  unfold fullPinnedCountError fullPinnedExpectedCount
  rw [hcount, hcard]
  simpa [M, r] using
    (BoundedGaps.Maynard.primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
      (q := M) (r := r) hA hAB)

/-- The same error is bounded by maximal reduced-residue discrepancies at
the two endpoints. -/
theorem abs_fullPinnedCountError_primeInterval_le_max
    {H : Finset ℕ} {RD RE w Y m p A B : ℕ}
    (h : H) {d e d' e' : H → ℕ}
    (hdmem : d ∈ separatedFirstSupport H RD Y)
    (hd'mem : d' ∈ separatedFirstSupport H RD Y)
    (hemem : e ∈ fullySeparatedCompanionSupport H RE (primorial w) m)
    (he'mem : e' ∈ fullySeparatedCompanionSupport H RE (primorial w) m)
    (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w))
    (hm : 0 < m) (hp : p.Prime)
    (hRDp : RD ≤ p) (hREp : RE ≤ p) (hREY : RE ≤ Y)
    (hrest : FullPinnedRestricted h d e d' e')
    (hpre : largeGapPreSieved Y m p)
    (hmargin : ∀ q ∈ Finset.Ico A B,
      h.1 * (primorial w * q) < p)
    (hA : 0 < A) (hAB : A ≤ B) :
    |fullPinnedCountError w m p (auxiliaryPrimeInterval A B)
        h d e d' e'| ≤
      BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1)
          (fullPinnedOffModulus H h d e d' e') +
        BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1)
          (fullPinnedOffModulus H h d e d' e') := by
  let support := fullySeparatedSupportConditions hm hp
    (primorial_dvd_primorial hwY) hcover hRDp hREp hREY
  let hd := support.first_tuple d hdmem
  let hd' := support.first_tuple d' hd'mem
  let he := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hemem
  let he' := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'mem
  let hcop := fullPinnedOffModuli_coprime (h := h) support
    hdmem hd'mem hemem he'mem
  let M := fullPinnedOffModulus H h d e d' e'
  let r := fullPinnedCrtResidue p h d e d' e' hd hd' he he'
    hrest.1 hrest.2.1 hcop
  have hM : 0 < M := fullPinnedOffModulus_pos hd hd' he he'
  have hrcop : r.Coprime M := fullPinnedCrtResidue_coprime_modulus
    support h hdmem hd'mem hemem he'mem he he' hrest.1 hrest.2.1
    hp hRDp hREY hpre
  have hrlt : r < M := by
    dsimp [r, fullPinnedCrtResidue, pairedCrtResidue]
    exact Nat.chineseRemainder_lt_mul hcop _ _
      (pinnedPairOffModulus_pos hd hd').ne'
      (pinnedPairOffModulus_pos he he').ne'
  have hrmem : r ∈ BoundedGaps.Maynard.coprimeResidues M :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrlt, hrcop⟩
  calc
    _ ≤ BoundedGaps.Maynard.progressionDiscrepancy (B - 1) M r +
          BoundedGaps.Maynard.progressionDiscrepancy (A - 1) M r := by
      exact abs_fullPinnedCountError_primeInterval_le_global_sum h hdmem
        hd'mem hemem he'mem hwY hcover hm hp hRDp hREp hREY hrest
        hmargin hA hAB
    _ ≤ _ := add_le_add
      (BoundedGaps.Maynard.progressionDiscrepancy_le_max hM hrmem)
      (BoundedGaps.Maynard.progressionDiscrepancy_le_max hM hrmem)

end
end Erdos4
