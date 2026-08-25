import ErdosProblems.Erdos6.LargeOffFace
import Util.MaynardBFT.LargeFiberLower

/-!
# Separation of the large product candidate along one coordinate
-/

namespace MaynardBFT.Sieve

open Erdos6.Maynard

open Set
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

variable [P : Parameters] [T : ShiftTuple]

theorem tupleOffFace_largePowerTuple (m : largePowerTuple) :
    tupleOffFace largePowerTuple m = largeOffFace m := rfl

def tupleLargeCandidate (H : Finset ℕ) (t : H → ℝ) : ℝ :=
  by
    classical
    exact if t ∈ BoundedGaps.Maynard.finiteSimplexOf H then
      ∏ h : H, largeFiberProfile (t h)
    else 0

def tupleCoordinateOuterProfile {H : Finset ℕ} (R : ℕ) (m : H)
    (r : H → ℕ) : ℝ :=
  ∏ h ∈ (Finset.univ : Finset H).erase m,
    largeFiberProfile (Real.log (r h) / Real.log R)

theorem tupleLargeCandidate_eq_product_of_mem
    {H : Finset ℕ} {t : H → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf H) :
    tupleLargeCandidate H t = ∏ h : H, largeFiberProfile (t h) := by
  simp [tupleLargeCandidate, ht]

theorem tupleLargeCandidate_abs_le_one
    (H : Finset ℕ) (t : H → ℝ) :
    |tupleLargeCandidate H t| ≤ 1 := by
  by_cases ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf H
  · rw [tupleLargeCandidate_eq_product_of_mem ht,
      abs_of_nonneg (Finset.prod_nonneg fun h hh =>
        largeFiberProfile_nonneg (ht.1 h (Set.mem_univ h)).1)]
    calc
      (∏ h : H, largeFiberProfile (t h)) ≤ ∏ _h : H, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro h hh
          exact largeFiberProfile_nonneg (ht.1 h (Set.mem_univ h)).1
        · intro h hh
          exact largeFiberProfile_le_one (ht.1 h (Set.mem_univ h)).1
      _ = 1 := Finset.prod_const_one
  · rw [tupleLargeCandidate, if_neg ht]
    norm_num

theorem tupleLargeCandidate_update_eq_outer_mul_profile
    {H : Finset ℕ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hrm : r m = 1) (hR : 1 < R) {u : ℕ}
    (hu : u ∈ BoundedGaps.Maynard.maynardS2CoordinateFiberSupport
      H R W m r) :
    tupleLargeCandidate H
        (Function.update (fun h => Real.log (r h) / Real.log R) m
          (Real.log u / Real.log R)) =
      tupleCoordinateOuterProfile R m r *
        largeFiberProfile (Real.log u / Real.log R) := by
  let d := Function.update r m u
  have hdMem : d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W :=
    update_mem_support_of_mem_coordinateFiber m hr hrm hu
  have hsimplex := normalizedLog_mem_finiteSimplex_of_mem_support hR hdMem
  have hpoint :
      BoundedGaps.Maynard.normalizedDivisorLogTuple H R d =
        Function.update (fun h => Real.log (r h) / Real.log R) m
          (Real.log u / Real.log R) := by
    funext h
    by_cases hh : h = m
    · subst h
      simp [d, BoundedGaps.Maynard.normalizedDivisorLogTuple]
    · simp [d, BoundedGaps.Maynard.normalizedDivisorLogTuple, hh]
  rw [← hpoint, tupleLargeCandidate_eq_product_of_mem hsimplex]
  unfold tupleCoordinateOuterProfile
  rw [← Finset.mul_prod_erase (Finset.univ : Finset H)
    (fun h => largeFiberProfile
      (BoundedGaps.Maynard.normalizedDivisorLogTuple H R d h))
    (Finset.mem_univ m)]
  have hm : BoundedGaps.Maynard.normalizedDivisorLogTuple H R d m =
      Real.log u / Real.log R := by
    simp [d, BoundedGaps.Maynard.normalizedDivisorLogTuple]
  rw [hm]
  have hprod :
      (∏ h ∈ (Finset.univ : Finset H).erase m,
        largeFiberProfile
          (BoundedGaps.Maynard.normalizedDivisorLogTuple H R d h)) =
      ∏ h ∈ (Finset.univ : Finset H).erase m,
        largeFiberProfile (Real.log (r h) / Real.log R) := by
    apply Finset.prod_congr rfl
    intro h hh
    have hne : h ≠ m := (Finset.mem_erase.mp hh).1
    simp [BoundedGaps.Maynard.normalizedDivisorLogTuple, d, hne]
  rw [hprod]
  ring

theorem tupleCoordinateFiberSum_eq_outer_mul_scalarSum
    {H : Finset ℕ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hrm : r m = 1) (hR : 1 < R) :
    BoundedGaps.Maynard.maynardS2CoordinateFiberSum H R W
        (BoundedGaps.Maynard.maynardYValue H R W
          (tupleLargeCandidate H)) m r =
      tupleCoordinateOuterProfile R m r *
        (∑ u ∈ BoundedGaps.Maynard.maynardS2CoordinateFiberSupport
            H R W m r,
          ((ArithmeticFunction.moebius u : ℝ) ^ 2 / Nat.totient u) *
            largeFiberProfile (Real.log u / Real.log R)) := by
  rw [BoundedGaps.Maynard.maynardS2CoordinateFiberSum_maynardYValue_eq_sourceSum
    m hr hrm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [tupleLargeCandidate_update_eq_outer_mul_profile m hr hrm hR hu]
  ring

theorem tupleLargeCandidate_largePowerTuple_eq :
    tupleLargeCandidate largePowerTuple = largeTupleCandidate := by
  funext t
  by_cases ht : t ∈ BoundedGaps.Maynard.finiteSimplexOf largePowerTuple
  · rw [tupleLargeCandidate_eq_product_of_mem ht,
      ← largeTupleContinuousProduct_eq_largeTupleCandidate_of_mem_simplex ht]
    unfold largeTupleContinuousProduct
    apply Finset.prod_congr rfl
    intro h hh
    have hx := (ht.1 h (Set.mem_univ h)).1
    rw [largeFiberProfile_eq_largeG hx,
      largeContinuousG_eq_largeG (mul_nonneg (by positivity) hx)]
  · rw [tupleLargeCandidate, if_neg ht]
    unfold largeTupleCandidate largeCandidate
    rw [if_neg]
    intro hs
    have hs' : largeTupleReindex t ∈
        BoundedGaps.Maynard.maynardSimplex largeK := by
      simpa only [largeTupleReindex_apply] using hs
    exact ht (largeTupleReindex_mem_simplex_iff.mp hs')

end

end MaynardBFT.Sieve
