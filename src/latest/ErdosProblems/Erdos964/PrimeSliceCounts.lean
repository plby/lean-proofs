import ErdosProblems.Erdos964.SemiprimeSlices
import ErdosProblems.Erdos964.PrimeCharacterBounds

/-!
# Progression errors on the larger-prime slices

The endpoints are integer quotients of the exact affine endpoints. The
finite prime distribution error is bounded by the two prefix errors.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem primeInterval_eq_primesLE_sdiff (x y : ℕ) :
    (Finset.Ioc x y).filter Nat.Prime = y.primesLE \ x.primesLE := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
  by_cases hr : r.Prime
  · simp only [hr, and_true]
    omega
  · simp only [hr, and_false, false_and]

theorem primeInterval_discrepancy_le (x y q a : ℕ) (hxy : x ≤ y)
    (hq : 0 < q) (ha : a.Coprime q) :
    |(finiteResidueCount ((Finset.Ioc x y).filter Nat.Prime) q a : ℝ) -
      (((Finset.Ioc x y).filter Nat.Prime).card : ℝ) / q.totient| ≤
      maxProgressionDiscrepancy y q + maxProgressionDiscrepancy x q := by
  have hsub : x.primesLE ⊆ y.primesLE := by
    intro r hr
    have hr' := Nat.mem_primesLE.mp hr
    exact Nat.mem_primesLE.mpr ⟨hr'.1.trans hxy, hr'.2⟩
  rw [primeInterval_eq_primesLE_sdiff, finiteResidueCount_sdiff_cast _ _ hsub,
    Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub),
    finiteResidueCount_primesLE, finiteResidueCount_primesLE,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  change |((primeCountUpTo y q a : ℝ) - primeCountUpTo x q a) -
    ((primeCountTotal y : ℝ) - primeCountTotal x) / q.totient| ≤ _
  rw [sub_div, sub_sub_sub_comm]
  exact (abs_sub _ _).trans (add_le_add
    (progressionDiscrepancy_le_max_of_coprime y q a hq ha)
    (progressionDiscrepancy_le_max_of_coprime x q a hq ha))

theorem primeSlice_eq_primeInterval (L U p x y : ℕ) (hp : 0 < p)
    (hlo : p * L ≤ x) (hhi : y ≤ p * U) :
    primeSlice ((Finset.Ioc L U).filter Nat.Prime) p x y =
      (Finset.Ioc (x / p) (y / p)).filter Nat.Prime := by
  ext r
  simp only [primeSlice, Finset.mem_filter, Finset.mem_Ioc]
  have hlow : x < p * r ↔ x / p < r := by
    rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm r p]
  have hhigh : p * r ≤ y ↔ r ≤ y / p := by
    rw [Nat.le_div_iff_mul_le hp, Nat.mul_comm r p]
  have hL : L ≤ x / p := by
    rw [Nat.le_div_iff_mul_le hp, Nat.mul_comm L p]
    exact hlo
  have hU : y / p ≤ U := by
    exact (Nat.div_le_div_right hhi).trans_eq (Nat.mul_div_cancel_left U hp)
  rw [hlow, hhigh]
  constructor
  · exact fun h => ⟨h.2, h.1.2⟩
  · intro h
    exact ⟨⟨⟨hL.trans_lt h.1.1, h.1.2.trans hU⟩, h.2⟩, h.1⟩

theorem finiteCoprimeCount_eq_card (S : Finset ℕ) (q : ℕ)
    (hS : ∀ r ∈ S, r.Coprime q) : finiteCoprimeCount S q = S.card := by
  unfold finiteCoprimeCount
  rw [Finset.filter_eq_self.mpr hS]

theorem primeSlice_coprime_count_eq_card (L U p x y q : ℕ)
    (hq : 0 < q) (hqL : q ≤ L) :
    finiteCoprimeCount (primeSlice ((Finset.Ioc L U).filter Nat.Prime) p x y) q =
      (primeSlice ((Finset.Ioc L U).filter Nat.Prime) p x y).card := by
  apply finiteCoprimeCount_eq_card
  intro r hr
  have hr' := Finset.mem_filter.mp (Finset.mem_filter.mp hr).1
  apply hr'.2.coprime_iff_not_dvd.mpr
  intro hrq
  have hle := Nat.le_of_dvd hq hrq
  have hlt := (Finset.mem_Ioc.mp hr'.1).1
  omega

theorem primeSlice_discrepancy_le (L U p x y q a : ℕ) (hp : 0 < p)
    (hxy : x ≤ y) (hlo : p * L ≤ x) (hhi : y ≤ p * U)
    (hq : 0 < q) (ha : a.Coprime q) :
    |(finiteResidueCount (primeSlice ((Finset.Ioc L U).filter Nat.Prime) p x y) q a : ℝ) -
      ((primeSlice ((Finset.Ioc L U).filter Nat.Prime) p x y).card : ℝ) / q.totient| ≤
      maxProgressionDiscrepancy (y / p) q + maxProgressionDiscrepancy (x / p) q := by
  rw [primeSlice_eq_primeInterval L U p x y hp hlo hhi]
  exact primeInterval_discrepancy_le (x / p) (y / p) q a (Nat.div_le_div_right hxy) hq ha

end Erdos964
