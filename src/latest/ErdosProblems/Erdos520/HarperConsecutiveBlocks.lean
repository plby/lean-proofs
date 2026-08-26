import ErdosProblems.Erdos520.HarperQuarticBudget
import ErdosProblems.Erdos520.HarperBlockIndependence

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Consecutive scheduled prime ranges

This is the shifted counterpart of `harperScheduledPrimeRange`.  It lets a
whole finite path of scheduled blocks be treated as one prime interval, so
all deterministic Taylor errors are controlled by one summable tail.
-/

theorem exists_harperBlock_bracket_from_iff (start n m : ℕ) :
    (∃ k < n, harperBlockEndpoint (start + k) < m ∧
        m ≤ harperBlockEndpoint (start + k + 1)) ↔
      harperBlockEndpoint start < m ∧
        m ≤ harperBlockEndpoint (start + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      constructor
      · rintro ⟨k, hk, hklo, hkhi⟩
        by_cases hkn : k < n
        · have hprev := ih.mp ⟨k, hkn, hklo, hkhi⟩
          exact ⟨hprev.1, hprev.2.trans
            (monotone_harperBlockEndpoint (by omega))⟩
        · have hkeq : k = n := by omega
          subst k
          have hmono : harperBlockEndpoint start ≤
              harperBlockEndpoint (start + n) :=
            monotone_harperBlockEndpoint (by omega)
          exact ⟨hmono.trans_lt hklo, by simpa [Nat.add_assoc] using! hkhi⟩
      · rintro ⟨hstart, htop⟩
        by_cases hm : m ≤ harperBlockEndpoint (start + n)
        · obtain ⟨k, hk, hklo, hkhi⟩ := ih.mpr ⟨hstart, hm⟩
          exact ⟨k, by omega, hklo, hkhi⟩
        · refine ⟨n, by omega, Nat.lt_of_not_ge hm, ?_⟩
          simpa [Nat.add_assoc] using! htop

/-- Union of `n` scheduled blocks starting at block `start`. -/
def harperScheduledPrimeRangeFrom (y start n : ℕ) :
    Finset (HarperPrimeIndex y) :=
  (Finset.range n).biUnion
    (fun k ↦ harperScheduledPrimeBlock y (start + k))

@[simp] theorem mem_harperScheduledPrimeRangeFrom
    {y start n : ℕ} (p : HarperPrimeIndex y) :
    p ∈ harperScheduledPrimeRangeFrom y start n ↔
      harperBlockEndpoint start < p.1 ∧
        p.1 ≤ harperBlockEndpoint (start + n) := by
  rw [harperScheduledPrimeRangeFrom]
  simp only [Finset.mem_biUnion, Finset.mem_range,
    mem_harperScheduledPrimeBlock]
  exact exists_harperBlock_bracket_from_iff start n p.1

theorem harperScheduledPrimeRangeFrom_eq_interval (y start n : ℕ) :
    harperScheduledPrimeRangeFrom y start n =
      harperPrimeInterval y (harperBlockEndpoint start)
        (harperBlockEndpoint (start + n)) := by
  ext p
  simp

theorem pairwiseDisjoint_harperScheduledPrimeBlock_add
    (y start n : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range n) : Set ℕ)
      (fun k ↦ harperScheduledPrimeBlock y (start + k)) := by
  intro i hi j hj hij
  apply disjoint_harperScheduledPrimeBlock y
  omega

/-- Summing the centered increment of each consecutive block is the same as
summing once over their union. -/
theorem sum_harperCenteredLinearPrimeBlockSum_eq_rangeFrom
    (y start n : ℕ) (t u : ℝ) (eta : HarperPrimeCube y) :
    (∑ k ∈ Finset.range n,
        harperCenteredLinearPrimeBlockSum y
          (harperScheduledPrimeBlock y (start + k)) t u eta) =
      harperCenteredLinearPrimeBlockSum y
        (harperScheduledPrimeRangeFrom y start n) t u eta := by
  have h := Finset.sum_biUnion
    (f := fun p : HarperPrimeIndex y ↦
      harperCenteredLinearPrimeIncrement p.1 t u (eta p))
    (pairwiseDisjoint_harperScheduledPrimeBlock_add y start n)
  simpa only [harperScheduledPrimeRangeFrom,
    harperCenteredLinearPrimeBlockSum] using! h.symm

/-- The explicit quadratic drifts add over the same consecutive union. -/
theorem sum_harperLogMainBlockMean_eq_rangeFrom
    (y start n : ℕ) (t u : ℝ) :
    (∑ k ∈ Finset.range n,
        harperLogMainBlockMean y
          (harperScheduledPrimeBlock y (start + k)) t u) =
      harperLogMainBlockMean y
        (harperScheduledPrimeRangeFrom y start n) t u := by
  have h := Finset.sum_biUnion
    (f := fun p : HarperPrimeIndex y ↦
      harperLinearPrimeMean p.1 t u - harperPrimeSecondHarmonic p.1 u)
    (pairwiseDisjoint_harperScheduledPrimeBlock_add y start n)
  simpa only [harperScheduledPrimeRangeFrom,
    harperLogMainBlockMean] using! h.symm

/-- The entire cubic Taylor error of a consecutive block path is bounded
by the tail at its first block, uniformly in the path length. -/
theorem harperBlockCubicRemainder_rangeFrom_le
    (y start n : ℕ) :
    harperBlockCubicRemainder y
        (harperScheduledPrimeRangeFrom y start n) ≤
      (4 / 3 : ℝ) *
        (Real.sqrt (harperBlockEndpoint start : ℝ))⁻¹ := by
  let S := harperScheduledPrimeRangeFrom y start n
  let e : HarperPrimeIndex y ↪ ℕ := Function.Embedding.subtype _
  let A := harperBlockEndpoint start
  let B := harperBlockEndpoint (start + n)
  have hsubset : S.map e ⊆ Finset.Ioc A B := by
    intro m hm
    rw [Finset.mem_map] at hm
    obtain ⟨p, hp, rfl⟩ := hm
    simpa only [Finset.mem_Ioc, e, A, B] using!
      (mem_harperScheduledPrimeRangeFrom p).mp hp
  have hsum :
      (∑ m ∈ S.map e, (Real.sqrt (m : ℝ))⁻¹ ^ 3) ≤
        ∑ m ∈ Finset.Ioc A B, (Real.sqrt (m : ℝ))⁻¹ ^ 3 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro m hmB hmS
    positivity
  have hA : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr
    (harperBlockEndpoint_pos start).ne'
  have hAB : A ≤ B := monotone_harperBlockEndpoint (by omega)
  have htail := sum_Ioc_harperCubicScale_le_inv_sqrt hA hAB
  unfold harperBlockCubicRemainder
  calc
    (∑ p ∈ S, (2 / 3 : ℝ) *
        (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) =
        ∑ m ∈ S.map e, (2 / 3 : ℝ) *
          (Real.sqrt (m : ℝ))⁻¹ ^ 3 := by
      rw [Finset.sum_map]
      rfl
    _ = (2 / 3 : ℝ) *
        ∑ m ∈ S.map e, (Real.sqrt (m : ℝ))⁻¹ ^ 3 := by
      rw [Finset.mul_sum]
    _ ≤ (2 / 3 : ℝ) *
        ∑ m ∈ Finset.Ioc A B, (Real.sqrt (m : ℝ))⁻¹ ^ 3 := by
      gcongr
    _ ≤ (2 / 3 : ℝ) *
        (2 * (Real.sqrt (A : ℝ))⁻¹) := by
      gcongr
    _ = (4 / 3 : ℝ) *
        (Real.sqrt (harperBlockEndpoint start : ℝ))⁻¹ := by
      dsimp [A]
      ring

/-! ## True logarithmic blocks versus centered linear blocks -/

/-- The quadratic logarithmic block is exactly its centered random part plus
its deterministic tilted mean. -/
theorem harperLogMainBlockSum_eq_centered_add_mean
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (t u : ℝ) (eta : HarperPrimeCube y) :
    harperLogMainBlockSum y S u eta =
      harperCenteredLinearPrimeBlockSum y S t u eta +
        harperLogMainBlockMean y S t u := by
  unfold harperLogMainBlockSum harperCenteredLinearPrimeBlockSum
    harperLogMainBlockMean harperCoordinateLogMain
    harperCenteredLinearPrimeIncrement harperLinearPrimeMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Pointwise, a true logarithmic block differs from the centered linear
block plus its explicit drift only by the deterministic cubic tail. -/
theorem abs_harperLogBlockSum_sub_centered_add_mean_le
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (h4 : ∀ p ∈ S, 4 ≤ p.1) (t u : ℝ) (eta : HarperPrimeCube y) :
    |harperLogBlockSum y S u eta -
        (harperCenteredLinearPrimeBlockSum y S t u eta +
          harperLogMainBlockMean y S t u)| ≤
      harperBlockCubicRemainder y S := by
  rw [← harperLogMainBlockSum_eq_centered_add_mean]
  exact abs_harperLogBlockSum_sub_main_le y S h4 u eta

/-- Consecutive-path form with one explicit error bound independent of the
number of blocks. -/
theorem abs_harperLogRangeFrom_sub_centered_add_mean_le
    (y start n : ℕ) (t u : ℝ) (eta : HarperPrimeCube y) :
    |harperLogBlockSum y (harperScheduledPrimeRangeFrom y start n) u eta -
        (harperCenteredLinearPrimeBlockSum y
            (harperScheduledPrimeRangeFrom y start n) t u eta +
          harperLogMainBlockMean y
            (harperScheduledPrimeRangeFrom y start n) t u)| ≤
      (4 / 3 : ℝ) *
        (Real.sqrt (harperBlockEndpoint start : ℝ))⁻¹ := by
  exact (abs_harperLogBlockSum_sub_centered_add_mean_le y
    (harperScheduledPrimeRangeFrom y start n)
    (fun p hp ↦ by
      have hmem := (mem_harperScheduledPrimeRangeFrom p).mp hp
      have hbase := harperBlockEndpoint_ge_sixteen start
      omega)
    t u eta).trans (harperBlockCubicRemainder_rangeFrom_le y start n)

end Problem520
end Erdos
