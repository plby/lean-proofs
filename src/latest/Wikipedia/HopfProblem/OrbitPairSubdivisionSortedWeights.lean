import Wikipedia.HopfProblem.OrbitPairSubdivisionEmbedding
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The weights of a simplex with sorted coordinates

For decreasing nonnegative coordinates, multiply successive coordinate
differences by the prefix cardinality. Telescoping recovers each original
coordinate, and a finite double-sum identity proves that these new weights
still sum to one.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz

variable {n : ℕ}

def extendCoordinates (r : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ := Fin.snoc r 0

def coordinateGap (r : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  r j - extendCoordinates r j.succ

theorem coordinateGap_nonneg (r : Fin (n + 1) → ℝ) (hr : Antitone r)
    (h0 : ∀ j, 0 ≤ r j) (j : Fin (n + 1)) : 0 ≤ coordinateGap r j := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simpa [coordinateGap, extendCoordinates] using h0 (Fin.last n)
  · change 0 ≤ r i.castSucc - extendCoordinates r i.succ.castSucc
    rw [extendCoordinates, Fin.snoc_castSucc]
    exact sub_nonneg.mpr (hr i.castSucc_le_succ)

theorem coordinateGap_tail (r : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (∑ j, if i ≤ j then coordinateGap r j else 0) = r i := by
  classical
  have hf : Finset.univ.filter (fun j : Fin (n + 1) ↦ i ≤ j) = Finset.Icc i (Fin.last n) := by
    ext j
    simp [Fin.le_last]
  rw [← Finset.sum_filter, hf]
  have h := Fin.sum_Icc_sub (a := i) (b := Fin.last n) (Fin.le_last i) (extendCoordinates r)
  have he : (∑ j ∈ Finset.Icc i (Fin.last n), coordinateGap r j) =
      -(∑ j ∈ Finset.Icc i (Fin.last n),
        (extendCoordinates r j.succ - extendCoordinates r j.castSucc)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp [coordinateGap, extendCoordinates]
  rw [he, h]
  simp [extendCoordinates]

def sortedWeight (r : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  ((j.val + 1 : ℕ) : ℝ) * coordinateGap r j

theorem sortedWeight_sum (r : Fin (n + 1) → ℝ) : ∑ j, sortedWeight r j = ∑ i, r i := by
  classical
  have hc (j : Fin (n + 1)) :
      (∑ i, if i ≤ j then coordinateGap r j else 0) = sortedWeight r j := by
    have hf : Finset.univ.filter (fun i : Fin (n + 1) ↦ i ≤ j) = Finset.Iic j := by
      ext i
      simp
    rw [← Finset.sum_filter, hf]
    simp [sortedWeight]
  calc
    ∑ j, sortedWeight r j = ∑ j, ∑ i, if i ≤ j then coordinateGap r j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hc j).symm
    _ = ∑ i, ∑ j, if i ≤ j then coordinateGap r j else 0 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun i _ ↦ coordinateGap_tail r i)

def sortedWeights (r : Fin (n + 1) → ℝ) (hr : Antitone r)
    (h0 : ∀ j, 0 ≤ r j) (h1 : ∑ j, r j = 1) : Simplex n :=
  ⟨sortedWeight r, fun j ↦ mul_nonneg (Nat.cast_nonneg _) (coordinateGap_nonneg r hr h0 j),
    (sortedWeight_sum r).trans h1⟩

end Wikipedia.HopfProblem.OrbitPair.Subdivision
