/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.SparseStructure

/-!
# Explicit constants for the leaf-rich sparse case

The constants here are deliberately generous.  Their role is only to make
the contraction estimate and the repeated-obstruction losses simultaneously
negligible for each fixed odd cycle.
-/

namespace Erdos570

open Erdos79

def oddSparsePathLength (r : ℕ) : ℕ := 5 * (r + 2)

def oddSparseA (r : ℕ) : ℕ := 4 * oddSparsePathLength r + 2

def oddSparseC (r : ℕ) : ℕ := 6 * oddSparsePathLength r + 2

def oddLeafRamseyCost (r x : ℕ) : ℕ :=
  (2 * r + 2) * (1 + 2 * x)

def oddLeafBatch (r x : ℕ) : ℕ :=
  (r + 1) + oddLeafRamseyCost r x

def oddSparseP (r : ℕ) : ℕ := oddSparseA r * (6 * (r + 1))

def oddSparseE (r : ℕ) : ℕ :=
  oddSparseA r * (8 * (r + 1)) + oddSparseC r

def oddSparseD (r : ℕ) : ℕ :=
  oddSparseE r + 8 * (r + 1) * (r + 1) + 2

def oddSparseVertexThreshold (r : ℕ) : ℕ :=
  (oddSparseD r - 1) * (oddSparseP r + oddSparseE r) + 1

def oddSparseEdgeThreshold (r : ℕ) : ℕ :=
  oddSparseD r * oddSparseVertexThreshold r

theorem oddSparseD_two_le (r : ℕ) : 2 ≤ oddSparseD r := by
  simp [oddSparseD]

theorem sparse_vertex_threshold_le
    {r m n : ℕ}
    (hm : oddSparseEdgeThreshold r ≤ m)
    (hdensity : (oddSparseD r - 1) * m < oddSparseD r * n) :
    oddSparseVertexThreshold r ≤ n := by
  have hD : 2 ≤ oddSparseD r := oddSparseD_two_le r
  unfold oddSparseEdgeThreshold at hm
  by_contra hn
  have hn' : n < oddSparseVertexThreshold r := Nat.lt_of_not_ge hn
  have hDpos : 0 < oddSparseD r := by omega
  have hmul : oddSparseD r * n <
      oddSparseD r * oddSparseVertexThreshold r :=
    (Nat.mul_lt_mul_left hDpos).mpr hn'
  have hmSelf : m ≤ (oddSparseD r - 1) * m := by
    calc
      m = 1 * m := by simp
      _ ≤ (oddSparseD r - 1) * m :=
        Nat.mul_le_mul_right m (by omega)
  omega

/-- In the non-long-path branch, the sparse density condition forces enough
leaves for both the Ramsey deletion and the final two-batch embedding. -/
theorem twice_oddLeafBatch_le_leafVertices
    (r : ℕ) (H : GraphCode) [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hconn : H.graph.Connected)
    (hm : oddSparseEdgeThreshold r ≤ H.edgeCount)
    (hdensity : (oddSparseD r - 1) * H.edgeCount <
      oddSparseD r * H.vertexCount)
    (hshort : ¬∃ t : ℕ, oddSparsePathLength r ≤ t ∧
      ∃ p : Fin (t + 2) → Fin H.vertexCount,
        IsSuspendedPath H.graph p) :
    2 * oddLeafBatch r (sparseExcess H) ≤ (leafVertices H).card := by
  have hstruct := long_suspendedPath_or_sparse_vertex_bound H hH hconn
    (oddSparsePathLength r)
  rcases hstruct with hlong | hbound
  · exact (hshort hlong).elim
  have hexact := connected_edge_add_one_eq_vertex_add_excess H hconn
  have hnlarge := sparse_vertex_threshold_le hm hdensity
  by_contra hnot
  have hleaf : (leafVertices H).card <
      2 * oddLeafBatch r (sparseExcess H) := Nat.lt_of_not_ge hnot
  have hleafCoarse : (leafVertices H).card ≤
      6 * (r + 1) + 8 * (r + 1) * sparseExcess H := by
    unfold oddLeafBatch oddLeafRamseyCost at hleaf
    nlinarith
  have hnPE : H.vertexCount ≤
      oddSparseP r + oddSparseE r * sparseExcess H := by
    unfold oddSparseP oddSparseE oddSparseA oddSparseC at *
    nlinarith
  have hdensityExcess : (oddSparseD r - 1) * sparseExcess H <
      H.vertexCount + (oddSparseD r - 1) := by
    have hDtwo := oddSparseD_two_le r
    have hDpred : oddSparseD r - 1 + 1 = oddSparseD r := by
      omega
    have heqmul := congrArg (fun y ↦ (oddSparseD r - 1) * y) hexact
    simp only [Nat.mul_add, Nat.mul_one] at heqmul
    have hdensity' : (oddSparseD r - 1) * H.edgeCount <
        (oddSparseD r - 1) * H.vertexCount + H.vertexCount := by
      calc
        (oddSparseD r - 1) * H.edgeCount <
            oddSparseD r * H.vertexCount := hdensity
        _ = (oddSparseD r - 1) * H.vertexCount + H.vertexCount := by
          conv_lhs => rw [← hDpred]
          rw [Nat.add_mul, one_mul]
    omega
  have hmulN := Nat.mul_le_mul_left (oddSparseD r - 1) hnPE
  have hEpos : 0 < oddSparseE r := by
    simp [oddSparseE, oddSparseA, oddSparseC, oddSparsePathLength]
  have hmulX : oddSparseE r * ((oddSparseD r - 1) * sparseExcess H) <
      oddSparseE r * (H.vertexCount + (oddSparseD r - 1)) :=
    (Nat.mul_lt_mul_left hEpos).mpr hdensityExcess
  unfold oddSparseVertexThreshold at hnlarge
  have hgap : oddSparseE r + 1 ≤ oddSparseD r - 1 := by
    unfold oddSparseD
    omega
  ring_nf at hmulN hmulX
  nlinarith

/-- The same constants leave enough outside vertices to choose all internal
connectors in the alternating-cycle argument. -/
theorem oddLeafBatch_common_room
    {r m n N : ℕ} {x : ℕ}
    (hexact : m + 1 = n + x)
    (hm : oddSparseEdgeThreshold r ≤ m)
    (hdensity : (oddSparseD r - 1) * m < oddSparseD r * n)
    (hhost : 2 * m + (r + 1) ≤ N) :
    (r + 1) * (oddLeafBatch r x - 1) + (r + 2) ≤ N - n := by
  have hnlarge := sparse_vertex_threshold_le hm hdensity
  have hdensityExcess : (oddSparseD r - 1) * x <
      n + (oddSparseD r - 1) := by
    have hDpred : oddSparseD r - 1 + 1 = oddSparseD r := by
      have := oddSparseD_two_le r
      omega
    have heqmul := congrArg (fun y ↦ (oddSparseD r - 1) * y) hexact
    simp only [Nat.mul_add, Nat.mul_one] at heqmul
    have hdensity' : (oddSparseD r - 1) * m <
        (oddSparseD r - 1) * n + n := by
      calc
        (oddSparseD r - 1) * m < oddSparseD r * n := hdensity
        _ = (oddSparseD r - 1) * n + n := by
          conv_lhs => rw [← hDpred]
          rw [Nat.add_mul, one_mul]
    omega
  have hcoef : 8 * (r + 1) * (r + 1) + 1 ≤ oddSparseD r - 1 := by
    unfold oddSparseD
    omega
  have hxBound : 8 * (r + 1) * (r + 1) * x <
      n + oddSparseD r := by
    have hmul := Nat.mul_le_mul_right x hcoef
    rw [Nat.add_mul] at hmul
    omega
  have hnBig : oddSparseD r + 6 * (r + 1) * (r + 1) + 6 ≤ n := by
    have hPbig : 14 * (r + 1) * (r + 1) + 7 ≤ oddSparseP r := by
      unfold oddSparseP oddSparseA oddSparsePathLength
      nlinarith
    have hfactor : oddSparseP r + oddSparseE r ≤
        (oddSparseD r - 1) * (oddSparseP r + oddSparseE r) := by
      calc
        oddSparseP r + oddSparseE r =
            1 * (oddSparseP r + oddSparseE r) := by simp
        _ ≤ (oddSparseD r - 1) *
            (oddSparseP r + oddSparseE r) :=
          Nat.mul_le_mul_right _ (by
            have := oddSparseD_two_le r
            omega)
    have hsmall : oddSparseD r + 6 * (r + 1) * (r + 1) + 6 ≤
        oddSparseP r + oddSparseE r + 1 := by
      unfold oddSparseD
      nlinarith
    exact hsmall.trans (by
      unfold oddSparseVertexThreshold at hnlarge
      omega)
  have hbatch : (r + 1) * (oddLeafBatch r x - 1) + 2 ≤ m := by
    let X := 4 * (r + 1) * (r + 1) * x
    let P := 3 * (r + 1) * (r + 1)
    have hx' : 2 * X < n + oddSparseD r := by
      dsimp only [X]
      convert hxBound using 1 <;> ring
    have hn' : oddSparseD r + 2 * P + 6 ≤ n := by
      dsimp only [P]
      nlinarith
    have hsum : P + X + 2 ≤ n - 1 := by omega
    have hcoarse : (r + 1) * (oddLeafBatch r x - 1) + 2 ≤
        P + X + 2 := by
      calc
        (r + 1) * (oddLeafBatch r x - 1) + 2 ≤
            (r + 1) * oddLeafBatch r x + 2 :=
          Nat.add_le_add_right
            (Nat.mul_le_mul_left (r + 1) (Nat.sub_le _ _)) 2
        _ = P + X + 2 := by
          dsimp only [P, X]
          unfold oddLeafBatch oddLeafRamseyCost
          ring
    have hnM : n - 1 ≤ m := by omega
    exact hcoarse.trans (hsum.trans hnM)
  have houtside : m + r - 1 ≤ N - n := by omega
  omega

end Erdos570
