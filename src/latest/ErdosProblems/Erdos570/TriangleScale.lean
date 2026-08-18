/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleCliqueDense
import ErdosProblems.Erdos570.SparseLeaf
import ErdosProblems.Erdos570.TriangleMiddle

/-!
# Dense and scale estimates for the triangle case

For `C₃`, the EFRS cycle--clique estimate is already below `2m` when
the target order is less than `sqrt (2m)`.  Above that order, the density
gap in the middle branch absorbs the triangle-specific square-root loss.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The EFRS bound for `R(C₃,Kₙ)` is below the strengthened budget
whenever `n < sqrt (2m)`. -/
theorem triangle_dense_connected_input
    {H : GraphCode} {B : ℕ} (hH : NoIsolated H)
    (hconn : H.graph.Connected)
    (hsmall : H.vertexCount < Nat.sqrt (2 * H.edgeCount)) :
    graphRamseyNumber (cycleCode 3) H ≤ oddBudget B 1 H.edgeCount := by
  have hn2 : 2 ≤ H.vertexCount := by
    letI : Nonempty (Fin H.vertexCount) := hconn.nonempty
    let v : Fin H.vertexCount := Classical.choice inferInstance
    obtain ⟨w, hvw⟩ := H.graph.exists_adj_iff_not_isIsolated.mpr (hH v)
    have hne : v ≠ w := hvw.ne
    have hv : v.val < H.vertexCount := v.isLt
    have hw : w.val < H.vertexCount := w.isLt
    omega
  have hnpos : 1 ≤ H.vertexCount := by omega
  have hpow : H.vertexCount ≤ H.vertexCount ^ ((3 - 1) / 2) := by simp
  have hram := graphRamseyNumber_cycle_complete_le_efrs
    (m := 3) (a := H.vertexCount) (n := H.vertexCount)
    (by omega) hnpos hn2 hpow
  have htarget := graphRamseyNumber_le_complete_of_vertexCount_le
    (cycleCode 3) H (n := H.vertexCount) (by simp)
  have hsquare : (H.vertexCount + 1) * (H.vertexCount + 1) ≤
      Nat.sqrt (2 * H.edgeCount) * Nat.sqrt (2 * H.edgeCount) := by
    exact Nat.mul_le_mul (by omega) (by omega)
  have hsqrt : Nat.sqrt (2 * H.edgeCount) * Nat.sqrt (2 * H.edgeCount) ≤
      2 * H.edgeCount := Nat.sqrt_le _
  have hpoly : ((3 - 2) * (H.vertexCount + 2) + 1) *
        (H.vertexCount - 1) ≤ 2 * H.edgeCount := by
    calc
      ((3 - 2) * (H.vertexCount + 2) + 1) *
          (H.vertexCount - 1) ≤
          (H.vertexCount + 1) * (H.vertexCount + 1) := by
            have hsub : H.vertexCount - 1 + 1 = H.vertexCount := by omega
            nlinarith
      _ ≤ _ := hsquare.trans hsqrt
  exact htarget.trans (hram.trans (hpoly.trans (by
    unfold oddBudget
    omega)))

/-- A square-root threshold large enough to absorb the triangle-middle
error `6*sqrt(2m) + sqrt(m) + 2`. -/
def triangleScaleRoot (D : ℕ) : ℕ := 14 * D

/-- The non-sparse density inequality turns the explicit square-root error
into the additive gap `m-n` needed by `TriangleMiddleRoom`. -/
theorem triangle_gap_of_scale_and_density
    {D m n q : ℕ} (hD : 2 ≤ D)
    (hq : q = Nat.sqrt (2 * m))
    (hscale : triangleScaleRoot D ≤ Nat.sqrt m)
    (hdensity : D * n ≤ (D - 1) * m) :
    6 * q + Nat.sqrt m + 2 ≤ m - n := by
  have hqle : q ≤ 2 * Nat.sqrt m := by
    rw [hq]
    exact sqrt_two_mul_le_two_sqrt m
  have hspos : 2 ≤ Nat.sqrt m := by
    have : 28 ≤ Nat.sqrt m := by
      exact (show 28 ≤ 14 * D by omega).trans
        (by simpa [triangleScaleRoot] using hscale)
    omega
  have herr : 6 * q + Nat.sqrt m + 2 ≤ 14 * Nat.sqrt m := by
    nlinarith
  have hscaled : D * (6 * q + Nat.sqrt m + 2) ≤ m := by
    calc
      D * (6 * q + Nat.sqrt m + 2) ≤ D * (14 * Nat.sqrt m) :=
        Nat.mul_le_mul_left D herr
      _ = triangleScaleRoot D * Nat.sqrt m := by
        simp [triangleScaleRoot]
        ring
      _ ≤ Nat.sqrt m * Nat.sqrt m :=
        Nat.mul_le_mul_right (Nat.sqrt m) hscale
      _ ≤ m := Nat.sqrt_le m
  let x := 6 * q + Nat.sqrt m + 2
  have hDpred : D - 1 + 1 = D := Nat.sub_add_cancel (by omega)
  have hsum : D * (n + x) ≤ D * m := by
    dsimp only [x]
    calc
      D * (n + (6 * q + Nat.sqrt m + 2)) =
          D * n + D * (6 * q + Nat.sqrt m + 2) := by ring
      _ ≤ (D - 1) * m + m := Nat.add_le_add hdensity hscaled
      _ = (D - 1 + 1) * m := by ring
      _ = D * m := by rw [hDpred]
  have hnx : n + x ≤ m := Nat.le_of_mul_le_mul_left hsum (by omega)
  exact Nat.le_sub_of_add_le (by simpa [x, add_comm] using hnx)

end Erdos570
