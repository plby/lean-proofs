/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Canonical dense-reservoir parameters. -/

import ErdosProblems.Erdos717.OptimalReservoir
import ErdosProblems.Erdos717.SparseParameters

open Function Set
open SimpleGraph

namespace Erdos717

/-- The optimized dense-reservoir alternative with all integer parameters
chosen canonically from the order and edge count. -/
theorem dense_reservoir_order_inequality
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a k : ℕ) (hind : G.indepNum ≤ a)
    (hn : 0 < Fintype.card V) (hm : 0 < G.edgeFinset.card)
    (hmle : G.edgeFinset.card ≤ Fintype.card V * Fintype.card V)
    (hXlarge : 320 * Fintype.card V ≤ G.edgeFinset.card)
    (hLlarge : 5000 *
      (Fintype.card V * Fintype.card V * Fintype.card V) ≤
        G.edgeFinset.card * G.edgeFinset.card)
    (ha : 1 ≤ a) (hk : 2 ≤ k)
    (hnot : ¬Erdos718.ContainsCliqueSubdivision G k) :
    let X0 := reservoirSizeParameter G.edgeFinset.card (Fintype.card V)
    let L := reservoirRouteParameter G.edgeFinset.card (Fintype.card V)
    let Q := X0 / 5
    Q < k ∨ L ^ (a - 1) * Q < 38 ^ (a - 1) * k ^ (2 * a - 1) := by
  classical
  let n := Fintype.card V
  let m := G.edgeFinset.card
  let X0 := reservoirSizeParameter m n
  let L := reservoirRouteParameter m n
  let Q := X0 / 5
  have hX0 : 20 ≤ X0 := by
    exact reservoirSizeParameter_ge_twenty m n hn
      (by simpa only [m, n] using hXlarge)
  have hL : 5 ≤ L := by
    apply reservoirRouteParameter_ge_five m n hn
    simpa only [m, n, pow_two] using hLlarge
  have hLX : 5 * L ≤ X0 :=
    five_mul_reservoirRouteParameter_le_size m n hn
      (by simpa only [m, n] using hmle)
  have harith : ∀ s t e : ℕ,
      s ≤ n → t ≤ n → m ≤ 2 * e →
      t * (t * (X0 * X0) + 40 * (s * s * L)) ≤ e * e := by
    intro s t e hs ht hme
    have hinner : t * (t * (X0 * X0) + 40 * (s * s * L)) ≤
        n * (n * (X0 * X0) + 40 * (n * n * L)) := by
      apply Nat.mul_le_mul ht
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_right (X0 * X0) ht
      · exact Nat.mul_le_mul_left 40
          (Nat.mul_le_mul_right L (Nat.mul_le_mul hs hs))
    have hparameters := reservoirParameters_edge_square m n
    have hmeSquare : m * m ≤ (2 * e) * (2 * e) :=
      Nat.mul_le_mul hme hme
    have hscaled : 4 *
        (n * (n * (X0 * X0) + 40 * (n * n * L))) ≤ 4 * (e * e) := by
      calc
        4 * (n * (n * (X0 * X0) + 40 * (n * n * L))) =
            4 * n * (n * (X0 * X0) + 40 * (n * n * L)) := by ring
        _ ≤ m * m := by simpa only [X0, L] using hparameters
        _ ≤ (2 * e) * (2 * e) := hmeSquare
        _ = 4 * (e * e) := by ring
    exact hinner.trans (Nat.le_of_mul_le_mul_left hscaled (by norm_num))
  obtain ⟨U, hUcard, _hUsupport, hreservoir⟩ :=
    exists_short_path_reservoir G G le_rfl X0 L hm hX0 hLX
      (by simpa only [n, m] using harith)
  exact local_reservoir_order_inequality G U Q L a k
    (by simpa only [Q] using hUcard) hreservoir ha
    (indepBoundOn_of_indepNum_le hind) hL hk hnot

end Erdos717
