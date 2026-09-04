/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Canonical integer parameters for the sparse induction. -/

import ErdosProblems.Erdos717.SparseDenseStep

open Function Set
open SimpleGraph

namespace Erdos717

def degreeCutParameter (m n : ℕ) : ℕ := (4 * m) ⌈/⌉ n

def patternParameter (D a n : ℕ) : ℕ := (4 * D * a) ⌈/⌉ n

def reservoirSizeParameter (m n : ℕ) : ℕ := m / (16 * n)

def reservoirRouteParameter (m n : ℕ) : ℕ := m * m / (1000 * (n * n * n))

def patternSurvivorParameter (X0 a b : ℕ) : ℕ :=
  (X0 / 5) / a.choose b

theorem degreeCutParameter_spec (m n : ℕ) (hn : 0 < n) :
    4 * m ≤ n * (degreeCutParameter m n + 1) := by
  have h := (ceilDiv_le_iff_le_mul hn).mp
    (show (4 * m) ⌈/⌉ n ≤ degreeCutParameter m n + 1 by
      simp [degreeCutParameter])
  exact h

theorem patternParameter_spec (D a n : ℕ) (hn : 0 < n) :
    4 * D * a ≤ (patternParameter D a n + 1) * n := by
  have h : 4 * D * a ≤ n * patternParameter D a n := by
    exact (ceilDiv_le_iff_le_mul hn).mp le_rfl
  nlinarith

theorem patternSurvivorParameter_spec (X0 a b : ℕ) :
    a.choose b * patternSurvivorParameter X0 a b ≤ X0 / 5 := by
  exact Nat.mul_div_le _ _

theorem reservoirSizeParameter_upper (m n : ℕ) :
    16 * n * reservoirSizeParameter m n ≤ m := by
  exact Nat.mul_div_le _ _

theorem reservoirRouteParameter_upper (m n : ℕ) :
    1000 * (n * n * n) * reservoirRouteParameter m n ≤ m * m := by
  exact Nat.mul_div_le _ _

theorem reservoirSizeParameter_ge_twenty
    (m n : ℕ) (hn : 0 < n) (h : 320 * n ≤ m) :
    20 ≤ reservoirSizeParameter m n := by
  rw [reservoirSizeParameter, Nat.le_div_iff_mul_le (by positivity)]
  nlinarith

theorem reservoirRouteParameter_ge_five
    (m n : ℕ) (hn : 0 < n) (h : 5000 * (n * n * n) ≤ m * m) :
    5 ≤ reservoirRouteParameter m n := by
  rw [reservoirRouteParameter, Nat.le_div_iff_mul_le (by positivity)]
  convert h using 1 <;> ring

theorem five_mul_reservoirRouteParameter_le_size
    (m n : ℕ) (hn : 0 < n) (hm : m ≤ n * n) :
    5 * reservoirRouteParameter m n ≤ reservoirSizeParameter m n := by
  rw [reservoirSizeParameter, Nat.le_div_iff_mul_le (by positivity)]
  have hL := reservoirRouteParameter_upper m n
  have hmm : m * m ≤ m * (n * n) := Nat.mul_le_mul_left m hm
  have hscaled : (n * n) *
      (1000 * n * reservoirRouteParameter m n) ≤ (n * n) * m := by
    calc
      (n * n) * (1000 * n * reservoirRouteParameter m n) =
          1000 * (n * n * n) * reservoirRouteParameter m n := by ring
      _ ≤ m * m := hL
      _ ≤ m * (n * n) := hmm
      _ = (n * n) * m := by ring
  have hn2 : 0 < n * n := Nat.mul_pos hn hn
  have hcancel : 1000 * n * reservoirRouteParameter m n ≤ m :=
    Nat.le_of_mul_le_mul_left hscaled hn2
  nlinarith

/-- The canonical reservoir parameters satisfy the DRC second-moment
inequality with ample slack. -/
theorem reservoirParameters_edge_square
    (m n : ℕ) :
    4 * n *
      (n * (reservoirSizeParameter m n * reservoirSizeParameter m n) +
        40 * (n * n * reservoirRouteParameter m n)) ≤ m * m := by
  have hX := reservoirSizeParameter_upper m n
  have hL := reservoirRouteParameter_upper m n
  have hsquare : (16 * n * reservoirSizeParameter m n) ^ 2 ≤ m ^ 2 :=
    Nat.pow_le_pow_left hX 2
  have hm : m ^ 2 = m * m := by ring
  rw [hm] at hsquare
  nlinarith

/-- The sparse high-density step with every auxiliary integer fixed
canonically from the graph and its pruned core. -/
theorem sparse_dense_step_canonical
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a k : ℕ) (hind : G.indepNum ≤ a)
    (ha : 16 * a ≤ Fintype.card V)
    (hE : 0 < G.edgeFinset.card)
    (hhigh : G.edgeSet.ncard ≤ 1000 *
      (sparseCore G
        (degreeCutParameter G.edgeFinset.card (Fintype.card V))
        (patternParameter
          (degreeCutParameter G.edgeFinset.card (Fintype.card V)) a
          (Fintype.card V))).edgeSet.ncard)
    (hXlarge : 320 * Fintype.card V ≤
      (sparseCore G
        (degreeCutParameter G.edgeFinset.card (Fintype.card V))
        (patternParameter
          (degreeCutParameter G.edgeFinset.card (Fintype.card V)) a
          (Fintype.card V))).edgeSet.ncard)
    (hLlarge : 5000 * (Fintype.card V * Fintype.card V * Fintype.card V) ≤
      (sparseCore G
        (degreeCutParameter G.edgeFinset.card (Fintype.card V))
        (patternParameter
          (degreeCutParameter G.edgeFinset.card (Fintype.card V)) a
          (Fintype.card V))).edgeSet.ncard ^ 2)
    (hb : 1 ≤ patternParameter
      (degreeCutParameter G.edgeFinset.card (Fintype.card V)) a
      (Fintype.card V))
    (hba : patternParameter
      (degreeCutParameter G.edgeFinset.card (Fintype.card V)) a
      (Fintype.card V) ≤ a)
    (hk : 2 ≤ k) (hnot : ¬Erdos718.ContainsCliqueSubdivision G k) :
    let D := degreeCutParameter G.edgeFinset.card (Fintype.card V)
    let b := patternParameter D a (Fintype.card V)
    let h := (sparseCore G D b).edgeSet.ncard
    let X0 := reservoirSizeParameter h (Fintype.card V)
    let L := reservoirRouteParameter h (Fintype.card V)
    let Q := patternSurvivorParameter X0 a b
    Q < k ∨ L ^ (b - 1) * Q < 38 ^ (b - 1) * k ^ (2 * b - 1) := by
  dsimp only
  let n := Fintype.card V
  let m := G.edgeFinset.card
  let D := degreeCutParameter m n
  let b := patternParameter D a n
  let H := sparseCore G D b
  let h := H.edgeSet.ncard
  let X0 := reservoirSizeParameter h n
  let L := reservoirRouteParameter h n
  let Q := patternSurvivorParameter X0 a b
  have hn : 0 < n := by
    have hedges := G.card_edgeFinset_le_card_choose_two
    have : 0 < n.choose 2 := lt_of_lt_of_le hE (by simpa [n] using hedges)
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    simp [hn0] at this
  have hmle : h ≤ n * n := by
    let : DecidableRel H.Adj := Classical.decRel H.Adj
    have hedges := H.card_edgeFinset_le_card_choose_two
    rw [Erdos718.MaderPrototype.card_edgeFinset_eq_ncard_edgeSet] at hedges
    change h ≤ n.choose 2 at hedges
    exact hedges.trans (by
      rw [Nat.choose_two_right]
      apply Nat.div_le_of_le_mul
      nlinarith [Nat.sub_le n 1])
  have hX0 : 20 ≤ X0 := by
    apply reservoirSizeParameter_ge_twenty h n hn
    simpa [h, H, b, D, m, n] using hXlarge
  have hL5 : 5 ≤ L := by
    apply reservoirRouteParameter_ge_five h n hn
    simpa [h, H, b, D, m, n, pow_two] using hLlarge
  have hLX : 5 * L ≤ X0 :=
    five_mul_reservoirRouteParameter_le_size h n hn hmle
  apply sparse_dense_step G a D b X0 L Q k hind ha
  · simpa [D, m, n] using degreeCutParameter_spec m n hn
  · have hp := patternParameter_spec D a n hn
    simpa [b, mul_comm] using hp
  · exact hE
  · exact hX0
  · exact hLX
  · simpa [h, H, b, D, m, n] using hhigh
  · have hp := reservoirParameters_edge_square h n
    simpa [h, H, X0, L, b, D, m, n, pow_two] using hp
  · exact hb
  · exact hba
  · exact patternSurvivorParameter_spec X0 a b
  · exact hL5
  · exact hk
  · exact hnot

end Erdos717
