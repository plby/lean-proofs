import ErdosProblems.Erdos73.BrickHorizontalPaths

/-! The actual zigzag path in an interior brick column over a row interval. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {c r : ℕ}

def brickColumnVertex (a b j : ℕ) (hab : a ≤ b) (hb : b < r)
    (hj : 0 < j) (hjc : j + 1 < c) (t : Fin (2 * (b - a) + 2)) :
    ElementaryWallVertex c r := by
  let row := a + t.val / 2
  let col := 2 * j + (t.val % 2 + row) % 2
  let x : Fin r × Fin (2 * c) :=
    (⟨row, by have ht := t.isLt; dsimp only [row]; omega⟩,
      ⟨col, by dsimp only [col]; omega⟩)
  refine ⟨x, rawBrickWall_degree_ge_two_of_interior x ?_ ?_⟩
  · change 0 < col
    dsimp only [col]
    omega
  · change col + 1 < 2 * c
    dsimp only [col]
    omega

theorem brickColumnVertex_injective (a b j : ℕ) (hab hb hj hjc) :
    Function.Injective (brickColumnVertex (c := c) (r := r) a b j hab hb hj hjc) := by
  intro t s he
  have hr := congrArg (fun w : ElementaryWallVertex c r => w.val.1.val) he
  have hc := congrArg (fun w : ElementaryWallVertex c r => w.val.2.val) he
  change a + t.val / 2 = a + s.val / 2 at hr
  change 2 * j + (t.val % 2 + (a + t.val / 2)) % 2 =
    2 * j + (s.val % 2 + (a + s.val / 2)) % 2 at hc
  exact Fin.ext (by omega)

theorem brickColumnVertex_adj (a b j : ℕ) (hab hb hj hjc)
    (t : ℕ) (ht : t + 1 < 2 * (b - a) + 2) :
    (elementaryWall c r).Adj
      (brickColumnVertex a b j hab hb hj hjc ⟨t, by omega⟩)
      (brickColumnVertex a b j hab hb hj hjc ⟨t + 1, ht⟩) := by
  by_cases hp : t % 2 = 0
  · apply Or.inl
    constructor
    · apply Fin.ext
      change a + t / 2 = a + (t + 1) / 2
      omega
    · apply pathGraph_adj.mpr
      change 2 * j + (t % 2 + (a + t / 2)) % 2 + 1 =
          2 * j + ((t + 1) % 2 + (a + (t + 1) / 2)) % 2 ∨
        2 * j + ((t + 1) % 2 + (a + (t + 1) / 2)) % 2 + 1 =
          2 * j + (t % 2 + (a + t / 2)) % 2
      omega
  · apply Or.inr
    constructor
    · apply Fin.ext
      change 2 * j + (t % 2 + (a + t / 2)) % 2 =
        2 * j + ((t + 1) % 2 + (a + (t + 1) / 2)) % 2
      omega
    · apply Or.inl
      change a + t / 2 + 1 = a + (t + 1) / 2 ∧
        (2 * j + (t % 2 + (a + t / 2)) % 2 + (a + t / 2)) % 2 = 1
      omega

theorem exists_brick_column_path (a b j : ℕ) (hab : a ≤ b) (hb : b < r)
    (hj : 0 < j) (hjc : j + 1 < c) :
    ∃ P : GraphPath (elementaryWall c r), P.source.val.1.val = a ∧
      P.target.val.1.val = b ∧
      (∀ w ∈ P.vertexSet, a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧
        2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * j + 1) := by
  let f := brickColumnVertex a b j hab hb hj hjc
  let hf := brickColumnVertex_injective a b j hab hb hj hjc
  let ha := brickColumnVertex_adj a b j hab hb hj hjc
  let P := GraphPath.ofSequence f hf ha
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [GraphPath.ofSequence_source]
    change a + 0 / 2 = a
    omega
  · rw [GraphPath.ofSequence_target]
    change a + (2 * (b - a) + 1) / 2 = b
    omega
  · intro w hw
    obtain ⟨t, rfl⟩ := (GraphPath.mem_ofSequence_vertexSet f hf ha w).mp hw
    have ht := t.isLt
    change a ≤ a + t.val / 2 ∧ a + t.val / 2 ≤ b ∧
      2 * j ≤ 2 * j + (t.val % 2 + (a + t.val / 2)) % 2 ∧
      2 * j + (t.val % 2 + (a + t.val / 2)) % 2 ≤ 2 * j + 1
    omega

end
end Erdos73
