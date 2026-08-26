import ErdosProblems.Erdos73.BrickColumnPaths

/-! End a zigzag connector at the first vertex of its final even row. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

theorem exists_brick_column_path_clipped {c r : ℕ} (a b j : ℕ)
    (hab : a ≤ b) (hb : b < r) (hj : 0 < j) (hjc : j + 1 < c)
    (haeven : a % 2 = 0) (hbeven : b % 2 = 0) :
    ∃ P : GraphPath (elementaryWall c r),
      P.source.val.1.val = a ∧ P.source.val.2.val = 2 * j ∧
      P.target.val.1.val = b ∧ P.target.val.2.val = 2 * j ∧
      ∀ w ∈ P.vertexSet, a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧
        2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * j + 1 ∧
        (w.val.1.val = b → w.val.2.val = 2 * j) := by
  let f (t : Fin (2 * (b - a) + 1)) :=
    brickColumnVertex a b j hab hb hj hjc t.castSucc
  have hf : Function.Injective f := (brickColumnVertex_injective a b j hab hb hj hjc).comp
    (Fin.castSucc_injective _)
  have ha (t : ℕ) (ht : t + 1 < 2 * (b - a) + 1) :
      (elementaryWall c r).Adj (f ⟨t, by omega⟩) (f ⟨t + 1, ht⟩) :=
    brickColumnVertex_adj a b j hab hb hj hjc t (by omega)
  let P := GraphPath.ofSequence f hf ha
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GraphPath.ofSequence_source]
    change a + 0 / 2 = a
    omega
  · rw [GraphPath.ofSequence_source]
    change 2 * j + (0 % 2 + (a + 0 / 2)) % 2 = 2 * j
    omega
  · rw [GraphPath.ofSequence_target]
    change a + (2 * (b - a)) / 2 = b
    omega
  · rw [GraphPath.ofSequence_target]
    change 2 * j + ((2 * (b - a)) % 2 + (a + (2 * (b - a)) / 2)) % 2 = 2 * j
    omega
  · intro w hw
    obtain ⟨t, rfl⟩ := (GraphPath.mem_ofSequence_vertexSet f hf ha w).mp hw
    have ht := t.isLt
    change a ≤ a + t.val / 2 ∧ a + t.val / 2 ≤ b ∧
      2 * j ≤ 2 * j + (t.val % 2 + (a + t.val / 2)) % 2 ∧
      2 * j + (t.val % 2 + (a + t.val / 2)) % 2 ≤ 2 * j + 1 ∧
      (a + t.val / 2 = b → 2 * j + (t.val % 2 + (a + t.val / 2)) % 2 = 2 * j)
    omega

end
end Erdos73
