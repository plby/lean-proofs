import ErdosProblems.Erdos633b.VertexInventory
import ErdosProblems.Erdos633b.CornerColumnTotals

/-! Separate the three actual outer vertices from the remaining angle inventory. -/

namespace Erdos633b.Tiling

def NonouterVertex {T : Triangle} {n : ℕ} (d : Tiling T n) :=
  {p : d.Vertex // p ∉ Set.range d.outerVertex}

instance {T : Triangle} {n : ℕ} (d : Tiling T n) : Finite d.NonouterVertex := by
  unfold NonouterVertex
  infer_instance

noncomputable instance {T : Triangle} {n : ℕ} (d : Tiling T n) :
    Fintype d.NonouterVertex := Fintype.ofFinite _

theorem nonouter_inventory {T : Triangle} {n : ℕ} (d : Tiling T n) (j : Fin 3) :
    d.cornerColumnCount j + (∑ p : d.NonouterVertex, d.vertexAngleCount p.val j) = n := by
  classical
  let e : (Fin 3 ⊕ d.NonouterVertex) ≃ d.Vertex :=
    (Equiv.sumCongr (Equiv.ofInjective d.outerVertex d.outerVertex_injective)
      (Equiv.refl _)).trans (Equiv.sumCompl (fun p : d.Vertex => p ∈ Set.range d.outerVertex))
  have hs := Fintype.sum_equiv e
    (Sum.elim (fun i => d.vertexAngleCount (d.outerVertex i) j)
      (fun p : d.NonouterVertex => d.vertexAngleCount p.val j))
    (fun p => d.vertexAngleCount p j) (by intro x; cases x <;> rfl)
  rw [Fintype.sum_sum_type] at hs
  simpa only [Sum.elim_inl, Sum.elim_inr, d.vertexAngleCount_outer,
    d.sum_vertexAngleCount, cornerColumnCount] using hs

theorem nonouter_count_balance {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hz : d.cornerColumnCount 2 = 0) (j : Fin 3) :
    d.cornerColumnCount j + (∑ p : d.NonouterVertex, d.vertexAngleCount p.val j) =
      ∑ p : d.NonouterVertex, d.vertexAngleCount p.val 2 := by
  have hj := d.nonouter_inventory j
  have h2 := d.nonouter_inventory 2
  rw [hz, zero_add] at h2
  exact hj.trans h2.symm

theorem nonouter_vertex_ne {T : Triangle} {n : ℕ} (d : Tiling T n)
    (p : d.NonouterVertex) (i : Fin 3) : p.val.val ≠ T.points i := by
  intro h
  apply p.property
  refine ⟨i, ?_⟩
  apply Subtype.ext
  simpa only [d.outerVertex_val] using h.symm

theorem vertex_mem_support {T : Triangle} {n : ℕ} (d : Tiling T n)
    (p : d.Vertex) : p.val ∈ T.support := by
  obtain ⟨⟨a, j⟩, h⟩ := p.property
  exact d.piece_subset a ⟨d.tile.points j, d.tile.vertex_mem_support j, h⟩

end Erdos633b.Tiling
