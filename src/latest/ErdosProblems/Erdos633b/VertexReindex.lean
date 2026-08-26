import ErdosProblems.Erdos633b.CornerReindex
import ErdosProblems.Erdos633b.VertexInventory

/-! Reference relabeling preserves actual vertex positions and transports
angle-incidence counts by explicit finite fiber equivalences. -/

namespace Erdos633b.Tiling

def vertexReindexEquiv {T : Triangle} {n : ℕ} (d : Tiling T n)
    (e : Equiv.Perm (Fin 3)) : (d.reindexTile e).Vertex ≃ d.Vertex where
  toFun p := ⟨p.val, by
    obtain ⟨⟨a, j⟩, hp⟩ := p.property
    exact ⟨(a, e.symm j), hp⟩⟩
  invFun p := ⟨p.val, by
    obtain ⟨⟨a, j⟩, hp⟩ := p.property
    refine ⟨(a, e j), ?_⟩
    change d.place a (d.tile.points (e.symm (e j))) = p.val
    simpa only [Equiv.symm_apply_apply] using hp⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem vertexAngleCount_reindexTile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (e : Equiv.Perm (Fin 3)) (p : (d.reindexTile e).Vertex) (j : Fin 3) :
    (d.reindexTile e).vertexAngleCount p j =
      d.vertexAngleCount (d.vertexReindexEquiv e p) (e.symm j) := by
  unfold vertexAngleCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro a
  constructor
  · intro h
    have hv := congrArg (fun x : (d.reindexTile e).Vertex => x.val) h
    exact Subtype.ext hv
  · intro h
    have hv := congrArg (fun x : d.Vertex => x.val) h
    exact Subtype.ext hv

end Erdos633b.Tiling
