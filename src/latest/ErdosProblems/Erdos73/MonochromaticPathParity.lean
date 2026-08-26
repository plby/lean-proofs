import ErdosProblems.Erdos73.ColumnHandleFamilies
import ErdosProblems.Erdos73.ParityColoring

/-! Same-colour junctions turn balanced corridors even and breaking handles odd. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W] [LinearOrder W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

theorem odd_length_of_parityBreaking_sameColor {color : V → Bool} {P : GraphPath G}
    (hP : ParityBreaking color P) (hc : color P.source = color P.target) : Odd P.walk.length := by
  rw [ParityBreaking, hc, Nat.odd_iff] at hP
  rw [Nat.odd_iff]
  omega

theorem GraphSubdivisionModel.even_edgePaths_of_monochromaticBranches
    (S : GraphSubdivisionModel H G) (col : BipartiteColoringOn G S.vertexSet)
    (b : Bool) (hb : ∀ w, col.color (S.branchVertex w) = b) (e : OrientedEdge H) :
    Even (S.edgePath e).walk.length := by
  have he := col.even_walk (S.edgePath e).walk (fun v hv =>
    (S.mem_vertexSet v).mpr (Or.inr ⟨e, List.mem_toFinset.mpr hv⟩))
  have hs : col.color (S.edgePath e).source = b :=
    (congrArg col.color (S.source_eq e)).trans (hb e.lo)
  have ht : col.color (S.edgePath e).target = b :=
    (congrArg col.color (S.target_eq e)).trans (hb e.hi)
  rw [hs, ht, Nat.even_iff] at he
  rw [Nat.even_iff]
  omega

theorem ColumnHandleFamily.odd_paths_of_monochromaticBranches
    {c r : ℕ} {S : GraphSubdivisionModel (elementaryWall c r) G}
    {col : BipartiteColoringOn G S.vertexSet} {I : Type*}
    (F : ColumnHandleFamily S col I) (b : Bool)
    (hb : ∀ w, col.color (S.branchVertex w) = b) (i : I) : Odd (F.path i).walk.length := by
  apply odd_length_of_parityBreaking_sameColor (F.clean i).breaking
  rw [F.source_eq, F.target_eq, hb, hb]

end
end Erdos73
