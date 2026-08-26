import ErdosProblems.Erdos73.SubdivisionOddRouting
import ErdosProblems.Erdos73.OrientedEdgeMaps

/-! Edge-indexed simple paths assemble into an actual subdivision. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {W V I : Type*} [Fintype W] [LinearOrder W] [Fintype V]
variable {H : SimpleGraph W} {G : SimpleGraph V}

structure EdgePathRealization (H : SimpleGraph W) (G : SimpleGraph V) (I : Type*) where
  branch : W → V
  injective : Function.Injective branch
  left : I → W
  right : I → W
  path : I → GraphPath G
  source_eq : ∀ i, (path i).source = branch (left i)
  target_eq : ∀ i, (path i).target = branch (right i)
  covers : ∀ e : OrientedEdge H, ∃ i, s(left i, right i) = s(e.lo, e.hi)
  branch_on_path : ∀ i w, branch w ∈ (path i).vertexSet → w = left i ∨ w = right i
  intersection : ∀ ⦃i j⦄, i ≠ j → ∀ x,
    x ∈ (path i).vertexSet → x ∈ (path j).vertexSet → ∃ w, x = branch w

namespace EdgePathRealization
variable (R : EdgePathRealization H G I)

def edgeIndex (e : OrientedEdge H) : I := (R.covers e).choose

theorem edgeIndex_eq (e : OrientedEdge H) :
    s(R.left (R.edgeIndex e), R.right (R.edgeIndex e)) = s(e.lo, e.hi) :=
  (R.covers e).choose_spec

theorem edgeIndex_injective : Function.Injective R.edgeIndex := by
  intro e f he
  apply OrientedEdge.eq_of_sym2_eq
  exact (R.edgeIndex_eq e).symm.trans (he ▸ R.edgeIndex_eq f)

theorem edgeIndex_endpoints (e : OrientedEdge H) (w : W) :
    (w = R.left (R.edgeIndex e) ∨ w = R.right (R.edgeIndex e)) ↔
      (w = e.lo ∨ w = e.hi) := by
  rcases Sym2.eq_iff.mp (R.edgeIndex_eq e) with he | he
  · rw [he.1, he.2]
  · rw [he.1, he.2, or_comm]

theorem path_connects (e : OrientedEdge H) :
    (R.path (R.edgeIndex e)).Connects {R.branch e.lo} {R.branch e.hi} := by
  simp only [GraphPath.Connects, mem_singleton, R.source_eq, R.target_eq]
  rcases Sym2.eq_iff.mp (R.edgeIndex_eq e) with he | he
  · exact Or.inl ⟨congrArg R.branch he.1, congrArg R.branch he.2⟩
  · exact Or.inr ⟨congrArg R.branch he.1, congrArg R.branch he.2⟩

def orientedPath (e : OrientedEdge H) : GraphPath G :=
  (R.path (R.edgeIndex e)).orientBetween (R.path_connects e)

theorem orientedPath_vertexSet (e : OrientedEdge H) :
    (R.orientedPath e).vertexSet = (R.path (R.edgeIndex e)).vertexSet :=
  GraphPath.orientBetween_vertexSet _ _

theorem orientedPath_branch (e : OrientedEdge H) (w : W)
    (hw : R.branch w ∈ (R.orientedPath e).vertexSet) : w = e.lo ∨ w = e.hi := by
  rw [R.orientedPath_vertexSet] at hw
  exact (R.edgeIndex_endpoints e w).mp (R.branch_on_path _ w hw)

def toSubdivisionModel : GraphSubdivisionModel H G where
  branchVertex := R.branch
  injective := R.injective
  edgePath := R.orientedPath
  source_eq := fun _ => GraphPath.orientBetween_source _ _
  target_eq := fun _ => GraphPath.orientBetween_target _ _
  branch_on_path := R.orientedPath_branch
  intersection := by
    intro e f hef x hx hy
    have hx' := hx
    have hy' := hy
    rw [R.orientedPath_vertexSet] at hx' hy'
    obtain ⟨w, hw⟩ := R.intersection (fun he => hef (R.edgeIndex_injective he)) x hx' hy'
    exact ⟨w, hw, R.orientedPath_branch e w (hw ▸ hx),
      R.orientedPath_branch f w (hw ▸ hy)⟩

theorem orientedPath_length (e : OrientedEdge H) :
    (R.orientedPath e).walk.length = (R.path (R.edgeIndex e)).walk.length := by
  let P := R.path (R.edgeIndex e)
  by_cases h : P.source ∈ ({R.branch e.lo} : Finset V) ∧
      P.target ∈ ({R.branch e.hi} : Finset V)
  · have he : R.orientedPath e = P := by
      dsimp only [orientedPath, GraphPath.orientBetween, GraphPath.orient]
      exact if_pos h
    exact congrArg (fun Q : GraphPath G => Q.walk.length) he
  · have he : R.orientedPath e = P.reverse := by
      dsimp only [orientedPath, GraphPath.orientBetween, GraphPath.orient]
      exact if_neg h
    exact (congrArg (fun Q : GraphPath G => Q.walk.length) he).trans P.walk.length_reverse

theorem toSubdivisionModel_odd (hodd : ∀ i, Odd (R.path i).walk.length)
    (e : OrientedEdge H) : Odd (R.toSubdivisionModel.edgePath e).walk.length := by
  change Odd (R.orientedPath e).walk.length
  rw [R.orientedPath_length]
  exact hodd _

end EdgePathRealization
end
end Erdos73
