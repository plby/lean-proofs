/-
Adapted from the Apache-2.0-licensed polynomial-grid-minor-theorem development,
https://github.com/EdouardBonnet/polynomial-grid-minor-theorem,
commit fe2848173913a00d85c64d2a17af63f2cf0d4fbf,
TreewidthSparsifierSection2.lean, independent minor path lifting.
The general packing construction below is local to this development.
-/
import ErdosProblems.Erdos73.MinorModels
import ErdosProblems.Erdos73.Paths

namespace Erdos73Infrastructure.SimpleGraph
namespace MinorModel
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}

noncomputable def liftGraphPath
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) : GraphPath G :=
  GraphPath.ofConnectedInduce
    (M.walkBranchUnion P.walk)
    (M.walkBranchUnion_connected P.walk)
    s t
    (M.mem_walkBranchUnion_of_mem_branch (by simp) hs)
    (M.mem_walkBranchUnion_of_mem_branch (by simp) ht)

@[simp] theorem liftGraphPath_source
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (liftGraphPath M P hs ht).source = s := rfl

@[simp] theorem liftGraphPath_target
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (liftGraphPath M P hs ht).target = t := rfl

/-- The lifted path uses only branch sets visited by the minor path. -/
theorem liftGraphPath_vertexSet_subset_walkBranchUnion
    (M : MinorModel H G) (P : GraphPath H)
    {s t : V}
    (hs : s ∈ M.branchSet P.source)
    (ht : t ∈ M.branchSet P.target) :
    (liftGraphPath M P hs ht).vertexSet ⊆ M.walkBranchUnion P.walk := by
  exact GraphPath.ofConnectedInduce_vertexSet_subset
    (M.walkBranchUnion P.walk)
    (M.walkBranchUnion_connected P.walk)
    s t
    (M.mem_walkBranchUnion_of_mem_branch (by simp) hs)
    (M.mem_walkBranchUnion_of_mem_branch (by simp) ht)

/-- Disjoint minor paths have disjoint branch unions in the host. -/
theorem walkBranchUnion_disjoint_of_vertexSet_disjoint
    (M : MinorModel H G) {P Q : GraphPath H}
    (hdisj : Disjoint P.vertexSet Q.vertexSet) :
    Disjoint (M.walkBranchUnion P.walk) (M.walkBranchUnion Q.walk) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvP hvQ
  rw [MinorModel.walkBranchUnion] at hvP hvQ
  rcases Finset.mem_biUnion.1 hvP with ⟨x, hxP, hvx⟩
  rcases Finset.mem_biUnion.1 hvQ with ⟨y, hyQ, hvy⟩
  by_cases hxy : x = y
  · subst y
    have hxP' : x ∈ P.vertexSet := by
      simpa [GraphPath.vertexSet] using hxP
    have hxQ' : x ∈ Q.vertexSet := by
      simpa [GraphPath.vertexSet] using hyQ
    exact Finset.disjoint_left.mp hdisj hxP' hxQ'
  · exact Finset.disjoint_left.mp (M.branch_disjoint hxy) hvx hvy

/-- If a host vertex lies both in the branch set of `w` and in the branch
union of a lifted minor path, then `w` is a vertex of that minor path. -/
theorem vertex_mem_of_branchSet_mem_walkBranchUnion
    (M : MinorModel H G) {P : GraphPath H} {w : W} {x : V}
    (hxw : x ∈ M.branchSet w)
    (hxU : x ∈ M.walkBranchUnion P.walk) :
    w ∈ P.vertexSet := by
  classical
  rw [MinorModel.walkBranchUnion] at hxU
  rcases Finset.mem_biUnion.1 hxU with ⟨z, hz, hxz⟩
  have hzw : z = w := by
    by_contra hne
    exact Finset.disjoint_left.mp (M.branch_disjoint hne) hxz hxw
  subst z
  simpa [GraphPath.vertexSet] using hz

/-- Lift a packing through a minor model, choosing original endpoints in
the corresponding branch sets. Its index type and cardinality are unchanged. -/
noncomputable def liftPacking {S T : Finset W} {A B : Finset V}
    (M : MinorModel H G) (P : PathPacking H S T)
    (s t : P.Index → V)
    (hs : ∀ i, s i ∈ M.branchSet (P.path i).source)
    (ht : ∀ i, t i ∈ M.branchSet (P.path i).target)
    (hc : ∀ i, (s i ∈ A ∧ t i ∈ B) ∨ (s i ∈ B ∧ t i ∈ A)) :
    PathPacking G A B where
  Index := P.Index
  path i := M.liftGraphPath (P.path i) (hs i) (ht i)
  connects := hc
  node_disjoint := by
    intro i j hij
    exact (M.walkBranchUnion_disjoint_of_vertexSet_disjoint
      (P.node_disjoint hij)).mono
        (M.liftGraphPath_vertexSet_subset_walkBranchUnion (P.path i) (hs i) (ht i))
        (M.liftGraphPath_vertexSet_subset_walkBranchUnion (P.path j) (hs j) (ht j))

@[simp] theorem liftPacking_card {S T : Finset W} {A B : Finset V}
    (M : MinorModel H G) (P : PathPacking H S T)
    (s t : P.Index → V)
    (hs : ∀ i, s i ∈ M.branchSet (P.path i).source)
    (ht : ∀ i, t i ∈ M.branchSet (P.path i).target)
    (hc : ∀ i, (s i ∈ A ∧ t i ∈ B) ∨ (s i ∈ B ∧ t i ∈ A)) :
    (M.liftPacking P s t hs ht hc).card = P.card := rfl

/-- Each original vertex of a lifted path belongs only to a branch indexed
by a vertex of the corresponding minor path. -/
theorem liftPacking_vertex_mem {S T : Finset W} {A B : Finset V}
    (M : MinorModel H G) (P : PathPacking H S T)
    (s t : P.Index → V)
    (hs : ∀ i, s i ∈ M.branchSet (P.path i).source)
    (ht : ∀ i, t i ∈ M.branchSet (P.path i).target)
    (hc : ∀ i, (s i ∈ A ∧ t i ∈ B) ∨ (s i ∈ B ∧ t i ∈ A))
    (i : P.Index) {x : V} {w : W} (hxw : x ∈ M.branchSet w)
    (hx : x ∈ ((M.liftPacking P s t hs ht hc).path i).vertexSet) :
    w ∈ (P.path i).vertexSet :=
  M.vertex_mem_of_branchSet_mem_walkBranchUnion hxw
    (M.liftGraphPath_vertexSet_subset_walkBranchUnion (P.path i) (hs i) (ht i) hx)

/-- The union of branches indexed by a connected finite set is connected.
This is the singleton-pattern instance of actual minor-model composition. -/
theorem connected_induce_branchUnion (M : MinorModel H G) (S : Finset W)
    (hS : (H.induce (S : Set W)).Connected) :
    (G.induce (↑(S.biUnion M.branchSet) : Set V)).Connected := by
  classical
  obtain ⟨s⟩ := hS.nonempty
  let N : MinorModel (⊥ : _root_.SimpleGraph Unit) H := {
    branchSet := fun _ => S
    branch_nonempty := fun _ => ⟨s.val, s.property⟩
    branch_connected := fun _ => hS
    branch_disjoint := fun x y hxy => (hxy (Subsingleton.elim x y)).elim
    adjacent := fun {_ _} h => h.elim }
  have heq : (N.trans M).branchSet () = S.biUnion M.branchSet := by
    ext x
    change x ∈ composeBranchSet N M () ↔ x ∈ S.biUnion M.branchSet
    rw [mem_composeBranchSet, Finset.mem_biUnion]
  have hc := (N.trans M).branch_connected ()
  rw [heq] at hc
  exact hc

end MinorModel
end Erdos73Infrastructure.SimpleGraph
