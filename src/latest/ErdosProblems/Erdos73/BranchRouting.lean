/- Actual minor branch sets obtained by attaching disjoint half-open paths. -/
import ErdosProblems.Erdos73.MinorModels
import ErdosProblems.Erdos73.GraphPaths

namespace Erdos73Infrastructure.SimpleGraph
variable {V I E : Type*} [DecidableEq V] [Fintype E]
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph I}

structure BranchRouting (H : _root_.SimpleGraph I) (G : _root_.SimpleGraph V) (E : Type*)
    [Fintype E] where
  base : I → Finset V
  nonempty : ∀ i, (base i).Nonempty
  connected : ∀ i, (G.induce (base i : Set V)).Connected
  disjoint : Pairwise fun i j => Disjoint (base i) (base j)
  source : E → I
  target : E → I
  source_ne_target : ∀ e, source e ≠ target e
  path : E → GraphPath G
  starts : ∀ e, (path e).source ∈ base (source e)
  ends : ∀ e, (path e).target ∈ base (target e)
  meets_base : ∀ e i v, v ∈ (path e).vertexSet → v ∈ base i → (path e).IsEndpoint v
  paths_disjoint : Pairwise fun e f => Disjoint (path e).vertexSet (path f).vertexSet
  realizes : ∀ ⦃i j⦄, H.Adj i j →
    ∃ e, (source e = i ∧ target e = j) ∨ (source e = j ∧ target e = i)

namespace BranchRouting
variable (R : BranchRouting H G E)

theorem path_nontrivial (e : E) : (R.path e).source ≠ (R.path e).target := by
  intro h
  exact Finset.disjoint_left.mp (R.disjoint (R.source_ne_target e)) (R.starts e)
    (h ▸ R.ends e)

theorem halfOpen_meets_base (e : E) (i : I) {v : V}
    (hv : v ∈ (R.path e).dropLast.vertexSet) (hvi : v ∈ R.base i) :
    R.source e = i := by
  have hp := R.meets_base e i v ((R.path e).dropLast_vertexSet_subset hv) hvi
  rcases hp with hsrc | htgt
  · by_contra hne
    exact Finset.disjoint_left.mp (R.disjoint hne) (R.starts e) (hsrc ▸ hvi)
  · exact ((R.path e).target_not_mem_dropLast_vertexSet (R.path_nontrivial e) (htgt ▸ hv)).elim

noncomputable def edgesFrom (i : I) : Finset E := by
  classical
  exact Finset.univ.filter fun e => R.source e = i

@[simp] theorem mem_edgesFrom (e : E) (i : I) : e ∈ R.edgesFrom i ↔ R.source e = i := by
  classical
  simp only [edgesFrom, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def augmentedBase (i : I) : Finset V :=
  R.base i ∪ (R.edgesFrom i).biUnion fun e => (R.path e).dropLast.vertexSet

theorem mem_augmentedBase (i : I) (v : V) : v ∈ R.augmentedBase i ↔
    v ∈ R.base i ∨ ∃ e, R.source e = i ∧ v ∈ (R.path e).dropLast.vertexSet := by
  classical
  simp only [augmentedBase, Finset.mem_union, Finset.mem_biUnion, mem_edgesFrom]

theorem base_subset_augmented (i : I) : R.base i ⊆ R.augmentedBase i := Finset.subset_union_left

theorem halfOpen_subset_augmented (e : E) :
    (R.path e).dropLast.vertexSet ⊆ R.augmentedBase (R.source e) := by
  intro v hv
  exact (R.mem_augmentedBase _ _).mpr (Or.inr ⟨e, rfl, hv⟩)

theorem augmented_connected (i : I) : (G.induce (R.augmentedBase i : Set V)).Connected := by
  classical
  have haux (S : Finset E) (hS : ∀ e ∈ S, R.source e = i) :
      (G.induce (↑(R.base i ∪ S.biUnion fun e => (R.path e).dropLast.vertexSet) : Set V)).Connected := by
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.biUnion_empty, Finset.union_empty]
      exact R.connected i
    | @insert e S he ih =>
      have hc := ih (fun f hf => hS f (Finset.mem_insert_of_mem hf))
      have hsrc : (R.path e).dropLast.source ∈ R.base i := by
        rw [← hS e (Finset.mem_insert_self _ _)]
        exact R.starts e
      have heq : R.base i ∪ (insert e S).biUnion (fun f => (R.path f).dropLast.vertexSet) =
          (R.base i ∪ S.biUnion (fun f => (R.path f).dropLast.vertexSet)) ∪
            (R.path e).dropLast.vertexSet := by
        rw [Finset.biUnion_insert]
        ac_rfl
      rw [heq, Finset.coe_union]
      exact _root_.SimpleGraph.induce_union_connected hc.preconnected
        (R.path e).dropLast.connected_induce_vertexSet.preconnected
        ⟨_, Finset.mem_union_left _ hsrc, (R.path e).dropLast.source_mem_vertexSet⟩
  exact haux (R.edgesFrom i) (fun e he => (R.mem_edgesFrom e i).mp he)

theorem augmented_disjoint : Pairwise fun i j => Disjoint (R.augmentedBase i) (R.augmentedBase j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rcases (R.mem_augmentedBase i v).mp hvi with hvi | ⟨e, hei, hve⟩
  · rcases (R.mem_augmentedBase j v).mp hvj with hvj | ⟨f, hfj, hvf⟩
    · exact Finset.disjoint_left.mp (R.disjoint hij) hvi hvj
    · exact hij ((R.halfOpen_meets_base f i hvf hvi).symm.trans hfj)
  · rcases (R.mem_augmentedBase j v).mp hvj with hvj | ⟨f, hfj, hvf⟩
    · exact hij (hei.symm.trans (R.halfOpen_meets_base e j hve hvj))
    · have hef : e ≠ f := fun h => hij (hei.symm.trans ((congrArg R.source h).trans hfj))
      exact Finset.disjoint_left.mp (R.paths_disjoint hef)
        ((R.path e).dropLast_vertexSet_subset hve) ((R.path f).dropLast_vertexSet_subset hvf)

noncomputable def toMinorModel : MinorModel H G where
  branchSet := R.augmentedBase
  branch_nonempty i := (R.nonempty i).mono (R.base_subset_augmented i)
  branch_connected := R.augmented_connected
  branch_disjoint := R.augmented_disjoint
  adjacent := by
    intro i j hij
    obtain ⟨e, he⟩ := R.realizes hij
    have hsrc : (R.path e).penultimate ∈ R.augmentedBase (R.source e) :=
      R.halfOpen_subset_augmented e (R.path e).dropLast.target_mem_vertexSet
    have htgt := R.base_subset_augmented (R.target e) (R.ends e)
    have hadj := (R.path e).penultimate_adj_target (R.path_nontrivial e)
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, hsrc, _, htgt, hadj⟩
    · exact ⟨_, htgt, _, hsrc, hadj.symm⟩

end BranchRouting
end Erdos73Infrastructure.SimpleGraph
