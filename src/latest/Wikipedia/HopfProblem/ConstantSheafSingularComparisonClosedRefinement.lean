import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Sets.Opens

/-!
# Closed locally finite refinements for actual cochain gluing

The closed supports of a genuine subordinate bump covering give a locally
finite closed cover subordinate to any open cover of a normal paracompact
space. Near a point only the finitely many closed members containing that
point can occur. This controls the choice of a local cochain representative
without averaging coefficients, so it also applies to integer coefficients.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable {X ι : Type*} [TopologicalSpace X]

/-- A genuine closed, locally finite cover with the original open-cover indices. -/
structure ClosedRefinement (U : ι → Opens X) where
  support : ι → Set X
  isClosed : ∀ i, IsClosed (support i)
  locallyFinite : LocallyFinite support
  subordinate : ∀ i, support i ⊆ U i
  covers : ∀ x : X, ∃ i, x ∈ support i

/-- An actual subordinate bump covering supplies the closed refinement. -/
theorem exists_closedRefinement [NormalSpace X] [ParacompactSpace X]
    (U : ι → Opens X) (hU : ∀ x : X, ∃ i, x ∈ U i) :
    Nonempty (ClosedRefinement U) := by
  obtain ⟨f, hf⟩ := BumpCovering.exists_isSubordinate
    (s := (univ : Set X)) isClosed_univ (fun i => (U i : Set X))
    (fun i => (U i).isOpen) (fun x _ => mem_iUnion.mpr (hU x))
  refine ⟨⟨fun i => tsupport (f i), fun i => isClosed_tsupport (f i),
    f.locallyFinite_tsupport, hf, ?_⟩⟩
  intro x
  refine ⟨f.ind x (mem_univ x), subset_tsupport _ ?_⟩
  change f (f.ind x (mem_univ x)) x ≠ 0
  rw [f.ind_apply x (mem_univ x)]
  exact one_ne_zero

namespace ClosedRefinement

variable {U : ι → Opens X} (R : ClosedRefinement U)

/-- A selected original index whose closed member contains the point. -/
def index (x : X) : ι := (R.covers x).choose

theorem mem_support_index (x : X) : x ∈ R.support (R.index x) :=
  (R.covers x).choose_spec

theorem mem_open_index (x : X) : x ∈ U (R.index x) :=
  R.subordinate (R.index x) (R.mem_support_index x)

/-- A point belongs to only finitely many of the original closed members. -/
theorem finite_at (x : X) : {i | x ∈ R.support i}.Finite :=
  R.locallyFinite.point_finite x

/-- Near a point no new closed member can appear, and a neighborhood can
simultaneously be made smaller than all prescribed neighborhoods for the
finitely many members containing that point. -/
theorem exists_controlled_neighborhood (x : X) (V : ι → Opens X)
    (hV : ∀ i, x ∈ R.support i → x ∈ V i) :
    ∃ W : Opens X, x ∈ W ∧
      (∀ i, x ∈ R.support i → W ≤ V i) ∧
      ∀ y ∈ W, ∀ i, y ∈ R.support i → x ∈ R.support i := by
  have hsets : ∀ᶠ y in 𝓝 x, ∀ i ∈ {j | x ∈ R.support j}, y ∈ V i :=
    (Filter.eventually_all_finite (R.finite_at x)).mpr
      (fun i hi => (V i).isOpen.mem_nhds (hV i hi))
  have hindices := R.locallyFinite.eventually_subset R.isClosed x
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp (hsets.and hindices)
  refine ⟨⟨W, hWo⟩, hxW, ?_, ?_⟩
  · intro i hi y hy
    exact (hW hy).1 i hi
  · intro y hy i hi
    exact (hW hy).2 hi

end ClosedRefinement

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
