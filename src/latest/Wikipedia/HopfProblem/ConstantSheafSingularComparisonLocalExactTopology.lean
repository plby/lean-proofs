import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Homotopy.LocallyContractible

/-!
# Nullhomotopic inclusions of open neighborhoods

Classical local contractibility provides a neighborhood whose inclusion
into a prescribed neighborhood is nullhomotopic.  The smaller neighborhood
need not itself be open.  Shrinking it to an open neighborhood and
precomposing the actual nullhomotopy gives the open-set inclusion needed
for local exactness of the singular cochain presheaf.

The conclusion concerns Mathlib's original `Opens.toTopCat` inclusion,
not an auxiliary map or an assumed contraction of the smaller open set.
-/

open CategoryTheory TopologicalSpace Topology

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalExact

universe u

/-- A point in an open set has a smaller open neighborhood whose actual
inclusion into the given open set is nullhomotopic.  The hypothesis is
classical local contractibility, with no open-contractible-basis assumption. -/
theorem exists_open_nullhomotopic_inclusion (X : TopCat.{u})
    (hLC : LocallyContractibleSpace X) (U : Opens X) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ContinuousMap.Nullhomotopic (((Opens.toTopCat X).map (homOfLE hVU)).hom) := by
  obtain ⟨N, hNU, hN, hnull⟩ := hLC x (U : Set X) (U.isOpen.mem_nhds hx)
  obtain ⟨V, hVN, hV, hxV⟩ := mem_nhds_iff.mp hN
  let W : Opens X := ⟨V, hV⟩
  have hWU : W ≤ U := hVN.trans hNU
  refine ⟨W, hWU, hxV, ?_⟩
  exact hnull.comp_left (ContinuousMap.inclusion hVN)

/-- A contractible-neighborhood basis supplies the same actual
nullhomotopic inclusion of open subspaces. -/
theorem exists_open_nullhomotopic_inclusion_of_stronglyLocallyContractible
    (X : TopCat.{u}) [StronglyLocallyContractibleSpace X]
    (U : Opens X) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ContinuousMap.Nullhomotopic (((Opens.toTopCat X).map (homOfLE hVU)).hom) :=
  exists_open_nullhomotopic_inclusion X
    StronglyLocallyContractibleSpace.locallyContractible U x hx

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalExact
