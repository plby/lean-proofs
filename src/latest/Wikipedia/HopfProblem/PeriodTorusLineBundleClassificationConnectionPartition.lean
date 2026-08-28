import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopologicalCover
import Wikipedia.HopfProblem.HolomorphicCousinSmoothCocycle

/-!
# A constructed smooth partition for the native transition cover

The partition used in the connection construction is obtained from the actual
open cover by the smooth partition-of-unity theorem on the finite-dimensional
real vector space underlying `ℂ²`. It is not additional input data.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnection

open HolomorphicCharacterBundle

local notation "Iℝ" => modelWithCornersSelf ℝ ComplexPlane₂

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

/-- The actual native transition cover admits a subordinate smooth partition. -/
theorem exists_subordinatePartition :
    ∃ ρ : SmoothPartitionOfUnity ι Iℝ ComplexPlane₂ univ, ρ.IsSubordinate A.baseSet :=
  SmoothPartitionOfUnity.exists_isSubordinate Iℝ isClosed_univ A.baseSet A.isOpen_baseSet
    (fun x _ => mem_iUnion.mpr ⟨A.indexAt x, A.mem_baseSet_at x⟩)

/-- A smooth partition obtained from the preceding existence theorem. -/
def subordinatePartition : SmoothPartitionOfUnity ι Iℝ ComplexPlane₂ univ :=
  (exists_subordinatePartition A).choose

theorem subordinatePartition_isSubordinate :
    (subordinatePartition A).IsSubordinate A.baseSet :=
  (exists_subordinatePartition A).choose_spec

theorem subordinatePartition_tsupport_subset (i : ι) :
    tsupport (subordinatePartition A i) ⊆ A.baseSet i :=
  subordinatePartition_isSubordinate A i

theorem subordinatePartition_locallyFinite :
    LocallyFinite (fun i => support (subordinatePartition A i)) :=
  (subordinatePartition A).locallyFinite

theorem subordinatePartition_tsupport_locallyFinite :
    LocallyFinite (fun i => tsupport (subordinatePartition A i)) :=
  (subordinatePartition A).locallyFinite.closure

theorem subordinatePartition_contDiff (i : ι) :
    ContDiff ℝ ∞ (subordinatePartition A i) :=
  (subordinatePartition A i).contMDiff.contDiff

theorem subordinatePartition_nonneg (i : ι) (x : ComplexPlane₂) :
    0 ≤ subordinatePartition A i x := (subordinatePartition A).nonneg i x

theorem subordinatePartition_sum_eq_one (x : ComplexPlane₂) :
    ∑ᶠ i, subordinatePartition A i x = 1 :=
  (subordinatePartition A).sum_eq_one (mem_univ x)

theorem subordinatePartition_sum_finsupport (x : ComplexPlane₂) :
    ∑ i ∈ (subordinatePartition A).finsupport x, subordinatePartition A i x = 1 :=
  (subordinatePartition A).sum_finsupport x (mem_univ x)

theorem subordinatePartition_mem_cover {x : ComplexPlane₂} {i : ι}
    (hi : i ∈ (subordinatePartition A).finsupport x) : x ∈ A.baseSet i :=
  HolomorphicCousin.mem_cover_of_mem_finsupport (subordinatePartition_isSubordinate A) hi

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnection
