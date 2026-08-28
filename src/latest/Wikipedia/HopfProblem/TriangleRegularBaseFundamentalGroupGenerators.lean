import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupGeneration
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCover
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupMeridians
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# The two positive meridians generate the twice-punctured plane

These are the actual radius-`1/2` circles about zero and one, both based
at `1/2`. The proof uses the explicit upper and lower slit cover and its
three proved path components, together with path subdivision. In
particular, no generation assertion about arbitrarily rebased loops is
assumed.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open TriangleRegularBaseFundamentalGroup

/-- The actual classes of the two positive circular meridians. -/
def meridianClass (b : Bool) : FundamentalGroup TwicePuncturedPlane meridianBasepoint :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
    (if b then positiveMeridianOne else positiveMeridianZero))

/-- Evaluate a free word as a product of actual meridian classes. -/
def meridianWordMap : FreeGroup Bool →* FundamentalGroup TwicePuncturedPlane meridianBasepoint :=
  FreeGroup.lift meridianClass

@[simp] theorem meridianWordMap_of (b : Bool) :
    meridianWordMap (FreeGroup.of b) = meridianClass b :=
  FreeGroup.lift_apply_of

private theorem base_mem_upper : meridianBasepoint ∈ upperSlit := by
  change (meridianBasepoint : ℂ) ∈ upperSlitPlane
  simpa using upperZeroPath_mem_upperSlitPlane 0

private theorem base_mem_lower : meridianBasepoint ∈ lowerSlit := by
  change (meridianBasepoint : ℂ) ∈ lowerSlitPlane
  simpa using lowerZeroPath_mem_lowerSlitPlane 0

private theorem left_mem_upper : meridianLeftPoint ∈ upperSlit := by
  change (meridianLeftPoint : ℂ) ∈ upperSlitPlane
  simpa using upperZeroPath_mem_upperSlitPlane 1

private theorem left_mem_lower : meridianLeftPoint ∈ lowerSlit := by
  change (meridianLeftPoint : ℂ) ∈ lowerSlitPlane
  simpa using lowerZeroPath_mem_lowerSlitPlane 1

private theorem right_mem_upper : meridianRightPoint ∈ upperSlit := by
  change (meridianRightPoint : ℂ) ∈ upperSlitPlane
  simpa using upperOnePath_mem_upperSlitPlane 1

private theorem right_mem_lower : meridianRightPoint ∈ lowerSlit := by
  change (meridianRightPoint : ℂ) ∈ lowerSlitPlane
  simpa using lowerOnePath_mem_lowerSlitPlane 1

/-- The two-set simply connected cover is instantiated by actual slit domains. -/
def meridianSlitCover : TwoSimplyConnectedCover TwicePuncturedPlane where
  U := upperSlit
  V := lowerSlit
  cover := upperSlit_union_lowerSlit
  simplyU := upperSlit_simplyConnectedSpace
  simplyV := lowerSlit_simplyConnectedSpace
  base := meridianBasepoint
  baseU := base_mem_upper
  baseV := base_mem_lower

private theorem switch_left :
    meridianSlitCover.switchClass meridianLeftPoint left_mem_upper left_mem_lower =
      meridianClass false :=
  meridianSlitCover.switchClass_eq_of_paths left_mem_upper left_mem_lower
    upperZeroPath lowerZeroPath upperZeroPath_mem_upperSlitPlane lowerZeroPath_mem_lowerSlitPlane

private theorem switch_right :
    meridianSlitCover.switchClass meridianRightPoint right_mem_upper right_mem_lower =
      (meridianClass true)⁻¹ := by
  rw [meridianSlitCover.switchClass_eq_of_paths right_mem_upper right_mem_lower
    upperOnePath lowerOnePath upperOnePath_mem_upperSlitPlane lowerOnePath_mem_lowerSlitPlane]
  change Path.Homotopic.Quotient.mk (upperOnePath.trans lowerOnePath.symm) =
    Path.Homotopic.Quotient.mk (lowerOnePath.trans upperOnePath.symm).symm
  rw [Path.trans_symm, Path.symm_symm]

private def overlapRepresentative : Fin 3 → TwicePuncturedPlane
  | 0 => meridianLeftPoint
  | 1 => meridianBasepoint
  | 2 => meridianRightPoint

private theorem overlapRepresentative_mem (i : Fin 3) :
    overlapRepresentative i ∈ slitOverlapStrip i := by
  fin_cases i <;>
    norm_num [overlapRepresentative, slitOverlapStrip, overlapStrip,
      meridianLeftPoint, meridianBasepoint, meridianRightPoint]

private theorem overlapRepresentative_mem_upper (i : Fin 3) :
    overlapRepresentative i ∈ meridianSlitCover.U :=
  (slitOverlapStrip_subset_overlap i (overlapRepresentative_mem i)).1

private theorem overlapRepresentative_mem_lower (i : Fin 3) :
    overlapRepresentative i ∈ meridianSlitCover.V :=
  (slitOverlapStrip_subset_overlap i (overlapRepresentative_mem i)).2

private theorem every_overlap_point_joined (x : TwicePuncturedPlane)
    (hxU : x ∈ meridianSlitCover.U) (hxV : x ∈ meridianSlitCover.V) :
    ∃ i : Fin 3, JoinedIn ((meridianSlitCover.U : Set TwicePuncturedPlane) ∩
      meridianSlitCover.V) (overlapRepresentative i) x := by
  have hx : x ∈ ⋃ i : Fin 3, (slitOverlapStrip i : Set TwicePuncturedPlane) := by
    rw [slitOverlapStrip_iUnion]
    exact ⟨hxU, hxV⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact ⟨i, slitOverlap_joinedIn_iff.mpr ⟨i, overlapRepresentative_mem i, hi⟩⟩

/-- Every actual loop class is a word in the two explicitly oriented meridians. -/
theorem meridianWordMap_surjective : Function.Surjective meridianWordMap := by
  apply MonoidHom.range_eq_top.mp
  apply meridianSlitCover.subgroup_eq_top_of_switchClass_mem
  intro x hxU hxV
  obtain ⟨i, hi⟩ := every_overlap_point_joined x hxU hxV
  rw [← meridianSlitCover.switchClass_eq_of_joinedIn
    (overlapRepresentative_mem_upper i) (overlapRepresentative_mem_lower i) hxU hxV hi]
  fin_cases i
  · change meridianSlitCover.switchClass meridianLeftPoint _ _ ∈ meridianWordMap.range
    rw [switch_left]
    exact ⟨FreeGroup.of false, meridianWordMap_of false⟩
  · change meridianSlitCover.switchClass meridianSlitCover.base _ _ ∈ meridianWordMap.range
    rw [meridianSlitCover.switchClass_base]
    exact meridianWordMap.range.one_mem
  · change meridianSlitCover.switchClass meridianRightPoint _ _ ∈ meridianWordMap.range
    rw [switch_right]
    exact meridianWordMap.range.inv_mem ⟨FreeGroup.of true, meridianWordMap_of true⟩

theorem meridianClasses_closure_eq_top : Subgroup.closure (range meridianClass) = ⊤ := by
  exact (FreeGroup.lift_surjective_iff_closure_range_eq_top).mp meridianWordMap_surjective

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
