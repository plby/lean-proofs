import Wikipedia.NoExoticSixSphere.UnitAttachingFace
import Wikipedia.NoExoticSixSphere.RoundedTraceSurgeryOverlaps

/-!
# Coordinates from the actual rounded end into unit-radius surgery

The original manifold is never recharted. The old surgery patch deletes
exactly the attaching core, and its collar parameter is the ordinary tube
vector of radius `sqrt (1 + u)`. Normalization makes this agree with the
handle-side squared-radius coordinate.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedHandleCorner RoundedTrace
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def face : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M :=
  A.unitClosedFace (by rw [hR]; norm_num)

include hR in
theorem handleRadius_eq_one : UnroundedTrace.handleRadius A = 1 := by
  rw [UnroundedTrace.handleRadius, hR]
  norm_num

theorem tube_mem_core_iff (s : Sphere 3) {v : Vector 3}
    (hv : v ∈ closedBall (0 : Vector 3) A.radius) : A.tube (s, v) ∈ range f ↔ v = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    have hz : (0 : Vector 3) ∈ closedBall 0 A.radius := mem_closedBall_self A.radius_pos.le
    have hp : (w, (⟨0, hz⟩ : closedBall (0 : Vector 3) A.radius)) = (s, ⟨v, hv⟩) :=
      A.tube_embedded.injective ((A.tube_core w).trans hw)
    have he := congrArg (fun p : Sphere 3 × closedBall (0 : Vector 3) A.radius ↦ p.2.val) hp
    exact he.symm
  · rintro rfl
    exact ⟨s, (A.tube_core s).symm⟩

variable [T2Space M]

omit [T2Space M] in
theorem range_face_coreMap : range (FramedSurgery.coreMap (E := Vector 4) (face A hR)) =
    range f := by
  congr 1
  funext s
  exact A.tube_core s

abbrev OldPatch := FramedSurgery.oldPatch (E := Vector 4) (face A hR)

abbrev Target := FramedSurgery.Boundary (E := Vector 4) (F := Vector 3) (face A hR) 2

def oldTubePoint (s : Sphere 3) {v : Vector 3}
    (hv : v ∈ closedBall (0 : Vector 3) A.radius) (hne : v ≠ 0) : OldPatch A hR :=
  ⟨A.tube (s, v), by
    change A.tube (s, v) ∉ range (FramedSurgery.coreMap (E := Vector 4) (face A hR))
    rw [range_face_coreMap A hR]
    exact fun h ↦ hne ((tube_mem_core_iff A s hv).mp h)⟩

variable [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
include hR in
theorem radialGap_eq_three : radialGap A = 3 := by
  rw [radialGap, hR, handleRadius_eq_one A hR]
  norm_num

omit [T2Space M] in
theorem collar_parameter_gt_neg_one (p : boundaryCollarParameters A) : -1 < p.val.2.2 := by
  have hp := (mem_boundaryCollarParameters_iff_interval A p.val).mp p.property
  nlinarith [collarHeight_lt_gap A, sq_nonneg A.innerRadius, hp.1]

def collarOriginalVector (p : boundaryCollarParameters A) : Vector 3 :=
  Real.sqrt (1 + p.val.2.2) • p.val.2.1.val

omit [T2Space M] in
theorem norm_collarOriginalVector (p : boundaryCollarParameters A) :
    ‖collarOriginalVector A p‖ = Real.sqrt (1 + p.val.2.2) := by
  rw [collarOriginalVector, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), ClosedHemisphere.unit_norm, mul_one]

omit [T2Space M] in
theorem collarOriginalVector_ne_zero (p : boundaryCollarParameters A) :
    collarOriginalVector A p ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_collarOriginalVector]
  exact Real.sqrt_pos.mpr (by linarith [collar_parameter_gt_neg_one A p])

omit [T2Space M] in
include hR in
theorem collarOriginalVector_mem (p : boundaryCollarParameters A) :
    collarOriginalVector A p ∈ closedBall (0 : Vector 3) A.radius := by
  have hp := (mem_boundaryCollarParameters_iff_interval A p.val).mp p.property
  rw [radialGap_eq_three A hR] at hp
  have hs : (Real.sqrt (1 + p.val.2.2)) ^ 2 = 1 + p.val.2.2 :=
    Real.sq_sqrt (by linarith [collar_parameter_gt_neg_one A p])
  rw [mem_closedBall, dist_zero_right, norm_collarOriginalVector, hR]
  nlinarith [Real.sqrt_nonneg (1 + p.val.2.2), hp.2]

def collarPoint (p : boundaryCollarParameters A) : OldPatch A hR :=
  oldTubePoint A hR p.val.1 (collarOriginalVector_mem A hR p) (collarOriginalVector_ne_zero A p)

def exteriorPoint (m : retainedExterior A) : OldPatch A hR :=
  ⟨m.val, by
    change m.val ∉ range (FramedSurgery.coreMap (E := Vector 4) (face A hR))
    rw [range_face_coreMap A hR]
    rintro ⟨s, hs⟩
    apply m.property
    exact ⟨(s, 0), ⟨mem_univ _, mem_closedBall_self (outerRadius_nonneg A)⟩,
      (A.tube_core s).trans hs⟩⟩

def handlePoint (p : boundaryHandleParameters A) : FramedSurgery.NewPatch (Vector 4) (Vector 3) :=
  (⟨p.val.1, (ball_subset_ball (handleCoreRadius_lt_one A).le)
    ((mem_boundaryHandleParameters_iff A p.val).mp p.property)⟩, p.val.2)

def exteriorMap (m : retainedExterior A) : Target A hR :=
  FramedSurgery.oldMap (E := Vector 4) (face A hR) 2 (exteriorPoint A hR m)

def handleMap (p : boundaryHandleParameters A) : Target A hR :=
  FramedSurgery.newMap (E := Vector 4) (face A hR) 2 (handlePoint A p)

def collarMap (p : boundaryCollarParameters A) : Target A hR :=
  FramedSurgery.oldMap (E := Vector 4) (face A hR) 2 (collarPoint A hR p)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
