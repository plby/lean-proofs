import Wikipedia.SmoothSixDPoincare.FramedSurgeryClosedOverlap
import Wikipedia.SmoothSixDPoincare.ClosedCoverHomeomorph

/-!
# The entire closed new face in the actual surgery boundary

The inner open-patch map and outer punctured-face map glue over two explicit
closed radial pieces. The resulting continuous map retains both the new
open disk coordinates and the common-corner identification exactly.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

abbrev ClosedNewFace (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :=
  MorseHandle.UnitDisk E × UnitSphere F

def newFaceInner (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :
    Set (ClosedNewFace E F) := {p | ‖p.1.val‖ ≤ (3 / 4 : ℝ)}

def newFaceOuter (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :
    Set (ClosedNewFace E F) := {p | (1 / 2 : ℝ) ≤ ‖p.1.val‖}

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem newFace_cover : newFaceInner E F ∪ newFaceOuter E F = univ := by
  apply eq_univ_of_forall
  intro p
  by_cases h : ‖p.1.val‖ ≤ (3 / 4 : ℝ)
  · exact Or.inl h
  · exact Or.inr (show (1 / 2 : ℝ) ≤ ‖p.1.val‖ by linarith)

theorem newFaceInner_closed : IsClosed (newFaceInner E F) :=
  isClosed_le (continuous_subtype_val.comp continuous_fst).norm continuous_const

theorem newFaceOuter_closed : IsClosed (newFaceOuter E F) :=
  isClosed_le continuous_const (continuous_subtype_val.comp continuous_fst).norm

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F]
  {G H X : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

def innerClosedFaceMap : C(newFaceInner E F, Boundary A n) :=
  (newMap A n).comp ⟨fun p =>
    (⟨p.val.1.val, mem_ball_zero_iff.mpr (p.property.trans_lt (by norm_num))⟩, p.val.2),
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)⟩

def outerClosedFaceMap : C(newFaceOuter E F, Boundary A n) :=
  (newOuterMap A n).comp ⟨fun p =>
    (⟨p.val.1.val, norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) p.property),
      mem_closedBall_zero_iff.mp p.val.1.property⟩, p.val.2),
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)⟩

theorem closedFace_agree (a : newFaceInner E F) (b : newFaceOuter E F) (h : a.val = b.val) :
    innerClosedFaceMap A n a = outerClosedFaceMap A n b := by
  have hlt : ‖b.val.1.val‖ < 1 := by
    rw [← h]
    exact a.property.trans_lt (by norm_num)
  let u : openPuncturedDisk E :=
    ⟨b.val.1.val, norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) b.property), hlt⟩
  have he := newOuterMap_open A n u b.val.2
  have hp :
      ((⟨a.val.1.val, mem_ball_zero_iff.mpr
        (a.property.trans_lt (by norm_num))⟩ : openUnitDisk E), a.val.2) =
      ((⟨u.val, mem_ball_zero_iff.mpr u.property.2⟩ : openUnitDisk E), b.val.2) :=
    Prod.ext (Subtype.ext (congrArg (fun p : ClosedNewFace E F => p.1.val) h))
      (congrArg (fun p : ClosedNewFace E F => p.2) h)
  exact (congrArg (newMap A n) hp).trans he.symm

def closedNewMap : C(ClosedNewFace E F, Boundary A n) :=
  ⟨ClosedCover.glue newFace_cover (innerClosedFaceMap A n) (outerClosedFaceMap A n),
    ClosedCover.continuous_glue newFace_cover newFaceInner_closed newFaceOuter_closed
      (innerClosedFaceMap A n) (outerClosedFaceMap A n)
      (innerClosedFaceMap A n).continuous (outerClosedFaceMap A n).continuous
      (closedFace_agree A n)⟩

theorem closedNewMap_inner (p : newFaceInner E F) :
    closedNewMap A n p.val = innerClosedFaceMap A n p :=
  ClosedCover.glue_left newFace_cover _ _ p

theorem closedNewMap_outer (p : newFaceOuter E F) :
    closedNewMap A n p.val = outerClosedFaceMap A n p :=
  ClosedCover.glue_right newFace_cover _ _ (closedFace_agree A n) p

theorem closedNewMap_open (p : NewPatch E F) :
    closedNewMap A n (⟨p.1.val, mem_closedBall_zero_iff.mpr
      (mem_ball_zero_iff.mp p.1.property).le⟩, p.2) = newMap A n p := by
  let q : ClosedNewFace E F := (⟨p.1.val, mem_closedBall_zero_iff.mpr
    (mem_ball_zero_iff.mp p.1.property).le⟩, p.2)
  by_cases h : ‖p.1.val‖ ≤ (3 / 4 : ℝ)
  · exact closedNewMap_inner A n ⟨q, h⟩
  · have hout : q ∈ newFaceOuter E F := by
      change (1 / 2 : ℝ) ≤ ‖p.1.val‖
      linarith
    have hu : p.1.val ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hout)
    exact (closedNewMap_outer A n ⟨q, hout⟩).trans
      (newOuterMap_open A n ⟨p.1.val, hu, mem_ball_zero_iff.mp p.1.property⟩ p.2)

theorem closedNewMap_corner (u : UnitSphere E) (v : UnitSphere F) :
    closedNewMap A n (⟨u.val, sphere_subset_closedBall u.property⟩, v) =
      oldMap A n (oldClosedOverlap A (u, boundaryPoint v)) := by
  let q : newFaceOuter E F := ⟨(⟨u.val, sphere_subset_closedBall u.property⟩, v), by
    change (1 / 2 : ℝ) ≤ ‖u.val‖
    rw [mem_sphere_zero_iff_norm.mp u.property]
    norm_num⟩
  exact (closedNewMap_outer A n q).trans (newOuterMap_corner A n u v)

end Wikipedia.SmoothSixDPoincare.FramedSurgery
