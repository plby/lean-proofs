import Wikipedia.NoExoticSixSphere.FamilyFlatteningGerm
import Wikipedia.NoExoticSixSphere.FlatDoublePointCoordinates
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Actual pair-space coordinate comparison for the family track

The product of the constructed source-coordinate changes carries actual
distinct same-image track pairs to actual flat-map double points. Its local
image relation also carries their closures, using the unchanged topologies.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.FamilyFlattening

variable {T E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : T → E × ℝ → E × F}

def Data.sourceCoordinates (d : Data f) :
    OpenPartialHomeomorph (E × (T × ℝ)) ((T × E) × ℝ) where
  toFun := d.forward
  invFun := d.inverse
  source := d.coord.source
  target := d.target
  map_source' _ hq := d.forward_mem_target hq
  map_target' _ hr := d.inverse_mem_source hr
  left_inv' _ hq := d.inverse_forward hq
  right_inv' r hr := by
    change flatOrder.symm (d.coord (d.inverse r)) = r
    rw [d.coord_inverse hr, ContinuousLinearEquiv.symm_apply_apply]
  open_source := d.coord.open_source
  open_target := d.target.isOpen
  continuousOn_toFun :=
    (flatOrder (T := T) (E := E)).symm.continuous.comp_continuousOn
      d.coord.toOpenPartialHomeomorph.continuousOn
  continuousOn_invFun := d.contDiffOn_inverse.continuousOn

def Data.pairCoordinates (d : Data f) :
    OpenPartialHomeomorph ((E × (T × ℝ)) × (E × (T × ℝ)))
      (((T × E) × ℝ) × ((T × E) × ℝ)) :=
  d.sourceCoordinates.prod d.sourceCoordinates

def track (f : T → E × ℝ → E × F) (q : E × (T × ℝ)) : (T × E) × F :=
  ((q.2.1, head f q), tail f q)

def trackDoublePoints (f : T → E × ℝ → E × F) :
    Set ((E × (T × ℝ)) × (E × (T × ℝ))) :=
  {q | q.1 ≠ q.2 ∧ track f q.1 = track f q.2}

theorem Data.flatMap_forward (d : Data f) {q : E × (T × ℝ)} (hq : q ∈ d.coord.source) :
    FlatDoubleCurve.flatMap d.flattened (d.forward q) = track f q := by
  unfold FlatDoubleCurve.flatMap Data.flattened
  rw [d.inverse_forward hq, d.forward_apply]
  rfl

theorem Data.isImage_trackDoublePoints (d : Data f) :
    d.pairCoordinates.IsImage (trackDoublePoints f) (FlatDoubleCurve.doublePoints d.flattened) := by
  intro r hr
  change (d.forward r.1 ≠ d.forward r.2 ∧
    FlatDoubleCurve.flatMap d.flattened (d.forward r.1) =
      FlatDoubleCurve.flatMap d.flattened (d.forward r.2)) ↔
    (r.1 ≠ r.2 ∧ track f r.1 = track f r.2)
  rw [d.flatMap_forward hr.1, d.flatMap_forward hr.2]
  constructor
  · rintro ⟨hn, he⟩
    exact ⟨fun h ↦ hn (congrArg d.forward h), he⟩
  · rintro ⟨hn, he⟩
    exact ⟨fun h ↦ hn (d.sourceCoordinates.injOn hr.1 hr.2 h), he⟩

theorem Data.isImage_closedTrackDoublePoints (d : Data f) :
    d.pairCoordinates.IsImage (closure (trackDoublePoints f))
      (closure (FlatDoubleCurve.doublePoints d.flattened)) :=
  d.isImage_trackDoublePoints.closure

theorem Data.contDiffOn_pairInverse (d : Data f) :
    ContDiffOn ℝ ∞ (fun r ↦ (d.inverse r.1, d.inverse r.2)) d.pairCoordinates.target :=
  (d.contDiffOn_inverse.comp contDiff_fst.contDiffOn (fun _ hr ↦ hr.1)).prodMk
    (d.contDiffOn_inverse.comp contDiff_snd.contDiffOn (fun _ hr ↦ hr.2))

omit [NormedSpace ℝ T] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem closedTrackDoublePoints_time_eq {r : (E × (T × ℝ)) × (E × (T × ℝ))}
    (hr : r ∈ closure (trackDoublePoints f)) : r.1.2.1 = r.2.2.1 := by
  apply closure_minimal (s := trackDoublePoints f)
    (t := {r : (E × (T × ℝ)) × (E × (T × ℝ)) | r.1.2.1 = r.2.2.1}) ?_
    (isClosed_eq continuous_fst.snd.fst continuous_snd.snd.fst) hr
  intro q hq
  exact congrArg (fun z : (T × E) × F ↦ z.1.1) hq.2

end NoExoticSixSphere.FamilyFlattening
