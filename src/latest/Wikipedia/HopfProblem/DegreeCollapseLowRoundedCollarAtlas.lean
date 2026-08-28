import Wikipedia.HopfProblem.DegreeCollapseLowAttachingDimension
import Wikipedia.HopfProblem.DegreeCollapseLowRoundedCollarHomeomorph
import Wikipedia.HopfProblem.DegreeCollapseLowRoundedCollarLevel
import Wikipedia.NoExoticSixSphere.SuperlevelBoundary
import Wikipedia.NoExoticSixSphere.SuperlevelInclusion
import Wikipedia.NoExoticSixSphere.ModelAtlasTransport

/-!

# A smooth boundary atlas on the actual open rounded collar

The regular superlevel construction gives a eight-dimensional boundary
manifold. Restrict it to the proved open parameter window and use the actual
collar homeomorphism to equip the relatively open subset of the rounded
attachment with this atlas. Its existing topology is retained.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel LowRoundedHandleCorner

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def collarLevelAtlas : SuperlevelAtlas (K := Vector 7) (collarModel d (7 - d))
    (collarLevel (d := d) (q := 7 - d) (bump A) (UnroundedTrace.handleRadius A)) :=
  collarSuperlevelAtlas (d := d) (q := 7 - d)
    (bump A) (UnroundedTrace.handleRadius_pos A) A.tube_dimension

abbrev CollarSuperlevel :=
  {p : (Collar d (7 - d)) // 0 ≤ collarLevel (bump A) (UnroundedTrace.handleRadius A) p}

def collarWindow : Opens (CollarSuperlevel A) where
  carrier := {p | p.val.1.2 ∈ ball (0 : Vector (7 - d)) A.radius ∧
    p.val.2 ∈ Ioo (-collarHeight A) (collarHeight A)}
  is_open' :=
    (isOpen_ball.preimage (continuous_subtype_val.fst.snd)).inter
      (isOpen_Ioo.preimage continuous_subtype_val.snd)

def collarParameterHomeomorph : collarParameters A ≃ₜ collarWindow A where
  toFun p := ⟨⟨p.val, p.property.2.2⟩, p.property.1, p.property.2.1⟩
  invFun p := ⟨p.val.val, p.property.1, p.property.2, p.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def collarWindowHomeomorph : collarPart A ≃ₜ collarWindow A :=
  (collarHomeomorph A).symm.trans (collarParameterHomeomorph A)

theorem collarWindowHomeomorph_val (p : collarPart A) :
    (collarWindowHomeomorph A p).val.val = ((collarHomeomorph A).symm p).val := rfl

@[instance_reducible]
def collarChartedSpace : ChartedSpace (ProductHalfSpace.Space (Vector 7)) (collarPart A) := by
  let := (collarLevelAtlas A).chartedSpace
  exact ModelAtlasTransport.atlas (collarWindowHomeomorph A)

theorem collar_isManifold : letI := collarChartedSpace A;
    IsManifold (ProductHalfSpace.model (Vector 7)) ∞ (collarPart A) := by
  let := (collarLevelAtlas A).chartedSpace
  let := (collarLevelAtlas A).isManifold
  exact ModelAtlasTransport.isManifold (collarWindowHomeomorph A)
    (ProductHalfSpace.model (Vector 7))

def collarWindowDiffeomorph : letI := (collarLevelAtlas A).chartedSpace;
    letI := collarChartedSpace A;
    collarPart A ≃ₘ⟮ProductHalfSpace.model (Vector 7), ProductHalfSpace.model (Vector 7)⟯
      collarWindow A := by
  let := (collarLevelAtlas A).chartedSpace
  exact ModelAtlasTransport.diffeomorph (collarWindowHomeomorph A)
    (ProductHalfSpace.model (Vector 7))

theorem collar_isBoundaryPoint_iff (p : collarPart A) : letI := collarChartedSpace A;
    (ProductHalfSpace.model (Vector 7)).IsBoundaryPoint p ↔
      collarLevel (bump A) (UnroundedTrace.handleRadius A)
        ((collarHomeomorph A).symm p).val = 0 := by
  let := (collarLevelAtlas A).chartedSpace
  let := (collarLevelAtlas A).isManifold
  let := collarChartedSpace A
  let := collar_isManifold A
  have h := ((collarWindowDiffeomorph A).isLocalDiffeomorph p).isBoundaryPoint_iff (by simp)
  rw [ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val,
    (collarLevelAtlas A).isBoundaryPoint_iff] at h
  exact h

theorem contMDiff_collarParameters : letI := collarChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 7)) (collarModel d (7 - d)) ∞
      (fun p : collarPart A ↦ ((collarHomeomorph A).symm p).val) := by
  let := (collarLevelAtlas A).chartedSpace
  let := (collarLevelAtlas A).isManifold
  let := collarChartedSpace A
  exact ((collarLevelAtlas A).contMDiff_subtype_val.comp
    (_root_.contMDiff_subtype_val (U := collarWindow A))).comp
      (collarWindowDiffeomorph A).contMDiff_toFun

theorem contMDiff_collar_ambient : letI := collarChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 7)) (𝓡 (e.ambientDimension + (1 + (1 + (d + 1))))) ∞
      (fun p : collarPart A ↦ p.val.val) := by
  let := collarChartedSpace A
  intro p
  have hsource := collarParameters_subset_source A ((collarHomeomorph A).symm p).property
  have hs := A.contMDiffOn_collarSheet.contMDiffAt
    (A.tubeHeightCoordinates.open_source.mem_nhds hsource)
  have hc := hs.comp p ((contMDiff_collarParameters A) p)
  exact hc.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun q ↦ (collarHomeomorph_symm_ambient A q).symm))

variable {B H P : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {J : ModelWithCorners ℝ B H}
  [TopologicalSpace P] [ChartedSpace H P]

theorem contMDiffAt_collar_iff_parameters (g : P → collarPart A) (x : P) :
    letI := collarChartedSpace A;
    ContMDiffAt J (ProductHalfSpace.model (Vector 7)) ∞ g x ↔
      ContMDiffAt J (collarModel d (7 - d)) ∞
        (fun y ↦ ((collarHomeomorph A).symm (g y)).val) x := by
  let := (collarLevelAtlas A).chartedSpace
  let := (collarLevelAtlas A).isManifold
  let := collarChartedSpace A
  constructor
  · intro hg
    exact (contMDiff_collarParameters A).contMDiffAt.comp x hg
  · intro hg
    let g' := collarWindowHomeomorph A ∘ g
    have hz : ContMDiffAt J (ProductHalfSpace.model (Vector 7)) ∞
        (fun y ↦ (g' y).val) x :=
      ((collarLevelAtlas A).contMDiffAt_iff_ambient (fun y ↦ (g' y).val) x).mpr hg
    have hw := (ContMDiffAt.subtypeVal_comp_iff (collarWindow A) g' x).mp hz
    have h := (collarWindowDiffeomorph A).symm.contMDiff_toFun.contMDiffAt.comp x hw
    change ContMDiffAt J (ProductHalfSpace.model (Vector 7)) ∞
      (fun y ↦ (collarWindowHomeomorph A).symm (collarWindowHomeomorph A (g y))) x at h
    simpa only [Homeomorph.symm_apply_apply] using h

theorem contMDiff_collar_iff_parameters (g : P → collarPart A) :
    letI := collarChartedSpace A;
    ContMDiff J (ProductHalfSpace.model (Vector 7)) ∞ g ↔
      ContMDiff J (collarModel d (7 - d)) ∞ (fun y ↦ ((collarHomeomorph A).symm (g y)).val) := by
  let := collarChartedSpace A
  exact forall_congr' (fun x ↦ contMDiffAt_collar_iff_parameters A g x)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
