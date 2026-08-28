import Wikipedia.NoExoticSixSphere.RoundedCollarHomeomorph
import Wikipedia.NoExoticSixSphere.FramedAttachingDimension
import Wikipedia.NoExoticSixSphere.RoundedCollarLevel
import Wikipedia.NoExoticSixSphere.SuperlevelBoundary
import Wikipedia.NoExoticSixSphere.SuperlevelInclusion
import Wikipedia.NoExoticSixSphere.ModelAtlasTransport

/-!
# A smooth boundary atlas on the actual open rounded collar

The regular superlevel construction gives a boundary manifold in one higher
dimension than the original manifold. Restrict it to the proved open
parameter window and use the actual
collar homeomorphism to equip the relatively open subset of the rounded
attachment with this atlas. Its existing topology is retained, and no global
compactness is assumed. The model dimension follows from the actual tube.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel RoundedHandleCorner

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def collarLevelAtlas : SuperlevelAtlas (K := Vector n) (collarModel (n - 3))
    (collarLevel (d := n - 3) (bump A) (UnroundedTrace.handleRadius A)) :=
  collarSuperlevelAtlasOfDimension (bump A) (UnroundedTrace.handleRadius_pos A)
    n A.sphere_transverse_dimension

abbrev CollarSuperlevel :=
  {p : Collar (n - 3) // 0 ≤ collarLevel (d := n - 3) (bump A) (UnroundedTrace.handleRadius A) p}

def collarWindow : Opens (CollarSuperlevel A) where
  carrier := {p | p.val.1.2 ∈ ball (0 : Vector (n - 3)) A.radius ∧
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
def collarChartedSpace : ChartedSpace (ProductHalfSpace.Space (Vector n)) (collarPart A) := by
  let := (collarLevelAtlas A).chartedSpace
  exact ModelAtlasTransport.atlas (collarWindowHomeomorph A)

theorem collar_isManifold : letI := collarChartedSpace A;
    IsManifold (ProductHalfSpace.model (Vector n)) ∞ (collarPart A) := by
  let := (collarLevelAtlas A).chartedSpace
  let := (collarLevelAtlas A).isManifold
  exact ModelAtlasTransport.isManifold (collarWindowHomeomorph A)
    (ProductHalfSpace.model (Vector n))

def collarWindowDiffeomorph : letI := (collarLevelAtlas A).chartedSpace;
    letI := collarChartedSpace A;
    collarPart A ≃ₘ⟮ProductHalfSpace.model (Vector n), ProductHalfSpace.model (Vector n)⟯
      collarWindow A := by
  let := (collarLevelAtlas A).chartedSpace
  exact ModelAtlasTransport.diffeomorph (collarWindowHomeomorph A)
    (ProductHalfSpace.model (Vector n))

theorem collar_isBoundaryPoint_iff (p : collarPart A) : letI := collarChartedSpace A;
    (ProductHalfSpace.model (Vector n)).IsBoundaryPoint p ↔
      collarLevel (d := n - 3) (bump A) (UnroundedTrace.handleRadius A)
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
    ContMDiff (ProductHalfSpace.model (Vector n)) (collarModel (n - 3)) ∞
      (fun p : collarPart A ↦ ((collarHomeomorph A).symm p).val) := by
  let := (collarLevelAtlas A).chartedSpace
  let := (collarLevelAtlas A).isManifold
  let := collarChartedSpace A
  exact ((collarLevelAtlas A).contMDiff_subtype_val.comp
    (_root_.contMDiff_subtype_val (U := collarWindow A))).comp
      (collarWindowDiffeomorph A).contMDiff_toFun

theorem contMDiff_collar_ambient : letI := collarChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector n)) (𝓡 (e.ambientDimension + 6)) ∞
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
    ContMDiffAt J (ProductHalfSpace.model (Vector n)) ∞ g x ↔
      ContMDiffAt J (collarModel (n - 3)) ∞ (fun y ↦ ((collarHomeomorph A).symm (g y)).val) x := by
  let := (collarLevelAtlas A).chartedSpace
  let := (collarLevelAtlas A).isManifold
  let := collarChartedSpace A
  constructor
  · intro hg
    exact (contMDiff_collarParameters A).contMDiffAt.comp x hg
  · intro hg
    let g' := collarWindowHomeomorph A ∘ g
    have hz : ContMDiffAt J (ProductHalfSpace.model (Vector n)) ∞
        (fun y ↦ (g' y).val) x :=
      ((collarLevelAtlas A).contMDiffAt_iff_ambient (fun y ↦ (g' y).val) x).mpr hg
    have hw := (ContMDiffAt.subtypeVal_comp_iff (collarWindow A) g' x).mp hz
    have h := (collarWindowDiffeomorph A).symm.contMDiff_toFun.contMDiffAt.comp x hw
    change ContMDiffAt J (ProductHalfSpace.model (Vector n)) ∞
      (fun y ↦ (collarWindowHomeomorph A).symm (collarWindowHomeomorph A (g y))) x at h
    simpa only [Homeomorph.symm_apply_apply] using h

theorem contMDiff_collar_iff_parameters (g : P → collarPart A) :
    letI := collarChartedSpace A;
    ContMDiff J (ProductHalfSpace.model (Vector n)) ∞ g ↔
      ContMDiff J (collarModel (n - 3)) ∞ (fun y ↦ ((collarHomeomorph A).symm (g y)).val) := by
  let := collarChartedSpace A
  exact forall_congr' (fun x ↦ contMDiffAt_collar_iff_parameters A g x)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
