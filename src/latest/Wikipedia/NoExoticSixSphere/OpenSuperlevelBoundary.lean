import Wikipedia.NoExoticSixSphere.OpenSuperlevelAtlas
import Wikipedia.NoExoticSixSphere.RegularLevelDifferential

/-!
# The actual boundary of an open regular-superlevel piece

The native boundary subtype is homeomorphic to an open subset of the actual
zero fiber. This gives its codimension-one smooth structure using the
independently constructed regular-level atlas, with smooth inclusion and
an ambient smooth-map criterion.
-/

noncomputable section

open Set Topology TopologicalSpace Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OpenSuperlevelBoundary

section Topology

variable {M : Type*} [TopologicalSpace M] (f : M → ℝ)

def zeroInclusion (p : {x : M // f x = 0}) : {x : M // 0 ≤ f x} :=
  ⟨p.val, by rw [p.property]⟩

theorem continuous_zeroInclusion : Continuous (zeroInclusion f) :=
  continuous_subtype_val.subtype_mk _

def zeroWindow (U : Opens {x : M // 0 ≤ f x}) : Opens {x : M // f x = 0} :=
  ⟨zeroInclusion f ⁻¹' U, U.isOpen.preimage (continuous_zeroInclusion f)⟩

end Topology

variable {B H M K N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {f : M → ℝ} (A : SuperlevelAtlas (K := K) I f)
  (U : Opens {x : M // 0 ≤ f x}) [TopologicalSpace N] (e : N ≃ₜ U)

abbrev Boundary := letI := OpenSuperlevelAtlas.chartedSpace A U e;
  {x : N // (ProductHalfSpace.model K).IsBoundaryPoint x}

def homeomorph : Boundary A U e ≃ₜ zeroWindow f U := by
  let := OpenSuperlevelAtlas.chartedSpace A U e
  let forward : Boundary A U e → zeroWindow f U := fun p ↦
    ⟨⟨(e p.val).val.val, (OpenSuperlevelAtlas.isBoundaryPoint_iff A U e p.val).mp p.property⟩,
      (e p.val).property⟩
  let backward : zeroWindow f U → Boundary A U e := fun p ↦
    ⟨e.symm ⟨zeroInclusion f p.val, p.property⟩,
      (OpenSuperlevelAtlas.isBoundaryPoint_iff A U e _).mpr (by
        rw [e.apply_symm_apply]
        exact p.val.property)⟩
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro p
    apply Subtype.ext
    exact e.symm_apply_apply p.val
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    change (e (e.symm ⟨zeroInclusion f p.val, p.property⟩)).val.val = p.val.val
    rw [e.apply_symm_apply]
    rfl
  · have hc : Continuous (fun p : Boundary A U e ↦ (e p.val).val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp
        (e.continuous.comp continuous_subtype_val))
    exact (hc.subtype_mk _).subtype_mk _
  · exact (e.symm.continuous.comp
      (((continuous_zeroInclusion f).comp continuous_subtype_val).subtype_mk _)).subtype_mk _

theorem homeomorph_coordinates (p : Boundary A U e) :
    (homeomorph A U e p).val.val = (e p.val).val.val := rfl

variable (R : RegularLevelAtlas (K := K) I f)

@[instance_reducible]
def chartedSpace : ChartedSpace K (Boundary A U e) := by
  let := R.chartedSpace
  exact ModelAtlasTransport.atlas (homeomorph A U e)

theorem isManifold : letI := chartedSpace A U e R;
    IsManifold 𝓘(ℝ, K) ∞ (Boundary A U e) := by
  let := R.chartedSpace
  let := R.isManifold
  exact ModelAtlasTransport.isManifold (homeomorph A U e) 𝓘(ℝ, K)

def diffeomorph : letI := R.chartedSpace; letI := chartedSpace A U e R;
    Boundary A U e ≃ₘ⟮𝓘(ℝ, K), 𝓘(ℝ, K)⟯ zeroWindow f U := by
  let := R.chartedSpace
  exact ModelAtlasTransport.diffeomorph (homeomorph A U e) 𝓘(ℝ, K)

theorem contMDiff_coordinates : letI := chartedSpace A U e R;
    ContMDiff 𝓘(ℝ, K) I ∞ (fun p : Boundary A U e ↦ (e p.val).val.val) := by
  let := R.chartedSpace
  let := R.isManifold
  let := chartedSpace A U e R
  exact (R.contMDiff_subtype_val.comp
    (_root_.contMDiff_subtype_val (U := zeroWindow f U))).comp
      (diffeomorph A U e R).contMDiff_toFun

theorem contMDiff_inclusion : letI := OpenSuperlevelAtlas.chartedSpace A U e;
    letI := chartedSpace A U e R;
    ContMDiff 𝓘(ℝ, K) (ProductHalfSpace.model K) ∞
      (Subtype.val : Boundary A U e → N) := by
  let := OpenSuperlevelAtlas.chartedSpace A U e
  let := chartedSpace A U e R
  exact (OpenSuperlevelAtlas.contMDiff_iff_coordinates A U e Subtype.val).mpr
    (contMDiff_coordinates A U e R)

variable {B' H' P : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ B' H'}
  [TopologicalSpace P] [ChartedSpace H' P]

theorem contMDiffAt_iff_coordinates (g : P → Boundary A U e) (x : P) :
    letI := chartedSpace A U e R;
    ContMDiffAt J 𝓘(ℝ, K) ∞ g x ↔ ContMDiffAt J I ∞ (fun y ↦ (e (g y).val).val.val) x := by
  let := R.chartedSpace
  let := R.isManifold
  let := chartedSpace A U e R
  constructor
  · intro hg
    exact (contMDiff_coordinates A U e R).contMDiffAt.comp x hg
  · intro hg
    let g' := homeomorph A U e ∘ g
    have hz : ContMDiffAt J 𝓘(ℝ, K) ∞ (fun y ↦ (g' y).val) x :=
      (R.contMDiffAt_iff_ambient (fun y ↦ (g' y).val) x).mpr hg
    have hw := (ContMDiffAt.subtypeVal_comp_iff (zeroWindow f U) g' x).mp hz
    have h := (diffeomorph A U e R).symm.contMDiff_toFun.contMDiffAt.comp x hw
    change ContMDiffAt J 𝓘(ℝ, K) ∞
      (fun y ↦ (homeomorph A U e).symm (homeomorph A U e (g y))) x at h
    simpa only [Homeomorph.symm_apply_apply] using h

theorem contMDiff_iff_coordinates (g : P → Boundary A U e) :
    letI := chartedSpace A U e R;
    ContMDiff J 𝓘(ℝ, K) ∞ g ↔ ContMDiff J I ∞ (fun y ↦ (e (g y).val).val.val) := by
  let := chartedSpace A U e R
  exact forall_congr' (fun x ↦ contMDiffAt_iff_coordinates A U e R g x)

end NoExoticSixSphere.OpenSuperlevelBoundary
