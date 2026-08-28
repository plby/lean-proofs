import Wikipedia.NoExoticSixSphere.QuaternionicHopfNormalFrameHomotopy
import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductFrame

/-!
# Normal-frame homotopy on the actual product of Hopf fibers

The block homotopy retains the original product atlas and inclusion
differential. Both added normal coordinates, both signs, and both fixed
target-coordinate maps occur explicitly in its endpoint formula.
The subsequent comparison of collapse representatives is not asserted here.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff
open unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

theorem southPairAmbient_tangent_iff (p : Sphere 3 × Sphere 3) (v : SouthPairAmbientModel) :
    v ∈ (NormalFrameOfEquations.ambientDifferential
        ((𝓡 3).prod (𝓡 3)) southPairAmbient p).range ↔
      v.fst ∈ (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient p.1).range ∧
      v.snd ∈ (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient p.2).range := by
  rw [southPairAmbient_derivative]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨⟨z.1, rfl⟩, ⟨z.2, rfl⟩⟩
  · rintro ⟨⟨z, hz⟩, ⟨w, hw⟩⟩
    change NormalFrameOfEquations.ambientDifferential
      (𝓡 3) southFiberAmbient p.1 z = v.fst at hz
    change NormalFrameOfEquations.ambientDifferential
      (𝓡 3) southFiberAmbient p.2 w = v.snd at hw
    refine ⟨(z, w), ?_⟩
    change WithLp.toLp 2
      (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient p.1 z,
        NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient p.2 w) = v
    rw [hz, hw]
    rfl

theorem southPairAmbient_normal_iff (p : Sphere 3 × Sphere 3) (v : SouthPairAmbientModel) :
    v ∈ (NormalFrameOfEquations.ambientDifferential
        ((𝓡 3).prod (𝓡 3)) southPairAmbient p).rangeᗮ ↔
      v.fst ∈ (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient p.1).rangeᗮ ∧
      v.snd ∈ (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient p.2).rangeᗮ := by
  constructor
  · intro h
    rw [Submodule.mem_orthogonal'] at h
    constructor
    · rw [Submodule.mem_orthogonal']
      intro z hz
      have hh := h (WithLp.toLp 2 (z, (0 : V 8)))
        ((southPairAmbient_tangent_iff p _).mpr ⟨hz, Submodule.zero_mem _⟩)
      change inner ℝ v.fst z + inner ℝ v.snd 0 = 0 at hh
      simpa only [inner_zero_right, add_zero] using hh
    · rw [Submodule.mem_orthogonal']
      intro z hz
      have hh := h (WithLp.toLp 2 ((0 : V 8), z))
        ((southPairAmbient_tangent_iff p _).mpr ⟨Submodule.zero_mem _, hz⟩)
      change inner ℝ v.fst 0 + inner ℝ v.snd z = 0 at hh
      simpa only [inner_zero_right, zero_add] using hh
  · rintro ⟨hl, hr⟩
    rw [Submodule.mem_orthogonal'] at hl hr ⊢
    intro z hz
    obtain ⟨hzl, hzr⟩ := (southPairAmbient_tangent_iff p z).mp hz
    change inner ℝ v.fst z.fst + inner ℝ v.snd z.snd = 0
    rw [hl z.fst hzl, hr z.snd hzr, add_zero]

def southPairRadialFrame (t : ℝ) (p : Sphere 3 × Sphere 3) :
    SouthPairNormalModel →L[ℝ] SouthPairAmbientModel :=
  HilbertProduct.map (southRadialFrame t p.1) (southRadialFrame t p.2)

theorem southPairRadialFrame_injective (t : ℝ) (p : Sphere 3 × Sphere 3) :
    Function.Injective (southPairRadialFrame t p) := by
  intro v w h
  have hl := congrArg (fun x : SouthPairAmbientModel ↦ x.fst) h
  have hr := congrArg (fun x : SouthPairAmbientModel ↦ x.snd) h
  change southRadialFrame t p.1 v.fst = southRadialFrame t p.1 w.fst at hl
  change southRadialFrame t p.2 v.snd = southRadialFrame t p.2 w.snd at hr
  have hvl := southRadialFrame_injective t p.1 hl
  have hvr := southRadialFrame_injective t p.2 hr
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ
    SouthNormalModel SouthNormalModel).injective (Prod.ext hvl hvr)

theorem southPairRadialFrame_range (t : ℝ) (p : Sphere 3 × Sphere 3) :
    (southPairRadialFrame t p).range = (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) southPairAmbient p).rangeᗮ := by
  ext v
  rw [southPairAmbient_normal_iff]
  constructor
  · rintro ⟨w, rfl⟩
    constructor
    · rw [← southRadialFrame_range t p.1]
      exact ⟨w.fst, rfl⟩
    · rw [← southRadialFrame_range t p.2]
      exact ⟨w.snd, rfl⟩
  · rintro ⟨hl, hr⟩
    rw [← southRadialFrame_range t p.1] at hl
    rw [← southRadialFrame_range t p.2] at hr
    obtain ⟨z, hz⟩ := hl
    obtain ⟨w, hw⟩ := hr
    change southRadialFrame t p.1 z = v.fst at hz
    change southRadialFrame t p.2 w = v.snd at hw
    refine ⟨WithLp.toLp 2 (z, w), ?_⟩
    change WithLp.toLp 2 (southRadialFrame t p.1 z, southRadialFrame t p.2 w) = v
    rw [hz, hw]
    rfl

theorem contMDiff_southPairRadialFrame :
    ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3)))
      𝓘(ℝ, SouthPairNormalModel →L[ℝ] SouthPairAmbientModel) ∞
      (fun p : ℝ × (Sphere 3 × Sphere 3) ↦ southPairRadialFrame p.1 p.2) := by
  have hl : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3)))
      𝓘(ℝ, SouthNormalModel →L[ℝ] V 8) ∞
      (fun p : ℝ × (Sphere 3 × Sphere 3) ↦ southRadialFrame p.1 p.2.1) :=
    contMDiff_southRadialFrame.comp
      (f := fun p : ℝ × (Sphere 3 × Sphere 3) ↦ (p.1, p.2.1))
      (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))
  have hr : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3)))
      𝓘(ℝ, SouthNormalModel →L[ℝ] V 8) ∞
      (fun p : ℝ × (Sphere 3 × Sphere 3) ↦ southRadialFrame p.1 p.2.2) :=
    contMDiff_southRadialFrame.comp
      (f := fun p : ℝ × (Sphere 3 × Sphere 3) ↦ (p.1, p.2.2))
      (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd))
  exact contMDiff_const.clm_comp ((hl.clm_prodMap hr).clm_comp contMDiff_const)

theorem southPairRadialFrame_zero (p : Sphere 3 × Sphere 3) :
    southPairRadialFrame 0 p = southPairNormalFrame.ambient p := by
  rw [southPairRadialFrame, southRadialFrame_zero, southRadialFrame_zero,
    southPairNormalFrame_ambient]

theorem southPairRadialFrame_one (p : Sphere 3 × Sphere 3) (v w : V 4) (u s : ℝ) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    southPairRadialFrame 1 p (WithLp.toLp 2
        (WithLp.toLp 2 ((2 : ℝ) * (-u), (2 : ℝ) • targetTailChartEquiv.symm v),
          WithLp.toLp 2 ((2 : ℝ) * (-s), (2 : ℝ) • targetTailChartEquiv.symm w))) =
      WithLp.toLp 2
        (StereographicEquator.lift 7 (southChartFrame.ambient (southFiberDiffeomorph p.1) v) +
          u • (spherePole 7).val,
        StereographicEquator.lift 7 (southChartFrame.ambient (southFiberDiffeomorph p.2) w) +
          s • (spherePole 7).val) := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])
  exact congrArg (fun z : V 8 × V 8 ↦ (WithLp.toLp 2 z : SouthPairAmbientModel))
    (Prod.ext (southRadialFrame_one p.1 v u) (southRadialFrame_one p.2 w s))

def southPairRawNormalFrameMap :
    C(Sphere 3 × Sphere 3, SouthPairNormalModel →L[ℝ] SouthPairAmbientModel) :=
  ⟨southPairNormalFrame.ambient, southPairNormalFrame.contMDiff_ambient.continuous⟩

def southPairRotatedNormalFrameMap :
    C(Sphere 3 × Sphere 3, SouthPairNormalModel →L[ℝ] SouthPairAmbientModel) where
  toFun p := southPairRadialFrame 1 p
  continuous_toFun := by
    have h : Continuous (fun p : ℝ × (Sphere 3 × Sphere 3) ↦ southPairRadialFrame p.1 p.2) :=
      contMDiff_southPairRadialFrame.continuous
    exact h.comp (f := fun p : Sphere 3 × Sphere 3 ↦ ((1 : ℝ), p))
      (continuous_const.prodMk continuous_id)

def southPairNormalFrameHomotopy :
    southPairRawNormalFrameMap.Homotopy southPairRotatedNormalFrameMap where
  toFun p := southPairRadialFrame (p.1 : ℝ) p.2
  continuous_toFun := by
    have h : Continuous (fun p : ℝ × (Sphere 3 × Sphere 3) ↦ southPairRadialFrame p.1 p.2) :=
      contMDiff_southPairRadialFrame.continuous
    exact h.comp (f := fun p : I × (Sphere 3 × Sphere 3) ↦ ((p.1 : ℝ), p.2))
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left p := southPairRadialFrame_zero p
  map_one_left _ := rfl

theorem southPairNormalFrameHomotopy_injective (t : I) (p : Sphere 3 × Sphere 3) :
    Function.Injective (southPairNormalFrameHomotopy (t, p)) :=
  southPairRadialFrame_injective t p

theorem southPairNormalFrameHomotopy_range (t : I) (p : Sphere 3 × Sphere 3) :
    (southPairNormalFrameHomotopy (t, p)).range = (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) southPairAmbient p).rangeᗮ :=
  southPairRadialFrame_range t p

end NoExoticSixSphere.QuaternionicHopf
