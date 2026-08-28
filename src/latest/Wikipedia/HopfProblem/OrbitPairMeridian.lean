import Wikipedia.HopfProblem.OrbitPairNormalTubeGlobal
import Wikipedia.HopfProblem.OrbitPairRadialSmooth

/-!
# The actual meridian and its normal Hopf sphere

For every positive radius smaller than the proved injective normal
radius, we construct a linking sphere in the actual global orbit space.
The normal three-sphere in the original threefold projects to this
meridian by the radius-preserving Hopf map, in a commuting diagram.
-/

noncomputable section

open Set Topology Metric

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold CuspCircleNormalTrivialization

attribute [local instance] Threefold.chartedSpace

abbrev NormalSphere (r : ℝ) := sphere (0 : Normal) r
abbrev MeridianSphere (r : ℝ) := sphere (0 : Transverse) r

theorem normalSphere_norm {r : ℝ} (v : NormalSphere r) : ‖(v : Normal)‖ = r := by
  simpa only [mem_sphere, dist_zero_right] using v.property

theorem meridianSphere_norm {r : ℝ} (y : MeridianSphere r) : ‖(y : Transverse)‖ = r := by
  simpa only [mem_sphere, dist_zero_right] using y.property

/-- The Hopf map on the literal Euclidean spheres of the same radius. -/
def sphereHopfMap (r : ℝ) : C(NormalSphere r, MeridianSphere r) where
  toFun v := ⟨radialHopfMap v, by
    simp only [mem_sphere, dist_zero_right, norm_radialHopfMap, normalSphere_norm]⟩
  continuous_toFun := (continuous_radialHopfMap.comp continuous_subtype_val).subtype_mk _

@[simp] theorem sphereHopfMap_coe {r : ℝ} (v : NormalSphere r) :
    (sphereHopfMap r v : Transverse) = radialHopfMap v := rfl

theorem sphereHopfMap_surjective (r : ℝ) : Function.Surjective (sphereHopfMap r) := by
  intro y
  obtain ⟨v, hv⟩ := radialHopfMap_surjective y.val
  have hn : ‖v‖ = r := by
    rw [← norm_radialHopfMap, hv]
    exact meridianSphere_norm y
  exact ⟨⟨v, by simpa only [mem_sphere, dist_zero_right] using hn⟩, Subtype.ext hv⟩

/-- The meridian lies over a specified point of the original fixed sphere. -/
def meridianTubePoint (b : RiemannSphere) (r : ℝ) (hr : r < injectiveRadius)
    (y : MeridianSphere r) : normalOrbitTube :=
  ⟨(b, y), by
    change ‖(y : Transverse)‖ < injectiveRadius
    rw [meridianSphere_norm]
    exact hr⟩

theorem meridianTubePoint_continuous (b : RiemannSphere) (r : ℝ)
    (hr : r < injectiveRadius) : Continuous (meridianTubePoint b r hr) :=
  (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- The actual small normal sphere, expressed in the existing scalar framing. -/
def normalSphereTubePoint (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) (v : NormalSphere r) : roundNormalProduct :=
  ⟨(b, scalarCoordinates.symm v), by
    change Complex.normSq (scalarCoordinates.symm v).1 +
      Complex.normSq (scalarCoordinates.symm v).2 < injectiveRadius ^ 2
    rw [← norm_scalarCoordinates_sq, scalarCoordinates.apply_symm_apply, normalSphere_norm]
    exact (sq_lt_sq₀ hr₀.le injectiveRadius_pos.le).mpr hr⟩

theorem normalSphereTubePoint_continuous (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) : Continuous (normalSphereTubePoint b r hr₀ hr) :=
  (continuous_const.prodMk
    (scalarCoordinates.symm.continuous.comp continuous_subtype_val)).subtype_mk _

/-- The meridian map takes values in the actual global orbit quotient. -/
def meridian (b : RiemannSphere) (r : ℝ) (hr : r < injectiveRadius) :
    C(MeridianSphere r, CircleOrbitSpace.OrbitSpace) :=
  ⟨normalOrbitTubeMap ∘ meridianTubePoint b r hr,
    normalOrbitTubeMap_continuous.comp (meridianTubePoint_continuous b r hr)⟩

/-- The normal sphere map takes values in the original threefold. -/
def normalSphereMap (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) : C(NormalSphere r, Threefold.Space) :=
  ⟨roundProductMap ∘ normalSphereTubePoint b r hr₀ hr,
    roundProductMap_contMDiff.continuous.comp (normalSphereTubePoint_continuous b r hr₀ hr)⟩

theorem normalTubeProjection_normalSphereTubePoint (b : RiemannSphere) (r : ℝ)
    (hr₀ : 0 < r) (hr : r < injectiveRadius) (v : NormalSphere r) :
    normalTubeProjection (normalSphereTubePoint b r hr₀ hr v) =
      meridianTubePoint b r hr (sphereHopfMap r v) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change scalarHopfMap (scalarCoordinates.symm v) = radialHopfMap v
    rw [scalarHopfMap, scalarCoordinates.apply_symm_apply]

/-- The actual global quotient restricts to the Hopf map on this actual normal sphere. -/
theorem quotientMap_normalSphereMap (b : RiemannSphere) (r : ℝ)
    (hr₀ : 0 < r) (hr : r < injectiveRadius) (v : NormalSphere r) :
    CircleOrbitSpace.quotientMap (normalSphereMap b r hr₀ hr v) =
      meridian b r hr (sphereHopfMap r v) := by
  change CircleOrbitSpace.quotientMap (roundProductMap (normalSphereTubePoint b r hr₀ hr v)) = _
  rw [← normalOrbitTubeMap_projection, normalTubeProjection_normalSphereTubePoint]
  rfl

theorem meridian_injective (b : RiemannSphere) (r : ℝ) (hr : r < injectiveRadius) :
    Function.Injective (meridian b r hr) := by
  intro y z he
  have ht := normalOrbitTubeMap_injective he
  exact Subtype.ext (congrArg (fun p : normalOrbitTube => p.val.2) ht)

theorem normalSphereMap_injective (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) : Function.Injective (normalSphereMap b r hr₀ hr) := by
  intro v w he
  have ht := roundProductMap_injective he
  apply Subtype.ext
  apply scalarCoordinates.symm.injective
  exact congrArg (fun p : roundNormalProduct => p.val.2) ht

/-- The meridian is contained in the free orbit locus. -/
theorem meridian_not_mem_fixed (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) (y : MeridianSphere r) :
    meridian b r hr y ∉ range CircleOrbitSpace.fixedCurveMap := by
  change normalOrbitTubeMap (meridianTubePoint b r hr y) ∉
    range CircleOrbitSpace.fixedCurveMap
  rw [normalOrbitTubeMap_mem_fixed_iff]
  change (y : Transverse) ≠ 0
  intro hy
  have hn := meridianSphere_norm y
  rw [hy, norm_zero] at hn
  exact hr₀.ne' hn.symm

end Wikipedia.HopfProblem.OrbitPair
