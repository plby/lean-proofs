import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspRationalCurves
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The actual two-axis atlas on the global double curves

Each carrier below is the literal named double-curve subset of the glued
threefold, with its subspace topology. Its two affine parametrizations are
the original native cusp axes followed by the actual cusp open inclusion.
Their inversion transition constructs the complex atlas and the sphere
biholomorphism. No fixed-locus classification is assumed.
-/

noncomputable section

open Function Set Topology
open scoped Matrix ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCurve

open ToricCharts

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace
  Threefold.space_t2Space

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The literal global named curve, with its actual subspace topology. -/
abbrev Curve (i : Fin 3) := CuspGeometry.doubleCurve i

/-- The original double curve in the actual native cusp quotient. -/
abbrev NativeCurve (i : Fin 3) :=
  CuspQuotient.doubleCurve CuspGeometry.data.correction CuspGeometry.data.radius
    CuspGeometry.data.radius_pos i

/-- Restriction of the proved actual cusp open embedding to its named curve. -/
def nativeHomeomorph (i : Fin 3) : NativeCurve i ≃ₜ Curve i :=
  CuspGeometry.inclusion_openEmbedding.isEmbedding.homeomorphImage _

@[simp] theorem nativeHomeomorph_val (i : Fin 3) (x : NativeCurve i) :
    (nativeHomeomorph i x : Threefold.Space) = CuspGeometry.inclusion x.val := rfl

/-- The original two native axis maps, viewed inside the global named curve. -/
def charts (i : Fin 3) : TwoAffineCharts (Curve i) where
  left := nativeHomeomorph i ∘
    (CuspQuotient.curveCharts CuspGeometry.data.correction CuspGeometry.data.radius
      CuspGeometry.data.radius_pos i).left
  right := nativeHomeomorph i ∘
    (CuspQuotient.curveCharts CuspGeometry.data.correction CuspGeometry.data.radius
      CuspGeometry.data.radius_pos i).right
  continuous_left := (nativeHomeomorph i).continuous.comp
    (CuspQuotient.curveCharts CuspGeometry.data.correction CuspGeometry.data.radius
      CuspGeometry.data.radius_pos i).continuous_left
  continuous_right := (nativeHomeomorph i).continuous.comp
    (CuspQuotient.curveCharts CuspGeometry.data.correction CuspGeometry.data.radius
      CuspGeometry.data.radius_pos i).continuous_right
  left_injective := (nativeHomeomorph i).injective.comp
    (CuspQuotient.curveCharts CuspGeometry.data.correction CuspGeometry.data.radius
      CuspGeometry.data.radius_pos i).left_injective
  right_injective := (nativeHomeomorph i).injective.comp
    (CuspQuotient.curveCharts CuspGeometry.data.correction CuspGeometry.data.radius
      CuspGeometry.data.radius_pos i).right_injective
  inversion z hz := congrArg (nativeHomeomorph i)
    ((CuspQuotient.curveCharts CuspGeometry.data.correction CuspGeometry.data.radius
      CuspGeometry.data.radius_pos i).inversion z hz)
  endpoints_ne h :=
    (CuspQuotient.curveCharts CuspGeometry.data.correction CuspGeometry.data.radius
      CuspGeometry.data.radius_pos i).endpoints_ne ((nativeHomeomorph i).injective h)
  covered y := by
    obtain ⟨z, hz⟩ | ⟨z, hz⟩ :=
      (CuspQuotient.curveCharts CuspGeometry.data.correction CuspGeometry.data.radius
        CuspGeometry.data.radius_pos i).covered ((nativeHomeomorph i).symm y)
    · exact Or.inl ⟨z, by simp only [Function.comp_apply, hz, Homeomorph.apply_symm_apply]⟩
    · exact Or.inr ⟨z, by simp only [Function.comp_apply, hz, Homeomorph.apply_symm_apply]⟩

@[simp] theorem charts_left_val (i : Fin 3) (z : ℂ) :
    ((charts i).left z : Threefold.Space) =
      CuspGeometry.inclusion (CuspQuotient.axisMap CuspGeometry.data.correction
        CuspGeometry.data.radius CuspGeometry.data.radius_pos ToricSpace.referenceTriangle i z) :=
  rfl

@[simp] theorem charts_right_val (i : Fin 3) (z : ℂ) :
    ((charts i).right z : Threefold.Space) =
      CuspGeometry.inclusion (CuspQuotient.axisMap CuspGeometry.data.correction
        CuspGeometry.data.radius CuspGeometry.data.radius_pos
        (ToricFan.Triangle.upperNeighbour i) i z) := rfl

theorem charts_affineMap_val (i : Fin 3) (b : Bool) (z : ℂ) :
    ((charts i).affineMap b z : Threefold.Space) =
      CuspGeometry.inclusion
        ((CuspQuotient.curveCharts CuspGeometry.data.correction CuspGeometry.data.radius
          CuspGeometry.data.radius_pos i).affineMap b z).val := by
  cases b <;> rfl

/-- The atlas consists of the inverses of the actual two global axis maps. -/
@[instance_reducible] def chartedSpace (i : Fin 3) : ChartedSpace ℂ (Curve i) :=
  (charts i).chartedSpace

theorem isManifold (i : Fin 3) :
    letI := chartedSpace i
    IsManifold 𝓘(ℂ) ω (Curve i) := (charts i).isManifold

theorem charts_affineMap_holomorphic (i : Fin 3) (b : Bool) :
    letI := chartedSpace i
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((charts i).affineMap b) :=
  (charts i).affineMap_holomorphic b

/-- Each original affine axis is a local biholomorphism onto the actual curve. -/
theorem charts_affineMap_isLocalDiffeomorph (i : Fin 3) (b : Bool) :
    letI := chartedSpace i
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω ((charts i).affineMap b) := by
  let := chartedSpace i
  let := isManifold i
  have hp : ((charts i).parametrization b).symm ∈
      IsManifold.maximalAtlas 𝓘(ℂ) ω (Curve i) :=
    IsManifold.subset_maximalAtlas (mem_range_self b)
  let p : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ (Curve i) ω :=
    { toPartialEquiv := ((charts i).parametrization b).toPartialEquiv
      open_source := ((charts i).parametrization b).open_source
      open_target := ((charts i).parametrization b).open_target
      contMDiffOn_toFun := (charts_affineMap_holomorphic i b).contMDiffOn
      contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas hp }
  intro z
  refine ⟨p, ?_, fun _ _ => rfl⟩
  change z ∈ ((charts i).parametrization b).source
  rw [TwoAffineCharts.parametrization_source]
  trivial

/-- The sphere biholomorphism is constructed from the actual two-axis atlas. -/
def sphereBiholomorph (i : Fin 3) :
    letI := chartedSpace i
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) RiemannSphere (Curve i) ω := by
  letI := chartedSpace i
  exact
    { toEquiv := (charts i).homeomorph.toEquiv
      contMDiff_toFun := RiemannSphere.homeomorph_holomorphic (charts i)
      contMDiff_invFun := RiemannSphere.homeomorph_symm_holomorphic (charts i) }

/-- The bundled map is exactly the already constructed global parametrization. -/
@[simp] theorem sphereBiholomorph_val (i : Fin 3) (z : RiemannSphere) :
    letI := chartedSpace i
    (sphereBiholomorph i z : Threefold.Space) =
      CuspGeometry.doubleCurveParametrization i z := by
  let := chartedSpace i
  induction z using OnePoint.rec with
  | infty => rfl
  | coe z => rfl

@[simp] theorem sphereBiholomorph_zero (i : Fin 3) :
    letI := chartedSpace i
    (sphereBiholomorph i ((0 : ℂ) : RiemannSphere) : Threefold.Space) =
      CuspGeometry.lowerTriplePoint := by
  let := chartedSpace i
  rw [sphereBiholomorph_val, CuspGeometry.doubleCurveParametrization_zero]

@[simp] theorem sphereBiholomorph_infty (i : Fin 3) :
    letI := chartedSpace i
    (sphereBiholomorph i (∞ : RiemannSphere) : Threefold.Space) =
      CuspGeometry.upperTriplePoint := by
  let := chartedSpace i
  rw [sphereBiholomorph_val, CuspGeometry.doubleCurveParametrization_infty]

/-- The literal ambient inclusion is holomorphic for the constructed axis atlas. -/
theorem inclusion_holomorphic (i : Fin 3) :
    letI := chartedSpace i
    ContMDiff 𝓘(ℂ) IF ω (Subtype.val : Curve i → Threefold.Space) := by
  let := chartedSpace i
  apply (charts i).contMDiff_of_comp_affineMaps IF
  intro b
  cases b
  · exact CuspGeometry.inclusion_holomorphic.comp
      (CuspQuotient.axisMap_holomorphic CuspGeometry.data.correction CuspGeometry.data.radius
        CuspGeometry.data.radius_pos CuspGeometry.data.radius_lt_one
        CuspGeometry.data.holomorphic CuspGeometry.data.smallDrift ToricSpace.referenceTriangle i)
  · exact CuspGeometry.inclusion_holomorphic.comp
      (CuspQuotient.axisMap_holomorphic CuspGeometry.data.correction CuspGeometry.data.radius
        CuspGeometry.data.radius_pos CuspGeometry.data.radius_lt_one
        CuspGeometry.data.holomorphic CuspGeometry.data.smallDrift
        (ToricFan.Triangle.upperNeighbour i) i)

/-- Index one is the original second edge direction, without relabelling curves. -/
theorem edgeDirection_one : ToricFan.edgeDirection (1 : Fin 3) = ![0, 1] := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCurve
