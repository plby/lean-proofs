import Wikipedia.HopfProblem.HolomorphicMeromorphicField
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneFramesCoordinates

/-!
# The actual holomorphic coordinates used by a meromorphic sphere function

The original finite and reciprocal affine charts carry their literal
coordinate sections. The reciprocal coordinate has a nonzero holomorphic
germ at every point of its chart, including infinity, although its value
at infinity is zero. On the actual chart intersection the two coordinate
sections multiply to one, and the same equality holds in the original
meromorphic stalk fields.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereNative

open RiemannSphere HolomorphicFunctionSheaf.SphereH1
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

instance sphereGlobalDomain_connected : ConnectedSpace (⊤ : Opens RiemannSphere) :=
  Subtype.connectedSpace isConnected_univ

instance finiteChart_connected : ConnectedSpace finiteChart :=
  Subtype.connectedSpace (isConnected_range OnePoint.continuous_coe)

instance infinityChart_connected : ConnectedSpace infinityChart :=
  Subtype.connectedSpace (isConnected_range infinityParametrization_continuous)

/-- The actual affine coordinate as a native holomorphic section. -/
def finiteCoordinate : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere finiteChart :=
  fromFiniteSection finiteChart id 0 (fun _ _ => analyticAt_id)
    (fun h => (infty_not_mem_finiteChart h).elim)

@[simp] theorem finiteCoordinate_coe (z : ℂ) (hz : (z : RiemannSphere) ∈ finiteChart) :
    finiteCoordinate ⟨(z : RiemannSphere), hz⟩ = z := rfl

/-- The actual reciprocal coordinate, whose zero is the original point at infinity. -/
def infinityCoordinate :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere infinityChart :=
  ofInfinityCoefficient infinityChart le_rfl id (fun _ _ => analyticAt_id)

@[simp] theorem infinityCoordinate_coe (z : ℂ)
    (hz : (z : RiemannSphere) ∈ infinityChart) :
    infinityCoordinate ⟨(z : RiemannSphere), hz⟩ = z⁻¹ := rfl

@[simp] theorem infinityCoordinate_parametrization (u : ℂ)
    (hu : infinityParametrization u ∈ infinityChart) :
    infinityCoordinate ⟨infinityParametrization u, hu⟩ = u :=
  ofInfinityCoefficient_parametrization infinityChart le_rfl id
    (fun _ _ => analyticAt_id) u hu

/-- The reciprocal coordinate never vanishes as a holomorphic germ.
This is different from being nowhere zero as a function. -/
theorem infinityCoordinate_germ_ne_zero (x : infinityChart) :
    holomorphicGerm 𝓘(ℂ) RiemannSphere infinityChart x infinityCoordinate ≠ 0 := by
  intro hzero
  have he : infinityCoordinate = 0 :=
    HolomorphicFunctionSheaf.section_eq_of_germ_eq 𝓘(ℂ) infinityChart
      infinityCoordinate 0 x (by
        change holomorphicGerm 𝓘(ℂ) RiemannSphere infinityChart x infinityCoordinate =
          holomorphicGerm 𝓘(ℂ) RiemannSphere infinityChart x 0
        rw [hzero, map_zero])
  have hv := congrArg
    (fun f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere infinityChart =>
      f ⟨infinityParametrization 1, infinityParametrization_mem 1⟩) he
  change infinityCoordinate ⟨infinityParametrization 1, infinityParametrization_mem 1⟩ = 0 at hv
  rw [infinityCoordinate_parametrization] at hv
  exact one_ne_zero hv

/-- The actual coordinate identity on the full two-chart overlap. -/
theorem coordinate_restrictions_mul :
    HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere
        (inf_le_left : finiteChart ⊓ infinityChart ≤ finiteChart) finiteCoordinate *
      HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere
        (inf_le_right : finiteChart ⊓ infinityChart ≤ infinityChart) infinityCoordinate = 1 := by
  apply ContMDiffMap.ext
  rintro ⟨p, hp⟩
  obtain ⟨z, rfl⟩ := hp.1
  change finiteCoordinate ⟨(z : RiemannSphere), hp.1⟩ *
    infinityCoordinate ⟨(z : RiemannSphere), hp.2⟩ = 1
  rw [finiteCoordinate_coe, infinityCoordinate_coe]
  exact mul_inv_cancel₀ ((coe_mem_infinityChart_iff z).mp hp.2)

/-- The same identity in the literal original meromorphic germ field. -/
theorem coordinate_germs_mul (p : RiemannSphere)
    (hf : p ∈ finiteChart) (hi : p ∈ infinityChart) :
    sectionGerm 𝓘(ℂ) RiemannSphere finiteChart ⟨p, hf⟩ finiteCoordinate *
      sectionGerm 𝓘(ℂ) RiemannSphere infinityChart ⟨p, hi⟩ infinityCoordinate = 1 := by
  let x : (finiteChart ⊓ infinityChart : Opens RiemannSphere) := ⟨p, hf, hi⟩
  have h := congrArg (sectionGerm 𝓘(ℂ) RiemannSphere (finiteChart ⊓ infinityChart) x)
    coordinate_restrictions_mul
  simpa only [map_mul, map_one, sectionGerm_restrict] using h

theorem finite_germ_eq_inverse_infinity (p : RiemannSphere)
    (hf : p ∈ finiteChart) (hi : p ∈ infinityChart) :
    sectionGerm 𝓘(ℂ) RiemannSphere finiteChart ⟨p, hf⟩ finiteCoordinate =
      (sectionGerm 𝓘(ℂ) RiemannSphere infinityChart ⟨p, hi⟩ infinityCoordinate)⁻¹ := by
  have hne : sectionGerm 𝓘(ℂ) RiemannSphere infinityChart ⟨p, hi⟩ infinityCoordinate ≠ 0 :=
    fun h => infinityCoordinate_germ_ne_zero ⟨p, hi⟩
      ((sectionGerm_eq_zero_iff 𝓘(ℂ) RiemannSphere infinityChart ⟨p, hi⟩ _).mp h)
  calc
    _ = _ * ((sectionGerm 𝓘(ℂ) RiemannSphere infinityChart ⟨p, hi⟩ infinityCoordinate) *
        (sectionGerm 𝓘(ℂ) RiemannSphere infinityChart ⟨p, hi⟩ infinityCoordinate)⁻¹) := by
      rw [mul_inv_cancel₀ hne, mul_one]
    _ = _ := by rw [← mul_assoc, coordinate_germs_mul, one_mul]

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereNative
