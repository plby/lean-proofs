import Wikipedia.HopfProblem.RiemannSphereHolomorphicVectorFieldsCharts
import Wikipedia.HopfProblem.RiemannSphereHolomorphicVectorFieldsChartsSmooth
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The native cotangent line of the standard analytic sphere

The fibre at `p` is the full continuous complex-linear dual of the existing
`TangentSpace 𝓘(ℂ) p`.  Its topology and analytic atlas are Mathlib's Hom-bundle
structures, induced from the unchanged tangent bundle and the trivial target
line.  The local frames below are the actual differentials of the two standard
sphere coordinates, not formal generators of a separately named line.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical

open RiemannSphere.HolomorphicVectorFields

/-- The actual continuous complex-linear cotangent space. -/
abbrev CotangentSpace (p : RiemannSphere) :=
  TangentSpace 𝓘(ℂ) p →L[ℂ] Bundle.Trivial RiemannSphere ℂ p

/-- The native Hom bundle, with its existing induced topology and analytic atlas. -/
abbrev CotangentBundle := TotalSpace (ℂ →L[ℂ] ℂ) CotangentSpace

theorem native_holomorphicVectorBundle :
    ContMDiffVectorBundle ω (ℂ →L[ℂ] ℂ) CotangentSpace 𝓘(ℂ) := inferInstance

theorem native_isManifold :
    IsManifold (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω CotangentBundle := inferInstance

/-- Native dual-bundle charts induced by the two fixed standard tangent charts. -/
def cotangentTriv (b : Bool) :
    Trivialization (ℂ →L[ℂ] ℂ) (π (ℂ →L[ℂ] ℂ) CotangentSpace) :=
  trivializationAt (ℂ →L[ℂ] ℂ) CotangentSpace (chartCenter b)

instance cotangentTriv_memTrivializationAtlas (b : Bool) :
    MemTrivializationAtlas (cotangentTriv b) := by
  unfold cotangentTriv
  infer_instance

@[simp] theorem cotangentTriv_baseSet (b : Bool) :
    (cotangentTriv b).baseSet = (chartOpen b : Set RiemannSphere) := by
  change (chartAt ℂ (chartCenter b)).source ∩ Set.univ = _
  exact inter_univ _

/-- The actual derivative-coordinate equivalence on tangent fibres. -/
def tangentChartEquiv (b : Bool) (p : RiemannSphere) (hp : p ∈ chartOpen b) :
    TangentSpace 𝓘(ℂ) p ≃L[ℂ] ℂ :=
  (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) (chartCenter b)).continuousLinearEquivAt
    ℂ p hp

@[simp] theorem tangentChartEquiv_apply (b : Bool) (p : RiemannSphere)
    (hp : p ∈ chartOpen b) (v : TangentSpace 𝓘(ℂ) p) :
    tangentChartEquiv b p hp v = coordinate b p v := rfl

theorem tangentChartEquiv_eq_mfderiv (b : Bool) (p : RiemannSphere)
    (hp : p ∈ chartOpen b) (v : TangentSpace 𝓘(ℂ) p) :
    tangentChartEquiv b p hp v =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (chartCenter b)) p v :=
  coordinate_eq_mfderiv b hp v

/-- A scalar multiple of the actual chart differential, as a full cotangent fibre. -/
def cotangentFrameEquiv (b : Bool) (p : RiemannSphere) (hp : p ∈ chartOpen b) :
    ℂ ≃L[ℂ] CotangentSpace p :=
  (ContinuousLinearMap.toSpanSingletonCLE : ℂ ≃L[ℂ] (ℂ →L[ℂ] ℂ)).trans
    ((tangentChartEquiv b p hp).symm.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ))

theorem cotangentFrameEquiv_apply (b : Bool) (p : RiemannSphere)
    (hp : p ∈ chartOpen b) (c : ℂ) (v : TangentSpace 𝓘(ℂ) p) :
    cotangentFrameEquiv b p hp c v = c * coordinate b p v := by
  change coordinate b p v * c = c * coordinate b p v
  exact mul_comm _ _

/-- This local frame is precisely `d(chart_b)`, computed by the native manifold derivative. -/
theorem cotangentFrameEquiv_one_eq_mfderiv (b : Bool) (p : RiemannSphere)
    (hp : p ∈ chartOpen b) :
    cotangentFrameEquiv b p hp 1 =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (chartCenter b)) p := by
  apply ContinuousLinearMap.ext
  intro v
  rw [cotangentFrameEquiv_apply, one_mul, coordinate_eq_mfderiv b hp]
  rfl

/-- Scalar coefficient in a native dual tangent chart, defined by evaluation at one. -/
def cotangentCoefficient (b : Bool) (p : RiemannSphere) (α : CotangentSpace p) : ℂ :=
  ((cotangentTriv b) ⟨p, α⟩).2 1

theorem cotangentTriv_apply_snd (b : Bool) (p : RiemannSphere) (α : CotangentSpace p) :
    ((cotangentTriv b) ⟨p, α⟩).2 =
      α.comp ((trivializationAt ℂ (TangentSpace 𝓘(ℂ)) (chartCenter b)).symmL ℂ p) := by
  change ((Bundle.Trivial.trivialization RiemannSphere ℂ).continuousLinearMapAt ℂ p).comp
    (α.comp ((trivializationAt ℂ (TangentSpace 𝓘(ℂ)) (chartCenter b)).symmL ℂ p)) = _
  rw [Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp]

theorem cotangentTriv_frame (b : Bool) (p : RiemannSphere)
    (hp : p ∈ chartOpen b) (c : ℂ) :
    ((cotangentTriv b) ⟨p, cotangentFrameEquiv b p hp c⟩).2 =
      ContinuousLinearMap.toSpanSingletonCLE c := by
  rw [cotangentTriv_apply_snd]
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, cotangentFrameEquiv_apply,
    coordinate_eq_continuousLinearMapAt b hp,
    Trivialization.continuousLinearMapAt_symmL _ hp]
  change c * v = v * c
  exact mul_comm _ _

@[simp] theorem cotangentCoefficient_frame (b : Bool) (p : RiemannSphere)
    (hp : p ∈ chartOpen b) (c : ℂ) :
    cotangentCoefficient b p (cotangentFrameEquiv b p hp c) = c := by
  rw [cotangentCoefficient, cotangentTriv_frame]
  change (1 : ℂ) * c = c
  exact one_mul c

theorem cotangentCoefficient_eq_frameEquiv_symm (b : Bool) (p : RiemannSphere)
    (hp : p ∈ chartOpen b) (α : CotangentSpace p) :
    cotangentCoefficient b p α = (cotangentFrameEquiv b p hp).symm α := by
  obtain ⟨c, rfl⟩ := (cotangentFrameEquiv b p hp).surjective α
  rw [cotangentCoefficient_frame, ContinuousLinearEquiv.symm_apply_apply]

/-- Evaluation is multiplication of native cotangent and tangent coordinates. -/
theorem cotangentCoefficient_mul_coordinate (b : Bool) (p : RiemannSphere)
    (hp : p ∈ chartOpen b) (α : CotangentSpace p) (v : TangentSpace 𝓘(ℂ) p) :
    cotangentCoefficient b p α * coordinate b p v = α v := by
  obtain ⟨c, rfl⟩ := (cotangentFrameEquiv b p hp).surjective α
  rw [cotangentCoefficient_frame, cotangentFrameEquiv_apply]

/-- The complete native Hom coordinate is determined by its scalar coefficient. -/
theorem cotangentTriv_eq_span_coefficient (b : Bool) (p : RiemannSphere)
    (hp : p ∈ chartOpen b) (α : CotangentSpace p) :
    ((cotangentTriv b) ⟨p, α⟩).2 =
      ContinuousLinearMap.toSpanSingletonCLE (cotangentCoefficient b p α) := by
  obtain ⟨c, rfl⟩ := (cotangentFrameEquiv b p hp).surjective α
  rw [cotangentCoefficient_frame, cotangentTriv_frame]

/-- Scalar coefficients in fixed native cotangent charts are holomorphic on their source. -/
theorem cotangentCoefficient_holomorphicAt (b : Bool) {q : CotangentBundle}
    (hq : q.proj ∈ chartOpen b) :
    ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) 𝓘(ℂ) ω
      (fun r : CotangentBundle => cotangentCoefficient b r.proj r.2) q := by
  have hsource : q ∈ (cotangentTriv b).source := by
    apply (cotangentTriv b).mem_source.mpr
    rw [cotangentTriv_baseSet]
    exact hq
  have he : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ))
      (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω (cotangentTriv b) q :=
    (cotangentTriv b).contMDiffOn.contMDiffAt
      ((cotangentTriv b).open_source.mem_nhds hsource)
  exact he.snd.clm_apply contMDiffAt_const

end Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical
