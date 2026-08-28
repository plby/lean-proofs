import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSphereHolomorphic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSphereCoordinatesGauge

/-!
# The native canonical line of the sphere is the square base twist

The source is the actual Hom bundle of complex-linear cotangent spaces of
the existing standard analytic Riemann sphere.  The target is the actual
second power of the previously constructed infinity-ideal line bundle.
The comparison is a fibre-linear biholomorphism of these original total
spaces.  Its local signs are retained explicitly: `dz` maps to the finite
square frame and `dw` maps to minus the infinity square frame.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical

open RiemannSphere.HolomorphicVectorFields
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

local notation "Iₛ" => ModelWithCorners.prod (modelWithCornersSelf ℂ ℂ)
  (modelWithCornersSelf ℂ ℂ)
local notation "Iᴷ" => ModelWithCorners.prod (modelWithCornersSelf ℂ ℂ)
  (modelWithCornersSelf ℂ (ℂ →L[ℂ] ℂ))

/-- `K_{ℙ¹} ≃ O(-2∞)` as a genuine biholomorphism of the independently
constructed native bundle total spaces. -/
def canonicalDiffeomorph :
    Diffeomorph Iᴷ Iₛ CotangentBundle (BaseTwist.data.power 2).core.TotalSpace ω :=
  nativeDiffeomorph.symm.trans squareGauge.diffeomorph

/-- The same comparison on each full continuous-linear cotangent fibre. -/
def canonicalFiberEquiv (p : RiemannSphere) :
    CotangentSpace p ≃L[ℂ] (BaseTwist.data.power 2).core.Fiber p :=
  (nativeFiberEquiv p).symm.trans (squareGauge.fiberEquiv p)

@[simp] theorem canonicalDiffeomorph_proj (q : CotangentBundle) :
    (canonicalDiffeomorph q).proj = q.proj := rfl

@[simp] theorem canonicalDiffeomorph_symm_proj
    (q : (BaseTwist.data.power 2).core.TotalSpace) :
    (canonicalDiffeomorph.symm q).proj = q.proj := rfl

/-- The actual holomorphic total-space comparison restricts to the stated fibre CLE. -/
theorem canonicalDiffeomorph_mk (p : RiemannSphere) (α : CotangentSpace p) :
    canonicalDiffeomorph ⟨p, α⟩ = ⟨p, canonicalFiberEquiv p α⟩ := rfl

theorem canonicalDiffeomorph_symm_mk (p : RiemannSphere)
    (c : (BaseTwist.data.power 2).core.Fiber p) :
    canonicalDiffeomorph.symm ⟨p, c⟩ = ⟨p, (canonicalFiberEquiv p).symm c⟩ := rfl

theorem canonicalDiffeomorph_holomorphic :
    ContMDiff Iᴷ Iₛ ω canonicalDiffeomorph := canonicalDiffeomorph.contMDiff

theorem canonicalDiffeomorph_symm_holomorphic :
    ContMDiff Iₛ Iᴷ ω canonicalDiffeomorph.symm := canonicalDiffeomorph.symm.contMDiff

/-- The full local comparison is the constant gauge `1` in the finite
chart and `-1` in the reciprocal chart. -/
theorem canonicalDiffeomorph_localCoefficient (b : Bool) (q : CotangentBundle)
    (hq : q.proj ∈ data.baseSet b) :
    ((BaseTwist.data.power 2).core.localTriv b (canonicalDiffeomorph q)).2 =
      (chartSign b : ℂ) * cotangentCoefficient b q.proj q.2 := by
  change ((BaseTwist.data.power 2).core.localTriv b (squareGauge.map (fromNative q))).2 = _
  rw [squareGauge.map_localCoefficient b (fromNative q) hq,
    squareGauge_value, fromNative_localTriv b q hq]

theorem canonicalDiffeomorph_finiteCoefficient (q : CotangentBundle)
    (hq : q.proj ∈ finiteChart) :
    ((BaseTwist.data.power 2).core.localTriv false (canonicalDiffeomorph q)).2 =
      cotangentCoefficient false q.proj q.2 := by
  simpa only [chartSign_false, Units.val_one, one_mul] using
    canonicalDiffeomorph_localCoefficient false q hq

/-- The minus sign is forced by the actual derivative `d(1/z) = -z⁻² dz`. -/
theorem canonicalDiffeomorph_infinityCoefficient (q : CotangentBundle)
    (hq : q.proj ∈ infinityChart) :
    ((BaseTwist.data.power 2).core.localTriv true (canonicalDiffeomorph q)).2 =
      -cotangentCoefficient true q.proj q.2 := by
  simpa only [chartSign_true, Units.val_neg, Units.val_one, neg_one_mul] using
    canonicalDiffeomorph_localCoefficient true q hq

/-- Actual local differentials map to the signed square ideal frames. -/
theorem canonicalFiberEquiv_differentialFrame (b : Bool) (p : RiemannSphere)
    (hp : p ∈ data.baseSet b) (c : ℂ) :
    ((BaseTwist.data.power 2).core.localTriv b
      ⟨p, canonicalFiberEquiv p
        (cotangentFrameEquiv b p (mem_chartOpen_of_data hp) c)⟩).2 =
      (chartSign b : ℂ) * c := by
  rw [← canonicalDiffeomorph_mk,
    canonicalDiffeomorph_localCoefficient b _ hp, cotangentCoefficient_frame]

/-- The native manifold differential of the finite coordinate maps to the
finite square frame, and that of the reciprocal coordinate to its negative. -/
theorem canonicalFiberEquiv_mfderiv (b : Bool) (p : RiemannSphere)
    (hp : p ∈ data.baseSet b) :
    ((BaseTwist.data.power 2).core.localTriv b
      ⟨p, canonicalFiberEquiv p
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (chartCenter b)) p)⟩).2 =
      (chartSign b : ℂ) := by
  rw [← cotangentFrameEquiv_one_eq_mfderiv b p (mem_chartOpen_of_data hp),
    canonicalFiberEquiv_differentialFrame b p hp 1, mul_one]

end Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical
