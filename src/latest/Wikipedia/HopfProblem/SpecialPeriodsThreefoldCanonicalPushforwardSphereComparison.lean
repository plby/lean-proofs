import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSphereNative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSphereCoordinates

/-!
# Intrinsic fibre comparison for the sphere cotangent cocycle

Every fibre of the derivative cocycle is identified with the full native
continuous-linear cotangent space.  These identifications agree in every
actual sphere chart, using the already proved derivative of inversion.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical

open RiemannSphere.HolomorphicVectorFields
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

theorem mem_chartOpen_of_data {b : Bool} {p : RiemannSphere}
    (hp : p ∈ data.baseSet b) : p ∈ chartOpen b := by
  rw [chartOpen_eq_frameChart]
  exact hp

/-- Native differential frames transform by the inverse tangent derivative. -/
theorem cotangentFrame_transition (a b : Bool) (p : RiemannSphere)
    (ha : p ∈ chartOpen a) (hb : p ∈ chartOpen b) (c : ℂ) :
    cotangentFrameEquiv a p ha c =
      cotangentFrameEquiv b p hb ((data.transition a b p : ℂ) * c) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [cotangentFrameEquiv_apply, cotangentFrameEquiv_apply]
  have hab : p ∈ (frameChart a : Set RiemannSphere) ∩ frameChart b := by
    rw [← chartOpen_eq_frameChart a, ← chartOpen_eq_frameChart b]
    exact ⟨ha, hb⟩
  rw [tangentCoordinate_transition a b p hab v,
    mul_mul_mul_comm, mul_inv_cancel₀ (data.transition_ne_zero a b p), one_mul]

/-- The scalar coefficient change is induced by actual native dual tangent frames. -/
theorem cotangentCoefficient_transition (a b : Bool) (p : RiemannSphere)
    (ha : p ∈ chartOpen a) (hb : p ∈ chartOpen b) (α : CotangentSpace p) :
    cotangentCoefficient b p α =
      (data.transition a b p : ℂ) * cotangentCoefficient a p α := by
  obtain ⟨c, rfl⟩ := (cotangentFrameEquiv a p ha).surjective α
  rw [cotangentCoefficient_frame,
    cotangentFrame_transition a b p ha hb c, cotangentCoefficient_frame]

/-- Each derivative-cocycle fibre is the entire native cotangent space. -/
def nativeFiberEquiv (p : RiemannSphere) : data.core.Fiber p ≃L[ℂ] CotangentSpace p :=
  cotangentFrameEquiv (data.indexAt p) p (mem_chartOpen_of_data (data.mem_baseSet_at p))

theorem nativeFiberEquiv_apply (p : RiemannSphere) (c : data.core.Fiber p)
    (v : TangentSpace 𝓘(ℂ) p) :
    nativeFiberEquiv p c v =
      id (α := ℂ) c * coordinate (data.indexAt p) p v :=
  cotangentFrameEquiv_apply _ _ _ _ _

/-- The intrinsic fibre identification respects every original bundle chart. -/
theorem nativeFiberEquiv_local (b : Bool) (p : RiemannSphere)
    (hp : p ∈ data.baseSet b) (c : data.core.Fiber p) :
    nativeFiberEquiv p c = cotangentFrameEquiv b p (mem_chartOpen_of_data hp)
      ((data.core.localTriv b) ⟨p, c⟩).2 :=
  cotangentFrame_transition (data.indexAt p) b p
    (mem_chartOpen_of_data (data.mem_baseSet_at p)) (mem_chartOpen_of_data hp) c

theorem nativeFiberEquiv_coefficient (b : Bool) (p : RiemannSphere)
    (hp : p ∈ data.baseSet b) (c : data.core.Fiber p) :
    cotangentCoefficient b p (nativeFiberEquiv p c) =
      ((data.core.localTriv b) ⟨p, c⟩).2 := by
  rw [nativeFiberEquiv_local b p hp c, cotangentCoefficient_frame]

/-- The underlying map to the independently constructed native cotangent total space. -/
def toNative (q : data.core.TotalSpace) : CotangentBundle :=
  ⟨q.proj, nativeFiberEquiv q.proj q.2⟩

/-- The inverse map reads an actual cotangent fibre in its preferred differential frame. -/
def fromNative (q : CotangentBundle) : data.core.TotalSpace :=
  ⟨q.proj, (nativeFiberEquiv q.proj).symm q.2⟩

@[simp] theorem toNative_proj (q : data.core.TotalSpace) :
    (toNative q).proj = q.proj := rfl

@[simp] theorem fromNative_proj (q : CotangentBundle) :
    (fromNative q).proj = q.proj := rfl

@[simp] theorem fromNative_toNative (q : data.core.TotalSpace) :
    fromNative (toNative q) = q := by
  cases q with
  | mk p c =>
    exact congrArg (fun c : data.core.Fiber p => (⟨p, c⟩ : data.core.TotalSpace))
      ((nativeFiberEquiv p).symm_apply_apply c)

@[simp] theorem toNative_fromNative (q : CotangentBundle) :
    toNative (fromNative q) = q := by
  cases q with
  | mk p α =>
    exact congrArg (fun α : CotangentSpace p => (⟨p, α⟩ : CotangentBundle))
      ((nativeFiberEquiv p).apply_symm_apply α)

/-- A base-preserving equivalence of the independently defined total spaces. -/
def nativeEquiv : data.core.TotalSpace ≃ CotangentBundle where
  toFun := toNative
  invFun := fromNative
  left_inv := fromNative_toNative
  right_inv := toNative_fromNative

/-- Forward comparison in the original native Hom-bundle charts. -/
theorem toNative_localTriv (b : Bool) (q : data.core.TotalSpace)
    (hq : q.proj ∈ data.baseSet b) :
    ((cotangentTriv b) (toNative q)).2 =
      ContinuousLinearMap.toSpanSingletonCLE ((data.core.localTriv b q).2) := by
  change ((cotangentTriv b) ⟨q.proj, nativeFiberEquiv q.proj q.2⟩).2 = _
  rw [nativeFiberEquiv_local b q.proj hq q.2, cotangentTriv_frame]

/-- Inverse comparison in every original derivative-cocycle chart. -/
theorem fromNative_localTriv (b : Bool) (q : CotangentBundle)
    (hq : q.proj ∈ data.baseSet b) :
    ((data.core.localTriv b) (fromNative q)).2 =
      cotangentCoefficient b q.proj q.2 := by
  have h := nativeFiberEquiv_coefficient b q.proj hq ((nativeFiberEquiv q.proj).symm q.2)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Evaluation is the intrinsic dual pairing, expressed in any actual pair of charts. -/
theorem toNative_pairing (b : Bool) (p : RiemannSphere)
    (hp : p ∈ data.baseSet b) (c : data.core.Fiber p) (v : TangentSpace 𝓘(ℂ) p) :
    nativeFiberEquiv p c v =
      ((data.core.localTriv b) ⟨p, c⟩).2 * coordinate b p v := by
  rw [nativeFiberEquiv_local b p hp c, cotangentFrameEquiv_apply]

end Wikipedia.HopfProblem.CanonicalGlobal.SphereCanonical
