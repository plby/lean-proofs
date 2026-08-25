import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Transport
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.SupportTransport.LinearAction
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.SupportTransport.Finite

/-!
# Complex actions on actual support normals

An affine symmetry of a set transports its actual supporting segments.
Consequently the complex support-normal set is closed under the action of
the linear part. Horizontal reflection gives conjugation, and an ordinary
reflection composed with it gives multiplication by the squared axis direction.

Only invariance of the named set is used; there is no assumption that a
symmetry permutes the pieces of a dissection.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

noncomputable section

open FaceBounds PlaneIsometries ComplexConjugate

/-- A known complex action of the linear part transports every actual
supporting normal with its original segment-length threshold. -/
theorem mem_complexSupportingNormalsAtLeast_image_of_linear_action
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {K : Set Plane} {δ : ℝ}
    (F : ℂ → ℂ)
    (hlinear : ∀ p, complexEquiv (e.linearIsometryEquiv p) = F (complexEquiv p))
    {z : ℂ} (hz : z ∈ complexSupportingNormalsAtLeast K δ) :
    F z ∈ complexSupportingNormalsAtLeast (e '' K) δ := by
  have hn := mem_supportingNormalsAtLeast_image_affineIsometry e hz
  have hc := complexEquiv_mem_complexSupportingNormalsAtLeast.mpr hn
  change complexEquiv (e.linearIsometryEquiv (!₂[z.re, z.im] : Plane)) ∈
    complexSupportingNormalsAtLeast (e '' K) δ at hc
  simpa only [hlinear, complexEquiv_coordinate_normal] using hc

/-- Actual set invariance gives closure of support normals under the
linear complex action. -/
theorem mapsTo_complexSupportingNormalsAtLeast_of_linear_action
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {K : Set Plane} {δ : ℝ}
    (hK : e '' K = K) (F : ℂ → ℂ)
    (hlinear : ∀ p, complexEquiv (e.linearIsometryEquiv p) = F (complexEquiv p)) :
    MapsTo F (complexSupportingNormalsAtLeast K δ)
      (complexSupportingNormalsAtLeast K δ) := by
  intro z hz
  simpa only [hK] using
    mem_complexSupportingNormalsAtLeast_image_of_linear_action e F hlinear hz

/-- A direct linear complex action preserves the support-normal set of
an invariant actual set. -/
theorem mul_mem_complexSupportingNormalsAtLeast_of_linear_action
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {K : Set Plane} {δ : ℝ}
    (hK : e '' K = K) (a : ℂ)
    (hlinear : ∀ p, complexEquiv (e.linearIsometryEquiv p) = a * complexEquiv p)
    {z : ℂ} (hz : z ∈ complexSupportingNormalsAtLeast K δ) :
    a * z ∈ complexSupportingNormalsAtLeast K δ :=
  mapsTo_complexSupportingNormalsAtLeast_of_linear_action e hK
    (fun w => a * w) hlinear hz

/-- A reversing linear complex action preserves the support-normal set
of an invariant actual set. -/
theorem mul_conj_mem_complexSupportingNormalsAtLeast_of_linear_action
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {K : Set Plane} {δ : ℝ}
    (hK : e '' K = K) (a : ℂ)
    (hlinear : ∀ p, complexEquiv (e.linearIsometryEquiv p) =
      a * conj (complexEquiv p))
    {z : ℂ} (hz : z ∈ complexSupportingNormalsAtLeast K δ) :
    a * conj z ∈ complexSupportingNormalsAtLeast K δ :=
  mapsTo_complexSupportingNormalsAtLeast_of_linear_action e hK
    (fun w => a * conj w) hlinear hz

/-- Horizontal symmetry closes the actual support-normal set under
ordinary complex conjugation. -/
theorem conj_mem_complexSupportingNormalsAtLeast_of_horizontal
    {K : Set Plane} {δ : ℝ} (hK : ReflectionSeparation.horizontal '' K = K)
    {z : ℂ} (hz : z ∈ complexSupportingNormalsAtLeast K δ) :
    conj z ∈ complexSupportingNormalsAtLeast K δ :=
  mapsTo_complexSupportingNormalsAtLeast_of_linear_action
    ReflectionSeparation.horizontal hK conj horizontal_linear_complex_action hz

/-- The ordinary affine axis formula alone determines the action on
actual supporting normals. -/
theorem mul_conj_mem_complexSupportingNormalsAtLeast_of_axis_form
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {K : Set Plane} {δ : ℝ}
    (hK : e '' K = K) (c : ℂ) (u : Circle)
    (hform : ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ)))
    {z : ℂ} (hz : z ∈ complexSupportingNormalsAtLeast K δ) :
    ((u ^ 2 : Circle) : ℂ) * conj z ∈ complexSupportingNormalsAtLeast K δ :=
  mul_conj_mem_complexSupportingNormalsAtLeast_of_linear_action e hK
    ((u ^ 2 : Circle) : ℂ) (linear_complex_action_of_axis_form e c u hform) hz

/-- Two reversing symmetries yield the corresponding direct action on
actual support normals. -/
theorem mul_mem_complexSupportingNormalsAtLeast_of_two_reversing_actions
    (e f : Plane ≃ᵃⁱ[ℝ] Plane) {K : Set Plane} {δ : ℝ}
    (heK : e '' K = K) (hfK : f '' K = K) (a b : ℂ)
    (helinear : ∀ p, complexEquiv (e.linearIsometryEquiv p) =
      a * conj (complexEquiv p))
    (hflinear : ∀ p, complexEquiv (f.linearIsometryEquiv p) =
      b * conj (complexEquiv p))
    {z : ℂ} (hz : z ∈ complexSupportingNormalsAtLeast K δ) :
    (a * conj b) * z ∈ complexSupportingNormalsAtLeast K δ := by
  have hfz := mul_conj_mem_complexSupportingNormalsAtLeast_of_linear_action
    f hfK b hflinear hz
  have hefz := mul_conj_mem_complexSupportingNormalsAtLeast_of_linear_action
    e heK a helinear hfz
  simpa only [map_mul, starRingEnd_self_apply, mul_assoc] using hefz

/-- An ordinary reflection and horizontal reflection preserve the normal
set under multiplication by the squared axis direction. -/
theorem mul_mem_complexSupportingNormalsAtLeast_of_axis_form_and_horizontal
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {K : Set Plane} {δ : ℝ}
    (heK : e '' K = K) (hK : ReflectionSeparation.horizontal '' K = K)
    (c : ℂ) (u : Circle)
    (hform : ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ)))
    {z : ℂ} (hz : z ∈ complexSupportingNormalsAtLeast K δ) :
    ((u ^ 2 : Circle) : ℂ) * z ∈ complexSupportingNormalsAtLeast K δ := by
  have hconj := conj_mem_complexSupportingNormalsAtLeast_of_horizontal hK hz
  simpa only [starRingEnd_self_apply] using
    mul_conj_mem_complexSupportingNormalsAtLeast_of_axis_form e heK c u hform hconj

end

end Puzzling139335.N4MiddleInvolutions.Reflection
