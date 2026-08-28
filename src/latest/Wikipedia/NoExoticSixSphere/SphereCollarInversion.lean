import Wikipedia.NoExoticSixSphere.SmoothLocalExtension
import Wikipedia.NoExoticSixSphere.SphereAnnulusCoordinates
import Mathlib.Geometry.Euclidean.Inversion.Calculus

/-!
# Reversing a sphere collar by actual Euclidean inversion

Unit inversion fixes every point of the boundary sphere, sends its radial
derivative to the negative radial vector, and has injective differential
away from the origin. A smooth ambient collar extension composed with
inversion can be extended smoothly across the origin without changing any
value on the radius-one-to-two annulus.
-/

noncomputable section

open Function Set Metric
open scoped ContDiff

namespace NoExoticSixSphere.SphereCollarInversion

open GLOrthonormalization EuclideanGeometry

def map {p : ℕ} : Vector (p + 1) → Vector (p + 1) := inversion 0 1

theorem norm_map {p : ℕ} (x : Vector (p + 1)) : ‖map x‖ = 1 / ‖x‖ := by
  simpa only [map, dist_zero_right, one_pow] using
    dist_inversion_center (0 : Vector (p + 1)) x 1

theorem map_coe {p : ℕ} (s : Sphere p) : map s.val = s.val :=
  inversion_of_mem_sphere s.property

theorem contDiffAt_map {p : ℕ} {x : Vector (p + 1)} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ map x :=
  contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx

theorem fderiv_map_radial {p : ℕ} (s : Sphere p) :
    fderiv ℝ map s.val s.val = -s.val := by
  have hs : s.val ≠ 0 := by
    intro he
    have hn := ClosedHemisphere.unit_norm s
    rw [he, norm_zero] at hn
    norm_num at hn
  rw [map, (hasFDerivAt_inversion hs).fderiv]
  simp only [dist_zero_right, ClosedHemisphere.unit_norm, div_self one_ne_zero,
    one_pow, one_smul, sub_zero]
  exact Submodule.reflection_orthogonalComplement_singleton_eq_neg s.val

theorem injective_fderiv_map {p : ℕ} {x : Vector (p + 1)} (hx : x ≠ 0) :
    Injective (fderiv ℝ map x) := by
  rw [map, (hasFDerivAt_inversion hx).fderiv]
  exact (smul_right_injective (Vector (p + 1))
    (pow_ne_zero 2 (div_ne_zero one_ne_zero (dist_ne_zero.mpr hx)))).comp
      ((ℝ ∙ (x - 0))ᗮ.reflection).injective

theorem exists_smooth_ambient_extension {p : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : Vector (p + 1) → F) (hH : ContDiff ℝ ∞ H) :
    ∃ G : C(Vector (p + 1), F), ContDiff ℝ ∞ G ∧
      ∀ x ∈ SphereAnnulus.domain p, G x = H (map x) := by
  let K : Set (Vector (p + 1)) := {x | 1 / 2 ≤ ‖x‖}
  let U : Set (Vector (p + 1)) := {x | x ≠ 0}
  have hK : IsClosed K := isClosed_le continuous_const continuous_norm
  have hU : IsOpen U := isOpen_ne
  have hKU : K ⊆ U := by
    intro x hx he
    change 1 / 2 ≤ ‖x‖ at hx
    rw [he, norm_zero] at hx
    norm_num at hx
  have hs : ContDiffOn ℝ ∞ (H ∘ map) U :=
    fun x hx ↦ (hH.contDiffAt.comp x (contDiffAt_map hx)).contDiffWithinAt
  obtain ⟨G, hG, hGeq⟩ := exists_contDiff_eqOn_closed (H ∘ map) hK hU hKU hs
  refine ⟨⟨G, hG.continuous⟩, hG, ?_⟩
  intro x hx
  exact hGeq (by change 1 / 2 ≤ ‖x‖; exact le_trans (by norm_num) hx.1)

end NoExoticSixSphere.SphereCollarInversion
