import Wikipedia.NoExoticSixSphere.SphereCylinderVector
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# An actual smooth cylinder chart for the punctured sphere

The inverse records the ratio of the first coordinate to the tail norm and
normalizes the tail. The fallback value at a pole is never used on the chart
target. Both inverse laws and smoothness are proved for the original sphere
atlas and the ordinary product atlas on `ℝ × Sⁿ`.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereCylinder

def band (n : ℕ) : Set (Sphere (n + 1)) := {y | tail n y.val ≠ 0}

theorem isOpen_band (n : ℕ) : IsOpen (band n) :=
  isOpen_ne.preimage ((tail n).continuous.comp continuous_subtype_val)

def inverse (n : ℕ) (y : Sphere (n + 1)) : ℝ × Sphere n :=
  (y.val 0 / ‖tail n y.val‖,
    SphereRadialRetraction.retract (Wikipedia.HopfProblem.SphereHomology.basePoint n)
      (tail n y.val))

theorem inverse_point (n : ℕ) (p : ℝ × Sphere n) : inverse n (point n p) = p := by
  apply Prod.ext
  · change (point n p).val 0 / ‖tail n (point n p).val‖ = p.1
    rw [point_head, norm_tail_point]
    exact mul_div_cancel_left₀ p.1 (inv_ne_zero (norm_ne_zero_iff.mpr (vector_ne_zero n p)))
  · apply Subtype.ext
    change (SphereRadialRetraction.retract _ (tail n (point n p).val)).val = p.2.val
    rw [SphereRadialRetraction.retract, dif_neg (tail_point_ne_zero n p)]
    change NormedSpace.normalize (tail n (point n p).val) = p.2.val
    rw [tail_point, NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr (norm_pos_iff.mpr (vector_ne_zero n p)))]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm p.2)

theorem vector_inverse (n : ℕ) (y : Sphere (n + 1)) (hy : y ∈ band n) :
    vector n (inverse n y) = ‖tail n y.val‖⁻¹ • y.val := by
  have hr : (SphereRadialRetraction.retract
      (Wikipedia.HopfProblem.SphereHomology.basePoint n) (tail n y.val)).val =
      ‖tail n y.val‖⁻¹ • tail n y.val := by
    rw [SphereRadialRetraction.retract, dif_neg hy]
    rfl
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change y.val 0 / ‖tail n y.val‖ = ‖tail n y.val‖⁻¹ * y.val 0
    rw [div_eq_mul_inv, mul_comm]
  · change (SphereRadialRetraction.retract _ (tail n y.val)).val j =
      ‖tail n y.val‖⁻¹ * y.val j.succ
    rw [hr]
    rfl

theorem point_inverse (n : ℕ) (y : Sphere (n + 1)) (hy : y ∈ band n) :
    point n (inverse n y) = y := by
  apply Subtype.ext
  change NormedSpace.normalize (vector n (inverse n y)) = y.val
  rw [vector_inverse n y hy, NormedSpace.normalize_smul_of_pos
    (inv_pos.mpr (norm_pos_iff.mpr hy))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm y)

theorem contMDiffAt_inverse (n : ℕ) {y : Sphere (n + 1)} (hy : y ∈ band n) :
    ContMDiffAt (𝓡 (n + 1)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞ (inverse n) y := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = (n + 1) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hc : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 2)) ∞
      (fun z : Sphere (n + 1) ↦ z.val) := contMDiff_coe_sphere
  have ht : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞
      (fun z : Sphere (n + 1) ↦ tail n z.val) := (tail n).contDiff.contMDiff.comp hc
  have hh : ContMDiff (𝓡 (n + 1)) (𝓘(ℝ, ℝ)) ∞
      (fun z : Sphere (n + 1) ↦ z.val 0) :=
    ((ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin (n + 1)))).comp
      (join n).symm.toContinuousLinearMap).contDiff.contMDiff.comp hc
  have hn : ContMDiffAt (𝓡 (n + 1)) (𝓘(ℝ, ℝ)) ∞
      (fun z : Sphere (n + 1) ↦ ‖tail n z.val‖) y :=
    (contDiffAt_norm ℝ hy).comp_contMDiffAt
      (f := fun z : Sphere (n + 1) ↦ tail n z.val) (x := y) (ht y)
  exact ((hh y).div₀ hn (norm_ne_zero_iff.mpr hy)).prodMk
    ((SphereRadialRetraction.contMDiffAt_retract _ hy).comp y (ht y))

/-- Smooth product coordinates on the sphere minus its two poles. -/
def chart (n : ℕ) : PartialDiffeomorph ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 (n + 1))
    (ℝ × Sphere n) (Sphere (n + 1)) ∞ where
  toFun := point n
  invFun := inverse n
  source := univ
  target := band n
  map_source' p _ := tail_point_ne_zero n p
  map_target' _ _ := mem_univ _
  left_inv' p _ := inverse_point n p
  right_inv' y hy := point_inverse n y hy
  open_source := isOpen_univ
  open_target := isOpen_band n
  contMDiffOn_toFun := (contMDiff_point n).contMDiffOn
  contMDiffOn_invFun _y hy := (contMDiffAt_inverse n hy).contMDiffWithinAt

end NoExoticSixSphere.SphereCylinder
