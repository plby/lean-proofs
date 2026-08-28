import Wikipedia.NoExoticSixSphere.SphereCapPinchCoordinates
import Wikipedia.NoExoticSixSphere.SphereHeadReflection

/-!
# A smooth positive axial dilation of the actual three-sphere

The rational formula has a strictly positive denominator on the whole
unit sphere, including both poles. It preserves the actual unit norm and
is jointly smooth at every positive scale. Scale one is the identity.
This will compare the scale-dependent cap-to-pinch coordinates.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def axisDenominator (c h : ℝ) : ℝ := (1 - h) + c ^ 2 * (1 + h)

def axisNumerator (c h : ℝ) : ℝ := (c ^ 2 - 1) + (c ^ 2 + 1) * h

theorem source_head_tail_sq (x : Sphere 3) :
    (x.val 0) ^ 2 + ‖SphereCylinder.tail 2 x.val‖ ^ 2 = 1 := by
  have h := SphereCylinder.norm_join_sq 2 (x.val 0) (SphereCylinder.tail 2 x.val)
  rw [join_head_tail, ClosedHemisphere.unit_norm, one_pow] at h
  exact h.symm

theorem source_head_bounds (x : Sphere 3) : -1 ≤ x.val 0 ∧ x.val 0 ≤ 1 := by
  have h := source_head_tail_sq x
  constructor <;> nlinarith [sq_nonneg ‖SphereCylinder.tail 2 x.val‖]

theorem axisDenominator_pos {c : ℝ} (hc : 0 < c) (x : Sphere 3) :
    0 < axisDenominator c (x.val 0) := by
  obtain ⟨hl, hr⟩ := source_head_bounds x
  by_cases hh : 0 < 1 + x.val 0
  · exact add_pos_of_nonneg_of_pos (by linarith) (mul_pos (sq_pos_of_pos hc) hh)
  · have he : x.val 0 = -1 := by linarith
    simp [axisDenominator, he]

def axisVector (c : ℝ) (x : Sphere 3) : Vector 4 :=
  (axisDenominator c (x.val 0))⁻¹ •
    SphereCylinder.join 2 (axisNumerator c (x.val 0), (2 * c) • SphereCylinder.tail 2 x.val)

theorem axis_numerator_norm (c : ℝ) (x : Sphere 3) :
    axisNumerator c (x.val 0) ^ 2 + (2 * c) ^ 2 * ‖SphereCylinder.tail 2 x.val‖ ^ 2 =
      axisDenominator c (x.val 0) ^ 2 := by
  calc
    _ = axisDenominator c (x.val 0) ^ 2 + (2 * c) ^ 2 *
        ((x.val 0) ^ 2 + ‖SphereCylinder.tail 2 x.val‖ ^ 2 - 1) := by
      dsimp [axisNumerator, axisDenominator]
      ring
    _ = _ := by rw [source_head_tail_sq]; ring

theorem norm_axisVector {c : ℝ} (hc : 0 < c) (x : Sphere 3) : ‖axisVector c x‖ = 1 := by
  have hd := (axisDenominator_pos hc x).ne'
  have hs : ‖axisVector c x‖ ^ 2 = 1 := by
    rw [axisVector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, SphereCylinder.norm_join_sq,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, axis_numerator_norm, ← mul_pow,
      inv_mul_cancel₀ hd]
    norm_num
  nlinarith [norm_nonneg (axisVector c x)]

def axisDilation (c : ℝ) (x : Sphere 3) : Sphere 3 :=
  SphereRadialRetraction.retract pinchPole (axisVector c x)

theorem axisDilation_val {c : ℝ} (hc : 0 < c) (x : Sphere 3) :
    (axisDilation c x).val = axisVector c x := by
  have hn := norm_axisVector hc x
  have hne : axisVector c x ≠ 0 := norm_ne_zero_iff.mp (hn ▸ one_ne_zero)
  simp only [axisDilation, SphereRadialRetraction.retract, dif_neg hne,
    NormedSpace.normalize, hn, inv_one, one_smul]

theorem contMDiffAt_axisVector (p : ℝ × Sphere 3) (hp : 0 < p.1) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 4) ∞
      (fun q : ℝ × Sphere 3 ↦ axisVector q.1 q.2) p := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hx : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 4) ∞
      (fun q : ℝ × Sphere 3 ↦ q.2.val) := contMDiff_coe_sphere.comp contMDiff_snd
  have hh : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × Sphere 3 ↦ q.2.val 0) :=
    (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) 2).contMDiff.comp hx
  have hc : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : ℝ × Sphere 3 → ℝ) := contMDiff_fst
  have hd : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × Sphere 3 ↦ axisDenominator q.1 (q.2.val 0)) :=
    (contMDiff_const.sub hh).add ((hc.pow 2).mul (contMDiff_const.add hh))
  have hn : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × Sphere 3 ↦ axisNumerator q.1 (q.2.val 0)) :=
    ((hc.pow 2).sub contMDiff_const).add (((hc.pow 2).add contMDiff_const).mul hh)
  have ht : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × Sphere 3 ↦ (2 * q.1) • SphereCylinder.tail 2 q.2.val) :=
    (contMDiff_const.mul hc).smul ((SphereCylinder.tail 2).contDiff.contMDiff.comp hx)
  exact ((hd p).inv₀ (axisDenominator_pos hp p.2).ne').smul
    (((SphereCylinder.join 2).contDiff.contMDiff.comp (hn.prodMk_space ht)) p)

theorem contMDiffAt_axisDilation (p : ℝ × Sphere 3) (hp : 0 < p.1) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × Sphere 3 ↦ axisDilation q.1 q.2) p := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hn : axisVector p.1 p.2 ≠ 0 :=
    norm_ne_zero_iff.mp ((norm_axisVector hp p.2) ▸ one_ne_zero)
  exact (SphereRadialRetraction.contMDiffAt_retract (n := 3) pinchPole hn).comp p
    (contMDiffAt_axisVector p hp)

theorem axisDilation_one (x : Sphere 3) : axisDilation 1 x = x := by
  apply Subtype.ext
  rw [axisDilation_val (by norm_num : (0 : ℝ) < 1)]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change (axisDenominator 1 (x.val 0))⁻¹ * axisNumerator 1 (x.val 0) = x.val 0
    norm_num [axisDenominator, axisNumerator]
    ring
  · change (axisDenominator 1 (x.val 0))⁻¹ * ((2 * 1) * x.val j.succ) = x.val j.succ
    norm_num [axisDenominator]
    ring

end NoExoticSixSphere.SphereSumNeck
