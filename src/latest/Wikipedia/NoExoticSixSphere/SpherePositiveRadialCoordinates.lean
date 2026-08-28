import Wikipedia.NoExoticSixSphere.SphereSumNeckRadialCoordinates
import Wikipedia.NoExoticSixSphere.PartialDiffeomorphProduct
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# Positive radial coordinates and arbitrary increasing smooth radial profiles

The ordinary radius and normalized direction form an actual native partial
diffeomorphism. The scalar inverse-function theorem therefore turns every
positive radial profile with nonzero derivative into local sphere-product
coordinates, without prescribing a closed-form scalar inverse.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def positiveRadial (q : Parameter) : Vector 3 := q.1 • q.2.val

def positiveRadialInverse (x : Vector 3) : Parameter :=
  (‖x‖, SphereRadialRetraction.retract (Stiefel.pole 2) x)

theorem positiveRadialInverse_left (q : Parameter) (hq : 0 < q.1) :
    positiveRadialInverse (positiveRadial q) = q := by
  apply Prod.ext
  · change ‖q.1 • q.2.val‖ = q.1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq, ClosedHemisphere.unit_norm, mul_one]
  · exact radial_retract_smul q.2 hq

theorem positiveRadialInverse_right (x : Vector 3) (hx : x ≠ 0) :
    positiveRadial (positiveRadialInverse x) = x := by
  change ‖x‖ • (SphereRadialRetraction.retract (Stiefel.pole 2) x).val = x
  rw [SphereRadialRetraction.retract, dif_neg hx]
  exact NormedSpace.norm_smul_normalize x

theorem contMDiff_positiveRadial : ContMDiff Model (𝓡 3) ∞ positiveRadial := by
  let : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff Model (𝓡 3) ∞ (fun q : Parameter ↦ q.2.val) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  exact contMDiff_fst.smul hs

theorem contMDiffAt_positiveRadialInverse {x : Vector 3} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) Model ∞ positiveRadialInverse x := by
  let : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact (contDiffAt_norm ℝ hx).contMDiffAt.prodMk
    (SphereRadialRetraction.contMDiffAt_retract (n := 2) (Stiefel.pole 2) hx)

def positiveRadialChart : PartialDiffeomorph Model (𝓡 3) Parameter (Vector 3) ∞ where
  toFun := positiveRadial
  invFun := positiveRadialInverse
  source := {q | 0 < q.1}
  target := {x | x ≠ 0}
  map_source' q hq := smul_ne_zero hq.ne' (ne_zero_of_mem_unit_sphere q.2)
  map_target' _ hx := norm_pos_iff.mpr hx
  left_inv' := positiveRadialInverse_left
  right_inv' := positiveRadialInverse_right
  open_source := isOpen_lt continuous_const continuous_fst
  open_target := isOpen_ne
  contMDiffOn_toFun := contMDiff_positiveRadial.contMDiffOn
  contMDiffOn_invFun _ hx := (contMDiffAt_positiveRadialInverse hx).contMDiffWithinAt

theorem exists_scalar_coordinates {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) {t : ℝ}
    (hd : deriv ρ t ≠ 0) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      t ∈ c.source ∧ (c : ℝ → ℝ) = ρ := by
  let L : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.smulOfNeZero ℝ ℝ (deriv ρ t) hd).toContinuousLinearEquiv
  have hf : HasFDerivAt ρ L.toContinuousLinearMap t := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    change HasDerivAt ρ (deriv ρ t * 1) t
    simpa only [mul_one] using! (hρ.differentiable (by simp) t).hasDerivAt
  obtain ⟨c, hc, _, he⟩ := exists_partialDiffeomorph_of_contDiffOn isOpen_univ (mem_univ t)
    hρ.contDiffOn ⟨L, hf.fderiv.symm⟩
  exact ⟨c, hc, he⟩

theorem isLocalDiffeomorphAt_radial_profile {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (q : Parameter) (hp : 0 < ρ q.1) (hd : deriv ρ q.1 ≠ 0) :
    IsLocalDiffeomorphAt Model (𝓡 3) ∞ (fun w : Parameter ↦ ρ w.1 • w.2.val) q := by
  obtain ⟨c, hc, he⟩ := exists_scalar_coordinates hρ hd
  let d := partialDiffeomorphProd c (Diffeomorph.refl (𝓡 2) (Sphere 2) ∞).toPartialDiffeomorph
  refine ⟨d.trans positiveRadialChart, ⟨⟨hc, mem_univ _⟩, ?_⟩, ?_⟩
  · change 0 < c q.1
    rwa [he]
  · intro w _
    change ρ w.1 • w.2.val = c w.1 • w.2.val
    rw [he]

end NoExoticSixSphere.SphereSumNeck
