import Wikipedia.NoExoticSixSphere.SphereCylinderRadialCoordinates
import Wikipedia.NoExoticSixSphere.SphereSuspensionTargetChart

/-!
# The actual ambient suspension differential in the product target chart

Radial normalization cancels exactly in the cylinder coordinates. Near
an equatorial fiber point the centered extension is therefore height
divided by tail norm, together with the original radial extension.
Its actual Frechet derivative has the new height column and the old
derivative block, in fixed ordered Euclidean target coordinates.
-/

noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereCylinder

theorem retract_join_mem_band (m : ℕ) (a : Sphere (m + 1)) (s : ℝ)
    (v : EuclideanSpace ℝ (Fin (m + 1))) (hv : v ≠ 0) :
    SphereRadialRetraction.retract a (join m (s, v)) ∈ band m := by
  have hq := join_ne_zero_of_tail_ne_zero m s hv
  change tail m (SphereRadialRetraction.retract a (join m (s, v))).val ≠ 0
  rw [SphereRadialRetraction.retract, dif_neg hq]
  change tail m (‖join m (s, v)‖⁻¹ • join m (s, v)) ≠ 0
  rw [map_smul, tail_join]
  exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hq)) hv

end NoExoticSixSphere.SphereCylinder

namespace NoExoticSixSphere.SphereMapSuspension

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} (f : C(Sphere m, Sphere n)) (b : Sphere n)
  (c : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞)

def radialCenteredMap (a : Sphere (m + 1)) : Vector (m + 2) → Vector (n + 1) :=
  SphereLevelEquations.extend a
    (CenteredChartCoordinates.coordinates (map f) (targetCylinderChart c) (equator n b))

theorem radialCenteredMap_join (a : Sphere (m + 1)) (a₀ : Sphere m)
    (s : ℝ) (v : Vector (m + 1)) (hv : v ≠ 0) :
    radialCenteredMap f b c a (SphereCylinder.join m (s, v)) =
      EuclideanProduct.coordinates n (s / ‖v‖,
        SphereLevelEquations.extend a₀ (CenteredChartCoordinates.coordinates f c b) v) := by
  change CenteredChartCoordinates.coordinates (map f) (targetCylinderChart c) (equator n b)
    (SphereRadialRetraction.retract a (SphereCylinder.join m (s, v))) = _
  rw [centered_coordinates_map_band c f b _ (SphereCylinder.retract_join_mem_band m a s v hv),
    SphereCylinder.inverse_retract_join m a a₀ s v hv]
  rfl

variable (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (hb : b ∈ c.source)

include hf hb in
theorem hasFDerivAt_radialCenteredMap_join (a : Sphere (m + 1)) (a₀ x : Sphere m)
    (hx : f x = b) :
    HasFDerivAt (radialCenteredMap f b c a ∘ SphereCylinder.join m)
      ((EuclideanProduct.coordinates n).toContinuousLinearMap.comp
        ((ContinuousLinearMap.fst ℝ ℝ (Vector (m + 1))).prod
          ((fderiv ℝ (SphereLevelEquations.extend a₀
            (CenteredChartCoordinates.coordinates f c b)) x.val).comp
              (ContinuousLinearMap.snd ℝ ℝ (Vector (m + 1)))))) (0, x.val) := by
  let : Fact (Module.finrank ℝ (Vector (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  let old := SphereLevelEquations.extend a₀ (CenteredChartCoordinates.coordinates f c b)
  have ho : DifferentiableAt ℝ old x.val :=
    (SphereLevelEquations.contDiffAt_extend a₀
      (CenteredChartCoordinates.contMDiffAt_coordinates f c b (hf x)
        (hx.symm ▸ hb))).differentiableAt (by simp)
  have hs : HasFDerivAt (fun p : ℝ × Vector (m + 1) ↦ p.2)
      (ContinuousLinearMap.snd ℝ ℝ (Vector (m + 1))) (0, x.val) := hasFDerivAt_snd
  have hp := (SphereCylinder.hasFDerivAt_height_ratio m x).prodMk
    (ho.hasFDerivAt.comp (0, x.val) hs)
  have hfinal := (EuclideanProduct.coordinates n).hasFDerivAt.comp (0, x.val) hp
  have he : radialCenteredMap f b c a ∘ SphereCylinder.join m =ᶠ[𝓝 (0, x.val)]
      (fun p : ℝ × Vector (m + 1) ↦ EuclideanProduct.coordinates n (p.1 / ‖p.2‖, old p.2)) := by
    have ht : ∀ᶠ p : ℝ × Vector (m + 1) in 𝓝 (0, x.val), p.2 ≠ 0 :=
      (isOpen_ne.preimage (continuous_snd : Continuous
        (fun p : ℝ × Vector (m + 1) ↦ p.2))).mem_nhds (ne_zero_of_mem_unit_sphere x)
    filter_upwards [ht] with p hp
    exact radialCenteredMap_join f b c a a₀ p.1 p.2 hp
  exact he.hasFDerivAt_iff.mpr hfinal

include hf hb in
theorem fderiv_radialCenteredMap_join (a : Sphere (m + 1)) (a₀ x : Sphere m)
    (hx : f x = b) :
    fderiv ℝ (radialCenteredMap f b c a ∘ SphereCylinder.join m) (0, x.val) =
      (EuclideanProduct.coordinates n).toContinuousLinearMap.comp
        ((ContinuousLinearMap.fst ℝ ℝ (Vector (m + 1))).prod
          ((fderiv ℝ (SphereLevelEquations.extend a₀
            (CenteredChartCoordinates.coordinates f c b)) x.val).comp
              (ContinuousLinearMap.snd ℝ ℝ (Vector (m + 1))))) :=
  (hasFDerivAt_radialCenteredMap_join f b c hf hb a a₀ x hx).fderiv

end NoExoticSixSphere.SphereMapSuspension
