import Wikipedia.NoExoticSixSphere.SphereSuspensionAmbientCoordinates

/-!
# The full defining-equation derivative of an actual suspension

At an equatorial fiber point the sphere norm equation has no height
derivative. Together with the actual radial target derivative this gives
the full block formula, with the old norm and target equations retained.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereCylinder

open GLOrthonormalization

theorem hasFDerivAt_normEquation_join (m : ℕ) (x : Sphere m) :
    HasFDerivAt (fun p : ℝ × Vector (m + 1) ↦ ‖join m p‖ ^ 2 - 1)
      ((fderiv ℝ (fun v : Vector (m + 1) ↦ ‖v‖ ^ 2 - 1) x.val).comp
        (ContinuousLinearMap.snd ℝ ℝ (Vector (m + 1)))) (0, x.val) := by
  have hN : ContDiff ℝ ∞ (fun v : Vector (m + 1) ↦ ‖v‖ ^ 2 - 1) :=
    (contDiff_id.norm_sq (𝕜 := ℝ)).sub contDiff_const
  have hT := ((hN.differentiable (by simp) x.val).hasFDerivAt).comp
    ((0 : ℝ), x.val) (hasFDerivAt_snd (𝕜 := ℝ))
  have hF : HasFDerivAt (fun p : ℝ × Vector (m + 1) ↦ p.1)
      (ContinuousLinearMap.fst ℝ ℝ (Vector (m + 1))) (0, x.val) := hasFDerivAt_fst
  have hS : HasFDerivAt (fun p : ℝ × Vector (m + 1) ↦ p.1 * p.1)
      (0 : (ℝ × Vector (m + 1)) →L[ℝ] ℝ) (0, x.val) := by
    convert! hF.mul hF using 1
    simp only [zero_smul, add_zero]
  have he : (fun p : ℝ × Vector (m + 1) ↦ ‖join m p‖ ^ 2 - 1) =
      (fun p ↦ p.1 * p.1 + (‖p.2‖ ^ 2 - 1)) := by
    funext p
    rw [norm_join_sq]
    ring
  rw [he]
  convert! hS.add hT using 1
  simp only [zero_add]

end NoExoticSixSphere.SphereCylinder

namespace NoExoticSixSphere.SphereLevelEquations

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]

theorem fderiv_equations_radial_components (a : UnitSphere E)
    (g : UnitSphere E → F) (x : UnitSphere E)
    (hg : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g x) (v : E) :
    fderiv ℝ (equations a g) x.val v = WithLp.toLp 2
      (fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2 - 1) x.val v,
        fderiv ℝ (extend a g) x.val v) := by
  rw [fderiv_equations_apply a g x hg, fderiv_extend a g x hg]
  rfl

end NoExoticSixSphere.SphereLevelEquations

namespace NoExoticSixSphere.SphereMapSuspension

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} (f : C(Sphere m, Sphere n)) (b : Sphere n)
  (c : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞)
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (hb : b ∈ c.source)

include hf hb in
theorem fderiv_suspensionEquations_join (a : Sphere (m + 1)) (a₀ x : Sphere m)
    (hx : f x = b) (s : ℝ) (v : Vector (m + 1)) :
    fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart (map f) (equator n b)
      (targetCylinderChart c) a ∘ SphereCylinder.join m) (0, x.val) (s, v) =
      WithLp.toLp 2
        ((fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart f b c a₀) x.val v).fst,
          EuclideanProduct.coordinates n (s,
            (fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart f b c a₀)
              x.val v).snd)) := by
  let : Fact (Module.finrank ℝ (Vector (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hN := SphereCylinder.hasFDerivAt_normEquation_join m x
  have hR := hasFDerivAt_radialCenteredMap_join f b c hf hb a a₀ x hx
  have hP := hN.prodMk hR
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Vector (n + 1))).symm.hasFDerivAt.comp
    (0, x.val) hP
  have he := congrArg (fun L : (ℝ × Vector (m + 1)) →L[ℝ]
      WithLp 2 (ℝ × Vector (n + 1)) ↦ L (s, v)) h.fderiv
  change fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart (map f) (equator n b)
      (targetCylinderChart c) a ∘ SphereCylinder.join m) (0, x.val) (s, v) =
    WithLp.toLp 2 (fderiv ℝ (fun y : Vector (m + 1) ↦ ‖y‖ ^ 2 - 1) x.val v,
      EuclideanProduct.coordinates n (s, fderiv ℝ
        (SphereLevelEquations.extend a₀ (CenteredChartCoordinates.coordinates f c b))
        x.val v)) at he
  have hOld := SphereLevelEquations.fderiv_equations_radial_components a₀
    (CenteredChartCoordinates.coordinates f c b) x
    (CenteredChartCoordinates.contMDiffAt_coordinates f c b (hf x) (hx.symm ▸ hb)) v
  change fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart f b c a₀) x.val v = _
    at hOld
  rw [hOld]
  exact he

end NoExoticSixSphere.SphereMapSuspension
