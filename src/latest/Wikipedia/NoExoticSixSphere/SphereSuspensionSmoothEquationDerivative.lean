import Wikipedia.NoExoticSixSphere.SphereSuspensionEquationDerivative

/-!
# The full derivative retained by fiber-preserving smooth suspension

Agreement of the sphere maps near an equatorial fiber point gives
agreement of their actual radial equations near the ambient point.
Consequently the globally smooth suspension representative has exactly
the computed full suspension derivative, not merely an equivalent fiber.
-/

noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereLevelEquations

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {m : ℕ} [hdim : Fact (Module.finrank ℝ E = m + 1)]

include hdim in
theorem equations_eventuallyEq_of_sphere_germ (a x : UnitSphere E)
    (g g' : UnitSphere E → F) (h : g =ᶠ[𝓝 x] g') :
    equations a g =ᶠ[𝓝 x.val] equations a g' := by
  have ht : Tendsto (SphereRadialRetraction.retract a) (𝓝 x.val) (𝓝 x) := by
    have hc := (SphereRadialRetraction.contMDiffAt_retract (n := m) a
      (ne_zero_of_mem_unit_sphere x)).continuousAt
    rw [ContinuousAt, SphereRadialRetraction.retract_coe] at hc
    exact hc
  filter_upwards [h.comp_tendsto ht] with v hv
  change WithLp.toLp 2 (‖v‖ ^ 2 - 1, g (SphereRadialRetraction.retract a v)) =
    WithLp.toLp 2 (‖v‖ ^ 2 - 1, g' (SphereRadialRetraction.retract a v))
  change g (SphereRadialRetraction.retract a v) = g' (SphereRadialRetraction.retract a v) at hv
  rw [hv]

end NoExoticSixSphere.SphereLevelEquations

namespace NoExoticSixSphere.SphereMapSuspension

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

theorem equator_val_join (m : ℕ) (x : Sphere m) :
    (equator m x).val = SphereCylinder.join m (0, x.val) := by
  ext i
  exact Fin.cases (equator_head x) (fun j ↦ equator_tail x j) i

variable {m n : ℕ} (f : C(Sphere m, Sphere n)) (b : Sphere n)
  (c : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞)
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (hb : b ∈ c.source)
  (g : C(Sphere (m + 1), Sphere (n + 1)))
  (hg : ContMDiff (𝓡 (m + 1)) (𝓡 (n + 1)) ∞ g)

include hf hb hg in
theorem fderiv_smoothSuspensionEquations (a : Sphere (m + 1)) (a₀ x : Sphere m)
    (hx : f x = b) (hgerm : (g : Sphere (m + 1) → Sphere (n + 1)) =ᶠ[𝓝 (equator m x)] map f)
    (s : ℝ) (v : Vector (m + 1)) :
    fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart g (equator n b)
      (targetCylinderChart c) a) (equator m x).val (SphereCylinder.join m (s, v)) =
      WithLp.toLp 2
        ((fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart f b c a₀) x.val v).fst,
          EuclideanProduct.coordinates n (s,
            (fderiv ℝ (SphereFiberNormalFrame.equationsWithTargetChart f b c a₀)
              x.val v).snd)) := by
  let : Fact (Module.finrank ℝ (Vector (m + 2)) = (m + 1) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hpoint : g (equator m x) = equator n b := by
    rw [hgerm.self_of_nhds, map_equator, hx]
  have hc : CenteredChartCoordinates.coordinates g (targetCylinderChart c) (equator n b)
      =ᶠ[𝓝 (equator m x)]
        CenteredChartCoordinates.coordinates (map f) (targetCylinderChart c) (equator n b) := by
    filter_upwards [hgerm] with y hy
    exact congrArg (fun z ↦ targetCylinderChart c z - targetCylinderChart c (equator n b)) hy
  have hE := SphereLevelEquations.equations_eventuallyEq_of_sphere_germ (m := m + 1)
    a (equator m x) _ _ hc
  have ht : Tendsto (SphereCylinder.join m) (𝓝 ((0 : ℝ), x.val))
      (𝓝 (equator m x).val) := by
    rw [equator_val_join]
    exact (SphereCylinder.join m).continuousAt
  have hd := (hE.comp_tendsto ht).fderiv_eq (𝕜 := ℝ)
  have hD := (SphereFiberNormalFrame.contDiffAt_equationsWithTargetChart g hg (equator n b)
    (targetCylinderChart c) (equator_mem_targetCylinderChart c b hb) a (equator m x)
      hpoint).differentiableAt (by simp)
  have hD' : DifferentiableAt ℝ (SphereFiberNormalFrame.equationsWithTargetChart g
      (equator n b) (targetCylinderChart c) a) (SphereCylinder.join m (0, x.val)) := by
    rw [← equator_val_join]
    exact hD
  have hchain := fderiv_comp ((0 : ℝ), x.val) hD' (SphereCylinder.join m).differentiableAt
  rw [ContinuousLinearEquiv.fderiv, ← equator_val_join] at hchain
  have he := congrArg (fun L : (ℝ × Vector (m + 1)) →L[ℝ]
      WithLp 2 (ℝ × Vector (n + 1)) ↦ L (s, v)) (hchain.symm.trans hd)
  exact he.trans (fderiv_suspensionEquations_join f b c hf hb a a₀ x hx s v)

end NoExoticSixSphere.SphereMapSuspension
