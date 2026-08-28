import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenBoundary
import Wikipedia.HopfProblem.DegreeCollapseReflectedTimeCollar
import Wikipedia.HopfProblem.DegreeCollapseReflectedLinking
import Wikipedia.HopfProblem.DegreeCollapseReflectedTimeZeroDiffeomorph

/-!
# Actual torsion-clearing iteration from the supplied original filling

The original reflected fiber, native atlas, full normal framing, regular
time, and proved collar form a concrete initial state. Finite surgery
iteration kills its positive-half H3. The original endpoint retains its
original regular-fiber atlas through the complete boundary diffeomorphism.
The supplied initial filling and its low homology hypotheses are explicit;
this does not construct the threefold's missing initial filling.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (hdim : m = n + 6) (a : Sphere m)
  (eBoundary : EndpointFiber d ≃ₜ Sphere 6)
  [SimplyConnectedSpace (NonnegativeHalf d)]
  [Subsingleton (SingularHomology (NonnegativeHalf d) 2)]

def referenceCollaredState : CollaredSevenState (EndpointFiber d) := by
  let := fiberAtlas d 6 hdim
  let := fiber_isManifold d 6 hdim
  let := compactSpace_fiber d hmiss
  let : SimplyConnectedSpace (EndpointFiber d) := simplyConnectedSpace_of_homeomorph eBoundary
  let : SimplyConnectedSpace (Fiber d) := fiber_simplyConnected_of_half d
  let := fiber_second_homology_of_endpoint_sphere d eBoundary
  let : SimplyConnectedSpace (TimeCollar.NonnegativeHalf (time d)) :=
    inferInstanceAs (SimplyConnectedSpace (NonnegativeHalf d))
  exact CollaredSevenState.ofCollar (embedding d hmiss 6 hdim)
    (euclideanNormalFraming d hmiss 6 hdim a) (time d) (contMDiff_time d 6 hdim)
    (regular_time_zero d 6 hdim) (seamTimeCollar d)

def referenceStateZeroDiffeomorph :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim);
    letI := (referenceCollaredState d hmiss hdim a eBoundary).zeroAtlas;
    EndpointFiber d ≃ₘ⟮𝓡 6, 𝓡 6⟯ (referenceCollaredState d hmiss hdim a eBoundary).Zero := by
  let := fiberAtlas d 6 hdim
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim)
  let := timeZeroAtlas d 6 hdim
  exact timeZeroDiffeomorph d 6 hdim

theorem exists_cleared_reference_state [Finite (SingularHomology (NonnegativeHalf d) 3)] :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim);
    ∃ U : CollaredSevenState (EndpointFiber d),
      (referenceCollaredState d hmiss hdim a eBoundary).Reachable U ∧
      Finite (SingularHomology U.Space 3) ∧
      Subsingleton (SingularHomology (TimeCollar.NonnegativeHalf U.time) 3) ∧
      (letI := U.zeroAtlas; Nonempty (EndpointFiber d ≃ₘ⟮𝓡 6, 𝓡 6⟯ U.Zero)) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim)
  let := endpoint_homology_of_sphere d eBoundary 2 (by decide) (by decide)
  let := endpoint_homology_of_sphere d eBoundary 3 (by decide) (by decide)
  let := endpoint_homology_of_sphere d eBoundary 4 (by decide) (by decide)
  let S := referenceCollaredState d hmiss hdim a eBoundary
  let : Finite (SingularHomology S.Space 3) := by
    change Finite (SingularHomology (Fiber d) 3)
    exact fiber_third_homology_finite_of_endpoint_sphere d eBoundary
  obtain ⟨U, hSU, hfinite, hzero⟩ := S.exists_cleared
  refine ⟨U, hSU, hfinite, hzero, ?_⟩
  let := S.zeroAtlas
  let := U.zeroAtlas
  obtain ⟨D⟩ := hSU.zero_diffeomorphic
  exact ⟨(referenceStateZeroDiffeomorph d hmiss hdim a eBoundary).trans D⟩

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
