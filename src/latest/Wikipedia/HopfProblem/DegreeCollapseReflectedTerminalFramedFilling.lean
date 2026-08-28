import Wikipedia.HopfProblem.DegreeCollapseReflectedTorsionIteration
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenTerminalFilling

/-!
# The original supplied endpoint bounds the actual terminal framed half

The finite surgery construction and its native boundary diffeomorphism
give a geometric framed filling of the endpoint with its original atlas.
That filling is simply connected and has zero H2, H3, and H4. The initial
regular collared cylinder and its low homology hypotheses remain inputs;
neither a missing initial filling nor smooth disk recognition is asserted.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere SingularMayerVietoris

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (hdim : m = n + 6) (a : Sphere m)
  (eBoundary : EndpointFiber d ≃ₜ Sphere 6)
  [SimplyConnectedSpace (NonnegativeHalf d)]
  [Subsingleton (SingularHomology (NonnegativeHalf d) 2)]
  [Finite (SingularHomology (NonnegativeHalf d) 3)]

include hmiss a eBoundary in
theorem exists_cleared_endpoint_framedFilling :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim);
    ∃ F : FramedSevenFilling (𝓡 6) (EndpointFiber d),
      letI := F.topology;
      SimplyConnectedSpace F.W ∧ Subsingleton (SingularHomology F.W 2) ∧
      Subsingleton (SingularHomology F.W 3) ∧ Subsingleton (SingularHomology F.W 4) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim)
  let := endpoint_homology_of_sphere d eBoundary 2 (by decide) (by decide)
  let := endpoint_homology_of_sphere d eBoundary 4 (by decide) (by decide)
  obtain ⟨U, _, hfinite, hzero, hD⟩ :=
    exists_cleared_reference_state d hmiss hdim a eBoundary
  let : Finite (SingularHomology U.Space 3) := hfinite
  let := U.zeroAtlas
  obtain ⟨D⟩ := hD
  refine ⟨U.framedFilling.reparametrizeBoundary D, ?_⟩
  change SimplyConnectedSpace U.Half ∧ Subsingleton (SingularHomology U.Half 2) ∧
    Subsingleton (SingularHomology U.Half 3) ∧ Subsingleton (SingularHomology U.Half 4)
  exact ⟨U.halfSimplyConnected, U.half_second_homology, hzero, U.half_fourth_homology⟩

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
