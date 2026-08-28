import Wikipedia.HopfProblem.DegreeCollapseReflectedTerminalFramedFilling
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenUpperHomology

/-!
# The supplied original endpoint bounds a simply connected acyclic framed filling

The finite surgery path, the actual terminal half, all positive homology
vanishings, and the original boundary diffeomorphism are retained together.
The initial filling remains an explicit input. Acyclicity and simple
connectivity are not asserted to be a smooth disk recognition theorem.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse

open NoExoticSixSphere SingularMayerVietoris PeriodTorusHigherHomology

namespace CollaredSevenState

theorem exists_acyclic_framedFilling {B : Type} [TopologicalSpace B]
    (S : CollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6)
    [Finite (SingularHomology S.Space 3)] :
    letI := S.zeroAtlas;
    ∃ (U : CollaredSevenState B) (h : S.Reachable U),
      Finite (SingularHomology U.Space 3) ∧
      (let F := h.framedFilling; letI := F.topology;
        SimplyConnectedSpace F.W ∧ ∀ k : ℕ, k ≠ 0 → Subsingleton (SingularHomology F.W k)) := by
  let := S.zeroAtlas
  have hB (j : ℕ) (hj : j ≠ 0) (h6 : j ≠ 6) : Subsingleton (SingularHomology B j) := by
    let : Subsingleton (SingularHomology (Sphere 6) j) :=
      SphereHomology.unitSphere_homology_subsingleton 5 j hj h6
    exact (homotopyEquivHomologyEquiv eBoundary.toHomotopyEquiv j).injective.subsingleton
  let := hB 2 (by decide) (by decide)
  let := hB 3 (by decide) (by decide)
  let := hB 4 (by decide) (by decide)
  obtain ⟨U, h, hfinite, hzero⟩ := S.exists_cleared
  let : Finite (SingularHomology U.Space 3) := hfinite
  let : Subsingleton (SingularHomology U.Half 3) := hzero
  refine ⟨U, h, hfinite, ?_⟩
  change SimplyConnectedSpace U.Half ∧
    ∀ k : ℕ, k ≠ 0 → Subsingleton (SingularHomology U.Half k)
  exact ⟨U.halfSimplyConnected, U.half_positive_homology_of_sphere eBoundary⟩

end CollaredSevenState

namespace ReflectedCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (hdim : m = n + 6) (a : Sphere m)
  (eBoundary : EndpointFiber d ≃ₜ Sphere 6)
  [SimplyConnectedSpace (NonnegativeHalf d)]
  [Subsingleton (SingularHomology (NonnegativeHalf d) 2)]
  [Finite (SingularHomology (NonnegativeHalf d) 3)]

include hmiss a eBoundary in
theorem exists_acyclic_endpoint_framedFilling :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim);
    ∃ F : FramedSevenFilling (𝓡 6) (EndpointFiber d),
      letI := F.topology;
      SimplyConnectedSpace F.W ∧ ∀ k : ℕ, k ≠ 0 → Subsingleton (SingularHomology F.W k) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hdim)
  obtain ⟨U, _, hfinite, hzero, hD⟩ :=
    exists_cleared_reference_state d hmiss hdim a eBoundary
  let : Finite (SingularHomology U.Space 3) := hfinite
  let : Subsingleton (SingularHomology U.Half 3) := hzero
  let := U.zeroAtlas
  obtain ⟨D⟩ := hD
  refine ⟨U.framedFilling.reparametrizeBoundary D, ?_⟩
  change SimplyConnectedSpace U.Half ∧
    ∀ k : ℕ, k ≠ 0 → Subsingleton (SingularHomology U.Half k)
  exact ⟨U.halfSimplyConnected, U.half_positive_homology_of_sphere eBoundary⟩

end ReflectedCylinder
end Wikipedia.HopfProblem.DegreeCollapse
