import Wikipedia.HomotopyGroupsOfSpheres.CubeBoundary

/-!
# Circle-valued boundary corrections on higher cubes

The original disk/cube homeomorphism identifies the boundary of an
(n+3)-cube with the ordinary (n+2)-sphere. Its simple connectedness
supplies a real logarithm of every circle-valued boundary map. Tietze
extension then gives an exact circle-valued extension over the cube.
These are the boundary corrections needed for higher Hopf lifts.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HomotopyGroupsOfSpheres

namespace NoExoticSixSphere.HigherHopf

open Wikipedia.HopfProblem.DegreeCollapse

def coordinates (n : ℕ) : EuclideanSpace ℝ (Fin (n + 3)) ≃L[ℝ] (Fin (n + 3) → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 3) ↦ ℝ)

def sphereCubeBoundary (n : ℕ) : Sphere (n + 2) ≃ₜ Cube.boundary (Fin (n + 3)) where
  toFun v := ⟨DiskCube.homeomorph (coordinates n)
      ⟨v.val, by
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact (mem_sphere_zero_iff_norm.mp v.property).le⟩,
    (DiskCube.boundary_iff (coordinates n) _).mpr (mem_sphere_zero_iff_norm.mp v.property)⟩
  invFun u := ⟨((DiskCube.homeomorph (coordinates n)).symm u.val).val,
    mem_sphere_zero_iff_norm.mpr
      ((DiskCube.symm_boundary_iff (coordinates n) u.val).mpr u.property)⟩
  left_inv v := by
    apply Subtype.ext
    change (((DiskCube.homeomorph (coordinates n)).symm
      ((DiskCube.homeomorph (coordinates n)) ⟨v.val, _⟩)).val) = v.val
    rw [Homeomorph.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    exact (DiskCube.homeomorph (coordinates n)).apply_symm_apply u.val
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem boundary_simplyConnected (n : ℕ) :
    SimplyConnectedSpace (Cube.boundary (Fin (n + 3))) :=
  (sphereCubeBoundary n).symm.toHomotopyEquiv.simplyConnectedSpace

theorem boundary_locallyPathConnected (n : ℕ) :
    LocallyPathConnectedSpace (Cube.boundary (Fin (n + 3))) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
    ⟨by simp⟩
  let : LocallyPathConnectedSpace (Sphere (n + 2)) :=
    ChartedSpace.locallyPathConnectedSpace
      (H := EuclideanSpace ℝ (Fin (n + 2))) (M := Sphere (n + 2))
  exact (sphereCubeBoundary n).isQuotientMap.locallyPathConnectedSpace

theorem boundary_circle_log (n : ℕ) (g : C(Cube.boundary (Fin (n + 3)), Circle)) :
    ∃ F : C(Cube.boundary (Fin (n + 3)), ℝ), ∀ u, Circle.exp (F u) = g u := by
  let := boundary_simplyConnected n
  let := boundary_locallyPathConnected n
  let u₀ : Cube.boundary (Fin (n + 3)) := ⟨0, ⟨0, Or.inl rfl⟩⟩
  obtain ⟨F, ⟨_, hF⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    g u₀ (Complex.arg (g u₀)) (Circle.exp_arg (g u₀))
  exact ⟨F, fun u ↦ congrFun hF u⟩

theorem boundary_circle_extension (n : ℕ) (g : C(Cube.boundary (Fin (n + 3)), Circle)) :
    ∃ G : C(Fin (n + 3) → I, Circle), ∀ u : Cube.boundary (Fin (n + 3)), G u.val = g u := by
  obtain ⟨F, hF⟩ := boundary_circle_log n g
  obtain ⟨K, hK⟩ := F.exists_restrict_eq
    (Wikipedia.HopfProblem.SixSphereCube.isClosed_cubeBoundaryN (n + 3))
  refine ⟨⟨fun u ↦ Circle.exp (K u), by fun_prop⟩, fun u ↦ ?_⟩
  change Circle.exp (K u.val) = g u
  have hu : K u.val = F u := DFunLike.congr_fun hK u
  rw [hu, hF]

end NoExoticSixSphere.HigherHopf
