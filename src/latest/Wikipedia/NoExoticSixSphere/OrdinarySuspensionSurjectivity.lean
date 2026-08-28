import Wikipedia.NoExoticSixSphere.SpherePrescribedPoints
import Wikipedia.NoExoticSixSphere.SemicircleSuspensionDescent

/-!
# Actual desuspension in the native sphere stability range

First prescribe the two pole values of the original map by a homotopy.
Its latitude paths form a genuine fixed-endpoint family. The checked
minimum-path representative theorem supplies an equatorial direction map;
descent of the whole path homotopy identifies its literal suspension with
the original map. No abstract surjectivity assumption is introduced.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SemicircleSuspension

theorem south_ne_north (m : ℕ) : south m ≠ north m := by
  intro h
  have hh := congrArg (fun x : Sphere (m + 1) ↦ x.val 0) h
  simp [south, north, antipode, spherePole] at hh
  linarith

end NoExoticSixSphere.SemicircleSuspension

namespace NoExoticSixSphere.SphereMapSuspension

open GLOrthonormalization SemicircleSuspension
open Wikipedia.HopfProblem.OrbitPair SpherePolygonEnergy

theorem exists_homotopic_suspension {m n : ℕ} (hd : m + 2 < 2 * (n + 1))
    (f : C(Sphere (m + 1), Sphere (n + 1))) :
    ∃ g : C(Sphere m, Sphere n), f.Homotopic (map g) := by
  let : Fact (Module.finrank ℝ (Vector (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨F, hF, hFs, hFn⟩ := exists_sphere_map_prescribed_pair f
    (south m) (north m) (south_ne_north m) (south n) (north n)
  let P := spherePathMap F hFs hFn
  obtain ⟨Y, ⟨H⟩⟩ := exists_minimumPathMap_representative (I := 𝓡 m)
    (south n) (north n) (north_eq_neg_south n)
    (by simpa only [finrank_euclideanSpace_fin] using hd) P
  let D := equatorialDirection n
  let g : C(Sphere m, Sphere n) := (D.symm : C(_, _)).comp Y
  have hg : pathMap g = (minimumPathMap (south n) (north n) (north_eq_neg_south n)).comp Y := by
    apply ContinuousMap.ext
    intro x
    change minimumPathMap (south n) (north n) (north_eq_neg_south n) (D (D.symm (Y x))) = _
    rw [Homeomorph.apply_symm_apply]
    rfl
  have hleft : descend P = F := descend_spherePathMap F hFs hFn
  have hright : descend ((minimumPathMap (south n) (north n) (north_eq_neg_south n)).comp Y) =
      map g := by
    rw [← hg, descend_pathMap]
  exact ⟨g, hF.trans ⟨(descendHomotopy H.toHomotopy).cast hleft hright⟩⟩

end NoExoticSixSphere.SphereMapSuspension
