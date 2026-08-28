import Wikipedia.NoExoticSixSphere.SphereConnectivity
import Wikipedia.HopfProblem.OrbitPairSphereNullhomotopyCriterion
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Connectivity of actual Cartesian products of spheres

Coordinate homotopies combine in the original product topology. Actual
lower-dimensional sphere-map contractions therefore give native
homotopy vanishing for these products, with every basepoint retained.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.SphereProductConnectivity

theorem simplyConnected_pi {ι : Type} {X : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, SimplyConnectedSpace (X i)] : SimplyConnectedSpace (∀ i, X i) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro x γ
  let H := fun i ↦ (SimplyConnectedSpace.paths_homotopic
    (γ.map (continuous_apply i)) (Path.refl (x i))).some
  exact ⟨{
    toFun := fun p i ↦ H i p
    continuous_toFun := continuous_pi (fun i ↦ (H i).continuous)
    map_zero_left := fun t ↦ funext (fun i ↦ (H i).apply_zero t)
    map_one_left := fun t ↦ funext (fun i ↦ (H i).apply_one t)
    prop' := fun s t ht ↦ funext (fun i ↦ (H i).eq_fst s ht) }⟩

theorem sphereMap_nullhomotopic {ι : Type} {n d : ℕ} (hd : d < n)
    (f : C(Sphere d, ι → Sphere n)) : ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  choose c hc using fun i : ι ↦ sphere_sphere_nullhomotopic hd ((ContinuousMap.eval i).comp f)
  refine ⟨c, ⟨{
    toFun := fun p i ↦ (hc i).some p
    continuous_toFun := continuous_pi (fun i ↦ (hc i).some.continuous)
    map_zero_left := fun x ↦ funext (fun i ↦ (hc i).some.apply_zero x)
    map_one_left := fun x ↦ funext (fun i ↦ (hc i).some.apply_one x) }⟩⟩

theorem pi_subsingleton {ι : Type} {n d : ℕ} (hd : 0 < d) (hdn : d < n)
    (x : ι → Sphere n) : Subsingleton (π_ d (ι → Sphere n) x) :=
  Wikipedia.HopfProblem.OrbitPair.SphereNullhomotopy.pi_subsingleton_of_sphere_nullhomotopies
    hd (sphereMap_nullhomotopic hdn) x

end NoExoticSixSphere.SphereProductConnectivity
