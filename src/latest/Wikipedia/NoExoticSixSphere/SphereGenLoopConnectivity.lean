import Wikipedia.NoExoticSixSphere.CubeCollar
import Wikipedia.NoExoticSixSphere.CubeSphereRetract
import Wikipedia.NoExoticSixSphere.RelativeSphereConnectivity
import Wikipedia.NoExoticSixSphere.RetractionHomotopyTransfer

/-!
# Contraction of lower-dimensional generalized loops in a sphere

Collar the cube boundary, extend the collared loop to a same-dimensional
sphere using the checked retraction, and apply relative smooth approximation
and point avoidance. Restricting the contraction back to the cube retains
every boundary face. Thus this concerns the actual native generalized loops,
not just unbased homotopy classes of sphere maps.
-/

open scoped Manifold ContDiff Topology
open Set

namespace NoExoticSixSphere

theorem sphere_genLoop_homotopic_const {m n : ℕ} (hm : 0 < m) (hmn : m < n)
    (b : Sphere n) (p : GenLoop (Fin m) (Sphere n) b) :
    GenLoop.Homotopic p GenLoop.const := by
  obtain ⟨e, r, hre⟩ := CubeSphereRetract.exists_retract m
  let p' := CubeCollar.genLoop p
  let F : C(Sphere m, Sphere n) := p'.1.comp r
  let S : Set (Sphere m) := r ⁻¹' Cube.boundary (Fin m)
  let U : Set (Sphere m) := r ⁻¹' CubeCollar.region (Fin m)
  have hS : IsClosed S := (CubeCollar.isClosed_boundary (Fin m)).preimage r.continuous
  have hU : IsOpen U := (CubeCollar.isOpen_region (Fin m)).preimage r.continuous
  have hSU : S ⊆ U := fun _ hx ↦ CubeCollar.boundary_subset_region (Fin m) hx
  have hSne : S.Nonempty := by
    let x : Fin m → unitInterval := fun _ ↦ 0
    refine ⟨e x, ?_⟩
    change r (e x) ∈ Cube.boundary (Fin m)
    rw [show r (e x) = x from ContinuousMap.congr_fun hre x]
    exact ⟨⟨0, hm⟩, Or.inl rfl⟩
  have hFUeq : ∀ z ∈ U, F z = b := fun _ hz ↦ CubeCollar.genLoop_eq_base p hz
  have hFU : ContMDiffOn (𝓡 m) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (fun z ↦ (F z : EuclideanSpace ℝ (Fin (n + 1)))) U := by
    have hc : ContMDiffOn (𝓡 m) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
        (fun _ : Sphere m ↦ (b : EuclideanSpace ℝ (Fin (n + 1)))) U := contMDiffOn_const
    exact hc.congr (fun z hz ↦ congrArg Subtype.val (hFUeq z hz))
  obtain ⟨H⟩ := sphereMap_nullhomotopicRel_of_dim_lt (I := 𝓡 m) n F b hS hSne
    (hU.mem_nhdsSet.mpr hSU) hFU (fun z hz ↦ hFUeq z (hSU hz))
    (by simpa only [finrank_euclideanSpace_fin] using hmn)
  have H' := (RetractionHomotopyTransfer.precompose H e).cast
    (RetractionHomotopyTransfer.comp_retract e r hre p'.1) rfl
  rw [RetractionHomotopyTransfer.preimage_retract e r hre] at H'
  exact GenLoop.Homotopic.trans ⟨CubeCollar.homotopy p⟩ ⟨H'⟩

theorem subsingleton_sphereHomotopyGroup_of_pos {m n : ℕ} (hm : 0 < m) (hmn : m < n)
    (b : Sphere n) : Subsingleton (HomotopyGroup (Fin m) (Sphere n) b) := by
  refine ⟨fun x y ↦ Quotient.inductionOn₂ x y ?_⟩
  intro p q
  apply Quotient.sound
  exact (sphere_genLoop_homotopic_const hm hmn b p).trans
    (sphere_genLoop_homotopic_const hm hmn b q).symm

end NoExoticSixSphere
