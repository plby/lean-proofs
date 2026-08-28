import Wikipedia.NoExoticSixSphere.SphereFourTubeHalfImageRelation

/-!
# Even longitude and an integral meridian coefficient

The actual product third-homology equivalence decomposes the boundary
class with the original sphere markings. Longitude projection equal to
twice the generator gives coefficient exactly two; the meridian
coefficient is unrestricted. This does not assert its quadratic parity.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.PeriodTorusHigherHomology ProductThirdHomology

theorem two_longitude_decomposition (s v₀ : Sphere 3)
    (v : SingularHomology (Sphere 3 × Sphere 3) 3)
    (hfst : singularHomologyMap ContinuousMap.fst 3 v = (2 : ℤ) • unitSphereTopClass 2) :
    ∃ k : ℤ, v =
      (2 : ℤ) • singularHomologyMap (leftSection v₀) 3 (unitSphereTopClass 2) +
        k • singularHomologyMap (rightSection s) 3 (unitSphereTopClass 2) := by
  let : Subsingleton (π_ 2 (Sphere 3) s) := subsingleton_sphereHomotopyGroup (by decide) s
  let : Subsingleton (π_ 2 (Sphere 3) v₀) := subsingleton_sphereHomotopyGroup (by decide) v₀
  obtain ⟨k, hk⟩ := unitSphereTopClass_generates 2 (singularHomologyMap ContinuousMap.snd 3 v)
  have he : equivalence s v₀ v = ((2 : ℤ) • unitSphereTopClass 2, k • unitSphereTopClass 2) :=
    Prod.ext ((equivalence_fst s v₀ v).trans hfst) ((equivalence_snd s v₀ v).trans hk.symm)
  refine ⟨k, ?_⟩
  calc
    v = (equivalence s v₀).symm (equivalence s v₀ v) :=
      ((equivalence s v₀).symm_apply_apply v).symm
    _ = (equivalence s v₀).symm
        ((2 : ℤ) • unitSphereTopClass 2, k • unitSphereTopClass 2) := congrArg _ he
    _ = _ := by rw [equivalence_symm_pair, map_zsmul, map_zsmul]

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (t τ : C(M, ℝ))
  (hpos : ∀ x ∈ Φ.target, 0 < t x)
  (hhalf : ∀ x, 0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1)
  (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)

theorem exists_even_longitude_relation
    (a : SingularHomology (halfCoreComplement Φ t) 3)
    (hclass : singularHomologyMap (subtypeInclusion (halfCoreComplement Φ t)) 3 a =
      (2 : ℤ) • singularHomologyMap (coreInHalf Φ hΦ t hpos) 3 (unitSphereTopClass 2))
    (s v₀ : Sphere 3) : ∃ k : ℤ,
    singularHomologyMap (halfComplementRetraction Φ hΦ t τ hpos hhalf) 3 a =
      (2 : ℤ) • singularHomologyMap
        ((boundaryInNewHalf Φ hΦ τ hinner).comp (leftSection v₀)) 3 (unitSphereTopClass 2) +
      k • singularHomologyMap
        ((boundaryInNewHalf Φ hΦ τ hinner).comp (rightSection s)) 3 (unitSphereTopClass 2) := by
  obtain ⟨v, hv, hfst⟩ :=
    exists_boundary_class_of_double_core_image Φ hΦ t τ hpos hhalf hinner a hclass
  obtain ⟨k, hk⟩ := two_longitude_decomposition s v₀ v hfst
  refine ⟨k, ?_⟩
  rw [hv, hk, map_add, map_zsmul, map_zsmul]
  simp only [singularHomologyMap_comp, LinearMap.comp_apply]

end NoExoticSixSphere.SphereFourTube
