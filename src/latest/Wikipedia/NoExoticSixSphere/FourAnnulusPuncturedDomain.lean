import Wikipedia.NoExoticSixSphere.FourAnnulusParityBallSystem
import Wikipedia.NoExoticSixSphere.SphereAnnulusFrontier

/-!
# The actual punctured annulus retains both original endpoint spheres

Removing the chosen open singularity balls leaves a compact domain with
injective native derivative everywhere. Its frontier consists of BOTH
original boundary spheres and the actual linking spheres. The literal
inner and outer endpoint parametrizations, and all original linking
parametrizations, remain continuous maps into this same punctured domain.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem

open GLOrthonormalization AnnulusDoublePoints SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g)

def puncturedAnnulus : Set (Vector 4) := domain 3 \ P.openHoles

theorem isCompact_puncturedAnnulus : IsCompact P.puncturedAnnulus :=
  (isCompact_domain 3).diff P.isOpen_openHoles

theorem injective_mfderiv_on_puncturedAnnulus (x : Vector 4) (hx : x ∈ P.puncturedAnnulus) :
    Injective (mfderiv (𝓡 4) (𝓡 7) g x) := by
  by_contra hs
  exact hx.2 (P.singular_subset_openHoles ⟨hx.1, hs⟩)

theorem interior_puncturedAnnulus :
    interior P.puncturedAnnulus = openDomain 3 \ P.closedHoles := by
  rw [puncturedAnnulus, sdiff_eq, interior_inter, interior_domain,
    interior_compl, P.closure_openHoles]
  rfl

theorem frontier_puncturedAnnulus : frontier P.puncturedAnnulus =
    (sphere (0 : Vector 4) 1 ∪ sphere 0 2) ∪ P.linkingBoundary := by
  have hboundary : domain 3 \ openDomain 3 = sphere (0 : Vector 4) 1 ∪ sphere 0 2 := by
    rw [← frontier_domain, (isClosed_domain 3).frontier_eq, interior_domain]
  rw [P.isCompact_puncturedAnnulus.isClosed.frontier_eq, P.interior_puncturedAnnulus,
    puncturedAnnulus, ← hboundary, ← P.closedHoles_sdiff_openHoles]
  ext x
  have hCI : x ∈ P.closedHoles → x ∈ openDomain 3 :=
    fun hx ↦ P.closedHoles_subset_interior hx
  have hIA : x ∈ openDomain 3 → x ∈ domain 3 := fun hx ↦ openDomain_subset_domain 3 hx
  have hUC : x ∈ P.openHoles → x ∈ P.closedHoles :=
    fun hx ↦ P.openHoles_subset_closedHoles hx
  simp only [mem_sdiff, mem_union]
  tauto

theorem linkingBoundary_subset_puncturedAnnulus : P.linkingBoundary ⊆ P.puncturedAnnulus := by
  rw [← P.closedHoles_sdiff_openHoles]
  intro x hx
  exact ⟨openDomain_subset_domain 3 (P.closedHoles_subset_interior hx.1), hx.2⟩

theorem boundary_mem_puncturedAnnulus (x : Vector 4)
    (hx : x ∈ sphere 0 1 ∪ sphere 0 2) : x ∈ P.puncturedAnnulus := by
  apply P.isCompact_puncturedAnnulus.isClosed.frontier_subset
  rw [P.frontier_puncturedAnnulus]
  exact Or.inl hx

theorem boundary_disjoint_linkingBoundary :
    Disjoint (sphere (0 : Vector 4) 1 ∪ sphere 0 2) P.linkingBoundary := by
  apply disjoint_left.mpr
  intro x hx hlink
  rw [← P.closedHoles_sdiff_openHoles] at hlink
  have hnorm := P.closedHoles_subset_interior hlink.1
  rcases hx with hx | hx
  · exact (mem_sphere_zero_iff_norm.mp hx).not_gt hnorm.1
  · exact (mem_sphere_zero_iff_norm.mp hx).not_lt hnorm.2

theorem protected_mem_puncturedAnnulus (r₀ r₁ : ℝ)
    (hholes : P.closedHoles ⊆ {x | r₀ < ‖x‖ ∧ ‖x‖ < r₁})
    (x : Vector 4) (hx : x ∈ domain 3) (hend : ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖) :
    x ∈ P.puncturedAnnulus := by
  refine ⟨hx, ?_⟩
  intro hhole
  have hactive := hholes (P.openHoles_subset_closedHoles hhole)
  exact hend.elim (not_le_of_gt hactive.1) (not_le_of_gt hactive.2)

def innerBoundary : C(Sphere 3, P.puncturedAnnulus) where
  toFun q := ⟨q.val, P.boundary_mem_puncturedAnnulus q.val (Or.inl q.property)⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def outerBoundary : C(Sphere 3, P.puncturedAnnulus) where
  toFun q := ⟨(2 : ℝ) • q.val, P.boundary_mem_puncturedAnnulus _ (Or.inr (by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, ClosedHemisphere.unit_norm]
    norm_num))⟩
  continuous_toFun :=
    (show Continuous (fun q : Sphere 3 ↦ (2 : ℝ) • q.val) from
      continuous_subtype_val.const_smul (2 : ℝ)).subtype_mk _

def linkingSphere (x : singularSet g) : C(Sphere 3, P.puncturedAnnulus) where
  toFun q := ⟨(P.ball x).chart q.val,
    P.linkingBoundary_subset_puncturedAnnulus (mem_iUnion.mpr ⟨x, ⟨q.val, q.property, rfl⟩⟩)⟩
  continuous_toFun :=
    ((P.ball x).chart.contMDiffOn_toFun.continuousOn.mono
      (sphere_subset_closedBall.trans (P.ball x).ball_source)).domRestrict.subtype_mk _

end NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem
