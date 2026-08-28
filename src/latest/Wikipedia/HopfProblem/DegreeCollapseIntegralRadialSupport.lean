import Wikipedia.HopfProblem.DegreeCollapseRadialExteriorEquivalence
import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeCohomologyComparison

/-!
# The original integral extension from the core to a radial tube

The actual inclusion of tube complements is the proved radial homotopy
equivalence. The original ambient identity and pair sequence therefore
give an isomorphism of relative homology. Its original dual is exactly
the support-extension map, which is bijective in every degree.
-/

noncomputable section

open Function Set ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRadialSupport

open SingularMayerVietoris PeriodTorusHigherHomology NoExoticSixSphere

variable (B E : Type) [TopologicalSpace B] [NormedAddCommGroup E] [NormedSpace ℝ E]

def support (r : ℝ) : Set (B × E) := {p | ‖p.2‖ ≤ r}

omit [TopologicalSpace B] [NormedSpace ℝ E] in
theorem support_mono {r s : ℝ} (h : r ≤ s) : support B E r ⊆ support B E s :=
  fun _ hp ↦ hp.trans h

omit [TopologicalSpace B] [NormedSpace ℝ E] in
theorem support_zero : support B E 0 = range (fun b : B ↦ (b, (0 : E))) := by
  ext p
  constructor
  · intro hp
    have hz : p.2 = 0 := norm_eq_zero.mp (le_antisymm hp (norm_nonneg _))
    exact ⟨p.1, Prod.ext rfl hz.symm⟩
  · rintro ⟨b, rfl⟩
    exact norm_zero.le

def complementHomeomorph (r : ℝ) :
    ((support B E r)ᶜ : Set (B × E)) ≃ₜ RadialExterior.outside B E r :=
  Homeomorph.setCongr (by
    ext p
    change (¬ ‖p.2‖ ≤ r) ↔ r < ‖p.2‖
    exact not_le)

variable (r : ℝ) (hr : 0 ≤ r)

include hr in
omit [NormedSpace ℝ E] in
theorem complement_mapsTo :
    MapsTo (ContinuousMap.id (B × E)) (support B E r)ᶜ (support B E 0)ᶜ :=
  fun _ hx hy ↦ hx (support_mono B E hr hy)

def complementHomotopyEquiv :
    ((support B E r)ᶜ : Set (B × E)) ≃ₕ ((support B E 0)ᶜ : Set (B × E)) :=
  (complementHomeomorph B E r).toHomotopyEquiv.trans
    ((RadialExterior.homotopyEquiv B E r hr).trans
      (complementHomeomorph B E 0).symm.toHomotopyEquiv)

theorem complementHomotopyEquiv_toFun :
    (complementHomotopyEquiv B E r hr).toFun =
      RelativeSingularHomology.restrictedMap (ContinuousMap.id (B × E))
        (complement_mapsTo B E r hr) := by
  apply ContinuousMap.ext
  intro p
  exact Subtype.ext rfl

theorem restriction_homology_bijective (n : ℕ) :
    Bijective (RelativeSingularHomology.map (ContinuousMap.id (B × E))
      (complement_mapsTo B E r hr) n) := by
  apply RelativeSingularHomology.map_bijective_of_absolute
  · intro k
    rw [singularHomologyMap_id]
    exact bijective_id
  · intro k
    rw [← complementHomotopyEquiv_toFun]
    exact (homotopyEquivHomologyEquiv (complementHomotopyEquiv B E r hr) k).bijective

theorem extend_bijective (p : ℕ) :
    Bijective (IntegralSupportedCohomology.extend (support_mono B E hr) p) := by
  rw [IntegralSupportedCohomology.extend_eq_pullback]
  exact RelativeIntegralCap.cohomologyPullback_bijective_of_homology
    (ContinuousMap.id (B × E)) (complement_mapsTo B E r hr)
    (restriction_homology_bijective B E r hr) p

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRadialSupport
