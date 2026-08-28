import Wikipedia.NoExoticSixSphere.TimeCollarPositiveCoreComplement
import Wikipedia.NoExoticSixSphere.HomotopyRetractConnectivity

/-!
# The actual exterior half is a homotopy retract of the positive core complement

Radial retraction maps the positive core complement to the literal new
half. The new collar first pushes every exterior point into positive new
time, where its original point belongs to the positive core complement.
The composite is exactly the original new-collar slide endpoint.
-/

noncomputable section

open Function Set Filter ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B B' : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] [TopologicalSpace B] [TopologicalSpace B']
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (t τ : C(M, ℝ)) (C : TimeCollar t B) (D : TimeCollar τ B')
  (hpos : ∀ x ∈ Φ.target, 0 < t x)
  (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x)
  (hhalf : ∀ x, 0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1)

include hΦ hpos in
theorem rawRetraction_time_pos (x : CoreComplement Φ) (hx : 0 < t x.val) :
    0 < t (rawRetraction Φ x) := by
  classical
  by_cases hxT : x.val ∈ Φ.target
  · rw [rawRetraction, if_pos hxT]
    exact hpos _ (Φ.toPartialEquiv.map_source (hΦ.symm ▸ mem_univ _))
  · simpa only [rawRetraction, if_neg hxT] using hx

include hΦ hpos hout in
theorem modified_positive_time_old (x : M) (hx : 0 < τ x) : 0 < t x := by
  by_cases hxT : x ∈ Φ.target
  · exact hpos x hxT
  · rwa [modified_time_eq_old_of_not_target Φ τ hΦ t hout hxT] at hx

def positiveRetraction : C(positiveCoreComplement Φ hΦ t C hpos, NonnegativeHalf τ) := by
  let f := forgetPositiveComplement Φ hΦ t C hpos
  refine ⟨fun x ↦ ⟨rawRetraction Φ (f x), (hhalf _).mpr
    ⟨(rawRetraction_time_pos Φ hΦ t hpos (f x) x.val.property).le,
      rawRetraction_mem_exterior Φ hΦ (f x)⟩⟩, ?_⟩
  exact ((continuous_rawRetraction Φ hΦ).comp f.continuous).subtype_mk _

def interiorToCoreComplement : C(D.positiveInterior, positiveCoreComplement Φ hΦ t C hpos) := by
  let f : D.positiveInterior → C.positiveInterior := fun x ↦
    ⟨x.val, modified_positive_time_old Φ hΦ t τ hpos hout x.val x.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hmiss (x : D.positiveInterior) : f x ∉ range (positiveCore Φ hΦ t C hpos) := by
    intro hx
    have hcore := (mem_range_positiveCore_iff Φ hΦ t C hpos (f x)).mp hx
    exact ((hhalf x.val).mp x.property.le).2 (core_subset_openRegion_one Φ hcore)
  exact ⟨fun x ↦ ⟨f x, hmiss x⟩, hf.subtype_mk _⟩

theorem positiveRetraction_interior (x : D.positiveInterior) :
    positiveRetraction Φ hΦ t τ C hpos hhalf
      (interiorToCoreComplement Φ hΦ t τ C D hpos hout hhalf x) = D.interiorToHalf x := by
  apply Subtype.ext
  exact rawRetraction_eq_of_exterior Φ hΦ _ ((hhalf x.val).mp x.property.le).2

theorem half_retraction_right_homotopy :
    ((positiveRetraction Φ hΦ t τ C hpos hhalf).comp
      ((interiorToCoreComplement Φ hΦ t τ C D hpos hout hhalf).comp D.halfToInterior)
      ).Homotopic (ContinuousMap.id (NonnegativeHalf τ)) := by
  have he : (positiveRetraction Φ hΦ t τ C hpos hhalf).comp
      ((interiorToCoreComplement Φ hΦ t τ C D hpos hout hhalf).comp D.halfToInterior) =
      D.interiorToHalf.comp D.halfToInterior :=
    ContinuousMap.ext (fun x ↦ positiveRetraction_interior Φ hΦ t τ C D hpos hout hhalf
      (D.halfToInterior x))
  rw [he]
  exact ⟨D.halfInteriorSlide.symm⟩

end NoExoticSixSphere.SphereFourTube
