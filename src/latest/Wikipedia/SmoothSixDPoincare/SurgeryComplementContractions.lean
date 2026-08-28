import Wikipedia.SmoothSixDPoincare.SurgeryComplementHomeomorph
import Wikipedia.SmoothSixDPoincare.ImageComplementNullhomotopy

/-!
# Circle contractions in actual surgery belt-sphere complements

First remove the old smooth attaching sphere by the proved high-codimension
argument, then transfer its contractions through the constructed full
complement homeomorphism. `MorseSurgeryContractions` supplies the actual native
presentation and smooth attaching map. Old-boundary contractions remain the
topological premise of this intermediate transfer result.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

variable {F R X Y G H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X]

section General

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [FiniteDimensional ℝ N]

/-- A smooth attaching sphere of codimension at least three gives contractions
in the whole new belt-sphere complement. -/
theorem beltComplement_circle_nullhomotopies_of_sphere_dimension (n : ℕ)
    [Fact (Module.finrank ℝ N = n + 1)]
    (d : SurgeryBoundaryPair N F R X Y)
    (hattach : ContMDiff (𝓡 n) J ∞ d.attachingSphere)
    (hdim : 2 + n < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, X),
      ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, d.NewComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  have hold : ∀ f : C(Hemisphere.Sphere 1, d.OldComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
    apply ImageComplement.circle_nullhomotopies d.attachingSphere hattach _ hnull
    simpa only [finrank_euclideanSpace_fin] using hdim
  intro f
  let e := d.complementHomeomorph
  let forward : C(d.OldComplement, d.NewComplement) := ⟨e, e.continuous⟩
  let backward : C(d.NewComplement, d.OldComplement) := ⟨e.symm, e.symm.continuous⟩
  let f₀ : C(Hemisphere.Sphere 1, d.OldComplement) := backward.comp f
  obtain ⟨c, hc⟩ := hold f₀
  have heq : forward.comp f₀ = f := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (f x)
  have hout : (forward.comp f₀).Homotopic
      (ContinuousMap.const _ (e c)) := (Homotopic.refl forward).comp hc
  exact ⟨e c, heq ▸ hout⟩

/-- The index-two case, for any two-dimensional inner-product negative coordinate space. -/
theorem beltComplement_circle_nullhomotopies_of_finrank_two
    [Fact (Module.finrank ℝ N = 1 + 1)]
    (d : SurgeryBoundaryPair N F R X Y)
    (hattach : ContMDiff (𝓡 1) J ∞ d.attachingSphere)
    (hdim : 3 < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, X),
      ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, d.NewComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) :=
  d.beltComplement_circle_nullhomotopies_of_sphere_dimension 1 hattach hdim hnull

end General

/-- The standard two-dimensional-coordinate specialization. -/
theorem beltComplement_circle_nullhomotopies
    (d : SurgeryBoundaryPair (EuclideanSpace ℝ (Fin 2)) F R X Y)
    (hattach : ContMDiff (𝓡 1) J ∞ d.attachingSphere)
    (hdim : 3 < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, X),
      ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, d.NewComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact d.beltComplement_circle_nullhomotopies_of_finrank_two hattach hdim hnull

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
