import Wikipedia.NoExoticSixSphere.CorankOneCoordinatesGeneric
import Wikipedia.NoExoticSixSphere.CorankOneIsolated

/-!
# Generic isolation on the entire corank-one stratum

Use the constructed countable coordinate cover and simultaneous parameter
regularity. Each point has an open leading-block neighborhood on which the
actual residual inverse function theorem isolates it. Lower-rank points
are not excluded by this theorem.
-/

noncomputable section

open Set Function Module
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.CorankOneCoordinates

open CorankOne

variable {X V W E F : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem not_injective_of_corank_one (L : V →L[ℝ] W)
    (hr : finrank ℝ L.range = finrank ℝ E) (hv : finrank ℝ V = finrank ℝ E + 1) :
    ¬ Injective L := by
  intro h
  have hi := LinearMap.finrank_range_of_inj (f := L.toLinearMap) h
  omega

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem isDiscrete_of_regular_cover (D : X → V →L[ℝ] W) (hD : ContDiff ℝ ∞ D)
    (hv : finrank ℝ V = finrank ℝ E + 1) (hd : finrank ℝ X = finrank ℝ F)
    (C : Set (Coordinates V W E F))
    (hcov : ∀ L : V →L[ℝ] W, finrank ℝ L.range = finrank ℝ E →
      ∃ c ∈ C, L ∈ domain c)
    (hreg : ∀ c ∈ C, ∀ x, D x ∈ domain c → residual (operatorEquiv c (D x)) = 0 →
      Surjective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y))) x)) :
    IsDiscrete {x | finrank ℝ (D x).range = finrank ℝ E} := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨c, hc, hxc⟩ := hcov (D x) hx
  let Q := operatorEquiv c
  have hQ : ContDiff ℝ ∞ (fun y ↦ Q (D y)) := Q.contDiff.comp hD
  have hlocal : IsDiscrete (chartSingularSet (fun y ↦ Q (D y))) :=
    chartSingularSet_isDiscrete _ hQ hd (hreg c hc)
  have hxs : x ∈ chartSingularSet (fun y ↦ Q (D y)) :=
    ⟨hxc, (injective_operatorEquiv_iff c (D x)).not.mpr
      (not_injective_of_corank_one (D x) hx hv)⟩
  obtain ⟨U, hU, hUx⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hlocal x hxs
  have hNx : x ∈ U := by
    have h : x ∈ U ∩ chartSingularSet (fun y ↦ Q (D y)) := by
      rw [hUx]
      exact mem_singleton x
    exact h.1
  refine ⟨U ∩ D ⁻¹' (domain c : Set (V →L[ℝ] W)),
    hU.inter ((domain c).isOpen.preimage hD.continuous), ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hyU, hyc⟩, hyr⟩
    have hys : y ∈ chartSingularSet (fun z ↦ Q (D z)) :=
      ⟨hyc, (injective_operatorEquiv_iff c (D y)).not.mpr
        (not_injective_of_corank_one (D y) hyr hv)⟩
    have h : y ∈ U ∩ chartSingularSet (fun z ↦ Q (D z)) := ⟨hyU, hys⟩
    rwa [hUx] at h
  · intro hy
    rcases mem_singleton_iff.mp hy with rfl
    exact ⟨⟨hNx, hxc⟩, hx⟩

theorem ae_corank_one_isDiscrete [MeasurableSpace (V →L[ℝ] W)]
    [BorelSpace (V →L[ℝ] W)] (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (D : X → V →L[ℝ] W) (hD : ContDiff ℝ ∞ D)
    (hv : finrank ℝ V = finrank ℝ E + 1)
    (hw : finrank ℝ W = finrank ℝ E + finrank ℝ F)
    (hd : finrank ℝ X = finrank ℝ F) :
    ∀ᵐ A ∂μ, IsDiscrete {x | finrank ℝ (D x + A).range = finrank ℝ E} := by
  obtain ⟨C, hC, hcov⟩ := exists_countable_cover hv hw
  apply (ae_regular_countable_coordinates μ C hC D hD).mono
  intro A hA
  exact isDiscrete_of_regular_cover (fun x ↦ D x + A) (hD.add contDiff_const) hv hd C hcov hA

end NoExoticSixSphere.CorankOneCoordinates
