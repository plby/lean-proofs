import Wikipedia.HopfProblem.DegreeCollapseNativeSingleBeltCrossing
import Wikipedia.SmoothSixDPoincare.BeltTransverseChart

/-!
# A full native chart recognizing the actual index-three belt

The negative coordinates split as a height and a two-plane, and a centered
chart parametrizes the original positive sphere. The original Morse belt
neighborhood then gives a native five-dimensional chart. Its zero normal
plane is exactly the entire belt inside that chart, not just a subset.
The chart may be restricted to any prescribed open belt neighborhood.
-/

noncomputable section

open Set Function Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

theorem exists_middle_belt_chart (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by have h := (S.data q).chart.finrank_negative_add_positive
          have hi := (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
          omega⟩
    ∀ U : Set (S.data q).UpperLevel, IsOpen U → (S.data q).surgery.beltSphere v ∈ U →
      ∃ Φ : PartialDiffeomorph
          𝓘(ℝ, (ℝ × EuclideanSpace ℝ (Fin 2)) × EuclideanSpace ℝ (Fin 2))
          𝓘(ℝ, RegularLevel.Model E)
          ((ℝ × EuclideanSpace ℝ (Fin 2)) × EuclideanSpace ℝ (Fin 2)) (S.data q).UpperLevel ∞,
        (0 : (ℝ × EuclideanSpace ℝ (Fin 2)) × EuclideanSpace ℝ (Fin 2)) ∈ Φ.source ∧
        Φ 0 = (S.data q).surgery.beltSphere v ∧ Φ.target ⊆ U ∧
        (∀ z ∈ Φ.source, Φ z ∈ range (S.data q).surgery.beltSphere ↔ z.1 = 0) ∧
        ∃ χ : PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2))
            (sphere (0 : (S.data q).chart.PositiveCoordinates) 1) ∞,
          (0 : EuclideanSpace ℝ (Fin 2)) ∈ χ.source ∧ χ 0 = v ∧
          ∀ y : EuclideanSpace ℝ (Fin 2),
            Φ (beltCrossingBelt y) = (S.data q).surgery.beltSphere (χ y) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  have hneg : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 3 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
  have hsplit := (S.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) := ⟨by omega⟩
  change ∀ U : Set (S.data q).UpperLevel, IsOpen U → (S.data q).surgery.beltSphere v ∈ U → _
  intro U hU hvU
  let D := EuclideanSpace ℝ (Fin 2)
  let d := S.data q
  let χ := NativeParametrization.centered (D := D) v
  have hχ0 : (0 : D) ∈ χ.source := NativeParametrization.zero_mem_centered_source v
  have hχv : χ 0 = v := NativeParametrization.centered_zero v
  let L : (ℝ × D) ≃L[ℝ] d.chart.NegativeCoordinates :=
    ContinuousLinearEquiv.ofFinrankEq (by simp only [D, Module.finrank_prod,
      Module.finrank_self, finrank_euclideanSpace_fin]; exact hneg.symm)
  let P := L.prodCongr (ContinuousLinearEquiv.refl ℝ D)
  let C := d.beltLocalCoordinates hf 2 χ
  let Ψ := P.toDiffeomorph.toPartialDiffeomorph.trans C
  have hΨ0 : (0 : (ℝ × D) × D) ∈ Ψ.source := by
    refine ⟨mem_univ _, ?_⟩
    change P 0 ∈ C.source
    rw [map_zero, d.beltLocalCoordinates_source hf 2 χ]
    exact ⟨hχ0, d.belt_zero_mem_surgerySource (χ 0)⟩
  have haxis (y : D) : Ψ (beltCrossingBelt y) = d.surgery.beltSphere (χ y) := by
    change C (L 0, y) = _
    rw [map_zero, d.beltLocalCoordinates_apply hf 2 χ (0, y)
      (d.belt_zero_mem_surgerySource (χ y))]
    exact d.beltSurgeryHomeomorph_zero (χ y)
  have hcenter : Ψ 0 = d.surgery.beltSphere v := (haxis 0).trans (congrArg d.surgery.beltSphere hχv)
  have hrecognition (z : (ℝ × D) × D) (hz : z ∈ Ψ.source) :
      Ψ z ∈ range d.surgery.beltSphere ↔ z.1 = 0 := by
    constructor
    · rintro ⟨w, hw⟩
      have hc : d.beltNormal (Ψ z) = d.radius • L z.1 :=
        d.beltLocalCoordinates_normal hf 2 χ (P z) hz.2
      rw [← hw, d.beltNormal_belt] at hc
      have hLzero : L z.1 = 0 := (smul_eq_zero.mp hc.symm).resolve_left d.radius_pos.ne'
      exact L.injective (hLzero.trans L.map_zero.symm)
    · intro hz0
      have he : z = beltCrossingBelt z.2 := Prod.ext hz0 rfl
      rw [he, haxis]
      exact mem_range_self _
  let Φ := PartialChart.restrictTarget Ψ hU
  have hΦ0 : (0 : (ℝ × D) × D) ∈ Φ.source := ⟨hΨ0, by
    change Ψ 0 ∈ U
    rw [hcenter]
    exact hvU⟩
  refine ⟨Φ, hΦ0, hcenter, ?_, ?_, χ, hχ0, hχv, haxis⟩
  · exact inter_subset_right
  · intro z hz
    exact hrecognition z hz.1

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
