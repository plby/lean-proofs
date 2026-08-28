import Wikipedia.HopfProblem.DegreeCollapseThreeSheetNormalSigns
import Wikipedia.SmoothSixDPoincare.MorseBeltNormalRegularity

/-!
# The fixed native three-belt normal map determines Whitney corner signs

The original negative Morse coordinates supply the globally fixed normal
detector. Its vanishing and surjective derivative along the entire belt are
proved from the actual Morse window. No orientation-consistency assumption
is added to the retained native strip data.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M} (D : MorseSurgeryData E f p)

def nativeThreeBeltSheetNormal
    (j : (ℝ × EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] D.chart.NegativeCoordinates) :
    D.UpperLevel → (ℝ × EuclideanSpace ℝ (Fin 2)) := j.symm ∘ D.beltNormal

theorem opposite_three_belt_corners_iff_normal_determinants
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (j : (ℝ × EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] D.chart.NegativeCoordinates)
    {S : Set D.UpperLevel} {a b : ℝ → D.UpperLevel}
    {k l : (ℝ × ℝ) → D.UpperLevel} {h : ℝ} :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∀ (tube : TubularBigon (E := RegularLevel.Model E)
        S (range D.surgery.beltSphere) a b k l h)
      (d : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
        (E := RegularLevel.Model E) S k)
      (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
        (E := RegularLevel.Model E) (range D.surgery.beltSphere) l),
      (tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) ↔
        (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 2) =>
          nativeThreeBeltSheetNormal D j (d.chart (w, 0))) (0, 0)).det *
        (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 2) =>
          nativeThreeBeltSheetNormal D j (d.chart (w, 0))) (1, 0)).det < 0 := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  intro tube d e
  have hq : ContMDiffOn 𝓘(ℝ, RegularLevel.Model E)
      𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) ∞ (nativeThreeBeltSheetNormal D j) D.beltNormalDomain :=
    j.symm.contDiff.contMDiff.comp_contMDiffOn (D.contMDiffOn_beltNormal hf)
  have hcenter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      e.chart (StripCoordinates.center t) ∈ range D.surgery.beltSphere :=
    (e.sheet _ (e.line ht)).mpr rfl
  have hcenterO (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      e.chart (StripCoordinates.center t) ∈ D.beltNormalDomain := by
    obtain ⟨v, hv⟩ := hcenter t ht
    exact hv ▸ D.belt_mem_normalDomain v
  apply opposite_three_sheet_corners_iff_normal_determinants tube d e
    (nativeThreeBeltSheetNormal D j) D.isOpen_beltNormalDomain hq
  · rintro y ⟨⟨v, rfl⟩, _⟩
    change j.symm (D.beltNormal (D.surgery.beltSphere v)) = 0
    rw [D.beltNormal_belt, map_zero]
  · exact hcenterO
  · intro t ht
    obtain ⟨v, hv⟩ := hcenter t ht
    rw [← hv]
    have hnormal := (D.contMDiffOn_beltNormal hf).contMDiffAt
      (D.isOpen_beltNormalDomain.mem_nhds (D.belt_mem_normalDomain v))
    have hJ : mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates)
        𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) j.symm
        (D.beltNormal (D.surgery.beltSphere v)) = j.symm.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact j.symm.toContinuousLinearMap.fderiv
    have hjSmooth : ContMDiff 𝓘(ℝ, D.chart.NegativeCoordinates)
        𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) ∞ j.symm := j.symm.contDiff.contMDiff
    rw [nativeThreeBeltSheetNormal, mfderiv_comp _ (hjSmooth.mdifferentiableAt (by simp))
      (hnormal.mdifferentiableAt (by simp)), hJ]
    exact j.symm.surjective.comp (D.surjective_beltNormal_derivative hf v)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
