import Wikipedia.NoExoticSixSphere.SardRankReduction
import Wikipedia.NoExoticSixSphere.SardFubini
import Wikipedia.NoExoticSixSphere.SardFlatInduction
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Nonzero-rank critical values under dimension induction

The local coordinate reduction, Fubini, invariance of Haar-null sets under
linear coordinates, and second countability give the nonzero-derivative
part of Sard from the explicitly stated lower-dimensional hypothesis.
-/

open scoped ContDiff Topology
open Set Filter Module MeasureTheory MeasureTheory.Measure

namespace NoExoticSixSphere.Sard

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem measure_image_nonzero_critical_of_lowerDimension
    (μ : Measure F) [IsAddHaarMeasure μ]
    (hSard : ∀ (g : EuclideanSpace ℝ (Fin (finrank ℝ E - 1)) →
        EuclideanSpace ℝ (Fin (finrank ℝ F - 1)))
      (V : Set (EuclideanSpace ℝ (Fin (finrank ℝ E - 1)))),
      IsOpen V → ContDiffOn ℝ ∞ g V →
        volume (g '' {z | z ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g z)}) = 0)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    μ (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x) ∧
      fderiv ℝ f x ≠ 0}) = 0 := by
  let s := {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x) ∧ fderiv ℝ f x ≠ 0}
  apply measure_image_eq_zero_of_local μ f s
  intro x hx
  obtain ⟨W, hW, hxW, _, e, V, g, hV, hg, hfirst, himage⟩ :=
    exists_nonzeroRankReduction hU hf hx.1 hx.2.2
  have hnull := measure_criticalValues_of_preserves_fst
    (volume : Measure ℝ) volume hSard hV hg hfirst
  have hAC : μ.map e ≪ (volume : Measure ℝ).prod
      (volume : Measure (EuclideanSpace ℝ (Fin (finrank ℝ F - 1)))) :=
    absolutelyContinuous_isAddHaarMeasure _ _
  have hpre := preimage_null_of_map_null e.continuous.measurable.aemeasurable (hAC hnull)
  refine ⟨s ∩ W, inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hxW)), ?_⟩
  apply measure_mono_null _ hpre
  rintro _ ⟨y, hy, rfl⟩
  exact himage ⟨f y, ⟨y, ⟨hy.2, hy.1.2.1⟩, rfl⟩, rfl⟩

end NoExoticSixSphere.Sard
