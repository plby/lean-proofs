/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Convergence in measure and an almost-sure subsequence for reversed interior counts.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.ReversalLaw
import ErdosProblems.Erdos521.InteriorStrongLaw
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem tendstoInMeasure_comp_varying_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : ℕ → Ω → ℝ) (L : ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (T : ℕ → Ω → Ω)
    (hT : ∀ n, MeasurePreserving (T n) μ μ)
    (h : TendstoInMeasure μ f atTop (fun _ ↦ L)) :
    TendstoInMeasure μ (fun n ω ↦ f n (T n ω)) atTop (fun _ ↦ L) := by
  apply tendstoInMeasure_iff_measureReal_dist.mpr
  intro η hη
  have hlim := tendstoInMeasure_iff_measureReal_dist.mp h η hη
  apply hlim.congr
  intro n
  have hS : NullMeasurableSet {ω | η ≤ dist (f n ω) L} μ :=
    ((hf n).aemeasurable.dist aemeasurable_const).nullMeasurableSet_preimage measurableSet_Ici
  have heq := Measure.measure_preimage_of_map_eq_self (hT n).map_eq hS
  exact congrArg ENNReal.toReal heq.symm

theorem interiorRootCount_tendstoInMeasure :
    TendstoInMeasure sequenceLaw (fun n ε ↦ (interiorRootCount ε n : ℝ) / Real.log n)
      atTop (fun _ ↦ 1 / Real.pi) :=
  tendstoInMeasure_of_tendsto_ae
    (fun n ↦ ((interiorRootCount_integrable n).div_const _).aestronglyMeasurable)
    ae_interiorRootCount_div_log_limit

theorem reversedInteriorRootCount_tendstoInMeasure :
    TendstoInMeasure sequenceLaw (fun n ε ↦
      (interiorRootCount (reversedCoefficients n ε) n : ℝ) / Real.log n)
      atTop (fun _ ↦ 1 / Real.pi) :=
  tendstoInMeasure_comp_varying_measurePreserving sequenceLaw
    (fun n ε ↦ (interiorRootCount ε n : ℝ) / Real.log n) (1 / Real.pi)
    (fun n ↦ ((interiorRootCount_integrable n).div_const _).aestronglyMeasurable)
    reversedCoefficients measurePreserving_reversedCoefficients interiorRootCount_tendstoInMeasure

theorem exists_reversedInteriorRootCount_subsequence_limit :
    ∃ u : ℕ → ℕ, StrictMono u ∧ ∀ᵐ ε ∂sequenceLaw,
      Tendsto (fun j ↦ (interiorRootCount (reversedCoefficients (u j) ε) (u j) : ℝ) /
        Real.log (u j)) atTop (𝓝 (1 / Real.pi)) :=
  reversedInteriorRootCount_tendstoInMeasure.exists_seq_tendsto_ae

end Erdos521
