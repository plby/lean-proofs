/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Adding an independent random variable preserves a uniform small-ball bound.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.FiniteSigns

namespace Erdos521

open MeasureTheory ProbabilityTheory

theorem smallBall_add_of_independent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y μ)
    {δ B : ℝ} (hB : 0 ≤ B)
    (hsmall : ∀ z : ℝ, μ.real {ω | |X ω - z| ≤ δ} ≤ B) (z : ℝ) :
    μ.real {ω | |X ω + Y ω - z| ≤ δ} ≤ B := by
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  let E := {p : ℝ × ℝ | |p.1 + p.2 - z| ≤ δ}
  have hE : MeasurableSet E := by dsimp [E]; measurability
  have hmap := hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have heq := congrArg (fun ν : Measure (ℝ × ℝ) ↦ ν E) hmap
  rw [Measure.map_apply (hX.prodMk hY) hE] at heq
  change μ {ω | |X ω + Y ω - z| ≤ δ} = ((μ.map X).prod (μ.map Y)) E at heq
  have hbound : μ {ω | |X ω + Y ω - z| ≤ δ} ≤ ENNReal.ofReal B := by
    rw [heq, Measure.prod_apply_symm hE]
    calc
      (∫⁻ y, (μ.map X) ((fun x ↦ (x, y)) ⁻¹' E) ∂μ.map Y) ≤
          ∫⁻ _y, ENNReal.ofReal B ∂μ.map Y := by
        apply lintegral_mono
        intro y
        dsimp only
        have hsection : MeasurableSet ((fun x : ℝ ↦ (x, y)) ⁻¹' E) := hE.preimage (by fun_prop)
        rw [Measure.map_apply hX hsection]
        change μ {ω | |X ω + y - z| ≤ δ} ≤ ENNReal.ofReal B
        have hset : {ω | |X ω + y - z| ≤ δ} = {ω | |X ω - (z - y)| ≤ δ} := by
          ext ω
          change (|X ω + y - z| ≤ δ) ↔ (|X ω - (z - y)| ≤ δ)
          rw [show X ω + y - z = X ω - (z - y) by ring]
        rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal (hsmall (z - y))
      _ = _ := by simp
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [measureReal_def, ENNReal.toReal_ofReal hB] using hreal

end Erdos521
