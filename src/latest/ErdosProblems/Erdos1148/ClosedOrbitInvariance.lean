import ErdosProblems.Erdos1148.ClosedOrbitMeasure

/-! # Flow invariance of closed-orbit length measure -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

def modularRightTranslate (h : SL(2, ℝ)) : ModularOrbitSpace → ModularOrbitSpace :=
  Quotient.map (fun g => g * h) (by
    intro g₁ g₂ hrel
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨γ, ?_⟩
    change (γ : SL(2, ℝ)) * (g₂ * h) = g₁ * h
    change (γ : SL(2, ℝ)) * g₂ = g₁ at hγ
    rw [← mul_assoc, hγ])

lemma modularRightTranslate_mk (h g : SL(2, ℝ)) :
    modularRightTranslate h (modularMk g) = modularMk (g * h) := rfl

lemma continuous_modularRightTranslate (h : SL(2, ℝ)) : Continuous (modularRightTranslate h) :=
  continuous_coinduced_dom.mpr (continuous_modularMk.comp (continuous_id.mul continuous_const))

lemma closedOrbitCurve_translate {g : SL(2, ℝ)} {T : ℝ} (hT : T ∈ flowPeriodGroup g)
    (s : ℝ) (x : AddCircle T) :
    modularRightTranslate (diagonalFlow s) (closedOrbitCurve hT x) =
      closedOrbitCurve hT (x + (s : AddCircle T)) := by
  induction x using Quotient.inductionOn' with | h a =>
    change modularMk ((g * diagonalFlow a) * diagonalFlow s) =
      modularMk (g * diagonalFlow (a + s))
    rw [diagonalFlow_add, mul_assoc]

theorem closedOrbitMeasure_flow_invariant {g : SL(2, ℝ)} {T : ℝ} [Fact (0 < T)]
    (hT : T ∈ flowPeriodGroup g) (s : ℝ) :
    Measure.map (modularRightTranslate (diagonalFlow s)) (closedOrbitMeasure hT) =
      closedOrbitMeasure hT := by
  have hc := (continuous_closedOrbitCurve hT).measurable
  have hr := (continuous_modularRightTranslate (diagonalFlow s)).measurable
  have ha : Measurable (fun x : AddCircle T => x + (s : AddCircle T)) :=
    (continuous_id.add continuous_const).measurable
  have heq : modularRightTranslate (diagonalFlow s) ∘ closedOrbitCurve hT =
      closedOrbitCurve hT ∘ (fun x : AddCircle T => x + (s : AddCircle T)) := by
    funext x
    exact closedOrbitCurve_translate hT s x
  rw [closedOrbitMeasure, Measure.map_map hr hc, heq, ← Measure.map_map hc ha,
    map_add_right_eq_self]

end Erdos1148.DukeArithmetic
