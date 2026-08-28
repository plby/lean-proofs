import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenPositiveBirth
import Wikipedia.HopfProblem.DegreeCollapseBirthCutIndexControl
import Wikipedia.HopfProblem.DegreeCollapsePositiveBeltPointCrossing
import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchRealization

/-!
# Construct the supported positive two/three birth above the retained cut

A short reverse-time segment from an actual regular-level point supplies
the birth location and its positive regular band. The resulting excellent
presentation belongs to the SAME state. Its literal original cut is equal
to the new cut, the new index-two point is first above it, every old critical
germ is retained, and the entire nonpositive germ remains unchanged.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_positive_two_three_birth_above_cut
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (z : {y : S.Space // P.function y = a}) :
    ∃ (Q : S.ExcellentMorsePresentation) (p r : S.Space),
      nativeMorseIndex (Vector 7) Q.function p = 2 ∧
      nativeMorseIndex (Vector 7) Q.function r = 3 ∧
      a < Q.function p ∧ Q.function p < Q.function r ∧
      (criticalPoints (Vector 7) Q.function).ncard =
        (criticalPoints (Vector 7) P.function).ncard + 2 ∧
      (∀ y, y ∈ criticalPoints (Vector 7) Q.function ↔
        y ∈ criticalPoints (Vector 7) P.function ∨ y = p ∨ y = r) ∧
      (∀ y ∈ criticalPoints (Vector 7) P.function, Q.function =ᶠ[𝓝 y] P.function) ∧
      (∀ y, S.time y ≤ 0 → Q.function =ᶠ[𝓝 y] P.function) ∧
      (∀ y, Q.function y = a ↔ P.function y = a) ∧
      (∀ y, Q.function y = a → y ∉ criticalPoints (Vector 7) Q.function) ∧
      (∀ s : criticalPoints (Vector 7) Q.function,
        Q.function s < Q.function p → Q.function s < a) ∧
      nativeMorseCount (Vector 7) Q.function 2 = nativeMorseCount (Vector 7) P.function 2 + 1 ∧
      nativeMorseCount (Vector 7) Q.function 3 = nativeMorseCount (Vector 7) P.function 3 + 1 ∧
      ∀ j, j ≠ 2 → j ≠ 3 →
        nativeMorseCount (Vector 7) Q.function j = nativeMorseCount (Vector 7) P.function j := by
  obtain ⟨l₀, u, hl₀, hau, hband⟩ := A.regular_interval_around_level hreg
  have hc : Continuous (fun s : ℝ => P.function (A.flow s z.val)) :=
    P.function.continuous.comp (A.flow.continuous continuous_id continuous_const)
  have h0 : (fun s : ℝ => P.function (A.flow s z.val)) 0 ∈ Iio u := by
    simpa only [Flow.map_zero_apply, z.property, mem_Iio] using hau
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
    (hc.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds h0))
  let x := A.flow (-ε / 2) z.val
  have hxu : P.function x < u := hεball (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith)
  have hax : a < P.function x := by
    have hh := FlowConstruction.strictAnti_flow_height P.smooth (A.smooth.of_le (by simp))
      A.flow A.integral A.zero A.descent (hreg z.val z.property) (show -ε / 2 < 0 by linarith)
    simpa only [Flow.map_zero_apply, z.property] using hh
  let l := (a + P.function x) / 2
  have hal : a < l := by dsimp [l]; linarith
  have hlx : l < P.function x := by dsimp [l]; linarith
  have hclosed : ∀ y, P.function y ∈ Icc l u → y ∉ criticalPoints (Vector 7) P.function := by
    intro y hy
    exact hband y ⟨(hl₀.trans hal).le.trans hy.1, hy.2⟩
  obtain ⟨Q, p, r, _, _, hip, hir, hpr, hpval, hrval, hcount, hcrit, hexterior,
      hkeep, hnegative, hcount₂, hcount₃, hother⟩ :=
    P.exists_positive_indexed_birth (ha.trans hal).le hclosed ⟨hlx, hxu⟩ (k := 2) (by decide)
  have hcrit' (y : S.Space) (hy : y ∈ criticalPoints (Vector 7) Q.function) :
      y ∈ criticalPoints (Vector 7) P.function ∨ y = p ∨ y = r := (hcrit y).mp hy
  have hap : a < Q.function p := hal.trans hpval.1
  have har : a < Q.function r := hal.trans hrval.1
  obtain ⟨heq, _⟩ := birth_preserves_lower_levels P.function.continuous Q.smooth
    (show (P.function ⁻¹' Ioo l u) ⊆ {y : S.Space | l < P.function y} from fun _ hy => hy.1)
    hexterior hkeep hcrit' hpval.1.le hrval.1.le hal
  have hgr := regular_level_of_retained_critical_germs hreg hcrit' hkeep hap har
  have hgap := birth_first_new_value_gap hcrit' hkeep hreg
    (fun y hy => hband y ⟨hl₀.le.trans hy.1.le, hy.2.le⟩) hpval.2 hpr
  exact ⟨Q, p, r, hip, hir, hap, hpr, hcount, hcrit, hkeep, hnegative,
    heq, hgr, hgap, hcount₂, hcount₃, hother⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
