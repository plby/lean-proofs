import Wikipedia.HopfProblem.DegreeCollapsePositiveOneHandleSelection
import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchRealization
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenNegativeConnectivity

/-!
# A selected positive merging handle has a positive minimum branch

The original nonpositive Morse sublevel is the literal negative half
through the exact sign comparison, hence path connected. Two distinct
old attaching components cannot both flow into that connected sublevel.
The actual dense-basin placement and native flow realization therefore
give two distinct minimum endpoints with at least one positive endpoint.
No endpoint, branch flow, or component-merging handle is supplied.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open MorseCancellation

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem negative_sublevel_pathConnected (eBoundary : B ≃ₜ Sphere 6) :
    PathConnectedSpace {x : S.Space // P.function x ≤ 0} := by
  let : SimplyConnectedSpace S.NegativeHalf := S.negativeHalf_simplyConnected_of_sphere eBoundary
  have hsets : {x : S.Space | P.function x ≤ 0} = {x : S.Space | S.time x ≤ 0} := by
    ext x
    constructor
    · intro hx
      exact le_of_not_gt (fun h => (not_lt_of_ge hx) ((P.positive_iff x).mpr h))
    · intro hx
      exact le_of_not_gt (fun h => (not_lt_of_ge hx) ((P.positive_iff x).mp h))
  let e : {x : S.Space // P.function x ≤ 0} ≃ₜ S.NegativeHalf := Homeomorph.setCongr hsets
  exact pathConnectedSpace_of_homotopyEquiv e.toHomotopyEquiv

theorem exists_positive_minimum_branches (eBoundary : B ≃ₜ Sphere 6)
    (p₀ : criticalPoints (Vector 7) P.function) (hp₀ : 0 < P.function p₀)
    (hzero₀ : nativeMorseIndex (Vector 7) P.function p₀ = 0) :
    ∃ (A : AdaptedSurgeryWindows (Vector 7) P.function)
      (q : criticalPoints (Vector 7) P.function),
      0 < A.toSurgeryWindows.lower q ∧ nativeMorseIndex (Vector 7) P.function q = 1 ∧
      ∃ (u v : sphere (0 : (A.data q).chart.NegativeCoordinates) 1)
        (V : (x : S.Space) → TangentSpace (𝓡 7) x) (G : Flow ℝ S.Space)
        (p r : criticalPoints (Vector 7) P.function),
        ¬Joined ((A.data q).coreBoundaryMap u) ((A.data q).coreBoundaryMap v) ∧
        ContMDiff (𝓡 7) (𝓡 7).tangent ∞
          (fun x => (⟨x, V x⟩ : TangentBundle (𝓡 7) S.Space)) ∧
        (∀ x, IsMIntegralCurve (fun t => G t x) V) ∧
        (∀ x ∈ criticalPoints (Vector 7) P.function, V x = 0) ∧
        (∀ x, x ∉ criticalPoints (Vector 7) P.function →
          mvfderiv (𝓡 7) P.function x (V x) < 0) ∧
        (∀ x ∈ criticalPoints (Vector 7) P.function, ∀ᶠ y in 𝓝 x, V y = A.field y) ∧
        nativeMorseIndex (Vector 7) P.function p = 0 ∧
        nativeMorseIndex (Vector 7) P.function r = 0 ∧ p ≠ r ∧
        (0 < P.function p ∨ 0 < P.function r) ∧
        P.function p < A.toSurgeryWindows.lower q ∧
        P.function r < A.toSurgeryWindows.lower q ∧
        (∀ x : (A.data q).LowerLevel,
          Tendsto (fun t => G t x) atBot (𝓝 q.val) ↔
            x ∈ range (A.data q).surgery.attachingSphere) ∧
        Tendsto (fun t => G t ((A.data q).surgery.attachingSphere u).val) atTop (𝓝 p.val) ∧
        Tendsto (fun t => G t ((A.data q).surgery.attachingSphere v).val) atTop (𝓝 r.val) ∧
        ∀ j : criticalPoints (Vector 7) P.function, j ≠ q → j ≠ p → j ≠ r → ∀ x,
          ¬(Tendsto (fun t => G t x) atBot (𝓝 q.val) ∧
            Tendsto (fun t => G t x) atTop (𝓝 j.val)) := by
  let : Nonempty B := Nonempty.map eBoundary.symm inferInstance
  obtain ⟨A, hcut, q, hq, hqone, u, v, hnot⟩ :=
    P.exists_positive_merging_one_handle p₀ hp₀ hzero₀
  obtain ⟨V, G, p, r, hV, hG, hzero, hdesc, hgerms, hpzero, hrzero, hpr,
    hpq, hrq, hback, hu, hv, _, hnoconnection⟩ :=
    A.realize_one_handle_minimum_branches P.smooth q hqone u v hnot
  let : LocallyPathConnectedSpace S.Space :=
    ChartedSpace.locallyPathConnectedSpace (Vector 7) S.Space
  let : PathConnectedSpace {x : S.Space // P.function x ≤ 0} :=
    P.negative_sublevel_pathConnected eBoundary
  have hpositive : 0 < P.function p ∨ 0 < P.function r :=
    one_forward_limit_above_connected_cut G P.smooth.continuous
      (FlowConstruction.antitone_flow_height P.smooth G hG hzero hdesc) (hcut q hq).le
      ((A.data q).coreBoundaryMap u) ((A.data q).coreBoundaryMap v) hnot hpq hrq hu hv
  exact ⟨A, q, hcut q hq, hqone, u, v, V, G, p, r, hnot, hV, hG, hzero, hdesc, hgerms,
    hpzero, hrzero, hpr, hpositive, hpq, hrq, hback, hu, hv, hnoconnection⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
