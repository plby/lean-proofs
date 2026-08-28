import Wikipedia.HopfProblem.DegreeCollapsePositiveTwoThreeLevelData
import Wikipedia.HopfProblem.DegreeCollapsePositiveConnectionExclusion
import Wikipedia.HopfProblem.DegreeCollapsePositiveTransversePairCancellation
import Wikipedia.HopfProblem.DegreeCollapseUnitTransverseIsotopyRealization

/-!
# Actual positive two/three cancellation at the retained original cut

The original presentation constructs the needed level isotopy. The new
presentation's original attaching and belt basins supply the actual
unique transverse connection and smooth ambient basin tubes. Its only
positive forward endpoint is the chosen two-handle, so positive value
descent makes the pair consecutive without assumptions on negative
endpoints. Native cancellation deletes that pair in the SAME state and
retains the entire nonpositive germ and every surviving intrinsic index.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] [SimplyConnectedSpace B]
  [Subsingleton (SingularHomology B 2)] {S : CollaredSevenState B}
  (P Q : S.ExcellentMorsePresentation)

theorem cancel_positive_two_three_pair_at_retained_cut
    (A : AdaptedSurgeryWindows (Vector 7) P.function)
    (T : AdaptedSurgeryWindows (Vector 7) Q.function) {a : ℝ} (ha : 0 < a)
    (hfr : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hgr : ∀ y, Q.function y = a → y ∉ criticalPoints (Vector 7) Q.function)
    (heq : ∀ y, Q.function y = a ↔ P.function y = a)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      4 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 3)
    (q r : criticalPoints (Vector 7) Q.function)
    (hq : nativeMorseIndex (Vector 7) Q.function q = 2)
    (hr : nativeMorseIndex (Vector 7) Q.function r = 3)
    (hqpositive : 0 < Q.function q)
    (hfirst : ∀ p : criticalPoints (Vector 7) Q.function, 0 < Q.function p →
      Q.function q ≤ Q.function p)
    (hqlower : 0 ≤ T.toSurgeryWindows.lower q)
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < Q.function r)
    (hgap : ∀ p : criticalPoints (Vector 7) Q.function, Q.function p < Q.function r →
      Q.function p < a)
    (hnewlow : ∀ p : criticalPoints (Vector 7) Q.function, 0 < Q.function p → Q.function p ≤ a →
      nativeMorseIndex (Vector 7) Q.function p ≤ 3) :
    ∃ R : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) R.function).ncard + 2 =
        (criticalPoints (Vector 7) Q.function).ncard ∧
      (∀ w, w ∈ criticalPoints (Vector 7) R.function ↔
        w ∈ criticalPoints (Vector 7) Q.function ∧ w ≠ q.val ∧ w ≠ r.val) ∧
      (∀ w ∈ criticalPoints (Vector 7) R.function,
        nativeMorseIndex (Vector 7) R.function w = nativeMorseIndex (Vector 7) Q.function w) ∧
      ∀ w, S.time w ≤ 0 → R.function =ᶠ[𝓝 w] Q.function := by
  let _ := RegularLevel.chartedSpace Q.smooth hgr
  let _ := RegularLevel.isManifold Q.smooth hgr
  have hnegq : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 2 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  have hsplit := (T.data q).chart.finrank_negative_add_positive
  simp only [finrank_euclideanSpace_fin] at hsplit
  let _ : Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by omega⟩
  obtain ⟨D, hD, hcount, α, z₀, β, v, hα, hβ, hcross, htrans, hαbasin, hβbasin, hends⟩ :=
    P.exists_positive_two_three_transverse_level_data Q A T ha hfr hgr heq hhigh hlow
      q r hq hr hfirst hqlower hqa har hgap hnewlow
  have hqcut : Q.function q < a := (T.toSurgeryWindows.value_lt_upper q).trans_le hqa
  obtain ⟨V, G, hV, hG, hzero, hdesc, hgerms, hbackr, hforwardq, hunique, hback, hforward,
      htubes⟩ := T.realize_unit_transverse_level_isotopy Q.smooth r q har hqcut hgr D hD hcount
    α β z₀ v (hα.mdifferentiableAt (by simp)) hβ hcross htrans
    (Filter.Eventually.of_forall hαbasin) hβbasin
  have hendsG (x : {y : S.Space // Q.function y = a})
      (hx : Tendsto (fun t => G t x.val) atBot (𝓝 r.val))
      (j : criticalPoints (Vector 7) Q.function) (hj : 0 < Q.function j)
      (hjlim : Tendsto (fun t => G t x.val) atTop (𝓝 j.val)) : j = q :=
    hends x ((hback x r.val).mp hx) j hj ((hforward x j.val).mp hjlim)
  have hnoconnection := no_other_positive_connections_of_level_endpoint_control G
    Q.function.continuous Q.distinct r q har hgap
    (FlowConstruction.antitone_flow_height Q.smooth G hG hzero hdesc) hendsG
  have hmodels : ∀ x ∈ criticalPoints (Vector 7) Q.function,
      ∃ c : SignedMorseChart (E := Vector 7) Q.function x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    intro x hx
    refine ⟨(T.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, T.critical_model_germ ⟨x, hx⟩] with y hy hyt
    exact hy.trans hyt
  obtain ⟨hC, hE, hC0, hE0, hCb, hEb, htransM⟩ := htubes
  exact Q.cancel_transverse_pair_of_no_other_positive_connection hV G hG hzero hdesc hmodels
    q r hqpositive (hqcut.trans har) (by rw [hq, hr]) hnoconnection
    hforwardq hbackr hunique hC hE hC0 hE0 hCb hEb htransM

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
