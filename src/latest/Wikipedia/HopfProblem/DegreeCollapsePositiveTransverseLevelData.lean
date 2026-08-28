import Wikipedia.HopfProblem.DegreeCollapsePositiveAttachingCirclePlacement
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenFirstPositiveHandle
import Wikipedia.HopfProblem.DegreeCollapseHandleTradeTransverseLevelData

/-!
# Construct the actual positive one/two cancellation data at the original cut

The original presentation supplies disk isotopy at the retained level;
the new presentation supplies its actual complete-flow attaching and belt
basins. The first positive one-handle's branches cross the original zero
boundary. Its constructed relative belt loop and the newborn attaching
circle give one whole-basin intersection and native transverse sheets.
Every other positive endpoint is excluded at the same original level.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

variable {B : Type} [TopologicalSpace B] [PathConnectedSpace B] {S : CollaredSevenState B}
  (P Q : S.ExcellentMorsePresentation)

theorem exists_positive_handle_trade_transverse_level_data
    (A : AdaptedSurgeryWindows (Vector 7) P.function)
    (T : AdaptedSurgeryWindows (Vector 7) Q.function) {a : ℝ} (ha : 0 < a)
    (hfr : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hgr : ∀ y, Q.function y = a → y ∉ criticalPoints (Vector 7) Q.function)
    (heq : ∀ y, Q.function y = a ↔ P.function y = a)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      3 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 4)
    (q r : criticalPoints (Vector 7) Q.function)
    (hq : nativeMorseIndex (Vector 7) Q.function q = 1)
    (hr : nativeMorseIndex (Vector 7) Q.function r = 2)
    [Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 5 + 1)]
    (hqpositive : 0 < Q.function q)
    (hfirst : ∀ p : criticalPoints (Vector 7) Q.function, 0 < Q.function p →
      Q.function q ≤ Q.function p)
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < Q.function r)
    (hgap : ∀ p : criticalPoints (Vector 7) Q.function, Q.function p < Q.function r →
      Q.function p < a)
    (hnewlow : ∀ p : criticalPoints (Vector 7) Q.function, 0 < Q.function p → Q.function p ≤ a →
      nativeMorseIndex (Vector 7) Q.function p ≤ 2) :
    let _ := RegularLevel.chartedSpace Q.smooth hgr
    ∃ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model (Vector 7)) 𝓘(ℝ, RegularLevel.Model (Vector 7))
        {y : S.Space // Q.function y = a} {y : S.Space // Q.function y = a} ∞,
      IsotopicToIdentity D ∧
      {x : {y : S.Space // Q.function y = a} |
        Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) ∧
        Tendsto (fun t => T.flow t (D x).val) atTop (𝓝 q.val)}.ncard = 1 ∧
      ∃ (α : C(Hemisphere.Sphere 1, {y : S.Space // Q.function y = a}))
        (z₀ : Hemisphere.Sphere 1)
        (β : sphere (0 : (T.data q).chart.PositiveCoordinates) 1 →
          {y : S.Space // Q.function y = a})
        (v : sphere (0 : (T.data q).chart.PositiveCoordinates) 1),
        ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ α ∧
        MDifferentiableAt (𝓡 5) 𝓘(ℝ, RegularLevel.Model (Vector 7)) β v ∧ β v = α z₀ ∧
        NativeTransversality.At (𝓡 1) (𝓡 5) 𝓘(ℝ, RegularLevel.Model (Vector 7)) α β z₀ v ∧
        (∀ z, Tendsto (fun t => T.flow t (α z).val) atBot (𝓝 r.val)) ∧
        (∀ᶠ w in 𝓝 v, Tendsto (fun t => T.flow t (D (β w)).val) atTop (𝓝 q.val)) ∧
        ∀ x : {y : S.Space // Q.function y = a},
          Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) →
          ∀ s : criticalPoints (Vector 7) Q.function, 0 < Q.function s →
            Tendsto (fun t => T.flow t (D x).val) atTop (𝓝 s.val) → s = q := by
  let _ := RegularLevel.chartedSpace Q.smooth hgr
  let _ := RegularLevel.isManifold Q.smooth hgr
  let _ : Fact (Module.finrank ℝ (T.data r).chart.NegativeCoordinates = 1 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (T.data r).chart).symm.trans hr⟩
  have hzero : ∀ y, Q.function y = 0 → y ∉ criticalPoints (Vector 7) Q.function :=
    RegularTimeMorse.regular_zero_not_critical Q.regular
  let : PathConnectedSpace {y : S.Space // Q.function y = 0} := Q.zeroLevel_pathConnected
  have hneg : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  let : Nontrivial (T.data q).chart.NegativeCoordinates :=
    Module.nontrivial_of_finrank_pos (by rw [hneg]; decide)
  obtain ⟨u, hu⟩ : (sphere (0 : (T.data q).chart.NegativeCoordinates) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hbranches (w : sphere (0 : (T.data q).chart.NegativeCoordinates) 1) :
      ((T.data q).surgery.attachingSphere w).val ∈
        FlowCancellation.levelBasin T.flow Q.function 0 :=
    T.first_above_cut_attaching_branches_cross Q.smooth hzero q hqpositive hfirst w
  obtain ⟨δ, hδ, hδi, hδd, z₀, v, β₀, hβ₀, hcross₀, htrans₀, hβbasin, hsingle, hendpoints⟩ :=
    T.exists_transverse_belt_loop_between_cuts Q.smooth q hq 5 hqpositive hzero ⟨u, hu⟩ hbranches
      hqa hgr hnewlow (by decide) (by simp) (by simp)
  obtain ⟨α, hα, _, _, hrange, D, hD, hplace, hplacement⟩ :=
    P.exists_positive_attaching_circle_placement Q A T ha hfr hgr heq hhigh hlow
      r har hgap δ hδ hδi hδd
  obtain ⟨β, hβ, hcross, htrans, hDβ⟩ := exists_transverse_sheet_of_circle_placement D
    (hα.mdifferentiableAt (by simp)) hβ₀ hplace hcross₀ htrans₀
  refine ⟨D, hD, unit_level_count_of_circle_placement T.flow D.toEquiv δ z₀ hplacement hsingle,
    α, z₀, β, v, hα, hβ, hcross, htrans, ?_, ?_, ?_⟩
  · intro z
    exact (hrange (α z)).mp ⟨z, rfl⟩
  · filter_upwards [hβbasin] with w hw
    rw [hDβ w]
    exact hw
  · intro x hx s hs hlim
    obtain ⟨z, hz⟩ := (hplacement x).mp hx
    rw [← hz] at hlim
    rcases hendpoints z with hbelow | hqend
    · have hbad : (δ z).val ∈ (FlowCancellation.levelBasin T.flow Q.function 0)ᶜ := by
        rw [levelBasin_compl_eq_endpoint_obstruction T Q.smooth hzero]
        exact Or.inl ⟨s, hs.le, hlim⟩
      exact (hbad hbelow).elim
    · exact Subtype.ext (tendsto_nhds_unique hlim hqend)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
