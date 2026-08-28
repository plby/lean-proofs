import Wikipedia.HopfProblem.DegreeCollapsePositiveFiberCirclePlacement
import Wikipedia.HopfProblem.DegreeCollapseSublevelFirstOneHandle
import Wikipedia.HopfProblem.DegreeCollapseTransverseBeltLoopDimension
import Wikipedia.HopfProblem.DegreeCollapseCirclePlacementTransverseSheets
import Wikipedia.HopfProblem.DegreeCollapseCirclePlacementCount

/-!
# Construct the dual trade's actual transverse level data

The first below-cut one-handle has its original branches in the unique
minimum basin there. The n=5 belt construction gives an actual transverse
loop. The ORIGINAL positive fiber supplies the circle isotopy placing
the newborn attaching circle on it, retaining the whole basin singleton
and both actual critical endpoints. No orbit or sheet is supplied.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_dual_trade_transverse_level_data
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ} (ha : 0 < a)
    (hfr : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hhigh : ∀ p : criticalPoints (Vector 7) P.function, a ≤ P.function p →
      3 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ a →
      nativeMorseIndex (Vector 7) P.function p ≤ 4)
    {g : S.Space → ℝ} (hg : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ g)
    (T : AdaptedSurgeryWindows (Vector 7) g) {b c : ℝ}
    (hgr : ∀ y, g y = b → y ∉ criticalPoints (Vector 7) g)
    (heq : ∀ y, g y = b ↔ P.function y = a)
    (m q r : criticalPoints (Vector 7) g)
    (hm : nativeMorseIndex (Vector 7) g m = 0)
    (hq : nativeMorseIndex (Vector 7) g q = 1)
    (hr : nativeMorseIndex (Vector 7) g r = 2)
    [Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 5 + 1)]
    (hqc : g q < c)
    (hbefore : ∀ p : criticalPoints (Vector 7) g, g p < g q → nativeMorseIndex (Vector 7) g p = 0)
    (hminimum : ∀ p : criticalPoints (Vector 7) g, g p < c →
      nativeMorseIndex (Vector 7) g p = 0 → p = m)
    (hqb : T.toSurgeryWindows.upper q ≤ b) (hbr : b < g r)
    (hgap : ∀ p : criticalPoints (Vector 7) g, g p < g r → g p < b)
    (hnewlow : ∀ p : criticalPoints (Vector 7) g, g p ≤ b → nativeMorseIndex (Vector 7) g p ≤ 2) :
    let _ := RegularLevel.chartedSpace hg hgr
    ∃ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model (Vector 7)) 𝓘(ℝ, RegularLevel.Model (Vector 7))
        {y : S.Space // g y = b} {y : S.Space // g y = b} ∞,
      g m < g q ∧ IsotopicToIdentity D ∧
      {x : {y : S.Space // g y = b} |
        Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) ∧
        Tendsto (fun t => T.flow t (D x).val) atTop (𝓝 q.val)}.ncard = 1 ∧
      ∃ (α : C(Hemisphere.Sphere 1, {y : S.Space // g y = b})) (z₀ : Hemisphere.Sphere 1)
        (β : sphere (0 : (T.data q).chart.PositiveCoordinates) 1 → {y : S.Space // g y = b})
        (v : sphere (0 : (T.data q).chart.PositiveCoordinates) 1),
        ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ α ∧
        MDifferentiableAt (𝓡 5) 𝓘(ℝ, RegularLevel.Model (Vector 7)) β v ∧ β v = α z₀ ∧
        NativeTransversality.At (𝓡 1) (𝓡 5) 𝓘(ℝ, RegularLevel.Model (Vector 7)) α β z₀ v ∧
        (∀ z, Tendsto (fun t => T.flow t (α z).val) atBot (𝓝 r.val)) ∧
        (∀ᶠ w in 𝓝 v, Tendsto (fun t => T.flow t (D (β w)).val) atTop (𝓝 q.val)) ∧
        ∀ x : {y : S.Space // g y = b}, Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) →
          Tendsto (fun t => T.flow t (D x).val) atTop (𝓝 m.val) ∨
          Tendsto (fun t => T.flow t (D x).val) atTop (𝓝 q.val) := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold hg hgr
  let _ : Fact (Module.finrank ℝ (T.data r).chart.NegativeCoordinates = 1 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (T.data r).chart).symm.trans hr⟩
  have hneg : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  let : Nontrivial (T.data q).chart.NegativeCoordinates :=
    Module.nontrivial_of_finrank_pos (by rw [hneg]; decide)
  obtain ⟨u, hu⟩ : (sphere (0 : (T.data q).chart.NegativeCoordinates) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hbranches (w : sphere (0 : (T.data q).chart.NegativeCoordinates) 1) :
      Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val) atTop (𝓝 m.val) :=
    T.first_one_branches_to_unique_minimum_below_cut hg m q hqc hbefore hminimum w
  have hmq : g m < g q := (T.forward_limit_below_regular_level hg
    (T.data q).lower_regular ((T.data q).surgery.attachingSphere ⟨u, hu⟩)
      (hbranches ⟨u, hu⟩)).trans (T.toSurgeryWindows.lower_lt_value q)
  obtain ⟨δ, hδ, hδi, hδd, z₀, v, β₀, hβ₀, hcross₀, htrans₀, hβbasin, hsingle, hendpoints⟩ :=
    T.exists_transverse_middle_belt_loop_in_dimension hg m q hm hq 5 ⟨u, hu⟩ hbranches
      hqb hgr hnewlow (by decide) (by simp) (by simp)
  obtain ⟨α, D, hα, _, _, hrange, hD, hplace, hplacement⟩ :=
    P.exists_attaching_circle_placement_of_positive_fiber A ha hfr hhigh hlow hg T hgr heq
      r hbr hgap δ hδ hδi hδd
  obtain ⟨β, hβ, hcross, htrans, hDβ⟩ := exists_transverse_sheet_of_circle_placement D
    (hα.mdifferentiableAt (by simp)) hβ₀ hplace hcross₀ htrans₀
  refine ⟨D, hmq, hD,
    unit_level_count_of_circle_placement T.flow D.toEquiv δ z₀ hplacement hsingle,
    α, z₀, β, v, hα, hβ, hcross, htrans, ?_, ?_, ?_⟩
  · intro z
    exact (hrange (α z)).mp ⟨z, rfl⟩
  · filter_upwards [hβbasin] with w hw
    rw [hDβ w]
    exact hw
  · intro x hx
    obtain ⟨z, hz⟩ := (hplacement x).mp hx
    rw [← hz]
    exact hendpoints z

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
