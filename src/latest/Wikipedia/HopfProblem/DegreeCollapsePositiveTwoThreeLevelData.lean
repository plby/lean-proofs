import Wikipedia.HopfProblem.DegreeCollapseFirstMeridianUpperTransport
import Wikipedia.HopfProblem.DegreeCollapsePositiveFiberSpherePlacement
import Wikipedia.HopfProblem.DegreeCollapseCirclePlacementTransverseSheets
import Wikipedia.HopfProblem.DegreeCollapseCirclePlacementCount

/-!
# Actual positive two/three cancellation data on the retained native cut

The new presentation supplies its constructed embedded meridian and
transverse forward-basin germ. The original presentation constructs the
two-sphere isotopy on the retained native fiber. The actual whole backward
basin of the new three-handle is thereby placed on that meridian, giving
one transverse connection and no other positive forward endpoint.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris

variable {B : Type} [TopologicalSpace B] [SimplyConnectedSpace B]
  [Subsingleton (SingularHomology B 2)] {S : CollaredSevenState B}
  (P Q : S.ExcellentMorsePresentation)

theorem exists_positive_two_three_transverse_level_data
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
    [Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1)]
    (hfirst : ∀ p : criticalPoints (Vector 7) Q.function, 0 < Q.function p →
      Q.function q ≤ Q.function p)
    (hqlower : 0 ≤ T.toSurgeryWindows.lower q)
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < Q.function r)
    (hgap : ∀ p : criticalPoints (Vector 7) Q.function, Q.function p < Q.function r →
      Q.function p < a)
    (hnewlow : ∀ p : criticalPoints (Vector 7) Q.function, 0 < Q.function p → Q.function p ≤ a →
      nativeMorseIndex (Vector 7) Q.function p ≤ 3) :
    let _ := RegularLevel.chartedSpace Q.smooth hgr
    ∃ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model (Vector 7)) 𝓘(ℝ, RegularLevel.Model (Vector 7))
        {y : S.Space // Q.function y = a} {y : S.Space // Q.function y = a} ∞,
      IsotopicToIdentity D ∧
      {x : {y : S.Space // Q.function y = a} |
        Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) ∧
        Tendsto (fun t => T.flow t (D x).val) atTop (𝓝 q.val)}.ncard = 1 ∧
      ∃ (α : C(Hemisphere.Sphere 2, {y : S.Space // Q.function y = a}))
        (z₀ : Hemisphere.Sphere 2)
        (β : sphere (0 : (T.data q).chart.PositiveCoordinates) 1 →
          {y : S.Space // Q.function y = a})
        (v : sphere (0 : (T.data q).chart.PositiveCoordinates) 1),
        ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ α ∧
        MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model (Vector 7)) β v ∧ β v = α z₀ ∧
        NativeTransversality.At (𝓡 2) (𝓡 4) 𝓘(ℝ, RegularLevel.Model (Vector 7)) α β z₀ v ∧
        (∀ z, Tendsto (fun t => T.flow t (α z).val) atBot (𝓝 r.val)) ∧
        (∀ᶠ w in 𝓝 v, Tendsto (fun t => T.flow t (D (β w)).val) atTop (𝓝 q.val)) ∧
        ∀ x : {y : S.Space // Q.function y = a},
          Tendsto (fun t => T.flow t x.val) atBot (𝓝 r.val) →
          ∀ j : criticalPoints (Vector 7) Q.function, 0 < Q.function j →
            Tendsto (fun t => T.flow t (D x).val) atTop (𝓝 j.val) → j = q := by
  let _ := RegularLevel.chartedSpace Q.smooth hgr
  let _ := RegularLevel.isManifold Q.smooth hgr
  let _ : Fact (Module.finrank ℝ (T.data r).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (T.data r).chart).symm.trans hr⟩
  obtain ⟨δ, hδ, hδi, hδd, v, β₀, hβ₀, hcross₀, htrans₀, hβbasin, hsingle, _, hendpoints⟩ :=
    Q.exists_transverse_first_meridian_at_higher_cut T q hq hfirst hqlower hqa hgr hnewlow
  obtain ⟨α, D, hα, _, _, hrange, hD, hplace, hplacement⟩ :=
    P.exists_attaching_two_sphere_placement_of_positive_fiber A ha hfr hhigh hlow Q.smooth
      T hgr heq r har hgap δ hδ hδi.injective hδd
  obtain ⟨β, hβ, hcross, htrans, hDβ⟩ := exists_transverse_sheet_of_circle_placement D
    (hα.mdifferentiableAt (by simp)) hβ₀ hplace hcross₀ htrans₀
  refine ⟨D, hD, unit_level_count_of_circle_placement T.flow D.toEquiv δ
    BeltMeridianSphere.pole hplacement hsingle,
      α, BeltMeridianSphere.pole, β, v, hα, hβ, hcross, htrans, ?_, ?_, ?_⟩
  · intro z
    exact (hrange (α z)).mp ⟨z, rfl⟩
  · filter_upwards [hβbasin] with w hw
    rw [hDβ w]
    exact hw
  · intro x hx j hj hlim
    obtain ⟨z, hz⟩ := (hplacement x).mp hx
    rw [← hz] at hlim
    exact hendpoints z j hj.le hlim

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
