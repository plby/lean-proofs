import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenOuterIndexMinimal
import Wikipedia.HopfProblem.DegreeCollapseRelativeTransverseBeltLoop
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarZero

/-!
# The first actual positive one-handle and its original lower-boundary branches

In a positively ordered presentation without births, the first positive
critical point has index one whenever an index-one point exists. Its two
original attaching directions both cross the original regular zero level:
their forward endpoints lie below the first positive critical value, so
regularity and minimality place those endpoints strictly below zero.
The actual time collar supplies connectedness of the original zero level.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.first_above_cut_attaching_branches_cross
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (q : criticalPoints E f) (hbq : b < f q)
    (hfirst : ∀ p : criticalPoints E f, b < f p → f q ≤ f p)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    ((S.data q).surgery.attachingSphere u).val ∈ FlowCancellation.levelBasin S.flow f b := by
  let x := (S.data q).surgery.attachingSphere u
  have hback := (S.attaching_basin_iff hf q x).mpr ⟨u, rfl⟩
  obtain ⟨_, _, p, hp, _, hforward, _⟩ := FlowCancellation.exists_native_descent_endpoints
    hf S.smooth S.flow S.integral S.zero S.descent S.distinct x.val
  have hpq : f p < f q := (S.forward_limit_below_regular_level hf (S.data q).lower_regular
    x hforward).trans (S.toSurgeryWindows.lower_lt_value q)
  have hnot : ¬b < f p := fun h => (not_le_of_gt hpq) (hfirst ⟨p, hp⟩ h)
  have hpb : f p < b := lt_of_le_of_ne (le_of_not_gt hnot) (fun h => hb p h hp)
  exact FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hback hforward hbq hpb

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem zeroLevel_pathConnected [PathConnectedSpace B] :
    PathConnectedSpace {y : S.Space // P.function y = 0} := by
  let e₀ : {y : S.Space // P.function y = 0} ≃ₜ {y : S.Space // S.time y = 0} :=
    Homeomorph.setCongr (Set.ext (fun y => P.zero_iff y))
  exact pathConnectedSpace_of_homotopyEquiv
    (e₀.trans S.collar.zeroHomeomorph).toHomotopyEquiv

theorem exists_first_positive_one_handle
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hnobirth : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      nativeMorseIndex (Vector 7) P.function p ≠ 0)
    (q₀ : criticalPoints (Vector 7) P.function) (hq₀ : 0 < P.function q₀)
    (hq₀one : nativeMorseIndex (Vector 7) P.function q₀ = 1) :
    ∃ q : criticalPoints (Vector 7) P.function,
      0 < P.function q ∧ nativeMorseIndex (Vector 7) P.function q = 1 ∧
      ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
        P.function q ≤ P.function p := by
  classical
  let _ := P.finite_criticalPoints.fintype
  let K := Finset.univ.filter (fun p : criticalPoints (Vector 7) P.function => 0 < P.function p)
  have hq₀K : q₀ ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₀⟩
  obtain ⟨q, hqK, hmin⟩ := K.exists_min_image
    (fun p : criticalPoints (Vector 7) P.function => P.function p) ⟨q₀, hq₀K⟩
  have hq : 0 < P.function q := (Finset.mem_filter.mp hqK).2
  have hfirst (p : criticalPoints (Vector 7) P.function) (hp : 0 < P.function p) :
      P.function q ≤ P.function p := hmin p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
  have hindex : nativeMorseIndex (Vector 7) P.function q ≤ 1 := by
    rcases (hfirst q₀ hq₀).eq_or_lt with heq | hlt
    · have he : q = q₀ := Subtype.ext (P.distinct q.property q₀.property heq)
      rw [he, hq₀one]
    · exact (horder q q₀ hq hlt).trans hq₀one.le
  have hne := hnobirth q hq
  exact ⟨q, hq, by omega, hfirst⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
