import Wikipedia.HopfProblem.DegreeCollapseBasinImageProjection
import Wikipedia.HopfProblem.DegreeCollapseBackwardObstructionAboveCut

/-!
# The higher-cut obstruction as an actual closed smooth image in the lower level

At a positive regular level below the requested cut, forward endpoints
cannot obstruct crossing that cut. Only backward critical endpoints
between the original cuts remain. Their actual smooth images project to
the native level without increasing source dimension, and their full
projected image is exactly the closed noncrossing set.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap TopologicalSpace
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] in
theorem backwardBetweenBasins_flow_iff (A : AdaptedSurgeryWindows E f)
    (c a t : ℝ) (x : M) :
    A.flow t x ∈ backwardBetweenBasins A c a ↔ x ∈ backwardBetweenBasins A c a := by
  constructor
  · rintro ⟨p, hcp, hpa, hp⟩
    exact ⟨p, hcp, hpa, (flow_time_atBot_limit_iff A.flow t x p.val).mp hp⟩
  · rintro ⟨p, hcp, hpa, hp⟩
    exact ⟨p, hcp, hpa, (flow_time_atBot_limit_iff A.flow t x p.val).mpr hp⟩

theorem AdaptedSurgeryWindows.between_backward_iff_not_crossing_above
    (A : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {c b a : ℝ} (hcb : c < b) (hba : b ≤ a)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (x : {y : M // f y = b}) :
    x.val ∈ backwardBetweenBasins A c a ↔
      x.val ∉ FlowCancellation.levelBasin A.flow f a := by
  change x.val ∈ backwardBetweenBasins A c a ↔
    x.val ∈ (FlowCancellation.levelBasin A.flow f a)ᶜ
  rw [levelBasin_compl_eq_endpoint_obstruction A hf ha]
  constructor
  · rintro ⟨p, _, hpa, hp⟩
    exact Or.inr ⟨p, hpa, hp⟩
  · rintro (⟨p, hap, hp⟩ | ⟨p, hpa, hp⟩)
    · have hpb := A.forward_limit_below_regular_level hf hb x hp
      exact ((hpb.trans_le hba).not_ge hap).elim
    · have hbp : b ≤ f p := by
        have hmono := FlowConstruction.antitone_flow_height hf A.flow A.integral
          A.zero A.descent x.val
        simpa only [A.flow.map_zero_apply, x.property] using
          hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hp) 0
      exact ⟨p, hcb.trans_le hbp, hpa, hp⟩

theorem AdaptedSurgeryWindows.exists_native_higher_cut_obstacle
    (A : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {c b a : ℝ} (hcb : c < b) (hba : b ≤ a)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (z₀ : {y : M // f y = b}) {d : ℕ}
    (hlow : ∀ p : criticalPoints E f, c < f p → f p ≤ a → nativeMorseIndex E f p ≤ d) :
    let _ := A.finite.fintype
    let K := BetweenBackwardBasinIndex A c a
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) K := ChartedSpace.ofDiscreteTopology
    let _ := RegularLevel.chartedSpace hf hb
    ∃ U : Opens (K × EuclideanSpace ℝ (Fin d)), ∃ g : C(U, {y : M // f y = b}),
      ContMDiff ((𝓡 0).prod (𝓡 d)) 𝓘(ℝ, RegularLevel.Model E) ∞ g ∧
      range g = {x | x.val ∉ FlowCancellation.levelBasin A.flow f a} ∧
      IsClosed (range g) := by
  let _ := A.finite.fintype
  let K := BetweenBackwardBasinIndex A c a
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold (𝓡 0) ∞ K := IsManifold.of_discreteTopology ∞
  let _ := RegularLevel.chartedSpace hf hb
  dsimp only
  obtain ⟨g₀, hg₀, hcover⟩ := A.exists_between_backward_obstruction_images hf c a hlow
  have hG : ContMDiff ((𝓡 0).prod (𝓡 d)) 𝓘(ℝ, E) ∞
      (fun z : K × EuclideanSpace ℝ (Fin d) => g₀ z.1 z.2) :=
    contMDiff_discrete_family g₀ hg₀
  let G : C(K × EuclideanSpace ℝ (Fin d), M) := ⟨_, hG.continuous⟩
  have hrange : range G = backwardBetweenBasins A c a := by
    rw [hcover]
    exact range_discrete_family g₀
  obtain ⟨U, g, hg, hrangeg⟩ := A.exists_native_level_image_of_invariant hf hb z₀
    (backwardBetweenBasins A c a) G hG hrange (backwardBetweenBasins_flow_iff A c a)
  have heq : range g = {x | x.val ∉ FlowCancellation.levelBasin A.flow f a} := by
    rw [hrangeg]
    ext x
    exact A.between_backward_iff_not_crossing_above hf hcb hba hb ha x
  refine ⟨U, g, hg, heq, ?_⟩
  rw [heq]
  have hB := (FlowCancellation.smooth_signed_level_time hf A.smooth A.flow A.integral
    (fun y hy => A.descent y (ha y hy))).1
  exact hB.isClosed_compl.preimage continuous_subtype_val

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
