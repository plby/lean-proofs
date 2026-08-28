import Wikipedia.HopfProblem.DegreeCollapseHandleTradeLevelCount
import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchRealization
import Wikipedia.HopfProblem.DegreeCollapseWholeLevelConnectionRealization

/-!
# Realizing a constructed unit level count as one actual complete connection

A regular interval around the original level is constructed from the finite
critical values. Native holonomy realizes the actual level isotopy, retaining
all critical field germs. Exact whole-level basin transport and crossing
uniqueness then give one connecting orbit, unique up to time translation.
Transversality and the later value rearrangement are separate obligations.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.realize_unit_level_isotopy
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) {a : ℝ} (hpa : a < f p) (hqa : f q < a)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f) :
    let _ := RegularLevel.chartedSpace hf ha
    ∀ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {y : M // f y = a} {y : M // f y = a} ∞,
      IsotopicToIdentity P →
      {x : {y : M // f y = a} | Tendsto (fun t => S.flow t x.val) atBot (𝓝 p.val) ∧
        Tendsto (fun t => S.flow t (P x).val) atTop (𝓝 q.val)}.ncard = 1 →
      ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M)
        (z : {y : M // f y = a}),
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => G t x) V) ∧
        (∀ x ∈ criticalPoints E f, V x = 0) ∧
        (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
        (∀ x ∈ criticalPoints E f, ∀ᶠ y in 𝓝 x, V y = S.field y) ∧
        Tendsto (fun t => G t z.val) atBot (𝓝 p.val) ∧
        Tendsto (fun t => G t z.val) atTop (𝓝 q.val) ∧
        (∀ x, Tendsto (fun t => G t x) atBot (𝓝 p.val) →
          Tendsto (fun t => G t x) atTop (𝓝 q.val) → ∃ t, G t z.val = x) ∧
        (∀ (x : {y : M // f y = a}) y,
          Tendsto (fun t => G t x.val) atBot (𝓝 y) ↔
            Tendsto (fun t => S.flow t x.val) atBot (𝓝 y)) ∧
        ∀ (x : {y : M // f y = a}) y,
          Tendsto (fun t => G t x.val) atTop (𝓝 y) ↔
            Tendsto (fun t => S.flow t (P x).val) atTop (𝓝 y) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf ha
  change ∀ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      {y : M // f y = a} {y : M // f y = a} ∞,
    IsotopicToIdentity P →
    {x : {y : M // f y = a} | Tendsto (fun t => S.flow t x.val) atBot (𝓝 p.val) ∧
      Tendsto (fun t => S.flow t (P x).val) atTop (𝓝 q.val)}.ncard = 1 → _
  intro P hP hcount
  obtain ⟨z₀, -⟩ := Set.ncard_eq_one.mp hcount
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level ha
  obtain ⟨r, C, W, V, H, G, -, -, -, -, -, -, hgeometry,
      hV, hG, hzero, hdesc, hgerms, -, hend, -, hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband ha z₀ P hP
  obtain ⟨hback, hforward⟩ := FlowSuspension.whole_level_basins_of_holonomy
    S.flow H G Subtype.val P (fun x y => (hgeometry x).2.1 y)
      (fun x y => (hgeometry x).2.2 y) hend hleft hright
  obtain ⟨z, hzb, hzf, hunique⟩ := FlowSuspension.exists_unique_connection_of_unit_level_count
    S.flow G hf.continuous hpa hqa P (fun x => hback x p.val)
      (fun x => hforward x q.val) hcount
  exact ⟨V, G, z, hV, hG, (fun x hx => (hzero x).mpr (S.zero x hx)),
    hdesc, hgerms, hzb, hzf, hunique, hback, hforward⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
