import Wikipedia.HopfProblem.DegreeCollapseHigherFamilyPassage

/-!
# Lower forward and backward basins survive a supported holonomy change

The new field agrees with the normalized original field below the support.
Every orbit with a lower backward endpoint stays below that endpoint's
height for all real times. Native uniqueness therefore identifies its
whole new curve with the normalized old curve, in both directions.
Starting below the support also keeps the whole positive half-orbit below
it, so every forward endpoint is preserved independently of backward limits.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem lower_backward_basins_preserved
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) W)
    (hgeometry : ∀ x, range (fun t => H t x) = range (fun t => S.flow t x) ∧
      (∀ p, Tendsto (fun t => H t x) atTop (𝓝 p) ↔
        Tendsto (fun t => S.flow t x) atTop (𝓝 p)) ∧
      ∀ p, Tendsto (fun t => H t x) atBot (𝓝 p) ↔
        Tendsto (fun t => S.flow t x) atBot (𝓝 p))
    {l : ℝ} (hout : ∀ y, f y ≤ l → T.field y = W y)
    (p : M) (hp : f p ≤ l) :
    (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 p) ↔
      Tendsto (fun t => S.flow t x) atBot (𝓝 p)) ∧
    ∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 p) →
      range (fun t => T.flow t x) = range (fun t => S.flow t x) := by
  have hnew (x : M) (hx : Tendsto (fun t => T.flow t x) atBot (𝓝 p)) :
      ∀ t, T.flow t x = H t x := by
    have hheight := hf.continuous.continuousAt.tendsto.comp hx
    have hmono := FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent x
    have hagree (t : ℝ) : T.field (T.flow t x) = W (T.flow t x) :=
      hout _ ((hmono.ge_of_tendsto hheight t).trans hp)
    intro t
    rcases le_total 0 t with ht | ht
    · exact FlowCancellation.native_flow_eq_on_positive_halfline (hW.of_le (by simp))
        H T.flow hH T.integral (fun s _ => hagree s) t ht
    · exact FlowCancellation.native_flow_eq_on_negative_halfline (hW.of_le (by simp))
        H T.flow hH T.integral (fun s _ => hagree s) t ht
  have hold (x : M) (hx : Tendsto (fun t => S.flow t x) atBot (𝓝 p)) :
      ∀ t, H t x = T.flow t x := by
    have hheight := hf.continuous.continuousAt.tendsto.comp hx
    have hmono := FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    have hbound (t : ℝ) : f (H t x) ≤ l := by
      have hm : H t x ∈ range (fun s => S.flow s x) :=
        (hgeometry x).1 ▸ mem_range_self t
      obtain ⟨s, hs⟩ := hm
      rw [← hs]
      exact (hmono.ge_of_tendsto hheight s).trans hp
    have hagree (t : ℝ) : W (H t x) = T.field (H t x) := (hout _ (hbound t)).symm
    intro t
    rcases le_total 0 t with ht | ht
    · exact FlowCancellation.native_flow_eq_on_positive_halfline (T.smooth.of_le (by simp))
        T.flow H T.integral hH (fun s _ => hagree s) t ht
    · exact FlowCancellation.native_flow_eq_on_negative_halfline (T.smooth.of_le (by simp))
        T.flow H T.integral hH (fun s _ => hagree s) t ht
  refine ⟨?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have heq : (fun t => T.flow t x) = fun t => H t x := funext (hnew x hx)
      rw [heq] at hx
      exact ((hgeometry x).2.2 p).mp hx
    · intro hx
      have heq : (fun t => H t x) = fun t => T.flow t x := funext (hold x hx)
      have hh := ((hgeometry x).2.2 p).mpr hx
      rwa [heq] at hh
  · intro x hx
    have heq : (fun t => H t x) = fun t => T.flow t x := funext (hold x hx)
    rw [← heq]
    exact (hgeometry x).1

theorem lower_forward_basins_preserved
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) W)
    (hgeometry : ∀ x p, Tendsto (fun t => H t x) atTop (𝓝 p) ↔
      Tendsto (fun t => S.flow t x) atTop (𝓝 p))
    {l : ℝ} (hout : ∀ y, f y ≤ l → T.field y = W y)
    (y : M) (hy : f y ≤ l) :
    ∀ p, Tendsto (fun t => T.flow t y) atTop (𝓝 p) ↔
      Tendsto (fun t => S.flow t y) atTop (𝓝 p) := by
  have hmono := FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent y
  have hbound (t : ℝ) (ht : 0 ≤ t) : f (T.flow t y) ≤ l := by
    have hh := hmono ht
    change f (T.flow t y) ≤ f (T.flow 0 y) at hh
    rw [T.flow.map_zero_apply] at hh
    exact hh.trans hy
  have heq : (fun t => T.flow t y) =ᶠ[atTop] (fun t => H t y) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact FlowCancellation.native_flow_eq_on_positive_halfline (hW.of_le (by simp))
      H T.flow hH T.integral (fun s hs => hout _ (hbound s hs)) t ht
  intro p
  exact (tendsto_congr' heq).trans (hgeometry y p)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
