import Wikipedia.HopfProblem.DegreeCollapseRegularCutSurgeryWindows
import Wikipedia.HopfProblem.DegreeCollapseRegularSublevelBody
import Wikipedia.HopfProblem.DegreeCollapseMorseFiniteCells
import Wikipedia.SmoothSixDPoincare.NativeFullSmoothStandardCaps
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyClosed
import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainRebase

/-!
# A full native smooth-boundary handle chain for an actual regular sublevel

Take the original finite native surgery prefix ending at the greatest
critical value below the cut. Rebase its empty lower end and transport
its upper end through the actual remaining regular band. Births, interior
handles, and caps all retain their genuine native attachment data. No
handle cancellation or smooth disk recognition is asserted here.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularMorseSublevel

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_upperSublevelChain (S : SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hs : S.HasSmoothExteriors hf)
    (j : Fin S.count) :
    ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
      (SmoothBoundaryBody.empty 𝓘(ℝ, RegularLevel.Model E))
      ((S.data (S.point j)).upperSmoothBody hf) (j.val + 1), c.HasStandardCaps := by
  have hcount : 0 < S.count := (Nat.zero_le j.val).trans_lt j.isLt
  let i : Fin S.count := ⟨0, hcount⟩
  have h : i.val + j.val < S.count := by simpa only [i, Nat.zero_add] using j.isLt
  obtain ⟨c, hc, _, _⟩ := S.exists_fullSmoothInterval_standardCaps hf hs i j.val h
  have hend : S.intervalEnd i j.val h = j := Fin.ext (Nat.zero_add _)
  have hchain : ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E)
      (Module.finrank ℝ E) ((S.data (S.first hcount)).lowerSmoothBody hf)
      ((S.data (S.point (S.intervalEnd i j.val h))).upperSmoothBody hf) (j.val + 1),
      c.HasStandardCaps := ⟨c, hc⟩
  rw [hend] at hchain
  obtain ⟨c', hc'⟩ := hchain
  let _ := S.first_lowerSmoothBody_isEmpty hf hcount
  let e := SmoothBoundaryBody.toEmptyEquiv ((S.data (S.first hcount)).lowerSmoothBody hf)
  exact ⟨c'.rebase e, c'.hasStandardCaps_rebase e hc'⟩

theorem exists_fullSmoothHandleChain
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) (a : ℝ)
    (ha : ∀ p, f p = a → p ∉ criticalPoints E f) :
    ∃ (k : ℕ) (c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E)
      (Module.finrank ℝ E) (SmoothBoundaryBody.empty 𝓘(ℝ, RegularLevel.Model E))
      (body hf a ha) k), c.HasStandardCaps := by
  by_cases hbelow : (criticalPoints E f ∩ {x : M | f x ≤ a}).Nonempty
  · have hcompact : IsCompact (criticalPoints E f ∩ {x : M | f x ≤ a}) :=
      (criticalPoints_isClosed hf).isCompact.inter_right
        (isClosed_le hf.continuous continuous_const)
    obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn hbelow hf.continuous.continuousOn
    obtain ⟨S, hs, hupper, _⟩ := exists_smooth_windows_respecting_cut hf hm hinj a
      (fun x hx he ↦ ha x he hx)
    let q : criticalPoints E f := ⟨p, hp.1⟩
    let j := S.point.symm q
    have hj : S.point j = q := S.point.apply_symm_apply q
    have hpa : f p < a := lt_of_le_of_ne hp.2 (fun he ↦ ha p he hp.1)
    have hqa : S.upper q < a := hupper q hpa
    obtain ⟨c, hc⟩ := exists_upperSublevelChain S hf hs j
    have hchain : ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E)
        (Module.finrank ℝ E) (SmoothBoundaryBody.empty 𝓘(ℝ, RegularLevel.Model E))
        ((S.data q).upperSmoothBody hf) (j.val + 1), c.HasStandardCaps := by
      rw [← hj]
      exact ⟨c, hc⟩
    obtain ⟨c', hc'⟩ := hchain
    obtain ⟨e⟩ := nonempty_regularBandBodyEquiv hf (S.data q).upper_regular ha hqa.le (by
      intro x hx hcrit
      have hxp : f x ≤ f p := hmax ⟨hcrit, hx.2⟩
      have hpos := sq_pos_of_pos (S.data q).radius_pos
      change f p + (S.data q).radius ^ 2 ≤ f x ∧ f x ≤ a at hx
      linarith [hx.1])
    exact ⟨j.val + 1, c'.retarget e, c'.hasStandardCaps_retarget e hc'⟩
  · let _ : IsEmpty (body hf a ha).body :=
      MorseCells.isEmpty_sublevel_of_no_critical hf
        (fun p hp hpa ↦ hbelow ⟨p, hp, hpa⟩)
    exact ⟨0, .nil (SmoothBoundaryBody.toEmptyEquiv (body hf a ha)).symm, True.intro⟩

end Wikipedia.HopfProblem.DegreeCollapse.RegularMorseSublevel
