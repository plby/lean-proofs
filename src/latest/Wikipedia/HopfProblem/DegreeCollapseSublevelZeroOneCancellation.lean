import Wikipedia.HopfProblem.DegreeCollapseSublevelFlowPointDescent
import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchUniqueness
import Wikipedia.HopfProblem.DegreeCollapseZeroOneUniqueOrbitCancellation

/-!
# Actual zero/one cancellation below a fixed upper cut

The realized minimum branches give the unique connecting orbit. Bounded
value descent retains that same flow; cancellation takes place in a band
strictly below the cut. The whole original upper germ and the literal
strict sublevel are fixed. All surviving native indices are retained.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f₀ : M → ℝ}

theorem cancel_realized_higher_minimum_below_cut
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : IsMorse E f₀)
    (hinj₀ : InjOn f₀ (criticalPoints E f₀)) (A : SurgeryWindows E f₀)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V)
    (hzero : ∀ x ∈ criticalPoints E f₀, V x = 0)
    (hdesc₀ : ∀ x, x ∉ criticalPoints E f₀ → mvfderiv 𝓘(ℝ, E) f₀ x (V x) < 0)
    (hmodels₀ : ∀ x ∈ criticalPoints E f₀, ∃ c : SignedMorseChart (E := E) f₀ x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : criticalPoints E f₀)
    (hpzero : nativeMorseIndex E f₀ p = 0) (hqone : nativeMorseIndex E f₀ q = 1)
    (hrp : f₀ r < f₀ p) (hp : f₀ p < A.lower q) {a : ℝ} (hqa : f₀ q < a)
    (u v : sphere (0 : (A.data q).chart.NegativeCoordinates) 1)
    (hback : ∀ x : (A.data q).LowerLevel,
      Tendsto (fun t => G t x) atBot (𝓝 q.val) ↔ x ∈ range (A.data q).surgery.attachingSphere)
    (hu : Tendsto (fun t => G t ((A.data q).surgery.attachingSphere u).val) atTop (𝓝 p.val))
    (hv : Tendsto (fun t => G t ((A.data q).surgery.attachingSphere v).val) atTop (𝓝 r.val))
    (hnoconnection : ∀ j : criticalPoints E f₀, j ≠ q → j ≠ p → j ≠ r → ∀ x,
      ¬(Tendsto (fun t => G t x) atBot (𝓝 q.val) ∧
        Tendsto (fun t => G t x) atTop (𝓝 j.val))) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      InjOn g (criticalPoints E g) ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f₀).ncard ∧
      (∀ x, x ∈ criticalPoints E g ↔ x ∈ criticalPoints E f₀ ∧ x ≠ p.val ∧ x ≠ q.val) ∧
      (∀ x ∈ criticalPoints E g, nativeMorseIndex E g x = nativeMorseIndex E f₀ x) ∧
      (∀ x, a ≤ f₀ x → g =ᶠ[𝓝 x] f₀) ∧ ∀ x, g x < a ↔ f₀ x < a := by
  have hpr : p ≠ r := fun h => (ne_of_lt hrp) (congrArg (fun x => f₀ x.val) h).symm
  obtain ⟨hzback, hunique⟩ := unique_connection_of_distinct_minimum_branches A
    hf₀.continuous G p r q hqone hpr hp u v hback hu hv
  obtain ⟨f, hf, hm, hcrit, hinj, _, _, hfpq, hfqa, hconsecutive, hdesc,
      hmodels, hindices, hkeep, hcut⟩ :=
    exists_flow_preserving_consecutive_pair_below_cut hf₀ hm₀ hinj₀ hV G hG hzero
      hdesc₀ hmodels₀ p r q hrp (hp.trans (A.lower_lt_value q)) hqa hnoconnection
  let pf : criticalPoints E f := ⟨p.val, hcrit.symm ▸ p.property⟩
  let qf : criticalPoints E f := ⟨q.val, hcrit.symm ▸ q.property⟩
  have hconsecutivef : ∀ z : criticalPoints E f, ¬(f pf < f z ∧ f z < f qf) := by
    intro z hz
    exact hconsecutive ⟨z.val, hcrit ▸ z.property⟩ hz
  obtain ⟨T₀⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  obtain ⟨T, _, _, _, hupper⟩ := T₀.exists_same_flow_windows_below_cut hf hm a
  obtain ⟨cp, hcp⟩ := hmodels pf pf.property
  obtain ⟨cq, hcq⟩ := hmodels qf qf.property
  have hpair := surgery_pair_band_isolation T.toSurgeryWindows pf qf hconsecutivef
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior⟩ := cancel_unique_zero_one_connection cp cq
    hf hm ((hindices p p.property).trans hpzero) ((hindices q q.property).trans hqone)
      hV G hG (fun x hx => hzero x (hcrit ▸ hx)) hdesc hinj pf.property qf.property hfpq
      (T.toSurgeryWindows.lower_lt_value pf) (T.toSurgeryWindows.value_lt_upper qf)
      hpair hu hzback hunique hcp hcq
  have hreg (x : M)
      (hx : f x ∈ Icc (T.toSurgeryWindows.lower pf) (T.toSurgeryWindows.upper qf)) :
      x ∉ criticalPoints E g := by
    intro h
    obtain ⟨hxc, hxp, hxq⟩ := (hcritg x).mp h
    exact (hpair x hxc hx).elim hxp hxq
  have hsurv (x : M) (hx : x ∈ criticalPoints E g) : g =ᶠ[𝓝 x] f :=
    hexterior x (fun h => hreg x ⟨h.1.le, h.2.le⟩ hx)
  have hinjg : InjOn g (criticalPoints E g) := by
    intro x hx y hy hxy
    apply hinj ((hcritg x).mp hx).1 ((hcritg y).mp hy).1
    exact (hsurv x hx).self_of_nhds.symm.trans (hxy.trans (hsurv y hy).self_of_nhds)
  refine ⟨g, hg, hmg, hinjg, hcount.trans (congrArg Set.ncard hcrit), ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [hcrit] using hcritg x
  · intro x hx
    exact (nativeMorseIndex_congr_germ (hsurv x hx)).trans
      (hindices x (hcrit ▸ ((hcritg x).mp hx).1))
  · intro x hx
    apply Filter.EventuallyEq.trans (hexterior x ?_) (hkeep x hx)
    intro hband
    have hxa : a ≤ f x := by rw [(hkeep x hx).self_of_nhds]; exact hx
    exact (not_lt_of_ge hxa) (hband.2.trans (hupper qf hfqa))
  · intro x
    apply Iff.trans _ (hcut x)
    by_cases hx : f x ∈ Ioo (T.toSurgeryWindows.lower pf) (T.toSurgeryWindows.upper qf)
    · have hgx := RegularBandReplacement.mem_open_band hf hg
        (fun y hy => (hexterior y hy).self_of_nhds) hreg hx
      exact iff_of_true (hgx.2.trans (hupper qf hfqa)) (hx.2.trans (hupper qf hfqa))
    · rw [(hexterior x hx).self_of_nhds]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
