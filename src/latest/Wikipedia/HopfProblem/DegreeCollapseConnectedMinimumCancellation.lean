import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchUniqueness
import Wikipedia.HopfProblem.DegreeCollapseFlowPreservingPointDescent
import Wikipedia.HopfProblem.DegreeCollapseZeroOneUniqueOrbitCancellation
import Wikipedia.HopfProblem.DegreeCollapseConnectedOneHandleSelection

/-!
# Actual critical-count reduction when there is more than one minimum

Connectedness selects a component-merging one-handle. A supported native
isotopy and its realized flow place its two branches in distinct minimum
basins. The higher minimum is made consecutive with the one-handle while
retaining this same flow. Its unique complete connecting orbit then gives
exact cancellation. The resulting function is excellent and has two fewer
critical points. No index ordering, Morse--Smale hypothesis, or supplied
geometric intersection count is required.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f₀ : M → ℝ}

theorem cancel_realized_higher_minimum
    (S : SurgeryWindows E f₀)
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : IsMorse E f₀)
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
    (hrp : f₀ r < f₀ p) (hp : f₀ p < S.lower q)
    (u v : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hback : ∀ x : (S.data q).LowerLevel,
      Tendsto (fun t => G t x) atBot (𝓝 q.val) ↔
        x ∈ range (S.data q).surgery.attachingSphere)
    (hu : Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val)
      atTop (𝓝 p.val))
    (hv : Tendsto (fun t => G t ((S.data q).surgery.attachingSphere v).val)
      atTop (𝓝 r.val))
    (hnoconnection : ∀ j : criticalPoints E f₀, j ≠ q → j ≠ p → j ≠ r → ∀ x,
      ¬(Tendsto (fun t => G t x) atBot (𝓝 q.val) ∧
        Tendsto (fun t => G t x) atTop (𝓝 j.val))) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      InjOn g (criticalPoints E g) ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f₀).ncard := by
  have hpr : p ≠ r := fun h => (ne_of_lt hrp) (congrArg (fun x => f₀ x.val) h).symm
  obtain ⟨hzback, hunique⟩ := unique_connection_of_distinct_minimum_branches
    S hf₀.continuous G p r q hqone hpr hp u v hback hu hv
  obtain ⟨f, hf, hm, hcrit, hinj, -, -, hpq, hconsecutive, hdesc, hmodels, hindices⟩ :=
    exists_flow_preserving_consecutive_pair hf₀ hm₀ S.distinct hV G hG hzero hdesc₀
      hmodels₀ p r q hrp (hp.trans (S.lower_lt_value q)) hnoconnection
  let pf : criticalPoints E f := ⟨p.val, by rw [hcrit]; exact p.property⟩
  let qf : criticalPoints E f := ⟨q.val, by rw [hcrit]; exact q.property⟩
  have hconsecutivef : ∀ z : criticalPoints E f, ¬(f pf < f z ∧ f z < f qf) := by
    intro z hz
    exact hconsecutive ⟨z.val, by rw [← hcrit]; exact z.property⟩ hz
  obtain ⟨T⟩ := nonempty_surgeryWindows hf hm hinj
  obtain ⟨cp, hcp⟩ := hmodels pf pf.property
  obtain ⟨cq, hcq⟩ := hmodels qf qf.property
  obtain ⟨g, hg, hmg, hcard, hcritg, hexterior⟩ := cancel_unique_zero_one_connection
    cp cq hf hm ((hindices p p.property).trans hpzero)
    ((hindices q q.property).trans hqone) hV G hG
    (fun x hx => hzero x (hcrit ▸ hx)) hdesc hinj pf.property qf.property hpq
    (T.lower_lt_value pf) (T.value_lt_upper qf)
    (surgery_pair_band_isolation T pf qf hconsecutivef) hu hzback hunique hcp hcq
  have hkeep := surviving_critical_germs_of_pair_band
    (surgery_pair_band_isolation T pf qf hconsecutivef) hcritg hexterior
  have hinjg := distinct_critical_values_of_surviving_germs hinj
    (fun x hx => ((hcritg x).mp hx).1) hkeep
  exact ⟨g, hg, hmg, hinjg, hcard.trans (congrArg Set.ncard hcrit)⟩

theorem exists_excellent_morse_reduction_of_multiple_minima
    (S : AdaptedSurgeryWindows E f₀)
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : IsMorse E f₀)
    (hmin : nativeMorseCount E f₀ 0 ≠ 1) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      InjOn g (criticalPoints E g) ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f₀).ncard := by
  obtain ⟨q, hqone, u, v, hnot⟩ := exists_native_one_handle_joining_components
    S.toSurgeryWindows hf₀ hmin
  obtain ⟨V, G, p, r, hV, hG, hzero, hdesc, hgerms, hpzero, hrzero, hpr,
      hp, hr, hback, hu, hv, -, hnoconnection⟩ :=
    S.realize_one_handle_minimum_branches hf₀ q hqone u v hnot
  have hmodels (x : M) (hx : x ∈ criticalPoints E f₀) :
      ∃ c : SignedMorseChart (E := E) f₀ x, ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    refine ⟨(S.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, S.critical_model_germ ⟨x, hx⟩] with y h₁ h₂
    exact h₁.trans h₂
  have hne : f₀ p ≠ f₀ r := fun h => hpr (Subtype.ext (S.distinct p.property r.property h))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact cancel_realized_higher_minimum S.toSurgeryWindows hf₀ hm₀ hV G hG hzero
      hdesc hmodels r p q hrzero hqone hlt hr v u hback hv hu
      (fun j hjq hjr hjp => hnoconnection j hjq hjp hjr)
  · exact cancel_realized_higher_minimum S.toSurgeryWindows hf₀ hm₀ hV G hG hzero
      hdesc hmodels p r q hpzero hqone hgt hp u v hback hu hv hnoconnection

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
