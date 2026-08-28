import Wikipedia.HopfProblem.DegreeCollapseSublevelFlowPointDescent
import Wikipedia.HopfProblem.DegreeCollapseNativeBasinConnectionCancellation
import Wikipedia.HopfProblem.DegreeCollapseSurvivingMorseGerms

/-!
# Native transverse pair cancellation below an untouched upper cut

The same actual flow and its transverse basin sheets survive bounded
critical-value descent. The pair is then cancelled in a native band
strictly below the cut. The original upper germ and literal strict
sublevel remain, together with every surviving critical index.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ} {m : ℕ}
  {A B HA HB X Y : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace HA] [TopologicalSpace HB]
  {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB}
  [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]

theorem cancel_transverse_pair_below_cut
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) (hdim : Module.finrank ℝ E = m + 1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodels : ∀ x ∈ criticalPoints E f, ∃ c : SignedMorseChart (E := E) f x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : criticalPoints E f) (hrp : f r < f p) (hpq : f p < f q)
    (hindex : nativeMorseIndex E f q = nativeMorseIndex E f p + 1)
    {b : ℝ} (hqb : f q < b)
    (hnoconnection : ∀ j : criticalPoints E f, j ≠ q → j ≠ p → j ≠ r → ∀ x,
      ¬(Tendsto (fun t => F t x) atBot (𝓝 q.val) ∧
        Tendsto (fun t => F t x) atTop (𝓝 j.val)))
    {z : M} (hzp : Tendsto (fun t => F t z) atTop (𝓝 p.val))
    (hzq : Tendsto (fun t => F t z) atBot (𝓝 q.val))
    (hunique : ∀ x, Tendsto (fun t => F t x) atBot (𝓝 q.val) →
      Tendsto (fun t => F t x) atTop (𝓝 p.val) → ∃ t, F t z = x)
    {α : X → M} {β : Y → M} {x : X} {y : Y}
    (hα : MDifferentiableAt I 𝓘(ℝ, E) α x) (hβ : MDifferentiableAt I' 𝓘(ℝ, E) β y)
    (hα0 : α x = z) (hβ0 : β y = z)
    (hαbasin : ∀ᶠ u in 𝓝 x, Tendsto (fun t => F t (α u)) atBot (𝓝 q.val))
    (hβbasin : ∀ᶠ u in 𝓝 y, Tendsto (fun t => F t (β u)) atTop (𝓝 p.val))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) α β x y) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      InjOn g (criticalPoints E g) ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ w, w ∈ criticalPoints E g ↔ w ∈ criticalPoints E f ∧ w ≠ p.val ∧ w ≠ q.val) ∧
      (∀ w ∈ criticalPoints E g, nativeMorseIndex E g w = nativeMorseIndex E f w) ∧
      (∀ w, b ≤ f w → g =ᶠ[𝓝 w] f) ∧ ∀ w, g w < b ↔ f w < b := by
  obtain ⟨h, hh, hmh, hcrit, hinjh, _, _, hpqh, hqbh, hconsecutive, hdesch,
      hmodelsh, hindices, hupperGerm, hcut⟩ :=
    exists_flow_preserving_consecutive_pair_below_cut hf hm hinj hV F hF hzero hdesc
      hmodels p r q hrp hpq hqb hnoconnection
  have hpcrit : p.val ∈ criticalPoints E h := hcrit.symm ▸ p.property
  have hqcrit : q.val ∈ criticalPoints E h := hcrit.symm ▸ q.property
  obtain ⟨cp, hcp⟩ := hmodelsh p.val hpcrit
  obtain ⟨cq, hcq⟩ := hmodelsh q.val hqcrit
  have hidx : Module.finrank ℝ cq.NegativeCoordinates =
      Module.finrank ℝ cp.NegativeCoordinates + 1 := by
    rw [← nativeMorseIndex_eq_chart cq, ← nativeMorseIndex_eq_chart cp,
      hindices q.val q.property, hindices p.val p.property]
    exact hindex
  have hcard : Fintype.card {i // cq.weights i = -1} =
      Fintype.card {i // cp.weights i = -1} + 1 := by
    simpa only [SignedMorseChart.NegativeCoordinates, MorseHandle.NegativeSpace,
      finrank_euclideanSpace] using hidx
  obtain ⟨W₀⟩ := nonempty_adaptedSurgeryWindows hh hmh hinjh
  obtain ⟨W, _, _, _, hupper⟩ := W₀.exists_same_flow_windows_below_cut hh hmh b
  let ph : criticalPoints E h := ⟨p.val, hpcrit⟩
  let qh : criticalPoints E h := ⟨q.val, hqcrit⟩
  have hconsecutiveh : ∀ s : criticalPoints E h, ¬(h ph < h s ∧ h s < h qh) := by
    intro s hs
    exact hconsecutive ⟨s.val, hcrit ▸ s.property⟩ hs
  have hpair := surgery_pair_band_isolation W.toSurgeryWindows ph qh hconsecutiveh
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior⟩ :=
    cancel_unique_connection_of_transverse_basin_sheets cp cq hh hmh hdim hcard V hV
      (fun w hw => hzero w (hcrit ▸ hw)) hdesch F hF hinjh hpcrit hqcrit hpqh
      (W.toSurgeryWindows.lower_lt_value ph) (W.toSurgeryWindows.value_lt_upper qh)
      hpair hzp hzq hunique hcp hcq hα hβ hα0 hβ0 hαbasin hβbasin htrans
  have hkeep := surviving_critical_germs_of_pair_band hpair hcritg hexterior
  have hinjg := distinct_critical_values_of_surviving_germs hinjh
    (fun w hw => ((hcritg w).mp hw).1) hkeep
  have hregular (w : M)
      (hw : h w ∈ Icc (W.toSurgeryWindows.lower ph) (W.toSurgeryWindows.upper qh)) :
      w ∉ criticalPoints E g := by
    intro hc
    obtain ⟨hc', hwp, hwq⟩ := (hcritg w).mp hc
    exact (hpair w hc' hw).elim hwp hwq
  rw [hcrit] at hcount
  refine ⟨g, hg, hmg, hinjg, hcount, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [hcritg w, hcrit]
  · intro w hw
    exact (nativeMorseIndex_congr_germ (hkeep w hw)).trans
      (hindices w (hcrit ▸ ((hcritg w).mp hw).1))
  · intro w hw
    apply Filter.EventuallyEq.trans (hexterior w ?_) (hupperGerm w hw)
    intro hband
    have hbw : b ≤ h w := by rw [(hupperGerm w hw).self_of_nhds]; exact hw
    exact (not_lt_of_ge hbw) (hband.2.trans (hupper qh hqbh))
  · intro w
    apply Iff.trans _ (hcut w)
    by_cases hw : h w ∈ Ioo (W.toSurgeryWindows.lower ph) (W.toSurgeryWindows.upper qh)
    · have hgw := RegularBandReplacement.mem_open_band hh hg
        (fun y hy => (hexterior y hy).self_of_nhds) hregular hw
      exact iff_of_true (hgw.2.trans (hupper qh hqbh)) (hw.2.trans (hupper qh hqbh))
    · rw [(hexterior w hw).self_of_nhds]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
