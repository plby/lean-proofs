import Wikipedia.HopfProblem.DegreeCollapseSublevelTransversePairCancellation

/-!
# Cancel an actual consecutive transverse pair below an untouched cut

When the critical values are already consecutive, there is no need to move
one value past other handles. A unique transverse connecting orbit suffices;
other lower critical endpoints of the upper handle are unrestricted. Native
pair cancellation retains the entire original upper germ and literal strict
sublevel, and every surviving critical index and critical-value distinction.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ} {m : ℕ}
  {A B HA HB X Y : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace HA] [TopologicalSpace HB]
  {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB}
  [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]

theorem cancel_consecutive_transverse_pair_below_cut
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
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ s : criticalPoints E f, ¬ (f p < f s ∧ f s < f q))
    (hindex : nativeMorseIndex E f q = nativeMorseIndex E f p + 1)
    {b : ℝ} (hqb : f q < b)
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
  obtain ⟨cp, hcp⟩ := hmodels p.val p.property
  obtain ⟨cq, hcq⟩ := hmodels q.val q.property
  have hidx : Module.finrank ℝ cq.NegativeCoordinates =
      Module.finrank ℝ cp.NegativeCoordinates + 1 := by
    rw [← nativeMorseIndex_eq_chart cq, ← nativeMorseIndex_eq_chart cp]
    exact hindex
  have hcard : Fintype.card {i // cq.weights i = -1} =
      Fintype.card {i // cp.weights i = -1} + 1 := by
    simpa only [SignedMorseChart.NegativeCoordinates, MorseHandle.NegativeSpace,
      finrank_euclideanSpace] using hidx
  obtain ⟨W₀⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  obtain ⟨W, _, _, _, hupper⟩ := W₀.exists_same_flow_windows_below_cut hf hm b
  have hpair := surgery_pair_band_isolation W.toSurgeryWindows p q hconsecutive
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior⟩ :=
    cancel_unique_connection_of_transverse_basin_sheets cp cq hf hm hdim hcard V hV
      hzero hdesc F hF hinj p.property q.property hpq
      (W.toSurgeryWindows.lower_lt_value p) (W.toSurgeryWindows.value_lt_upper q)
      hpair hzp hzq hunique hcp hcq hα hβ hα0 hβ0 hαbasin hβbasin htrans
  have hkeep := surviving_critical_germs_of_pair_band hpair hcritg hexterior
  have hinjg := distinct_critical_values_of_surviving_germs hinj
    (fun w hw => ((hcritg w).mp hw).1) hkeep
  have hregular (w : M)
      (hw : f w ∈ Icc (W.toSurgeryWindows.lower p) (W.toSurgeryWindows.upper q)) :
      w ∉ criticalPoints E g := by
    intro hc
    obtain ⟨hc', hwp, hwq⟩ := (hcritg w).mp hc
    exact (hpair w hc' hw).elim hwp hwq
  refine ⟨g, hg, hmg, hinjg, hcount, hcritg, ?_, ?_, ?_⟩
  · intro w hw
    exact nativeMorseIndex_congr_germ (hkeep w hw)
  · intro w hw
    apply hexterior w
    intro hband
    exact (not_lt_of_ge hw) (hband.2.trans (hupper q hqb))
  · intro w
    by_cases hw : f w ∈ Ioo (W.toSurgeryWindows.lower p) (W.toSurgeryWindows.upper q)
    · have hgw := RegularBandReplacement.mem_open_band hf hg
        (fun y hy => (hexterior y hy).self_of_nhds) hregular hw
      exact iff_of_true (hgw.2.trans (hupper q hqb)) (hw.2.trans (hupper q hqb))
    · rw [(hexterior w hw).self_of_nhds]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
