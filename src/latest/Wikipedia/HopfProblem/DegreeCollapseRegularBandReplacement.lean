import Wikipedia.SmoothSixDPoincare.RegularBandDiffeomorph
import Wikipedia.SmoothSixDPoincare.ManifoldFermat
import Wikipedia.SmoothSixDPoincare.MorseNegation

/-!
# Controlled critical values retain the actual band and endpoint levels

On a compact manifold, a replacement equal to the original function
outside its open band cannot escape the endpoint values inside the band
without an interior extremum. Native Fermat places that extremum among
the critical points, whose values are assumed to stay inside the band.
The critical-free case is a specialization: deleting all critical points
in the original band gives a genuine regular band for the replacement,
with the original endpoint level sets.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularBandReplacement

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {f g : M → ℝ} {a b : ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
  (hkeep : ∀ x, f x ∉ Ioo a b → g x = f x)
  (hreg : ∀ x, f x ∈ Icc a b → x ∉ criticalPoints E g)

include hf hg hkeep in
theorem lt_upper_of_critical_values
    (hvalues : ∀ y, f y ∈ Icc a b → y ∈ criticalPoints E g → g y ∈ Ioo a b)
    {x : M} (hx : f x ∈ Ioo a b) : g x < b := by
  have hcompact : IsCompact {y : M | f y ∈ Icc a b} :=
    (isClosed_Icc.preimage hf.continuous).isCompact
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn ⟨x, hx.1.le, hx.2.le⟩
    hg.continuous.continuousOn
  have hgp : g p ≤ b := by
    by_cases hpi : f p ∈ Ioo a b
    · have hcrit : p ∈ criticalPoints E g := by
        apply mem_criticalPoints_of_localMax hg
        filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds
          (isOpen_Ioo.mem_nhds hpi)] with y hy
        exact hmax ⟨hy.1.le, hy.2.le⟩
      exact (hvalues p hp hcrit).2.le
    · rw [hkeep p hpi]
      exact hp.2
  by_contra hn
  have hbx : b ≤ g x := le_of_not_gt hn
  have hcrit : x ∈ criticalPoints E g := by
    apply mem_criticalPoints_of_localMax hg
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds hx)] with y hy
    exact (hmax ⟨hy.1.le, hy.2.le⟩).trans (hgp.trans hbx)
  exact (not_le_of_gt (hvalues x ⟨hx.1.le, hx.2.le⟩ hcrit).2) hbx

include hf hg hkeep in
theorem mem_open_band_of_critical_values
    (hvalues : ∀ y, f y ∈ Icc a b → y ∈ criticalPoints E g → g y ∈ Ioo a b)
    {x : M} (hx : f x ∈ Ioo a b) : g x ∈ Ioo a b := by
  have hneg : -g x < -a := lt_upper_of_critical_values hf.neg hg.neg
    (a := -b) (b := -a) (fun y hy => by
      rw [hkeep y (by intro hy'; exact hy ⟨by linarith [hy'.2], by linarith [hy'.1]⟩)])
    (fun y hy hcrit => by
      rw [criticalPoints_neg] at hcrit
      have hv := hvalues y ⟨by linarith [hy.2], by linarith [hy.1]⟩ hcrit
      exact ⟨by linarith [hv.2], by linarith [hv.1]⟩)
    (show -f x ∈ Ioo (-b) (-a) from ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  exact ⟨by linarith, lt_upper_of_critical_values hf hg hkeep hvalues hx⟩

include hf hg hkeep hreg in
theorem lt_upper_of_mem_open_band {x : M} (hx : f x ∈ Ioo a b) : g x < b :=
  lt_upper_of_critical_values hf hg hkeep (fun y hy hcrit => (hreg y hy hcrit).elim) hx

include hf hg hkeep hreg in
theorem mem_open_band {x : M} (hx : f x ∈ Ioo a b) : g x ∈ Ioo a b :=
  mem_open_band_of_critical_values hf hg hkeep (fun y hy hcrit => (hreg y hy hcrit).elim) hx

include hf hg hkeep hreg in
theorem endpoint_and_band_comparisons (x : M) :
    (g x = a ↔ f x = a) ∧ (g x = b ↔ f x = b) ∧
    (g x ≤ a ↔ f x ≤ a) ∧ (g x ≤ b ↔ f x ≤ b) ∧
    (g x ∈ Icc a b ↔ f x ∈ Icc a b) := by
  by_cases hx : f x ∈ Ioo a b
  · have hgx := mem_open_band hf hg hkeep hreg hx
    constructor
    · constructor <;> intro h <;> linarith [hx.1, hgx.1]
    constructor
    · constructor <;> intro h <;> linarith [hx.2, hgx.2]
    constructor
    · constructor <;> intro h <;> linarith [hx.1, hgx.1]
    exact ⟨iff_of_true hgx.2.le hx.2.le,
      iff_of_true ⟨hgx.1.le, hgx.2.le⟩ ⟨hx.1.le, hx.2.le⟩⟩
  · rw [hkeep x hx]
    exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

variable [FiniteDimensional ℝ E] [T2Space M]

include hf hg hkeep hreg in
theorem exists_ambient_transport (hab : a ≤ b) :
    RegularLevel.AmbientEquivalent (E := E) f a b := by
  have hc := endpoint_and_band_comparisons hf hg hkeep hreg
  have hband (x : M) (hx : g x ∈ Icc a b) : x ∉ criticalPoints E g :=
    hreg x ((hc x).2.2.2.2.mp hx)
  obtain ⟨D, hlevel, hsublevel⟩ :=
    RegularLevel.exists_ambient_regularBand_transport hg hab hband
  have ha : {x : M | g x = a} = {x : M | f x = a} := Set.ext fun x => (hc x).1
  have hb : {x : M | g x = b} = {x : M | f x = b} := Set.ext fun x => (hc x).2.1
  have hsa : {x : M | g x ≤ a} = {x : M | f x ≤ a} := Set.ext fun x => (hc x).2.2.1
  have hsb : {x : M | g x ≤ b} = {x : M | f x ≤ b} := Set.ext fun x => (hc x).2.2.2.1
  rw [ha, hb] at hlevel
  rw [hsa, hsb] at hsublevel
  exact ⟨D, hlevel, hsublevel⟩

include hf hg hkeep hreg in
theorem exists_native_level_transport (hab : a ≤ b)
    (ha : ∀ x, f x = a → x ∉ criticalPoints E f)
    (hb : ∀ x, f x = b → x ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf ha
    letI := RegularLevel.chartedSpace hf hb
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      D '' {x : M | f x = a} = {x : M | f x = b} ∧
      D '' {x : M | f x ≤ a} = {x : M | f x ≤ b} ∧
      ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          {x : M // f x = a} {x : M // f x = b} ∞,
        ∀ x, (e x : M) = D x := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨D, hlevel, hsublevel⟩ := exists_ambient_transport hf hg hkeep hreg hab
  obtain ⟨e, he⟩ := RegularLevel.exists_levelDiffeomorph_of_ambient hf ha hb D hlevel
  exact ⟨D, hlevel, hsublevel, e, he⟩

end Wikipedia.HopfProblem.DegreeCollapse.RegularBandReplacement
