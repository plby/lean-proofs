import Wikipedia.HopfProblem.DegreeCollapseSmoothMinimumDisk
import Wikipedia.SmoothSixDPoincare.RegularBandDiffeomorph
import Wikipedia.SmoothSixDPoincare.ManifoldFermat
import Wikipedia.SmoothSixDPoincare.MorseNegation

/-!
# One positive critical point gives a native smooth disk on the entire positive side

Compactness and native Fermat make the sole positive critical point the
unique global maximum. Negate the original function, construct its actual
small minimum disk in a smooth chart, and transport that disk through
the whole critical-free band to the original zero level. The result
retains an open smooth neighborhood of the entire closed disk.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {p : M} (hp : 0 < f p)
  (hunique : ∀ x ∈ criticalPoints E f, 0 < f x → x = p)

omit [FiniteDimensional ℝ E] [T2Space M] in
include hf hp hunique in
theorem unique_global_max_of_unique_positive_critical : ∀ x, f p ≤ f x → x = p := by
  obtain ⟨q, _, hmax⟩ := isCompact_univ.exists_isMaxOn ⟨p, mem_univ p⟩
    hf.continuous.continuousOn
  have hq : q ∈ criticalPoints E f :=
    mem_criticalPoints_of_localMax hf (Eventually.of_forall fun x => hmax (mem_univ x))
  have hqp : q = p := hunique q hq (hp.trans_le (hmax (mem_univ p)))
  have hglobal (x : M) : f x ≤ f p := hqp ▸ hmax (mem_univ x)
  intro x hx
  exact hunique x (mem_criticalPoints_of_localMax hf
    (Eventually.of_forall fun y => (hglobal y).trans hx)) (hp.trans_le hx)

include hf hp hunique in
theorem nonempty_native_superlevel_disk_of_unique_positive_critical
    (hm : IsMorse E f) (hpcrit : p ∈ criticalPoints E f)
    (hzero : ∀ x, f x = 0 → x ∉ criticalPoints E f) :
    Nonempty (NativeSublevelDisk (Module.finrank ℝ E) E (fun x => -f x) 0) := by
  obtain ⟨c⟩ := nonempty_signedMorseChart hf hm p hpcrit
  have hmin : ∀ x, -f x ≤ -f p → x = p := by
    intro x hx
    exact unique_global_max_of_unique_positive_critical hf hp hunique x (by linarith)
  obtain ⟨a, ha, ⟨d⟩⟩ := exists_native_minimum_sublevel_disk c.neg hf.continuous.neg hmin
    (b := 0) (by simpa using neg_neg_of_pos hp)
  have hband (x : M) (hx : -f x ∈ Icc a 0) :
      x ∉ criticalPoints E (fun y => -f y) := by
    rw [criticalPoints_neg]
    intro hcrit
    by_cases hzero' : f x = 0
    · exact hzero x hzero' hcrit
    have hnonneg : 0 ≤ f x := by linarith [hx.2]
    have hpos : 0 < f x := lt_of_le_of_ne hnonneg (Ne.symm hzero')
    have hxp := hunique x hcrit hpos
    rw [hxp] at hx
    exact (not_le_of_gt ha.1) hx.1
  obtain ⟨D, hlevel, hsublevel⟩ :=
    RegularLevel.exists_ambient_regularBand_transport hf.neg ha.2.le hband
  exact ⟨d.transport D hsublevel hlevel⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
