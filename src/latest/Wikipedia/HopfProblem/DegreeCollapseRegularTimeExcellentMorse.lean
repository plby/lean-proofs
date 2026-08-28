import Wikipedia.HopfProblem.DegreeCollapseRegularTimeMorseFunction
import Wikipedia.HopfProblem.DegreeCollapseRelativeExcellentMorse

/-!
# An excellent Morse function with the same actual zero fiber and halves

Separate critical values only outside a protected regular zero band.
The exact equality in the band and strict uniform error elsewhere
preserve all signs and the boundary germs. Starting with any smooth
regular time, first construct its genuine Morse presentation, then carry
out this relative value separation. No new boundary atlas is prescribed.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse

open Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ}

theorem exists_excellent_preserving_zero_of_morse
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hreg : ∀ p, f p = 0 → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p)) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧ InjOn g (criticalPoints E g) ∧
      (∀ p, f p = 0 → g =ᶠ[𝓝 p] f) ∧
      (∀ p, g p = 0 ↔ f p = 0) ∧ (∀ p, 0 ≤ g p ↔ 0 ≤ f p) ∧
      (∀ p, 0 < g p ↔ 0 < f p) ∧
      ∀ p, g p = 0 → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g p) := by
  obtain ⟨r, hr, hband⟩ := exists_regular_zero_band hf hreg
  let O : Set M := {p | r / 2 < |f p|}
  have hO : IsOpen O := isOpen_lt continuous_const hf.continuous.abs
  have hKO : criticalPoints E f ⊆ O := by
    intro p hp
    have hpr : r < |f p| := lt_of_not_ge (fun h ↦ hband p h hp)
    exact (half_lt_self hr).trans hpr
  obtain ⟨g, hg, hmg, hcrit, hinj, hclose, hfixed⟩ :=
    exists_distinct_critical_values_relative hf hm O hO hKO (r / 2) (half_pos hr)
  have hfixedBand (p : M) (hp : |f p| ≤ r / 2) : g p = f p := by
    apply hfixed
    exact not_lt.mpr hp
  have hsign (p : M) : (g p = 0 ↔ f p = 0) ∧
      (0 ≤ g p ↔ 0 ≤ f p) ∧ (0 < g p ↔ 0 < f p) :=
    same_sign_of_near_equal (f p) (g p) (r / 2) (half_pos hr) (hfixedBand p) (hclose p)
  have hgerm (p : M) (hp : f p = 0) : g =ᶠ[𝓝 p] f := by
    have hmem : p ∈ {x : M | |f x| < r / 2} := by simpa [hp] using half_pos hr
    filter_upwards [(isOpen_lt hf.continuous.abs continuous_const).mem_nhds hmem] with x hx
    exact hfixedBand x hx.le
  refine ⟨g, hg, hmg, hcrit, hinj, hgerm, fun p ↦ (hsign p).1,
    fun p ↦ (hsign p).2.1, fun p ↦ (hsign p).2.2, ?_⟩
  intro p hp
  have hfp := (hsign p).1.mp hp
  rw [(hgerm p hfp).mfderiv_eq]
  exact hreg p hfp

theorem exists_excellent_preserving_zero
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ p, f p = 0 → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p)) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      InjOn g (criticalPoints E g) ∧
      (∀ p, f p = 0 → g =ᶠ[𝓝 p] f) ∧
      (∀ p, g p = 0 ↔ f p = 0) ∧ (∀ p, 0 ≤ g p ↔ 0 ≤ f p) ∧
      (∀ p, 0 < g p ↔ 0 < f p) ∧
      ∀ p, g p = 0 → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g p) := by
  obtain ⟨g₀, hg₀, hm₀, hgerm₀, hzero₀, hhalf₀, hpos₀, hreg₀⟩ :=
    exists_morse_preserving_zero hf hreg
  obtain ⟨g, hg, hm, _, hinj, hgerm, hzero, hhalf, hpos, hreg'⟩ :=
    exists_excellent_preserving_zero_of_morse hg₀ hm₀ hreg₀
  refine ⟨g, hg, hm, hinj, ?_, ?_, ?_, ?_, hreg'⟩
  · intro p hp
    exact (hgerm p ((hzero₀ p).mpr hp)).trans (hgerm₀ p hp)
  · exact fun p ↦ (hzero p).trans (hzero₀ p)
  · exact fun p ↦ (hhalf p).trans (hhalf₀ p)
  · exact fun p ↦ (hpos p).trans (hpos₀ p)

end Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse
