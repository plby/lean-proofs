import Wikipedia.HopfProblem.DegreeCollapseNativeMorseIndexNegation
import Wikipedia.HopfProblem.DegreeCollapseMinimalExcellentMorse

/-!
# Transporting the native Morse minimization and cancellation argument by negation

Negation preserves excellent functions and minimality of the critical count.
It reverses both critical values and complementary indices, preserving their
order. A genuine pair removal for the negative function gives a genuine
pair removal for the original function with the reversed outer band.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

theorem distinct_critical_values_neg (hinj : InjOn f (criticalPoints E f)) :
    InjOn (fun x => -f x) (criticalPoints E (fun x => -f x)) := by
  rw [criticalPoints_neg]
  intro x hx y hy hxy
  exact hinj hx hy (neg_injective hxy)

theorem minimal_excellent_morse_neg
    (hminimal : ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
      InjOn g (criticalPoints E g) →
      (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard) :
    ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
      InjOn g (criticalPoints E g) →
      (criticalPoints E (fun x => -f x)).ncard ≤ (criticalPoints E g).ncard := by
  intro g hg hmg hinjg
  have hh := hminimal (fun x => -g x) hg.neg (isMorse_neg hmg) (distinct_critical_values_neg hinjg)
  simpa only [criticalPoints_neg] using hh

variable [FiniteDimensional ℝ E]

theorem native_index_order_neg
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (horder : ∀ x ∈ criticalPoints E f, ∀ y ∈ criticalPoints E f,
      f x ≤ f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y) :
    ∀ x ∈ criticalPoints E (fun z => -f z), ∀ y ∈ criticalPoints E (fun z => -f z),
      -f x ≤ -f y → nativeMorseIndex E (fun z => -f z) x ≤
        nativeMorseIndex E (fun z => -f z) y := by
  rw [criticalPoints_neg]
  intro x hx y hy hxy
  obtain ⟨cx⟩ := nonempty_signedMorseChart hf hm x hx
  obtain ⟨cy⟩ := nonempty_signedMorseChart hf hm y hy
  have hix := nativeMorseIndex_neg_add cx
  have hiy := nativeMorseIndex_neg_add cy
  have hi := horder y hy x hx (neg_le_neg_iff.mp hxy)
  omega

theorem pair_removal_of_negative_function {φ : M → ℝ} {p q : M} {l u : ℝ}
    (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ) (hmφ : IsMorse E φ)
    (hcount : (criticalPoints E φ).ncard + 2 =
      (criticalPoints E (fun x => -f x)).ncard)
    (hcrit : ∀ z, z ∈ criticalPoints E φ ↔
      z ∈ criticalPoints E (fun x => -f x) ∧ z ≠ q ∧ z ≠ p)
    (hexterior : ∀ z, -f z ∉ Ioo (-u) (-l) → φ =ᶠ[𝓝 z] fun x => -f x) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p ∧ z ≠ q) ∧
      ∀ z, f z ∉ Ioo l u → g =ᶠ[𝓝 z] f := by
  refine ⟨fun z => -φ z, hφ.neg, isMorse_neg hmφ, ?_, ?_, ?_⟩
  · simpa only [criticalPoints_neg] using hcount
  · intro z
    rw [criticalPoints_neg, hcrit z, criticalPoints_neg]
    tauto
  · intro z hz
    have hz' : -f z ∉ Ioo (-u) (-l) := by
      intro hh
      exact hz ⟨neg_lt_neg_iff.mp hh.2, neg_lt_neg_iff.mp hh.1⟩
    filter_upwards [hexterior z hz'] with x hx
    rw [hx, neg_neg]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
