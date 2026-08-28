import Wikipedia.HopfProblem.HolomorphicCousinGlobal
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Correcting and gluing actual local beta-sections

This file is an abstract gluing helper for supplied local holomorphic functions
upstairs and their actual descended differences on an open cover of the complex
base.  Surjectivity of the base map proves the additive cocycle identity; it is
not an additional assumption.  The proved additive Cousin solver then supplies
the correction functions, and the corrected local functions glue to an actual
global holomorphic function.

Base-invariant corrections preserve all additive-affine transformation laws.
If a distinguished local function is `-τ` on an actual cusp sheet, the global
function plus `τ` has the explicit normalized analytic expression at infinity.
This helper does not assert the existence of the original local beta-sections.
-/

noncomputable section

open Function Filter Metric Set
open scoped Topology UpperHalfPlane Manifold ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsorGluing

open HolomorphicCousin

variable {X ι : Type*}

/-- Actual descended differences automatically satisfy the cocycle identity
when the base projection is surjective. -/
theorem descended_difference_cocycle {π : X → ℂ} (hπ : Surjective π)
    {U : ι → Set ℂ} {βlocal : ι → X → ℂ} {h : ι → ι → ℂ → ℂ}
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j →
      βlocal i z - βlocal j z = h i j (π z)) :
    ∀ i j k w, w ∈ U i → w ∈ U j → w ∈ U k →
      h i j w + h j k w = h i k w := by
  intro i j k w hi hj hk
  obtain ⟨z, rfl⟩ := hπ w
  rw [← hdiff i j z hi hj, ← hdiff j k z hj hk, ← hdiff i k z hi hk]
  ring

/-- The actual corrected global function, formed by choosing a cover member
at the image point.  The following lemmas prove independence of that choice. -/
def correctedGlue (π : X → ℂ) (U : ι → Set ℂ)
    (hcover : ∀ w, ∃ i, w ∈ U i) (βlocal : ι → X → ℂ)
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : NormalizedCocycleSolution U h i₀ R) (z : X) : ℂ :=
  βlocal (hcover (π z)).choose z - c.localPart (hcover (π z)).choose (π z)

/-- The chosen global function equals every corrected local function on its
literal preimage domain. -/
theorem correctedGlue_eq {π : X → ℂ} {U : ι → Set ℂ}
    {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j →
      βlocal i z - βlocal j z = h i j (π z))
    {i : ι} {z : X} (hz : π z ∈ U i) :
    correctedGlue π U hcover βlocal c z = βlocal i z - c.localPart i (π z) := by
  let j := (hcover (π z)).choose
  have hj : π z ∈ U j := (hcover (π z)).choose_spec
  change βlocal j z - c.localPart j (π z) = βlocal i z - c.localPart i (π z)
  have hb := hdiff j i z hj hz
  have hc := c.equation j i (π z) hj hz
  linear_combination hb - hc

/-- Local equality holds on a full upstairs neighborhood, which is the
analytic gluing statement needed for the selected global function. -/
theorem correctedGlue_eventuallyEq [TopologicalSpace X]
    {π : X → ℂ} (hπ : Continuous π) {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i))
    {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j →
      βlocal i z - βlocal j z = h i j (π z))
    {i : ι} {z : X} (hz : π z ∈ U i) :
    correctedGlue π U hcover βlocal c =ᶠ[𝓝 z]
      fun w => βlocal i w - c.localPart i (π w) := by
  filter_upwards [((hU i).preimage hπ).mem_nhds hz] with w hw
  exact correctedGlue_eq c hdiff hw

/-- Holomorphic pullback correction and actual local equality prove global
holomorphicity on the native upper-half-plane manifold. -/
theorem correctedGlue_holomorphic {π : ℍ → ℂ}
    (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π) {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) {hcover : ∀ w, ∃ i, w ∈ U i}
    {βlocal : ι → ℍ → ℂ}
    (hβ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) (π ⁻¹' U i))
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j →
      βlocal i z - βlocal j z = h i j (π z)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue π U hcover βlocal c) := by
  intro z
  obtain ⟨i, hi⟩ := hcover (π z)
  have hb : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) z :=
    (hβ i).contMDiffAt (((hU i).preimage hπ.continuous).mem_nhds hi)
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w => c.localPart i (π w)) z :=
    (c.local_analytic i (π z) hi).contDiffAt.contMDiffAt.comp z (hπ z)
  exact (hb.sub hc).congr_of_eventuallyEq
    (correctedGlue_eventuallyEq hπ.continuous hU c hdiff hi)

/-- Every shared additive-affine law survives the correction.  The index
type `G` can be the actual full triangle group, so this proves the law for
all words at once, not only the chosen generators. -/
theorem correctedGlue_additive_law {G : Type*} {π : X → ℂ} {U : ι → Set ℂ}
    {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j →
      βlocal i z - βlocal j z = h i j (π z))
    (A : G → X → X) (δ : G → X → ℂ)
    (hπA : ∀ g z, π (A g z) = π z)
    (hβA : ∀ i g z, π z ∈ U i → βlocal i (A g z) = βlocal i z + δ g z)
    (g : G) (z : X) :
    correctedGlue π U hcover βlocal c (A g z) =
      correctedGlue π U hcover βlocal c z + δ g z := by
  obtain ⟨i, hi⟩ := hcover (π z)
  have hiA : π (A g z) ∈ U i := by rwa [hπA g z]
  rw [correctedGlue_eq c hdiff hiA, correctedGlue_eq c hdiff hi,
    hπA g z, hβA i g z hi]
  ring

/-- On an actual cusp sheet where the original local function equals `-τ`,
the normalized infinity part is the exact extension of the corrected `β+τ`. -/
theorem correctedGlue_cusp {π : X → ℂ} {U : ι → Set ℂ}
    {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j →
      βlocal i z - βlocal j z = h i j (π z))
    (hRU : (ball (0 : ℂ) R)ᶜ ⊆ U i₀) {τ : X → ℂ} {W : Set X}
    (hβ₀ : ∀ z ∈ W, βlocal i₀ z = -τ z) {z : X} (hz : z ∈ W)
    (hlarge : R < ‖π z‖) :
    correctedGlue π U hcover βlocal c z + τ z = -c.infinityPart (π z)⁻¹ := by
  have hzU : π z ∈ U i₀ := hRU (by
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hlarge.le)
  rw [correctedGlue_eq c hdiff hzU, hβ₀ z hz, c.atInfinity (π z) hlarge]
  ring

/-- Construct the correction from the actual descended differences using
the proved Cousin solver, and construct the resulting global holomorphic
function.  No correction or cocycle identity is supplied as an assumption. -/
theorem exists_corrected_gluing {π : ℍ → ℂ}
    (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π) (hπsurj : Surjective π)
    {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) (hcover : ∀ w, ∃ i, w ∈ U i)
    {βlocal : ι → ℍ → ℂ}
    (hβ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) (π ⁻¹' U i))
    {h : ι → ι → ℂ → ℂ} (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j →
      βlocal i z - βlocal j z = h i j (π z))
    (i₀ : ι) {R : ℝ} (hR : 0 < R) (hRU : (ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ c : NormalizedCocycleSolution U h i₀ R,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue π U hcover βlocal c) ∧
      ∀ i, EqOn (correctedGlue π U hcover βlocal c)
        (fun z => βlocal i z - c.localPart i (π z)) (π ⁻¹' U i) := by
  obtain ⟨c⟩ := exists_normalized_holomorphic_cocycle_solution hU hcover hh
    (descended_difference_cocycle hπsurj hdiff) i₀ hR hRU
  exact ⟨c, correctedGlue_holomorphic hπ hU hβ c hdiff,
    fun _ _ hz => correctedGlue_eq c hdiff hz⟩

/-- The complete gluing helper, including all shared additive-affine laws and
the actual normalized analytic infinity expression.  Every local function and
descended difference remains an explicit input for later geometric instantiation. -/
theorem exists_glued_beta_with_cusp {G : Type*} {π : ℍ → ℂ}
    (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π) (hπsurj : Surjective π)
    {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) (hcover : ∀ w, ∃ i, w ∈ U i)
    {βlocal : ι → ℍ → ℂ}
    (hβ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) (π ⁻¹' U i))
    {h : ι → ι → ℂ → ℂ} (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j →
      βlocal i z - βlocal j z = h i j (π z))
    (i₀ : ι) {R : ℝ} (hR : 0 < R) (hRU : (ball (0 : ℂ) R)ᶜ ⊆ U i₀)
    (A : G → ℍ → ℍ) (δ : G → ℍ → ℂ) (hπA : ∀ g z, π (A g z) = π z)
    (hβA : ∀ i g z, π z ∈ U i → βlocal i (A g z) = βlocal i z + δ g z)
    (τ : ℍ → ℂ) (W : Set ℍ) (hβ₀ : ∀ z ∈ W, βlocal i₀ z = -τ z) :
    ∃ (β : ℍ → ℂ) (B : ℂ → ℂ),
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β ∧ AnalyticOnNhd ℂ B (ball 0 R⁻¹) ∧ B 0 = 0 ∧
      (∀ g z, β (A g z) = β z + δ g z) ∧
      ∀ z ∈ W, R < ‖π z‖ → β z + τ z = B (π z)⁻¹ := by
  obtain ⟨c, hc, _⟩ := exists_corrected_gluing hπ hπsurj hU hcover hβ hh hdiff i₀ hR hRU
  refine ⟨correctedGlue π U hcover βlocal c, fun u => -c.infinityPart u,
    hc, c.infinity_analytic.neg, ?_, ?_, ?_⟩
  · change -c.infinityPart 0 = 0
    rw [c.infinity_zero, neg_zero]
  · exact correctedGlue_additive_law c hdiff A δ hπA hβA
  · intro z hz hlarge
    exact correctedGlue_cusp c hdiff hRU hβ₀ hz hlarge

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsorGluing
