import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCore
import Wikipedia.HopfProblem.HolomorphicCousinGlobal

/-!
# Correcting affine sections by the actual homogeneous generator

Actual descended quotients of local differences satisfy the additive
cocycle identity by surjectivity.  The proved negative-one Cousin solver
then constructs correction coefficients.  Multiplication by the supplied
homogeneous function and subtraction from the local affine sections give
an actual global holomorphic function, preserving every affine word law.

This is an intermediate gluing lemma.  Local sections and their descended
quotients are explicit inputs here; their construction on the concrete
triangle cover is discharged in the separate concrete existence theorem.
-/

noncomputable section

open Function Filter Metric Set UpperHalfPlane
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Gluing

open HolomorphicCousin

variable {X ι : Type*}

/-- The additive identity follows from actual quotients, including points
where the denominator and all local differences vanish. -/
theorem descended_quotient_cocycle {p : X → ℂ} (hp : Surjective p)
    {U : ι → Set ℂ} {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ}
    (hq : ∀ i j z, p z ∈ U i → p z ∈ U j →
      h i j (p z) = (μ i z - μ j z) / F z) :
    ∀ i j k w, w ∈ U i → w ∈ U j → w ∈ U k →
      h i j w + h j k w = h i k w := by
  intro i j k w hi hj hk
  obtain ⟨z, rfl⟩ := hp w
  rw [hq i j z hi hj, hq j k z hj hk, hq i k z hi hk]
  ring

/-- At a zero of the homogeneous generator, equality of the local
sections is enough to recover the exact multiplication identity. -/
theorem difference_eq_mul_quotient {p : X → ℂ} {U : ι → Set ℂ}
    {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ}
    (hq : ∀ i j z, p z ∈ U i → p z ∈ U j →
      h i j (p z) = (μ i z - μ j z) / F z)
    (hz : ∀ i j z, p z ∈ U i → p z ∈ U j → F z = 0 → μ i z = μ j z)
    (i j : ι) (z : X) (hi : p z ∈ U i) (hj : p z ∈ U j) :
    μ i z - μ j z = F z * h i j (p z) := by
  rw [hq i j z hi hj]
  by_cases hF : F z = 0
  · rw [hz i j z hi hj hF, sub_self, zero_div, mul_zero]
  · exact (mul_div_cancel₀ (μ i z - μ j z) hF).symm

/-- Choose a cover member only after correcting its original local section. -/
def correctedGlue (p : X → ℂ) (U : ι → Set ℂ)
    (hcover : ∀ w, ∃ i, w ∈ U i) (μ : ι → X → ℂ) (F : X → ℂ)
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : NegativeOneCocycleSolution U h i₀ R) (z : X) : ℂ :=
  μ (hcover (p z)).choose z - F z * s.localPart (hcover (p z)).choose (p z)

theorem correctedGlue_eq {p : X → ℂ} {U : ι → Set ℂ}
    {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → X → ℂ} {F : X → ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j →
      μ i z - μ j z = F z * h i j (p z))
    {i : ι} {z : X} (hz : p z ∈ U i) :
    correctedGlue p U hcover μ F s z = μ i z - F z * s.localPart i (p z) := by
  let j := (hcover (p z)).choose
  have hj : p z ∈ U j := (hcover (p z)).choose_spec
  change μ j z - F z * s.localPart j (p z) = μ i z - F z * s.localPart i (p z)
  have hd := hdiff j i z hj hz
  have hs := s.equation j i (p z) hj hz
  linear_combination hd - F z * hs

theorem correctedGlue_eventuallyEq [TopologicalSpace X]
    {p : X → ℂ} (hp : Continuous p) {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i))
    {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → X → ℂ} {F : X → ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j →
      μ i z - μ j z = F z * h i j (p z))
    {i : ι} {z : X} (hz : p z ∈ U i) :
    correctedGlue p U hcover μ F s =ᶠ[𝓝 z]
      fun w => μ i w - F w * s.localPart i (p w) := by
  filter_upwards [((hU i).preimage hp).mem_nhds hz] with w hw
  exact correctedGlue_eq s hdiff hw

theorem correctedGlue_holomorphic {p : ℍ → ℂ}
    (hp : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω p) {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) {hcover : ∀ w, ∃ i, w ∈ U i}
    {μ : ι → ℍ → ℂ}
    (hμ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (μ i) (p ⁻¹' U i))
    {F : ℍ → ℂ} (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j →
      μ i z - μ j z = F z * h i j (p z)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue p U hcover μ F s) := by
  intro z
  obtain ⟨i, hi⟩ := hcover (p z)
  have hm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (μ i) z :=
    (hμ i).contMDiffAt (((hU i).preimage hp.continuous).mem_nhds hi)
  have hs : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w => s.localPart i (p w)) z :=
    (s.local_analytic i (p z) hi).contDiffAt.contMDiffAt.comp z (hp z)
  exact (hm.sub ((hF z).mul hs)).congr_of_eventuallyEq
    (correctedGlue_eventuallyEq hp.continuous hU s hdiff hi)

/-- Homogeneous multiplication makes every affine transformation law
survive the correction, for the entire genuine triangle group. -/
theorem correctedGlue_affine_law {p : ℍ → ℂ} {U : ι → Set ℂ}
    {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → ℍ → ℂ} {F : ℍ → ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j →
      μ i z - μ j z = F z * h i j (p z))
    (c : AffineCocycle)
    (hp : ∀ g z, p (triangleGeometricRepresentation g z) = p z)
    (hμ : ∀ i, c.EquivariantOn (μ i) (p ⁻¹' U i))
    (hF : ∀ g z, F (triangleGeometricRepresentation g z) = (c.scale g z : ℂ) * F z)
    (g : TriangleGroup) (z : ℍ) :
    correctedGlue p U hcover μ F s (triangleGeometricRepresentation g z) =
      c.fibreMap g z (correctedGlue p U hcover μ F s z) := by
  obtain ⟨i, hi⟩ := hcover (p z)
  have hig : p (triangleGeometricRepresentation g z) ∈ U i := by rwa [hp g z]
  rw [correctedGlue_eq s hdiff hig, correctedGlue_eq s hdiff hi,
    hp g z, hμ i g z hi, hF g z]
  simp only [AffineCocycle.fibreMap]
  ring

/-- On the actual zero seed at the cusp, this is the exact infinity
formula.  Its removability is proved using the actual cusp pole of `F`. -/
theorem correctedGlue_cusp {p : X → ℂ} {U : ι → Set ℂ}
    {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → X → ℂ} {F : X → ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j →
      μ i z - μ j z = F z * h i j (p z))
    (hRU : (ball (0 : ℂ) R)ᶜ ⊆ U i₀) {W : Set X}
    (hμ₀ : ∀ z ∈ W, μ i₀ z = 0) {z : X} (hz : z ∈ W)
    (hlarge : R < ‖p z‖) :
    correctedGlue p U hcover μ F s z = -F z * (p z)⁻¹ * s.infinityPart (p z)⁻¹ := by
  have hzU : p z ∈ U i₀ := hRU (by
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hlarge.le)
  rw [correctedGlue_eq s hdiff hzU, hμ₀ z hz, s.atInfinity (p z) hlarge]
  ring

/-- Construct the correction from actual descended quotients.  The
cocycle equation and corrected local agreement are both proved here. -/
theorem exists_corrected_gluing {p : ℍ → ℂ}
    (hp : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω p) (hps : Surjective p)
    {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) (hcover : ∀ w, ∃ i, w ∈ U i)
    {μ : ι → ℍ → ℂ}
    (hμ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (μ i) (p ⁻¹' U i))
    {F : ℍ → ℂ} (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    {h : ι → ι → ℂ → ℂ} (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hq : ∀ i j z, p z ∈ U i → p z ∈ U j →
      h i j (p z) = (μ i z - μ j z) / F z)
    (hz : ∀ i j z, p z ∈ U i → p z ∈ U j → F z = 0 → μ i z = μ j z)
    (i₀ : ι) {R : ℝ} (hR : 0 < R) (hRU : (ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ s : NegativeOneCocycleSolution U h i₀ R,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue p U hcover μ F s) ∧
      ∀ i, EqOn (correctedGlue p U hcover μ F s)
        (fun z => μ i z - F z * s.localPart i (p z)) (p ⁻¹' U i) := by
  obtain ⟨s⟩ := exists_negativeOne_holomorphic_cocycle_solution hU hcover hh
    (descended_quotient_cocycle hps hq) i₀ hR hRU
  have hd := difference_eq_mul_quotient hq hz
  exact ⟨s, correctedGlue_holomorphic hp hU hμ hF s hd,
    fun _ _ hi => correctedGlue_eq s hd hi⟩

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Gluing
