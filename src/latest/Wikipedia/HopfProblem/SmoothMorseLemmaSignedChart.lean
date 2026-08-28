import Wikipedia.HopfProblem.SmoothMorseLemmaLocal
import Wikipedia.HopfProblem.SmoothMorseLemmaSignedDiffeomorph

/-!
# Classical signed-square smooth Morse coordinates

The genuine local Morse chart is composed with the actual signed linear
coordinates supplied by Sylvester's theorem. Thus the original smooth
function becomes a sum of squares with coefficients exactly `-1` or `1`
in a native smooth partial diffeomorphism, with no zero coefficients and
no assumed coordinate system.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual Hessian at a point of an open smooth domain is symmetric. -/
theorem hessian_symmetric_of_contDiffOn {f : E → ℝ} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {a : E} (ha : a ∈ U) (u v : E) :
    fderiv ℝ (fderiv ℝ f) a u v = fderiv ℝ (fderiv ℝ f) a v u := by
  have hs := (hf.contDiffAt (hU.mem_nhds ha)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  exact hs u v

variable [FiniteDimensional ℝ E]

/-- The classical smooth Morse lemma on an open finite-dimensional real
domain. Both normal-form equalities concern the original function and
the actual forward and inverse maps of the constructed smooth chart. -/
theorem exists_signed_morse_chart_of_contDiffOn {f : E → ℝ} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (a : E) (ha : a ∈ U)
    (hc : fderiv ℝ f a = 0)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
      ∃ e : PartialDiffeomorph 𝓘(ℝ, E)
          𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) E (Fin (Module.finrank ℝ E) → ℝ) ∞,
        a ∈ e.source ∧ e.source ⊆ U ∧ e a = 0 ∧
        (∀ x ∈ e.source, f x = f a + ∑ i, w i * (e x i) ^ 2) ∧
        (∀ y ∈ e.target, f (e.symm y) = f a + ∑ i, w i * y i ^ 2) := by
  obtain ⟨e, hea, heU, hezero, _, hnormal, _⟩ :=
    exists_morse_chart_of_contDiffOn hf hU a ha hc hn
  obtain ⟨w, hw, C, hCzero, hC⟩ := exists_signed_diffeomorph
    (fderiv ℝ (fderiv ℝ f) a) (hessian_symmetric_of_contDiffOn hf hU ha) hn
  let φ := e.trans C.toPartialDiffeomorph
  have hsource : φ.source = e.source := by
    ext x
    change (x ∈ e.source ∧ e x ∈ (univ : Set E)) ↔ x ∈ e.source
    simp only [mem_univ, and_true]
  have haφ : a ∈ φ.source := hsource ▸ hea
  have hφU : φ.source ⊆ U := hsource ▸ heU
  have hφzero : φ a = 0 := by
    change C (e a) = 0
    rw [hezero, hCzero]
  have hφnormal (x : E) (hx : x ∈ φ.source) :
      f x = f a + ∑ i, w i * (φ x i) ^ 2 := by
    have hx' : x ∈ e.source := hsource ▸ hx
    calc
      f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (e x) (e x) :=
        hnormal x hx'
      _ = f a + ∑ i, w i * (C (e x) i) ^ 2 := by rw [hC]
      _ = f a + ∑ i, w i * (φ x i) ^ 2 := rfl
  refine ⟨w, hw, φ, haφ, hφU, hφzero, hφnormal, ?_⟩
  intro y hy
  have hr : φ (φ.symm y) = y := φ.right_inv hy
  simpa only [hr] using hφnormal (φ.symm y) (φ.map_target hy)

/-- The globally smooth specialization of the signed-square Morse lemma. -/
theorem exists_signed_morse_chart {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : E)
    (hc : fderiv ℝ f a = 0)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
      ∃ e : PartialDiffeomorph 𝓘(ℝ, E)
          𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) E (Fin (Module.finrank ℝ E) → ℝ) ∞,
        a ∈ e.source ∧ e a = 0 ∧
        (∀ x ∈ e.source, f x = f a + ∑ i, w i * (e x i) ^ 2) ∧
        (∀ y ∈ e.target, f (e.symm y) = f a + ∑ i, w i * y i ^ 2) := by
  obtain ⟨w, hw, e, hea, _, hezero, hnormal, hinverse⟩ :=
    exists_signed_morse_chart_of_contDiffOn hf.contDiffOn isOpen_univ a (mem_univ a) hc hn
  exact ⟨w, hw, e, hea, hezero, hnormal, hinverse⟩

end Wikipedia.HopfProblem.SmoothMorseLemma
