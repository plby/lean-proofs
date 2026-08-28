import Wikipedia.SmoothSixDPoincare.FiniteSmoothMotion
import Wikipedia.SmoothSixDPoincare.GraphMotionCutoff

/-!
# Small vertical steps for the supported graph trace

The sample time is fixed in each factor; the independent smooth control
parameter turns that factor on. All steps fix the horizontal and normal
coordinates, and their supports lie in one compact spatial projection.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

def verticalVector (δ : ℝ) : Space := ((0, δ), 0)

theorem norm_verticalVector {δ : ℝ} (hδ : 0 ≤ δ) : ‖verticalVector δ‖ = δ := by
  simp [verticalVector, Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hδ, hδ]

def graphStep (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (p : ℝ × Space) : Space :=
  p.2 + β ((i : ℝ) * δ, p.2) • (Real.smoothTransition p.1 • verticalVector δ)

theorem contDiff_graphStep {β : ℝ × Space → ℝ} (hβ : ContDiff ℝ ∞ β)
    (δ : ℝ) (i : ℕ) : ContDiff ℝ ∞ (graphStep β δ i) := by
  have hθ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact contDiff_snd.add ((hβ.comp (contDiff_const.prodMk contDiff_snd)).smul
    ((hθ.comp contDiff_fst).smul contDiff_const))

theorem graphStep_zero (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (z : Space) :
    graphStep β δ i (0, z) = z := by
  simp only [graphStep, Real.smoothTransition.zero, zero_smul, smul_zero, add_zero]

theorem graphStep_horizontal (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ) (z : Space) :
    (graphStep β δ i (t, z)).1.1 = z.1.1 := by
  simp [graphStep, verticalVector]

theorem graphStep_normal (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ) (z : Space) :
    (graphStep β δ i (t, z)).2 = z.2 := by
  simp [graphStep, verticalVector]

theorem graphStep_fixed (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ)
    {z : Space} (hz : z ∉ Prod.snd '' tsupport β) : graphStep β δ i (t, z) = z := by
  have hzero : β ((i : ℝ) * δ, z) = 0 := by
    by_contra hne
    exact hz ⟨((i : ℝ) * δ, z), subset_tsupport β hne, rfl⟩
  simp only [graphStep, hzero, zero_smul, add_zero]

/-- One displacement bound gives actual diffeomorphisms for every step and control time. -/
theorem exists_radius_graphStep {β : ℝ × Space → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ < ε → ∀ i : ℕ, ∀ t : ℝ,
      ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞,
        ∀ z, d z = graphStep β δ i (t, z) := by
  obtain ⟨ε, hε, hsmall⟩ := SmallPerturbation.exists_uniform_radius_bumpTranslation hβ hcompact
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε i t
  have hnorm : ‖Real.smoothTransition t • verticalVector δ‖ ≤ δ := by
    rw [norm_smul, norm_verticalVector hδ, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact mul_le_of_le_one_left hδ (Real.smoothTransition.le_one t)
  obtain ⟨d, hd, _⟩ :=
    hsmall ((i : ℝ) * δ) (Real.smoothTransition t • verticalVector δ) (hnorm.trans_lt hδε)
  exact ⟨d, hd⟩

/-- The endpoint of one step advances the tracked graph by exactly one time increment. -/
theorem graphStep_tracking {h : ℝ} {U : Set Space} (g : GraphMotionData h U)
    {δ : ℝ} {i : ℕ} (hi : (i : ℝ) * δ ∈ Icc (0 : ℝ) 1) (s : ℝ) :
    graphStep g.cutoff δ i (1, verticalGraph g.height ((i : ℝ) * δ) s) =
      verticalGraph g.height (((i : ℝ) + 1) * δ) s := by
  rw [graphStep, g.tracking _ hi, Real.smoothTransition.one, one_smul]
  ext <;> simp [verticalGraph, verticalVector, smul_eq_mul]
  ring

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
