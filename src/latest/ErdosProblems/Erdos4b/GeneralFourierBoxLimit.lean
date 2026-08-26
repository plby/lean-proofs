/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCorrectionBounds

/-!
# Pointwise convergence and uniform bounds on growing Fourier boxes

The conditions below collect the previously proved comparison hypotheses.
They are explicit obligations on the arithmetic data, not assumptions
about the truth of the desired asymptotic formula.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

structure DoubledFourierBoxConditions {ι : Type*} [Fintype ι]
    (M w : ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (L : (ι ⊕ ι) → ℝ) (T σ : ℝ) : Prop where
  scale_pos : ∀ i, 0 < L i
  integer_pos : 0 < M
  cutoff_pos : 0 < w
  exponent_nonneg : 0 ≤ σ
  cutoff_large : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w
  edge_card : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι
  generic : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true
  box_scale : ∀ i, (1 + T) / L i ≤ σ

theorem eventually_mem_fourierCoordinateBox {α ι : Type*} [Finite ι]
    {l : Filter α} {T : α → ℝ} (hT : Tendsto T l atTop) (ξ : ι → ℝ) :
    ∀ᶠ a in l, ξ ∈ fourierCoordinateBox (T a) := by
  have h : ∀ i, ∀ᶠ a in l, ‖ξ i‖ ≤ T a := fun i ↦ hT.eventually_ge_atTop _
  exact eventually_all.mpr h

theorem tendsto_one_of_eventually_norm_sub_le_exp
    {α : Type*} {l : Filter α} (z : α → ℂ) (B : α → ℝ)
    (hB : Tendsto B l (𝓝 0))
    (hbound : ∀ᶠ a in l, ‖z a - 1‖ ≤ Real.exp (B a) - 1) :
    Tendsto z l (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun a ↦ norm_nonneg _) hbound
  simpa only [Function.comp_def, Real.exp_zero, sub_self] using
    ((Real.continuous_exp.tendsto 0).comp hB).sub_const 1

theorem tendsto_normalizedDoubledFourierKernel_pointwise
    {α ι : Type*} [Fintype ι] {l : Filter α}
    (M w : α → ℕ) (edges : α → ℕ → Finset (ι × ι)) (companion : α → ℕ → Bool)
    (L : α → (ι ⊕ ι) → ℝ) (T σ : α → ℝ)
    (hdata : ∀ᶠ a in l, DoubledFourierBoxConditions (M a) (w a)
      (edges a) (companion a) (L a) (T a) (σ a))
    (hT : Tendsto T l atTop) (hσ : Tendsto σ l (𝓝 0))
    (hsmall : Tendsto (fun a ↦ σ a * (w a + 1)) l (𝓝 0))
    (hrelative : Tendsto (fun a ↦ doubledFourierRelativeErrorBound ι (M a) (w a) (σ a))
      l (𝓝 0)) (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    Tendsto (fun a ↦ normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ)
      l (𝓝 (doubledFourierPairKernel ξ)) := by
  let s (a : α) := doubledFourierTensorExponents (fun i _ ↦ L a i) ξ
  have hbox := eventually_mem_fourierCoordinateBox hT ξ
  have hn (i : ι ⊕ ι) (b : Bool) : Tendsto (fun a ↦ s a i b) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun a ↦ norm_nonneg _) _ hσ
    filter_upwards [hdata, hbox] with a ha hξ
    exact norm_doubledFourierTensorExponents_le_on_box
      (L a) ha.scale_pos ha.box_scale hξ i b
  have hZ : Tendsto (fun a ↦ doubledFourierZetaCorrection (L a) ξ) l (𝓝 1) := by
    have h := tendsto_finsetProd (s := Finset.univ)
      (fun i hi ↦ tendsto_selbergZetaQuotientCorrection (hn i false) (hn i true))
    simpa only [Finset.prod_const_one] using! h
  have hB : Tendsto (fun a ↦
      smallDoubledFourierReferenceProduct (ι := ι) (w a) (fun _ _ ↦ 0) /
        smallDoubledFourierReferenceProduct (w a) (s a)) l (𝓝 1) := by
    apply tendsto_one_of_eventually_norm_sub_le_exp _
      (fun a ↦ 24 * (Fintype.card (ι ⊕ ι) : ℝ) * σ a * (w a + 1))
    · simpa only [mul_zero, mul_assoc] using
        hsmall.const_mul (24 * (Fintype.card (ι ⊕ ι) : ℝ))
    · filter_upwards [hdata, hbox] with a ha hξ
      apply norm_smallDoubledFourierReferenceProduct_zero_div_sub_one_le
        (w a) (s a) ha.exponent_nonneg
      · intro i b
        rw [doubledFourierTensorExponents_re]
        exact (inv_pos.mpr (ha.scale_pos i)).le
      · intro i
        exact norm_doubledFourierTensorExponents_le_on_box
          (L a) ha.scale_pos ha.box_scale hξ i false
  have hR : Tendsto (fun a ↦ ∏' p : Nat.Primes,
      roughDoubledFourierRelativeFactor (w a) (edges a) (companion a) (s a) p) l (𝓝 1) := by
    apply tendsto_one_of_eventually_norm_sub_le_exp _ _ hrelative
    filter_upwards [hdata, hbox] with a ha hξ
    apply norm_tprod_roughDoubledFourierRelativeFactor_sub_one_le
      (edges a) (companion a) (s a) ha.integer_pos ha.cutoff_pos
      ha.exponent_nonneg ha.cutoff_large ha.edge_card ha.generic
    · intro i b
      rw [doubledFourierTensorExponents_re]
      exact (inv_pos.mpr (ha.scale_pos i)).le
    · intro i
      exact norm_doubledFourierTensorExponents_le_on_box
        (L a) ha.scale_pos ha.box_scale hξ i false
  have hlim := ((hB.mul hR).mul hZ).const_mul (doubledFourierPairKernel ξ)
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [hdata] with a ha
  exact (normalizedDoubledFourierKernel_eq_main_mul_corrections
    (edges a) (companion a) (L a) ha.scale_pos ha.integer_pos ha.cutoff_pos
      ha.cutoff_large ha.edge_card ha.generic ξ).symm

theorem eventually_norm_normalizedDoubledFourierKernel_le_on_box
    {α ι : Type*} [Fintype ι] {l : Filter α}
    (M w : α → ℕ) (edges : α → ℕ → Finset (ι × ι)) (companion : α → ℕ → Bool)
    (L : α → (ι ⊕ ι) → ℝ) (T σ : α → ℝ)
    (hdata : ∀ᶠ a in l, DoubledFourierBoxConditions (M a) (w a)
      (edges a) (companion a) (L a) (T a) (σ a))
    (hσ : Tendsto σ l (𝓝 0))
    (hsmall : Tendsto (fun a ↦ σ a * (w a + 1)) l (𝓝 0))
    (hrelative : Tendsto (fun a ↦ doubledFourierRelativeErrorBound ι (M a) (w a) (σ a))
      l (𝓝 0)) :
    ∀ᶠ a in l, ∀ ξ ∈ fourierCoordinateBox (T a),
      ‖normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ‖ ≤
        Real.exp (1 + (Fintype.card (ι ⊕ ι) : ℝ)) * ‖doubledFourierPairKernel ξ‖ := by
  obtain ⟨δ, hδ, hbound⟩ :=
    exists_uniform_normalizedDoubledFourierKernel_box_bound ι zero_lt_one
  have hsum : Tendsto (fun a ↦ 24 * (Fintype.card (ι ⊕ ι) : ℝ) * σ a * (w a + 1) +
      doubledFourierRelativeErrorBound ι (M a) (w a) (σ a)) l (𝓝 0) := by
    simpa only [mul_zero, zero_add, mul_assoc] using
      (hsmall.const_mul (24 * (Fintype.card (ι ⊕ ι) : ℝ))).add hrelative
  filter_upwards [hdata, hσ.eventually (gt_mem_nhds hδ),
    hsum.eventually (gt_mem_nhds zero_lt_one)] with a ha hσδ hsumone
  intro ξ hξ
  have herr := hbound (edges a) (companion a) (L a) ha.scale_pos ha.integer_pos ha.cutoff_pos
    ha.exponent_nonneg hσδ ha.cutoff_large ha.edge_card ha.generic ha.box_scale ξ hξ
  have htriangle := norm_le_norm_sub_add
    (normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ)
    (doubledFourierPairKernel ξ)
  have hexp := Real.exp_le_exp.mpr
    (add_le_add hsumone.le (le_refl (Fintype.card (ι ⊕ ι) : ℝ)))
  simp only [mul_one] at herr
  have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hexp 1)
    (norm_nonneg (doubledFourierPairKernel ξ))
  nlinarith

end

end Erdos4b
