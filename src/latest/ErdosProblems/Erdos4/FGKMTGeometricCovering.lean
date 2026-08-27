import ErdosProblems.Erdos4.FGKMTFiniteCovering
import ErdosProblems.Erdos4.FGKMTThinning

/-! Equal round degrees give an exact geometric survival model. -/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem modelSequence_eq_geometric (μ : ℕ → I → FiniteLaw (Finset V))
    {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hdegree : ∀ j < m, ∀ v, vertexDegree (μ j) v = (-Real.log ρ) * ρ ^ j)
    (j : ℕ) (hj : j ≤ m) (v : V) : modelSequence μ j v = ρ ^ j := by
  induction j with
  | zero => simp [modelSequence]
  | succ j ih =>
    have hjm : j < m := by omega
    rw [modelSequence, nextModel, ih (by omega), hdegree j hjm v,
      mul_div_cancel_right₀ _ (pow_ne_zero j hρ.ne'), neg_neg, Real.exp_log hρ, pow_succ]

noncomputable def geometric_round_bounds (μ : ℕ → I → FiniteLaw (Finset V))
    {m r : ℕ} {ρ δ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 ≤ δ)
    (hdegree : ∀ j < m, ∀ v, vertexDegree (μ j) v = (-Real.log ρ) * ρ ^ j)
    (scale : ℕ → I → ℝ)
    (hsize : ∀ j < m, ∀ i e, 0 < (μ j i).weight e → e.card ≤ r)
    (hmarginal : ∀ j < m, ∀ i v, (μ j i).prob (fun e => v ∈ e) ≤ scale j i)
    (hscale : ∀ j < m, ∀ i, scale j i ≤ δ)
    (hsquare : ∀ j < m, (∑ i, scale j i ^ 2) ≤ δ ^ 2)
    (hpair : ∀ j < m, ∀ v w, v ≠ w → pairDegree (μ j) v w ≤ δ)
    (j : ℕ) (hj : j < m) :
    RoundBounds (μ j) (modelSequence μ j) r (ρ ^ m) δ (-Real.log ρ) := by
  refine ⟨pow_pos hρ0 m, pow_le_one₀ hρ0.le hρ1, hδ,
    neg_nonneg.mpr (Real.log_nonpos hρ0.le hρ1), ?_, ?_,
    hsize j hj, scale j, hmarginal j hj, hscale j hj, hsquare j hj, hpair j hj, ?_⟩
  · intro v
    rw [modelSequence_eq_geometric μ hρ0 hdegree j hj.le v]
    exact pow_le_pow_of_le_one hρ0.le hρ1 hj.le
  · intro v
    rw [modelSequence_eq_geometric μ hρ0 hdegree j hj.le v]
    exact pow_le_one₀ hρ0.le hρ1
  · intro v
    rw [modelSequence_eq_geometric μ hρ0 hdegree j hj.le v, hdegree j hj v,
      mul_div_cancel_right₀ _ (pow_ne_zero j hρ0.ne')]

theorem geometric_degree_covering (μ : ℕ → I → FiniteLaw (Finset V))
    {m r : ℕ} (hr : 1 ≤ r) {ρ δ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 ≤ δ)
    (hdegree : ∀ j < m, ∀ v, vertexDegree (μ j) v = (-Real.log ρ) * ρ ^ j)
    (scale : ℕ → I → ℝ)
    (hsize : ∀ j < m, ∀ i e, 0 < (μ j i).weight e → e.card ≤ r)
    (hmarginal : ∀ j < m, ∀ i v, (μ j i).prob (fun e => v ∈ e) ≤ scale j i)
    (hscale : ∀ j < m, ∀ i, scale j i ≤ δ)
    (hsquare : ∀ j < m, (∑ i, scale j i ^ 2) ≤ δ ^ 2)
    (hpair : ∀ j < m, ∀ v w, v ≠ w → pairDegree (μ j) v w ≤ δ)
    (hsparse : δ ≤ coveringThreshold r (2 * r) (ρ ^ m) (-Real.log ρ) ^ (4 * 8 ^ m)) :
    ∃ choice : ℕ → I → Finset V,
      (∀ j < m, ∀ i, choice j i = ∅ ∨ 0 < (μ j i).weight (choice j i)) ∧
        ((Finset.univ \ coveredThrough choice m).card : ℝ) ≤
          2 * (Fintype.card V : ℝ) * ρ ^ m := by
  obtain ⟨choice, hlegal, hcard⟩ := finite_covering μ
    (pow_pos hρ0 m) hδ (neg_nonneg.mpr (Real.log_nonpos hρ0.le hρ1))
    (by omega : 1 ≤ 2 * r) le_rfl hsparse
    (geometric_round_bounds μ hρ0 hρ1 hδ hdegree scale hsize hmarginal hscale hsquare hpair)
  refine ⟨choice, hlegal, ?_⟩
  have hmodel : ∀ v, modelSequence μ m v = ρ ^ m :=
    modelSequence_eq_geometric μ hρ0 hdegree m le_rfl
  simpa only [hmodel, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hcard

end Erdos4.FGKMT
