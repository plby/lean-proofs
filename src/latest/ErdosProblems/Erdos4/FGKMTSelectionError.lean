import ErdosProblems.Erdos4.FGKMTSelection

/-!
# Error caused by trimming and normalizing a covering round

The selected edge law agrees with the raw reweighting up to the small
normalization error on good survivor sets. Bad survivor sets are charged
their probability, controlled by the two-moment concentration theorem.
-/

namespace Erdos4.FGKMT

theorem inverse_near_one {x t : ℝ} (ht : t ≤ 1 / 2) (hx : |x - 1| ≤ t) :
    |1 / x - 1| ≤ 2 * t := by
  have hbounds := abs_le.mp hx
  have hhalf : (1 / 2 : ℝ) ≤ x := by linarith
  have hpos : 0 < x := lt_of_lt_of_le (by norm_num) hhalf
  have ht0 : 0 ≤ t := (abs_nonneg _).trans hx
  have heq : 1 / x - 1 = (1 - x) / x := by field_simp
  rw [heq, abs_div, abs_of_pos hpos, abs_sub_comm 1 x]
  calc
    _ ≤ t / x := div_le_div_of_nonneg_right hx hpos.le
    _ ≤ t / (1 / 2) := div_le_div_of_nonneg_left ht0 (by norm_num) hhalf
    _ = _ := by ring

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem selection_event_error (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {κ t : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hp : ∀ v, κ ≤ p v) (hsize : ∀ e, 0 < μ.weight e → e.card ≤ r)
    (W : Finset V) (E : Finset V → Prop) (hE : ¬E ∅) :
    |(selectLaw μ p (fun v => hκ0.trans_le (hp v)) t W).prob E - eventNumerator μ p W E| ≤
      (2 * t + if t < |normalizer μ p W - 1| then 1 else 0) * (μ.prob E / κ ^ r) := by
  classical
  have hp0 : ∀ v, 0 < p v := fun v => hκ0.trans_le (hp v)
  have hnum0 := eventNumerator_nonneg μ p hp0 W E
  have hnum := eventNumerator_le μ p hκ0 hκ1 hp hsize W E
  rw [selectLaw_event μ p hp0 (by linarith : t < 1) W E hE]
  by_cases hgood : |normalizer μ p W - 1| ≤ t
  · rw [if_pos hgood, if_neg (not_lt_of_ge hgood), add_zero]
    have heq : eventNumerator μ p W E / normalizer μ p W - eventNumerator μ p W E =
        eventNumerator μ p W E * (1 / normalizer μ p W - 1) := by ring
    rw [heq, abs_mul, abs_of_nonneg hnum0]
    calc
      _ ≤ eventNumerator μ p W E * (2 * t) :=
        mul_le_mul_of_nonneg_left (inverse_near_one ht1 hgood) hnum0
      _ ≤ (μ.prob E / κ ^ r) * (2 * t) := mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = _ := by ring
  · have hbad : t < |normalizer μ p W - 1| := lt_of_not_ge hgood
    rw [if_neg hgood, if_pos hbad, zero_sub, abs_neg, abs_of_nonneg hnum0]
    have hB : 0 ≤ μ.prob E / κ ^ r := div_nonneg (μ.prob_nonneg E) (pow_pos hκ0 r).le
    exact hnum.trans (by nlinarith)

theorem mean_selection_event_error (ν μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {κ t δ ε : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hp : ∀ v, κ ≤ p v)
    (hsize : ∀ e, 0 < μ.weight e → e.card ≤ r)
    (hsparse : ∀ v : V, μ.prob (fun f => v ∈ f) ≤ δ)
    (hacc : SurvivalAccurate ν p (2 * r) ε) (E : Finset V → Prop) (hE : ¬E ∅) :
    ν.mean (fun W => |(selectLaw μ p (fun v => hκ0.trans_le (hp v)) t W).prob E -
        eventNumerator μ p W E|) ≤
      (2 * t + (3 * ε + (1 + ε) * (r : ℝ) * δ / κ ^ r) / t ^ 2) * (μ.prob E / κ ^ r) := by
  classical
  have hB : 0 ≤ μ.prob E / κ ^ r := div_nonneg (μ.prob_nonneg E) (pow_pos hκ0 r).le
  have hbad : ν.prob (fun W => t < |normalizer μ p W - 1|) ≤
      (3 * ε + (1 + ε) * (r : ℝ) * δ / κ ^ r) / t ^ 2 :=
    (ν.prob_mono (fun W hW => hW.le)).trans
      (normalizer_concentration ν μ p hκ0 hκ1 hδ hε ht0 hp hsize hsparse hacc)
  calc
    _ ≤ ν.mean (fun W => (2 * t + if t < |normalizer μ p W - 1| then 1 else 0) *
        (μ.prob E / κ ^ r)) :=
      ν.mean_mono (fun W => selection_event_error μ p hκ0 hκ1 ht0.le ht1 hp hsize W E hE)
    _ = (2 * t + ν.prob (fun W => t < |normalizer μ p W - 1|)) * (μ.prob E / κ ^ r) := by
      rw [FiniteLaw.mean_mul_const, FiniteLaw.mean_add, FiniteLaw.mean_const,
        ← FiniteLaw.prob_eq_mean]
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add le_rfl hbad) hB

end Erdos4.FGKMT
