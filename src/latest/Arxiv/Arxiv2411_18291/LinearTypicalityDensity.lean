import Arxiv.Arxiv2411_18291.TypicalityBounds

/-! # Density conversion with linear dependence on the neighborhood size

When the relative density error times the number of faces is small, taking
powers costs at most twice that product. This avoids the exponential factor
in the earlier, more general conversion estimate.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem relative_pow_error_linear {a b c : ℝ} {k h : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : |a - b| ≤ c * b) (hk : k ≤ h) (hsmall : c * h ≤ 1 / 2) :
    |a ^ k - b ^ k| ≤ (2 * c * h) * b ^ k := by
  obtain _ | j := k
  · simp only [pow_zero, sub_self, abs_zero, mul_one]
    positivity
  have hmax : max |a| |b| ≤ (1 + c) * b := by
    rw [abs_of_nonneg ha, abs_of_nonneg hb]
    have hu := (abs_le.mp hab).2
    exact max_le (by linarith only [hu]) (by nlinarith only [mul_nonneg hc hb])
  have hj : (j + 1 : ℝ) ≤ h := by exact_mod_cast hk
  have hpow : (1 + c) ^ j ≤ 2 := by
    have he : 1 + c ≤ Real.exp c := by linarith only [Real.add_one_le_exp c]
    have hjh : (j : ℝ) ≤ h := by exact_mod_cast Nat.le_of_succ_le hk
    calc
      _ ≤ (Real.exp c) ^ j := pow_le_pow_left₀ (by positivity) he j
      _ = Real.exp (c * j) := by rw [mul_comm, Real.exp_nat_mul]
      _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr
        ((mul_le_mul_of_nonneg_left hjh hc).trans hsmall)
      _ ≤ 2 := by
        convert Real.exp_bound_div_one_sub_of_interval
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
          using 1
        norm_num
  calc
    _ ≤ |a - b| * (j + 1) * max |a| |b| ^ j := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using
        (abs_pow_sub_pow_le (a := a) (b := b) (n := j + 1))
    _ ≤ (c * b) * h * ((1 + c) * b) ^ j := by gcongr
    _ = (c * h * (1 + c) ^ j) * b ^ (j + 1) := by
      rw [mul_pow, pow_succ]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hpow (mul_nonneg hc (Nat.cast_nonneg h))
      simpa only [mul_comm (c * h) 2, mul_assoc] using
        mul_le_mul_of_nonneg_right hh (pow_nonneg hb (j + 1))

variable {V : Type*} [Fintype V] [DecidableEq V] {r h : ℕ}

/-- Separate density and neighborhood errors before spending the final error budget. -/
theorem IsTypicalAt.to_isTypical_of_error_budget
    {G : Hypergraph V (r + 1)} {p c κ δ : ℝ}
    (hT : IsTypicalAt G p κ h) (hp : 0 ≤ p) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hd : |density G - p| ≤ c * p) (hsmall : c * h ≤ 1 / 2)
    (hbudget : κ + 2 * c * h ≤ δ * (1 - 2 * c * h)) :
    IsTypical G δ h := by
  intro A hA
  have hpow := relative_pow_error_linear (density_nonneg G) hp hc hd hA hsmall
  have hlow := (abs_le.mp hpow).1
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hscaled : |(Fintype.card V : ℝ) * p ^ A.card -
      Fintype.card V * density G ^ A.card| ≤
        Fintype.card V * ((2 * c * h) * p ^ A.card) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hn, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hpow hn
  have hB := mul_le_mul_of_nonneg_right hbudget
    (mul_nonneg hn (pow_nonneg hp A.card))
  have hL := mul_le_mul_of_nonneg_left hlow (mul_nonneg hδ hn)
  calc
    _ ≤ |(commonNeighbors G A).card - Fintype.card V * p ^ A.card| +
        |(Fintype.card V : ℝ) * p ^ A.card - Fintype.card V * density G ^ A.card| :=
      abs_sub_le _ _ _
    _ ≤ κ * (Fintype.card V * p ^ A.card) +
        Fintype.card V * ((2 * c * h) * p ^ A.card) := add_le_add (hT A hA) hscaled
    _ ≤ _ := by nlinarith only [hB, hL]

theorem IsTypicalAt.to_isTypical_linear {G : Hypergraph V (r + 1)} {p c : ℝ}
    (hT : IsTypicalAt G p (2 * c) h) (hp : 0 ≤ p) (hc : 0 ≤ c)
    (hd : |density G - p| ≤ c * p) (hsmall : c * h ≤ 1 / 4) :
    IsTypical G ((4 + 4 * h) * c) h := by
  intro A hA
  let η := 2 * c * h
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hpow := relative_pow_error_linear (density_nonneg G) hp hc hd hA
    (by linarith only [hsmall])
  change |density G ^ A.card - p ^ A.card| ≤ η * p ^ A.card at hpow
  have hratio : p ^ A.card ≤ 2 * density G ^ A.card := by
    have hl := (abs_le.mp hpow).1
    have hs := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hp A.card)
    dsimp only [η] at hl
    nlinarith only [hl, hs]
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hscaled : |(Fintype.card V : ℝ) * p ^ A.card -
      Fintype.card V * density G ^ A.card| ≤
        Fintype.card V * (η * p ^ A.card) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hn, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hpow hn
  calc
    _ ≤ |(commonNeighbors G A).card - Fintype.card V * p ^ A.card| +
        |(Fintype.card V : ℝ) * p ^ A.card - Fintype.card V * density G ^ A.card| :=
      abs_sub_le _ _ _
    _ ≤ (2 * c) * (Fintype.card V * p ^ A.card) +
        Fintype.card V * (η * p ^ A.card) := add_le_add (hT A hA) hscaled
    _ = (2 * c + η) * Fintype.card V * p ^ A.card := by ring
    _ ≤ (2 * c + η) * Fintype.card V * (2 * density G ^ A.card) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by dsimp only [η]; ring

theorem typical_failure_probability_linear (p : unitInterval) {c : ℝ} (hc : 0 ≤ c)
    (hn : r + 1 ≤ Fintype.card V)
    (hsize : (h * r : ℝ) ≤ c * Fintype.card V) (hsmall : c * h ≤ 1 / 4) :
    (BernoulliSubset.probability (Block V (r + 1)) p).real
      {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ c * p ∧
        IsTypical (sampleGraph ω) ((4 + 4 * h) * c) h)} ≤
      typicalFailureBound (Fintype.card V) r h p c := by
  let E := {ω : BernoulliSubset.Sample (Block V (r + 1)) |
    |((sampleGraph ω).card : ℝ) - (p : ℝ) * (Fintype.card V).choose (r + 1)| >
      c * ((p : ℝ) * (Fintype.card V).choose (r + 1))}
  let B := {ω : BernoulliSubset.Sample (Block V (r + 1)) |
    ¬ IsTypicalAt (sampleGraph ω) (p : ℝ) (2 * c) h}
  have hsub : {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ c * p ∧
      IsTypical (sampleGraph ω) ((4 + 4 * h) * c) h)} ⊆ E ∪ B := by
    intro ω hω
    by_cases hE : ω ∈ E
    · exact Or.inl hE
    · right
      change ¬ IsTypicalAt (sampleGraph ω) (p : ℝ) (2 * c) h
      intro hT
      have he : |((sampleGraph ω).card : ℝ) -
          (p : ℝ) * (Fintype.card V).choose (r + 1)| ≤
            c * ((p : ℝ) * (Fintype.card V).choose (r + 1)) := le_of_not_gt hE
      have hd := density_error_of_card_error (sampleGraph ω) hn he
      exact hω ⟨hd, hT.to_isTypical_linear p.property.1 hc hd hsmall⟩
  calc
    _ ≤ (BernoulliSubset.probability (Block V (r + 1)) p).real (E ∪ B) := measureReal_mono hsub
    _ ≤ (BernoulliSubset.probability (Block V (r + 1)) p).real E +
        (BernoulliSubset.probability (Block V (r + 1)) p).real B := measureReal_union_le E B
    _ ≤ _ := add_le_add (sampleGraph_card_concentration p hc)
      (typicalAt_failure_probability p hc hsize)

end Arxiv2411_18291
