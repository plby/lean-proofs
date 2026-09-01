import ErdosProblems.Erdos491.PrimeDensity
import ErdosProblems.Erdos491.DensityContradiction
import ErdosProblems.Erdos491.Normalization
import ErdosProblems.Erdos491.Exclusion

/-! # Unconditional logarithmic rigidity -/

open Filter
open scoped BigOperators Topology

namespace Erdos491

theorem normalized_completely_additive_eq_zero {h : ℕ → ℝ}
    (hh : PosCompletelyAdditive h) {K : ℝ} (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, 0 < n → |h (n + 1) - h n| ≤ K)
    (hnonneg : ∀ n : ℕ, 0 < n → 0 ≤ h n)
    (hlow : ∀ ε : ℝ, 0 < ε → ∃ p : ℕ, p.Prime ∧ h p < ε * Real.log (p : ℝ)) :
    ∀ n : ℕ, 0 < n → h n = 0 := by
  classical
  apply hh.eq_zero_of_prime
  intro p₀ hp₀
  by_contra hne
  have hp₀val : 0 < h p₀ := lt_of_le_of_ne (hnonneg p₀ hp₀.pos) (Ne.symm hne)
  have hlogp₀ : 0 < Real.log (p₀ : ℝ) := Real.log_pos (by exact_mod_cast hp₀.one_lt)
  let b : ℝ := h p₀ / (2 * Real.log (p₀ : ℝ))
  have hb : 0 < b := div_pos hp₀val (mul_pos (by norm_num) hlogp₀)
  have hbval : 0 < h p₀ - b * Real.log (p₀ : ℝ) := by
    have heq : h p₀ - b * Real.log (p₀ : ℝ) = h p₀ / 2 := by
      dsimp [b]
      field_simp
      ring
    rw [heq]
    positivity
  let ε : ℝ := b / 8
  have hε : 0 < ε := div_pos hb (by norm_num)
  let v : ℕ → ℝ := fun n ↦ h n - b * Real.log (n : ℝ)
  let w : ℕ → ℝ := fun n ↦ ε * Real.log (n : ℝ) - h n
  have hv : PosCompletelyAdditive v := hh.sub_const_mul_log b
  have hw : PosCompletelyAdditive w := hh.const_log_sub ε
  have hKv : 0 ≤ K + |b| * Real.log 2 := by positivity
  have hKw : 0 ≤ K + |ε| * Real.log 2 := by positivity
  obtain ⟨p₁, hp₁, hp₁low⟩ := hlow ε hε
  have hp₁val : 0 < w p₁ := by dsimp [w]; linarith
  obtain ⟨L₁, hL₁, d₁, hd₁, hdenseP⟩ :=
    positive_prime_density hw hKw (const_log_sub_gap_bound hgap ε) hp₁ hp₁val
  obtain ⟨L₂, hL₂, d₂, hd₂, hdenseQ⟩ :=
    positive_prime_density hv hKv (sub_log_forward_difference_bound hgap b) hp₀ hbval
  obtain ⟨C, hC, hgrowth⟩ := hh.exists_log_bound hK hgap
  obtain ⟨r : ℕ, hr⟩ := exists_nat_gt (4 * C / b)
  let k := r + 2
  have hk : 0 < k := by dsimp [k]; omega
  have hCk : C < b * (k : ℝ) / 4 := by
    have h := (div_lt_iff₀ hb).mp hr
    dsimp [k]
    push_cast
    nlinarith
  have hPk : ∀ᶠ X : ℕ in atTop,
      d₁ * (((X ^ k) ^ 4 : ℕ) : ℝ) ≤
        ((positivePrimesBetween w ((X ^ k) ^ 4) (L₁ * (X ^ k) ^ 4)).card : ℝ) *
          Real.log (((X ^ k) ^ 4 : ℕ) : ℝ) :=
    ((tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp
      (tendsto_pow_atTop hk.ne')).eventually hdenseP
  have hQk : ∀ᶠ X : ℕ in atTop,
      d₂ * ((X ^ k : ℕ) : ℝ) ≤
        ((positivePrimesBetween v (X ^ k) (L₂ * X ^ k)).card : ℝ) *
          Real.log ((X ^ k : ℕ) : ℝ) :=
    (tendsto_pow_atTop hk.ne').eventually hdenseQ
  have hbig : ∀ᶠ X : ℕ in atTop,
      b / 8 * Real.log (L₁ : ℝ) + K < b * (k : ℝ) / 4 * Real.log (X : ℝ) := by
    have ht : Tendsto (fun X : ℕ ↦ b * (k : ℝ) / 4 * Real.log (X : ℝ)) atTop atTop :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
        (by positivity : 0 < b * (k : ℝ) / 4)
    exact ht.eventually_gt_atTop _
  apply not_dense_affine_avoidance k L₁ L₂
    (dP := d₁ / (4 * (k : ℝ))) (dQ := d₂ / (k : ℝ)) (by positivity) (by positivity)
  filter_upwards [hPk, hQk, hbig, eventually_ge_atTop (2 : ℕ)] with X hPd hQd hbigX hX
  let P := positivePrimesBetween w ((X ^ k) ^ 4) (L₁ * (X ^ k) ^ 4)
  let Q := positivePrimesBetween v (X ^ k) (L₂ * X ^ k)
  have hPmem (p : ℕ) (hp : p ∈ P) :
      p.Prime ∧ (X ^ k) ^ 4 < p ∧ p ≤ L₁ * (X ^ k) ^ 4 ∧
        h p < b / 8 * Real.log (p : ℝ) := by
    have h := (mem_positivePrimesBetween w ((X ^ k) ^ 4) (L₁ * (X ^ k) ^ 4) p).mp hp
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    have hh := h.2.2.2
    change 0 < ε * Real.log (p : ℝ) - _ at hh
    dsimp [ε] at hh
    linarith
  have hQmem (q : ℕ) (hq : q ∈ Q) :
      q.Prime ∧ X ^ k < q ∧ q ≤ L₂ * X ^ k ∧ b * Real.log (q : ℝ) < h q := by
    have h := (mem_positivePrimesBetween v (X ^ k) (L₂ * X ^ k) q).mp hq
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    have hh := h.2.2.2
    change 0 < _ - b * Real.log (q : ℝ) at hh
    linarith
  refine ⟨P, Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hqm := hQmem q hq
    refine ⟨hqm.1, ?_, hqm.2.2.1⟩
    have hXXk : X ≤ X ^ k := le_self_pow (by omega : 1 ≤ X) hk.ne'
    exact hXXk.trans_lt hqm.2.1
  · intro p hp
    exact Finset.mem_range.mpr (by have := (hPmem p hp).2.2.1; omega)
  · change d₁ * (((X ^ k) ^ 4 : ℕ) : ℝ) ≤
        (P.card : ℝ) * Real.log (((X ^ k) ^ 4 : ℕ) : ℝ) at hPd
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at hPd
    calc
      (d₁ / (4 * (k : ℝ))) * ((X ^ k : ℕ) : ℝ) ^ 4 =
          (d₁ * ((X ^ k : ℕ) : ℝ) ^ 4) / (4 * (k : ℝ)) := by ring
      _ ≤ (P.card : ℝ) * Real.log (X : ℝ) := by
        apply (div_le_iff₀ (by positivity : 0 < 4 * (k : ℝ))).mpr
        push_cast
        nlinarith
  · change d₂ * ((X ^ k : ℕ) : ℝ) ≤
        (Q.card : ℝ) * Real.log ((X ^ k : ℕ) : ℝ) at hQd
    simp only [Nat.cast_pow, Real.log_pow] at hQd
    calc
      (d₂ / (k : ℝ)) * ((X ^ k : ℕ) : ℝ) =
          (d₂ * ((X ^ k : ℕ) : ℝ)) / (k : ℝ) := by ring
      _ ≤ (Q.card : ℝ) * Real.log (X : ℝ) := by
        apply (div_le_iff₀ (by positivity : 0 < (k : ℝ))).mpr
        push_cast
        nlinarith
  · intro p hp q hq u hu huX
    have hpm := hPmem p hp
    have hqm := hQmem q hq
    exact exclude_affine_divisor hh hnonneg hC.le hb hgap hgrowth
      (by omega : 0 < L₁) hX hCk hbigX hpm.1.pos hpm.2.2.1 hpm.2.2.2
      hqm.1.pos hqm.2.1.le hqm.2.2.2 hu huX

theorem completely_additive_bounded_gap_rigidity :
    CompletelyAdditiveBoundedGapRigidity := by
  intro g K hg hK hgap
  obtain ⟨C, _hC, hgrowth⟩ := hg.exists_log_bound hK hgap
  obtain ⟨c, hnonneg, hlow⟩ := exists_prime_slope_normalization hg hgrowth
  have hK' : 0 ≤ K + |c| * Real.log 2 := by positivity
  have hz := normalized_completely_additive_eq_zero (hg.sub_const_mul_log c) hK'
    (sub_log_forward_difference_bound hgap c) hnonneg hlow
  refine ⟨c, fun n hn ↦ ?_⟩
  exact sub_eq_zero.mp (hz n hn)

end Erdos491
