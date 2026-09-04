import ErdosProblems.Erdos988

open Filter Finset Topology
open scoped BigOperators

namespace Erdos991EnergyFromLog

noncomputable section

open Erdos988

/-- The nonnegative excess of the `k`-th shifted-inner-product moment over
the uniform-sphere value. -/
def momentGap (P : Finset S2) (k : ℕ) : ℝ :=
  powerSum P k - (P.card : ℝ) ^ 2 / (k + 1)

/-- The logarithmically weighted moment excess through degree `K`. -/
def truncatedLogGap (P : Finset S2) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K, momentGap P k / k

/-- The truncated logarithmic series with the diagonal terms removed. -/
def truncatedOffDiagonalLogMoment (P : Finset S2) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K, (powerSum P k - P.card) / k

lemma momentGap_nonneg (P : Finset S2) (k : ℕ) : 0 ≤ momentGap P k := by
  exact sub_nonneg.mpr (powerSum_welch_bound P k)

lemma powerSum_le_card_sq (P : Finset S2) (k : ℕ) :
    powerSum P k ≤ (P.card : ℝ) ^ 2 := by
  classical
  rw [powerSum]
  calc
    ∑ x ∈ P, ∑ y ∈ P, normalizedDot x y ^ k ≤
        ∑ x ∈ P, ∑ _y ∈ P, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact pow_le_one₀ (normalizedDot_nonneg x y) (normalizedDot_le_one x y)
    _ = (P.card : ℝ) ^ 2 := by simp [pow_two]

lemma momentGap_le_card_sq (P : Finset S2) (k : ℕ) :
    momentGap P k ≤ (P.card : ℝ) ^ 2 := by
  unfold momentGap
  have hden : 0 ≤ (P.card : ℝ) ^ 2 / (k + 1) := by positivity
  linarith [powerSum_le_card_sq P k]

lemma truncatedLogGap_nonneg (P : Finset S2) (K : ℕ) :
    0 ≤ truncatedLogGap P K := by
  unfold truncatedLogGap
  exact Finset.sum_nonneg fun k hk ↦
    div_nonneg (momentGap_nonneg P k) (Nat.cast_nonneg k)

lemma harmonic_cast_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  cases n with
  | zero => simp
  | succ n => exact_mod_cast (harmonic_pos (Nat.succ_ne_zero n)).le

lemma sum_Icc_one_div_mul_succ (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / ((k : ℝ) * (k + 1)) =
      (K : ℝ) / (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih]
      push_cast
      field_simp
      ring

lemma truncatedLogGap_eq_offDiagonal (P : Finset S2) (K : ℕ) :
    truncatedLogGap P K = truncatedOffDiagonalLogMoment P K +
      (P.card : ℝ) * (harmonic K : ℝ) -
      (P.card : ℝ) ^ 2 * (K : ℝ) / (K + 1) := by
  classical
  rw [truncatedLogGap, truncatedOffDiagonalLogMoment]
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
      momentGap P k / (k : ℝ) =
        (powerSum P k - P.card) / (k : ℝ) +
          (P.card : ℝ) * ((1 : ℝ) / k) -
          (P.card : ℝ) ^ 2 * (1 / ((k : ℝ) * (k + 1))) := by
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1)
    have hks0 : (k : ℝ) + 1 ≠ 0 := by positivity
    simp only [momentGap]
    field_simp
    ring
  have hsum :
      (∑ k ∈ Finset.Icc 1 K, momentGap P k / (k : ℝ)) =
        ∑ k ∈ Finset.Icc 1 K,
          ((powerSum P k - P.card) / (k : ℝ) +
            (P.card : ℝ) * ((1 : ℝ) / k) -
            (P.card : ℝ) ^ 2 * (1 / ((k : ℝ) * (k + 1)))) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k hk
  rw [hsum]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_Icc_one_div_mul_succ]
  have hharm : ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / k = (harmonic K : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      one_div]
  rw [hharm]
  ring

/-- The form of the Fekete logarithmic comparison needed downstream.
The right side is the continuous logarithmic average after removing the
diagonal; the exact telescoping diagonal correction then leaves at most
`n * harmonic n`. -/
lemma harmonic_log_bound_of_offDiagonal_bound
    (P : ℕ → Finset S2) (hcard : ∀ n, (P n).card = n)
    (hoff : ∀ n, truncatedOffDiagonalLogMoment (P n) n ≤
      (n : ℝ) * (n - 1)) :
    ∀ n, truncatedLogGap (P n) n ≤ (n : ℝ) * (harmonic n : ℝ) := by
  intro n
  rw [truncatedLogGap_eq_offDiagonal, hcard n]
  have hbase : (n : ℝ) * (n - 1) ≤ (n : ℝ) ^ 2 * (n : ℝ) / (n + 1) := by
    cases n with
    | zero => norm_num
    | succ n =>
        push_cast
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1 + 1)).2
        ring_nf
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
  linarith [hoff n]

lemma harmonic_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (harmonic n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have hlogReal : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogNat : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := hlogReal.comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hmajor : Tendsto (fun n : ℕ ↦ (1 + Real.log (n : ℝ)) / (n : ℝ))
      atTop (nhds 0) := by
    convert hone.add hlogNat using 1
    · funext n
      ring
    · ring_nf
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      div_nonneg (harmonic_cast_nonneg n) (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_le_div_of_nonneg_right (harmonic_le_one_add_log n)
      (Nat.cast_nonneg n)
  · exact hmajor

/-- The concrete logarithmic budget used for Fekete sets implies the
normalized-budget hypothesis below.  In the application, the Fekete
comparison and the diagonal correction give exactly
`truncatedLogGap (P n) n ≤ n * harmonic n`. -/
lemma log_budget_tendsto_of_harmonic_bound
    (P : ℕ → Finset S2)
    (hlog : ∀ n, truncatedLogGap (P n) n ≤ (n : ℝ) * (harmonic n : ℝ)) :
    Tendsto (fun n ↦ truncatedLogGap (P n) n / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      div_nonneg (truncatedLogGap_nonneg (P n) n) (sq_nonneg (n : ℝ))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      truncatedLogGap (P n) n / (n : ℝ) ^ 2 ≤
          ((n : ℝ) * (harmonic n : ℝ)) / (n : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right (hlog n) (sq_nonneg (n : ℝ))
      _ = (harmonic n : ℝ) / (n : ℝ) := by field_simp
  · exact harmonic_div_nat_tendsto_zero

/-- If the normalized logarithmic moment budget through degree `n` vanishes,
then every fixed normalized moment excess vanishes.  This is the finite-head
part of the logarithmic-to-chordal-energy argument. -/
lemma tendsto_normalized_momentGap_of_log_budget
    (P : ℕ → Finset S2)
    (hbudget : Tendsto
      (fun n ↦ truncatedLogGap (P n) n / (n : ℝ) ^ 2)
      atTop (nhds 0))
    (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n ↦ momentGap (P n) k / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      div_nonneg (momentGap_nonneg (P n) k) (sq_nonneg (n : ℝ))
  · filter_upwards [eventually_ge_atTop k] with n hn
    have hk_mem : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hk, hn⟩
    have hsingle : momentGap (P n) k / (k : ℝ) ≤ truncatedLogGap (P n) n := by
      unfold truncatedLogGap
      exact Finset.single_le_sum
        (s := Finset.Icc 1 n)
        (f := fun j ↦ momentGap (P n) j / (j : ℝ))
        (fun j hj ↦ div_nonneg (momentGap_nonneg (P n) j) (Nat.cast_nonneg j))
        hk_mem
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    calc
      momentGap (P n) k / (n : ℝ) ^ 2 =
          (k : ℝ) * ((momentGap (P n) k / (k : ℝ)) / (n : ℝ) ^ 2) := by
            field_simp
      _ ≤ (k : ℝ) * (truncatedLogGap (P n) n / (n : ℝ) ^ 2) := by
        gcongr
      _ = (fun n ↦ (k : ℝ) *
          (truncatedLogGap (P n) n / (n : ℝ) ^ 2)) n := rfl
  · simpa using hbudget.const_mul (k : ℝ)

/-- The exact finite-head/tail implication used for Erdős 991.

The hypothesis is the normalized truncated logarithmic budget naturally
obtained from the Fekete comparison inequality.  Positivity of all moment
gaps makes every fixed moment tend to zero.  Tannery's theorem then sums the
chordal expansion, dominated by the summable positive `chordCoeff` series. -/
theorem energyDeficit_div_sq_tendsto_zero_of_log_budget
    (P : ℕ → Finset S2) (hcard : ∀ n, (P n).card = n)
    (hbudget : Tendsto
      (fun n ↦ truncatedLogGap (P n) n / (n : ℝ) ^ 2)
      atTop (nhds 0)) :
    Tendsto (fun n ↦ energyDeficit (P n) / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  let f : ℕ → ℕ → ℝ := fun n r ↦
    chordCoeff r * (momentGap (P n) (r + 1) / (n : ℝ) ^ 2)
  have hcoeff : Summable chordCoeff := by
    simpa only [zero_add] using (hasSum_chordCoeff_nat_add 0).summable
  have hpoint (r : ℕ) : Tendsto (f · r) atTop (nhds 0) := by
    dsimp [f]
    simpa using (tendsto_normalized_momentGap_of_log_budget P hbudget
      (r + 1) (Nat.zero_lt_succ r)).const_mul (chordCoeff r)
  have hdom : ∀ n r, ‖f n r‖ ≤ chordCoeff r := by
    intro n r
    have hgap0 := momentGap_nonneg (P n) (r + 1)
    have hgap_le : momentGap (P n) (r + 1) ≤ (n : ℝ) ^ 2 := by
      simpa only [hcard n] using momentGap_le_card_sq (P n) (r + 1)
    have hratio0 : 0 ≤ momentGap (P n) (r + 1) / (n : ℝ) ^ 2 :=
      div_nonneg hgap0 (sq_nonneg (n : ℝ))
    have hratio1 : momentGap (P n) (r + 1) / (n : ℝ) ^ 2 ≤ 1 := by
      cases n with
      | zero =>
          have hz : momentGap (P 0) (r + 1) = 0 := le_antisymm (by simpa using hgap_le) hgap0
          simp [hz]
      | succ n =>
          apply (div_le_one (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2)).2
          simpa only [Nat.cast_add, Nat.cast_one] using hgap_le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (chordCoeff_pos r).le hratio0)]
    exact (mul_le_mul_of_nonneg_left hratio1 (chordCoeff_pos r).le).trans_eq (mul_one _)
  have htannery : Tendsto (fun n ↦ ∑' r, f n r) atTop (nhds 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
      hcoeff hpoint (Eventually.of_forall hdom)
  have hseries (n : ℕ) : HasSum (f n) (energyDeficit (P n) / (n : ℝ) ^ 2) := by
    have hs := (hasSum_energyDeficit (P n)).div_const ((n : ℝ) ^ 2)
    apply hs.congr
    intro s
    apply Finset.sum_congr rfl
    intro r hr
    simp only [f, momentGap, hcard n]
    push_cast
    ring
  convert htannery using 1
  funext n
  exact (hseries n).tsum_eq.symm

theorem energyDeficit_isLittleO_sq_of_log_budget
    (P : ℕ → Finset S2) (hcard : ∀ n, (P n).card = n)
    (hbudget : Tendsto
      (fun n ↦ truncatedLogGap (P n) n / (n : ℝ) ^ 2)
      atTop (nhds 0)) :
    (fun n ↦ energyDeficit (P n)) =o[atTop]
      (fun n ↦ (n : ℝ) ^ 2) := by
  have hzero : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 = 0 → energyDeficit (P n) = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn hzero
    exact (pow_ne_zero 2 (by exact_mod_cast hn.ne')).elim hzero
  exact (Asymptotics.isLittleO_iff_tendsto' hzero).2
    (energyDeficit_div_sq_tendsto_zero_of_log_budget P hcard hbudget)

theorem energyDeficit_isLittleO_sq_of_harmonic_log_bound
    (P : ℕ → Finset S2) (hcard : ∀ n, (P n).card = n)
    (hlog : ∀ n, truncatedLogGap (P n) n ≤
      (n : ℝ) * (harmonic n : ℝ)) :
    (fun n ↦ energyDeficit (P n)) =o[atTop]
      (fun n ↦ (n : ℝ) ^ 2) :=
  energyDeficit_isLittleO_sq_of_log_budget P hcard
    (log_budget_tendsto_of_harmonic_bound P hlog)

/-- The Fekete off-diagonal logarithmic bound directly implies that the
normalized chordal-energy deficit tends to zero. -/
theorem energyDeficit_div_sq_tendsto_zero_of_offDiagonal_log_bound
    (P : ℕ → Finset S2) (hcard : ∀ n, (P n).card = n)
    (hoff : ∀ n, truncatedOffDiagonalLogMoment (P n) n ≤
      (n : ℝ) * (n - 1)) :
    Tendsto (fun n ↦ energyDeficit (P n) / (n : ℝ) ^ 2)
      atTop (nhds 0) :=
  energyDeficit_div_sq_tendsto_zero_of_log_budget P hcard
    (log_budget_tendsto_of_harmonic_bound P
      (harmonic_log_bound_of_offDiagonal_bound P hcard hoff))

theorem energyDeficit_isLittleO_sq_of_offDiagonal_log_bound
    (P : ℕ → Finset S2) (hcard : ∀ n, (P n).card = n)
    (hoff : ∀ n, truncatedOffDiagonalLogMoment (P n) n ≤
      (n : ℝ) * (n - 1)) :
    (fun n ↦ energyDeficit (P n)) =o[atTop]
      (fun n ↦ (n : ℝ) ^ 2) :=
  energyDeficit_isLittleO_sq_of_harmonic_log_bound P hcard
    (harmonic_log_bound_of_offDiagonal_bound P hcard hoff)

end

end Erdos991EnergyFromLog
