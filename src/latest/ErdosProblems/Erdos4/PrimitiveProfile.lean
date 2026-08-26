import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# A monotone primitive profile for the multidimensional sieve

The profile is chosen so that its primitive divided by the profile is an
elementary rational expression. The parameters are real here; the eventual
dimension will be an integer chosen after the desired gain.
-/

open scoped BigOperators

namespace Erdos4.PrimitiveProfile

noncomputable def primitive (m k t : ℝ) : ℝ :=
  t * (1 + 4 * m * k * t) ^ (1 / m - 1)

noncomputable def profile (m k t : ℝ) : ℝ :=
  (1 + 4 * k * t) * (1 + 4 * m * k * t) ^ (1 / m - 2)

theorem base_pos {m k t : ℝ} (hm : 0 ≤ m) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    0 < 1 + 4 * m * k * t := by positivity

theorem profile_pos {m k t : ℝ} (hm : 0 ≤ m) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    0 < profile m k t := by
  unfold profile
  exact mul_pos (by positivity) (Real.rpow_pos_of_pos (base_pos hm hk ht) _)

theorem primitive_nonneg {m k t : ℝ} (hm : 0 ≤ m) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    0 ≤ primitive m k t := by
  exact mul_nonneg ht (Real.rpow_nonneg (base_pos hm hk ht).le _)

theorem profile_zero (m k : ℝ) : profile m k 0 = 1 := by simp [profile]

theorem primitive_zero (m k : ℝ) : primitive m k 0 = 0 := by simp [primitive]

theorem power_shift {m k t : ℝ} (hb : 0 < 1 + 4 * m * k * t) :
    (1 + 4 * m * k * t) ^ (1 / m - 1) =
      (1 + 4 * m * k * t) ^ (1 / m - 2) * (1 + 4 * m * k * t) := by
  rw [show 1 / m - 1 = (1 / m - 2) + 1 by ring]
  exact Real.rpow_add_one hb.ne' _

theorem profile_decomposition {m k t : ℝ} (hm : m ≠ 0)
    (hb : 0 < 1 + 4 * m * k * t) :
    profile m k t =
      (1 / m) * (1 + 4 * m * k * t) ^ (1 / m - 1) +
      (1 - 1 / m) * (1 + 4 * m * k * t) ^ (1 / m - 2) := by
  unfold profile
  rw [power_shift hb]
  field_simp
  ring

/-- The rational identity responsible for large gain on the dense half of
the simplex. -/
theorem primitive_div_profile {m k t : ℝ}
    (hm : 0 < m) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    primitive m k t / profile m k t =
      m * t - (m - 1) * t / (1 + 4 * k * t) := by
  have hb := base_pos hm.le hk ht
  have hp := Real.rpow_pos_of_pos hb (1 / m - 2)
  have hd : 0 < 1 + 4 * k * t := by positivity
  unfold primitive profile
  rw [power_shift hb]
  field_simp
  ring

theorem profile_antitoneOn {m k : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k) :
    AntitoneOn (profile m k) (Set.Ici 0) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hδ0 : 0 ≤ 1 / m := (one_div_pos.mpr hmpos).le
  have hδ1 : 1 / m ≤ 1 := (div_le_one hmpos).mpr hm
  intro s hs t ht hst
  have hbs := base_pos hmpos.le hk hs
  have hbt := base_pos hmpos.le hk ht
  have hbase : 1 + 4 * m * k * s ≤ 1 + 4 * m * k * t := by
    nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 4 * m) hk) (sub_nonneg.mpr hst)]
  rw [profile_decomposition hmpos.ne' hbs, profile_decomposition hmpos.ne' hbt]
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hbs hbase (by linarith : 1 / m - 1 ≤ 0)) hδ0)
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hbs hbase (by linarith : 1 / m - 2 ≤ 0))
      (sub_nonneg.mpr hδ1))

theorem profile_le_one {m k t : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    profile m k t ≤ 1 := by
  simpa only [profile_zero] using profile_antitoneOn hm hk (by simp) ht ht

theorem profile_one_le {m k t : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : profile m k 1 ≤ profile m k t :=
  profile_antitoneOn hm hk ht0 (by norm_num) ht1

theorem continuousAt_profile {m k t : ℝ} (hm : 0 ≤ m) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    ContinuousAt (profile m k) t := by
  have h1 : ContinuousAt (fun u : ℝ => 1 + 4 * k * u) t := by fun_prop
  have h2 : ContinuousAt (fun u : ℝ => 1 + 4 * m * k * u) t := by fun_prop
  exact h1.mul (h2.rpow_const (Or.inl (base_pos hm hk ht).ne'))

theorem hasDerivAt_primitive {m k t : ℝ} (hm : 0 < m) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    HasDerivAt (primitive m k) (profile m k t) t := by
  have hb := base_pos hm.le hk ht
  have hlin : HasDerivAt (fun u : ℝ => 1 + 4 * m * k * u) (4 * m * k) t := by
    simpa using ((hasDerivAt_id t).const_mul (4 * m * k)).const_add 1
  have h := (hasDerivAt_id t).mul (hlin.rpow_const (p := 1 / m - 1) (Or.inl hb.ne'))
  simp only [one_mul, id_eq] at h
  change HasDerivAt (primitive m k)
    ((1 + 4 * m * k * t) ^ (1 / m - 1) +
      t * (4 * m * k * (1 / m - 1) * (1 + 4 * m * k * t) ^ (1 / m - 1 - 1))) t at h
  have heq : profile m k t =
      (1 + 4 * m * k * t) ^ (1 / m - 1) +
      t * (4 * m * k * (1 / m - 1) * (1 + 4 * m * k * t) ^ (1 / m - 1 - 1)) := by
    unfold profile
    rw [power_shift hb, show 1 / m - 1 - 1 = 1 / m - 2 by ring]
    field_simp
    ring
  rw [heq]
  exact h

theorem primitive_strictMonoOn {m k : ℝ} (hm : 0 < m) (hk : 0 ≤ k) :
    StrictMonoOn (primitive m k) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro t ht
    exact (hasDerivAt_primitive hm hk ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := interior_subset ht
    rw [(hasDerivAt_primitive hm hk ht0).deriv]
    exact profile_pos hm.le hk ht0

theorem integral_profile {m k t : ℝ} (hm : 0 < m) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, profile m k u) = primitive m k t := by
  have hu : ∀ u ∈ Set.uIcc (0 : ℝ) t, 0 ≤ u := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    exact hu.1
  have hc : ContinuousOn (profile m k) (Set.uIcc (0 : ℝ) t) := by
    intro u huu
    exact (continuousAt_profile hm.le hk (hu u huu)).continuousWithinAt
  simpa only [primitive_zero, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u huu => hasDerivAt_primitive hm hk (hu u huu)) hc.intervalIntegrable

/-- Each coordinate loses at most `1 / (4k)` in the rational correction. -/
theorem correction_le {k t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) :
    t / (1 + 4 * k * t) ≤ 1 / (4 * k) := by
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + 4 * k * t)
    (by positivity : 0 < 4 * k)).mpr
  nlinarith

/-- Large gain when the total coordinate mass is at least one half. -/
theorem dense_gain {m : ℝ} {k : ℕ} (hm : 1 ≤ m) (hk : 0 < k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 ≤ t i) (hS : 1 / 2 ≤ ∑ i, t i) :
    m / 4 ≤ ∑ i, primitive m k (t i) / profile m k (t i) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hcorr : (∑ i : Fin k, t i / (1 + 4 * (k : ℝ) * t i)) ≤ 1 / 4 := by
    calc
      (∑ i : Fin k, t i / (1 + 4 * (k : ℝ) * t i)) ≤
          ∑ _i : Fin k, 1 / (4 * (k : ℝ)) :=
        Finset.sum_le_sum (fun i _hi => correction_le hkpos (ht i))
      _ = 1 / 4 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have heq : (∑ i, primitive m k (t i) / profile m k (t i)) =
      m * ∑ i, t i - (m - 1) * ∑ i, t i / (1 + 4 * (k : ℝ) * t i) := by
    simp_rw [primitive_div_profile hmpos hkpos.le (ht _)]
    simp only [mul_div_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [heq]
  have h1 := mul_le_mul_of_nonneg_left hS hmpos.le
  have h2 := mul_le_mul_of_nonneg_left hcorr (sub_nonneg.mpr hm)
  nlinarith

/-- The dimension condition makes the sparse half of the simplex contribute
the desired gain too. -/
theorem sparse_gain {m k : ℝ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hdim : m ^ 2 ≤ (4 * m * k) ^ (1 / m)) :
    m / 8 ≤ k * primitive m k (1 / 2) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hmk : 1 ≤ m * k := by nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hk)]
  have hδ : 1 / m ≤ 1 := (div_le_one hmpos).mpr hm
  have hb : 0 < 1 + 4 * m * k * (1 / 2) := by positivity
  have hbase : 1 + 4 * m * k * (1 / 2) ≤ 4 * m * k := by nlinarith
  have hp := Real.rpow_le_rpow_of_nonpos hb hbase (by linarith : 1 / m - 1 ≤ 0)
  have heq : k * ((1 / 2) * (4 * m * k) ^ (1 / m - 1)) =
      (4 * m * k) ^ (1 / m) / (8 * m) := by
    rw [Real.rpow_sub_one (by positivity : 4 * m * k ≠ 0)]
    field_simp
    ring
  calc
    m / 8 ≤ (4 * m * k) ^ (1 / m) / (8 * m) := by
      apply (le_div_iff₀ (by positivity : 0 < 8 * m)).mpr
      nlinarith
    _ = k * ((1 / 2) * (4 * m * k) ^ (1 / m - 1)) := heq.symm
    _ ≤ k * primitive m k (1 / 2) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by norm_num)) hkpos.le

/-- The pointwise simplex inequality: no multidimensional integral or
concentration theorem is needed for this variational gain. -/
theorem pointwise_gain {m : ℝ} {k : ℕ} (hm : 1 ≤ m) (hk : 0 < k)
    (hdim : m ^ 2 ≤ (4 * m * (k : ℝ)) ^ (1 / m))
    (t : Fin k → ℝ) (ht : ∀ i, 0 ≤ t i) (hS : ∑ i, t i ≤ 1) :
    m / 8 ≤ ∑ i, primitive m k (1 - (∑ j, t j) + t i) / profile m k (t i) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hmon := (primitive_strictMonoOn hmpos hkpos.le).monotoneOn
  by_cases hhalf : (∑ i, t i) ≤ 1 / 2
  · have hsparse := sparse_gain hm (by exact_mod_cast hk) hdim
    have hcoord : ∀ i, primitive m k (1 / 2) ≤
        primitive m k (1 - (∑ j, t j) + t i) / profile m k (t i) := by
      intro i
      have hv : 1 / 2 ≤ 1 - (∑ j, t j) + t i := by linarith [ht i]
      have hgp := profile_pos hmpos.le hkpos.le (ht i)
      apply (le_div_iff₀ hgp).mpr
      calc
        primitive m k (1 / 2) * profile m k (t i) ≤ primitive m k (1 / 2) * 1 :=
          mul_le_mul_of_nonneg_left (profile_le_one hm hkpos.le (ht i))
            (primitive_nonneg hmpos.le hkpos.le (by norm_num))
        _ = primitive m k (1 / 2) := mul_one _
        _ ≤ primitive m k (1 - (∑ j, t j) + t i) :=
          hmon (by norm_num) (show 0 ≤ 1 - (∑ j, t j) + t i by linarith) hv
    have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hcoord i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    exact hsparse.trans hsum
  · have hdense := dense_gain hm hk t ht (le_of_lt (lt_of_not_ge hhalf))
    have hcoord : ∀ i, primitive m k (t i) / profile m k (t i) ≤
        primitive m k (1 - (∑ j, t j) + t i) / profile m k (t i) := by
      intro i
      apply div_le_div_of_nonneg_right _ (profile_pos hmpos.le hkpos.le (ht i)).le
      exact hmon (ht i) (show 0 ≤ 1 - (∑ j, t j) + t i by linarith [ht i]) (by linarith)
    have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hcoord i)
    exact (by linarith : m / 8 ≤ m / 4).trans (hdense.trans hsum)

theorem exists_dimension {m : ℝ} (hm : 1 ≤ m) :
    ∃ k : ℕ, 0 < k ∧ m ^ 2 ≤ (4 * m * (k : ℝ)) ^ (1 / m) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ((m ^ 2) ^ m / (4 * m)))
  have hk1 : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkpos : 0 < k := by exact_mod_cast (lt_trans zero_lt_one hk1)
  have hpow : (m ^ 2) ^ m ≤ 4 * m * (k : ℝ) := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 4 * m)).mp ((le_max_right _ _).trans_lt hk)
    nlinarith
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (sq_nonneg m) m) hpow
    (one_div_pos.mpr hmpos).le
  rw [← Real.rpow_mul (sq_nonneg m), mul_one_div_cancel hmpos.ne', Real.rpow_one] at hroot
  exact ⟨k, hkpos, hroot⟩

/-- Unbounded pointwise gain, with the dimension fixed after the requested
constant and before any sieve parameter tends to infinity. -/
theorem exists_arbitrary_gain (M : ℝ) :
    ∃ m : ℝ, ∃ k : ℕ, 1 ≤ m ∧ 0 < k ∧
      ∀ t : Fin k → ℝ, (∀ i, 0 ≤ t i) → (∑ i, t i) ≤ 1 →
        M < ∑ i, primitive m k (1 - (∑ j, t j) + t i) / profile m k (t i) := by
  let m : ℝ := 8 * (|M| + 1)
  have hm : 1 ≤ m := by dsimp [m]; linarith [abs_nonneg M]
  obtain ⟨k, hk, hdim⟩ := exists_dimension hm
  refine ⟨m, k, hm, hk, ?_⟩
  intro t ht hS
  have hgain := pointwise_gain hm hk hdim t ht hS
  have hM : M < m / 8 := by dsimp [m]; linarith [le_abs_self M]
  exact hM.trans_le hgain

end Erdos4.PrimitiveProfile
