/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 542.
https://www.erdosproblems.com/forum/thread/542

Informal authors:
- Andrzej Schinzel
- György Szekeres

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos542.md
-/
import ErdosProblems.Erdos542.Erdos542Basic
import ErdosProblems.Erdos202

open Finset Set
open scoped BigOperators ArithmeticFunction.Omega

namespace Erdos542

lemma harmonic_band_lower (L V : ℕ) (hL : 1 ≤ L) (hLV : L ≤ V) :
    Real.log (((V + 1 : ℕ) : ℝ) / ((L + 1 : ℕ) : ℝ)) ≤
      ∑ k ∈ Finset.Ioc L V, (1 : ℝ) / k := by
  have hposL : 0 < ((L + 1 : ℕ) : ℝ) := by positivity
  have hposV : 0 < ((V + 1 : ℕ) : ℝ) := by positivity
  calc
    Real.log (((V + 1 : ℕ) : ℝ) / ((L + 1 : ℕ) : ℝ)) =
        ∫ x in ((L + 1 : ℕ) : ℝ)..((V + 1 : ℕ) : ℝ), x⁻¹ := by
          have hz : 0 ∉ Set.uIcc (((L + 1 : ℕ) : ℝ)) (((V + 1 : ℕ) : ℝ)) := by
            rw [Set.uIcc_of_le (by exact_mod_cast Nat.add_le_add_right hLV 1)]
            intro hm
            exact (not_lt_of_ge hm.1) hposL
          rw [integral_inv hz]
    _ ≤ ∑ k ∈ Finset.Ico (L + 1) (V + 1), ((k : ℝ)⁻¹) := by
          exact (inv_antitoneOn_Icc_right (by positivity)).integral_le_sum_Ico
            (Nat.add_le_add_right hLV 1)
    _ = ∑ k ∈ Finset.Ioc L V, (1 : ℝ) / k := by
          rw [Finset.Ico_add_one_right_eq_Icc, Finset.Icc_add_one_left_eq_Ioc]
          simp [one_div]

lemma harmonic_band_upper (L V : ℕ) (hL : 1 ≤ L) (hLV : L ≤ V) :
    (∑ k ∈ Finset.Ioc L V, (1 : ℝ) / k) ≤
      Real.log ((V : ℝ) / (L : ℝ)) := by
  have hposL : 0 < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hposV : 0 < (V : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hL.trans hLV))
  calc
    (∑ k ∈ Finset.Ioc L V, (1 : ℝ) / k) =
        ∑ i ∈ Finset.Ico L V, (((i + 1 : ℕ) : ℝ)⁻¹) := by
          induction V with
          | zero => omega
          | succ V ih =>
              by_cases h : L ≤ V
              · rw [Finset.sum_Ioc_succ_top h, Finset.sum_Ico_succ_top h,
                    ih h (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hL.trans h)))]
                simp [one_div]
              · have : L = V + 1 := by omega
                subst L
                simp
    _ ≤ ∫ x in (L : ℝ)..(V : ℝ), x⁻¹ := by
          exact (inv_antitoneOn_Icc_right (by positivity)).sum_le_integral_Ico hLV
    _ = Real.log ((V : ℝ) / (L : ℝ)) := by
          have hz : 0 ∉ Set.uIcc (L : ℝ) (V : ℝ) := by
            rw [Set.uIcc_of_le (by exact_mod_cast hLV)]
            intro hm
            exact (not_lt_of_ge hm.1) hposL
          rw [integral_inv hz]

noncomputable def logLower (j : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range 3,
    ((1 : ℝ) / (2 * j + 1)) ^ (2 * i + 1) / (2 * i + 1)

noncomputable def logUpper (j : ℕ) : ℝ :=
  2 * ((∑ i ∈ Finset.range 3,
    ((1 : ℝ) / (2 * j + 1)) ^ (2 * i + 1) / (2 * i + 1)) +
      ((1 : ℝ) / (2 * j + 1)) ^ 7 /
        (1 - ((1 : ℝ) / (2 * j + 1)) ^ 2))

lemma log_ratio_bounds (j : ℕ) (hj : 1 ≤ j) :
    logLower j ≤ Real.log (((j + 1 : ℕ) : ℝ) / (j : ℝ)) ∧
      Real.log (((j + 1 : ℕ) : ℝ) / (j : ℝ)) ≤ logUpper j := by
  let x : ℝ := 1 / (2 * j + 1 : ℕ)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one (by positivity)]
    norm_num
    omega
  have hratio : (1 + x) / (1 - x) = (((j + 1 : ℕ) : ℝ) / (j : ℝ)) := by
    dsimp [x]
    push_cast
    field_simp
    ring
  constructor
  · have h := Real.sum_range_le_log_div hx0 hx1 3
    rw [hratio] at h
    have h' :
        (∑ i ∈ Finset.range 3,
          ((1 : ℝ) / (2 * j + 1)) ^ (2 * i + 1) / (2 * i + 1)) ≤
            (1 : ℝ) / 2 * Real.log (((j + 1 : ℕ) : ℝ) / (j : ℝ)) := by
      simpa [x, Nat.cast_add, Nat.cast_mul] using h
    dsimp [logLower]
    nlinarith
  · have h := Real.log_div_le_sum_range_add hx0 hx1 3
    rw [hratio] at h
    have h' :
        (1 : ℝ) / 2 * Real.log (((j + 1 : ℕ) : ℝ) / (j : ℝ)) ≤
          (∑ i ∈ Finset.range 3,
            ((1 : ℝ) / (2 * j + 1)) ^ (2 * i + 1) / (2 * i + 1)) +
              ((1 : ℝ) / (2 * j + 1)) ^ 7 /
                (1 - ((1 : ℝ) / (2 * j + 1)) ^ 2) := by
      simpa [x, Nat.cast_add, Nat.cast_mul] using h
    dsimp [logUpper]
    nlinarith

def certificateSupport : Finset ℕ := {1, 2, 3, 4, 6, 10, 15, 16, 22, 28, 35, 36, 58}

lemma certificate_log_bounds :
    (1017 : ℝ) / 1000 ≤
        ∑ j ∈ certificateSupport, (certificate j : ℝ) * logLower j ∧
      (∑ j ∈ certificateSupport, (certificate j : ℝ) * logUpper j) ≤
        (1019 : ℝ) / 1000 := by
  norm_num [certificateSupport, Erdos542.certificate, logLower, logUpper]

lemma certificate_error_bound :
    (∑ j ∈ certificateSupport, (certificate j : ℝ) * (j + 1)) ≤ 11 := by
  norm_num [certificateSupport, Erdos542.certificate]

lemma floor_band_ratio_bounds (q j : ℕ) (hj : 1 ≤ j) (hq : 2 * (j + 1) ≤ q) :
    (((j + 1 : ℕ) : ℝ) / (j : ℝ)) /
          (1 + ((j + 1 : ℕ) : ℝ) / (q : ℝ)) ≤
        (((q / j + 1 : ℕ) : ℝ) / ((q / (j + 1) + 1 : ℕ) : ℝ)) ∧
      ((q / j : ℕ) : ℝ) / ((q / (j + 1) : ℕ) : ℝ) ≤
        (((j + 1 : ℕ) : ℝ) / (j : ℝ)) *
          (1 + ((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ)) := by
  let L := q / (j + 1)
  let V := q / j
  have hjpos : 0 < j := by omega
  have hqpos : 0 < q := by omega
  have hdenpos : 0 < q - j - 1 := by omega
  have hLpos : 0 < L := by
    dsimp [L]
    exact Nat.div_pos (by omega) (by omega)
  have hVpos : 0 < V := by
    dsimp [V]
    exact Nat.div_pos (by omega) hjpos
  have hVmul : V * j ≤ q := by
    dsimp [V]
    exact Nat.div_mul_le_self q j
  have hqV : q < j * (V + 1) := by
    dsimp [V]
    exact Nat.lt_mul_div_succ q hjpos
  have hLmul : L * (j + 1) ≤ q := by
    dsimp [L]
    exact Nat.div_mul_le_self q (j + 1)
  have hqL : q < (j + 1) * (L + 1) := by
    dsimp [L]
    exact Nat.lt_mul_div_succ q (by omega)
  have hLplus : (L + 1) * (j + 1) ≤ q + j + 1 := by
    calc
      (L + 1) * (j + 1) = L * (j + 1) + (j + 1) := by ring
      _ ≤ q + (j + 1) := Nat.add_le_add_right hLmul _
      _ = q + j + 1 := by omega
  have hqminus : q - j - 1 ≤ (j + 1) * L := by
    have hx : q < (j + 1) * L + (j + 1) := by
      calc
        q < (j + 1) * (L + 1) := hqL
        _ = (j + 1) * L + (j + 1) := by ring
    have hqle : q ≤ (j + 1) * L + j := by omega
    omega
  have hjR : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hdenR : (0 : ℝ) < ((q - j - 1 : ℕ) : ℝ) := by exact_mod_cast hdenpos
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hLpR : (0 : ℝ) < L + 1 := by positivity
  constructor
  · have h1 : ((q : ℝ) * ((j + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ)) ≤
        (j : ℝ) * (((q + j + 1 : ℕ) : ℝ)) * ((V + 1 : ℕ) : ℝ) := by
      calc
        (q : ℝ) * (j + 1 : ℕ) * (L + 1 : ℕ) ≤
            (q : ℝ) * (q + j + 1 : ℕ) := by
              have := (Nat.cast_le.mpr hLplus :
                (((L + 1) * (j + 1) : ℕ) : ℝ) ≤ (q + j + 1 : ℕ))
              push_cast at this ⊢
              nlinarith
        _ ≤ (j : ℝ) * (q + j + 1 : ℕ) * (V + 1 : ℕ) := by
              have := (Nat.cast_le.mpr (Nat.le_of_lt hqV) :
                (q : ℝ) ≤ (j * (V + 1) : ℕ))
              push_cast at this ⊢
              nlinarith
    dsimp [L, V] at h1 ⊢
    push_cast at h1 ⊢
    field_simp
    nlinarith
  · have h2 : ((V : ℝ) * (j : ℝ) * ((q - j - 1 : ℕ) : ℝ)) ≤
        (q : ℝ) * ((j + 1 : ℕ) : ℝ) * (L : ℝ) := by
      calc
        (V : ℝ) * j * (q - j - 1 : ℕ) ≤
            (q : ℝ) * (q - j - 1 : ℕ) := by
              have := (Nat.cast_le.mpr hVmul : ((V * j : ℕ) : ℝ) ≤ q)
              push_cast at this ⊢
              nlinarith
        _ ≤ (q : ℝ) * (j + 1 : ℕ) * L := by
              have := (Nat.cast_le.mpr hqminus :
                ((q - j - 1 : ℕ) : ℝ) ≤ ((j + 1) * L : ℕ))
              push_cast at this ⊢
              nlinarith
    have hdenEq : (((q - j - 1 : ℕ) : ℝ) + ((j + 1 : ℕ) : ℝ)) = q := by
      exact_mod_cast (show (q - j - 1) + (j + 1) = q by omega)
    dsimp [L, V] at h2 ⊢
    push_cast at h2 ⊢
    dsimp [L] at hLR
    field_simp [ne_of_gt hjR, ne_of_gt hdenR, ne_of_gt hLR]
    push_cast at hdenEq
    rw [hdenEq]
    ring_nf at h2 ⊢
    linarith

noncomputable def certificateBand (q j : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc (q / (j + 1)) (q / j), (1 : ℝ) / k

lemma certificateBand_log_bounds (q j : ℕ) (hj : 1 ≤ j) (hq : 2 * (j + 1) ≤ q) :
    Real.log (((j + 1 : ℕ) : ℝ) / (j : ℝ)) -
          ((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ) ≤ certificateBand q j ∧
      certificateBand q j ≤ Real.log (((j + 1 : ℕ) : ℝ) / (j : ℝ)) +
          ((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ) := by
  have hL : 1 ≤ q / (j + 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hLV : q / (j + 1) ≤ q / j := Nat.div_le_div_left (by omega) (by omega)
  have hVR : (0 : ℝ) < (q / j : ℕ) := by
    exact_mod_cast (show 0 < q / j by exact Nat.div_pos (by omega) (by omega))
  have hLR : (0 : ℝ) < (q / (j + 1) : ℕ) := by exact_mod_cast hL
  have hratio := floor_band_ratio_bounds q j hj hq
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hdenR : (0 : ℝ) < ((q - j - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < q - j - 1 by omega)
  have hRpos : 0 < (((j + 1 : ℕ) : ℝ) / (j : ℝ)) := by positivity
  have he0 : 0 ≤ (((j + 1 : ℕ) : ℝ) / (q : ℝ)) := by positivity
  have he0' : 0 ≤ (((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ)) := by positivity
  have hsmall : ((j + 1 : ℕ) : ℝ) / (q : ℝ) ≤
      ((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ) := by
    gcongr
    exact_mod_cast (show q - j - 1 ≤ q by omega)
  constructor
  · have hH := harmonic_band_lower (q / (j + 1)) (q / j) hL hLV
    have hlogratio :
        Real.log ((((j + 1 : ℕ) : ℝ) / (j : ℝ)) /
            (1 + ((j + 1 : ℕ) : ℝ) / (q : ℝ))) ≤
          Real.log (((q / j + 1 : ℕ) : ℝ) / ((q / (j + 1) + 1 : ℕ) : ℝ)) := by
      exact Real.log_le_log (by positivity) hratio.1
    have hlogsmall : Real.log (1 + ((j + 1 : ℕ) : ℝ) / (q : ℝ)) ≤
        ((j + 1 : ℕ) : ℝ) / (q : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + ((j + 1 : ℕ) : ℝ) / (q : ℝ) by positivity)
      linarith
    rw [Real.log_div hRpos.ne' (by positivity)] at hlogratio
    dsimp [certificateBand]
    linarith
  · have hH := harmonic_band_upper (q / (j + 1)) (q / j) hL hLV
    have hlogratio :
        Real.log (((q / j : ℕ) : ℝ) / ((q / (j + 1) : ℕ) : ℝ)) ≤
          Real.log ((((j + 1 : ℕ) : ℝ) / (j : ℝ)) *
            (1 + ((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ))) := by
      exact Real.log_le_log (div_pos hVR hLR) hratio.2
    have hlogsmall :
        Real.log (1 + ((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ)) ≤
          ((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ) := by
      have := Real.log_le_sub_one_of_pos
        (show 0 < 1 + ((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ) by positivity)
      linarith
    rw [Real.log_mul hRpos.ne' (by positivity)] at hlogratio
    dsimp [certificateBand]
    linarith

lemma div_eq_iff_mem_band {q k j : ℕ} (hk : 0 < k) (hj : 0 < j) :
    q / k = j ↔ k ∈ Finset.Ioc (q / (j + 1)) (q / j) := by
  rw [Finset.mem_Ioc]
  constructor
  · intro h
    constructor
    · rw [Nat.div_lt_iff_lt_mul (by omega)]
      have := Nat.lt_mul_div_succ q hk
      rw [h] at this
      nlinarith
    · rw [Nat.le_div_iff_mul_le hj]
      have := Nat.div_mul_le_self q k
      rw [h] at this
      nlinarith
  · rintro ⟨hlo, hhi⟩
    apply Nat.le_antisymm
    · rw [← Nat.lt_succ_iff]
      rw [Nat.div_lt_iff_lt_mul hk]
      rw [Nat.div_lt_iff_lt_mul (by omega)] at hlo
      simpa [mul_comm] using hlo
    · rw [Nat.le_div_iff_mul_le hk]
      rw [Nat.le_div_iff_mul_le hj] at hhi
      simpa [mul_comm] using hhi

lemma certificate_eq_support_sum (x : ℕ) :
    certificate x =
      ∑ j ∈ certificateSupport, if x = j then certificate j else 0 := by
  classical
  by_cases hx : x ∈ certificateSupport
  · simp [certificateSupport] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [certificateSupport, Erdos542.certificate]
  · have hx' := hx
    simp [certificateSupport] at hx'
    simp [certificateSupport, Erdos542.certificate, hx']

lemma certificate_support_pos {j : ℕ} (hj : j ∈ certificateSupport) : 1 ≤ j := by
  simp [certificateSupport] at hj
  omega

lemma certificateSum_cast_eq_bands (q : ℕ) :
    ((certificateSum q : ℚ) : ℝ) =
      ∑ j ∈ certificateSupport, (certificate j : ℝ) * certificateBand q j := by
  classical
  simp only [certificateSum, Rat.cast_sum, Rat.cast_div, Rat.cast_natCast]
  calc
    (∑ x ∈ Finset.Icc 1 q, (certificate (q / x) : ℝ) / (x : ℝ)) =
        ∑ x ∈ Finset.Icc 1 q,
          (∑ j ∈ certificateSupport,
            if q / x = j then (certificate j : ℝ) else 0) / (x : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          congr 1
          rw [certificate_eq_support_sum]
          push_cast
          apply Finset.sum_congr rfl
          intro j hj
          split_ifs <;> simp_all
    _ = ∑ x ∈ Finset.Icc 1 q,
          ∑ j ∈ certificateSupport,
            (if q / x = j then (certificate j : ℝ) else 0) / (x : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_div]
    _ = ∑ j ∈ certificateSupport,
          ∑ x ∈ Finset.Icc 1 q,
            (if q / x = j then (certificate j : ℝ) else 0) / (x : ℝ) := by
          rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos : 0 < j := by exact certificate_support_pos hj
  simp_rw [ite_div, zero_div]
  rw [← Finset.sum_filter]
  dsimp [certificateBand]
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun k _ => k)
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hkIcc := Finset.mem_Icc.mp hk.1
    exact (div_eq_iff_mem_band (by omega) hjpos).1 hk.2
  · intro k hk
    simp [div_eq_mul_inv]
  · intro k hk
    have hkband := hk
    rw [Finset.mem_Ioc] at hkband
    have hj1 := certificate_support_pos hj
    have hkpos : 0 < k := by
      exact lt_of_le_of_lt (Nat.zero_le _) hkband.1
    refine ⟨k, ?_, rfl⟩
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      constructor
      · omega
      · exact (hkband.2.trans (Nat.div_le_self q j))
    · exact (div_eq_iff_mem_band hkpos hjpos).2 hk
  · intro k hk
    simp [div_eq_mul_inv]

lemma certificate_nonneg_on_support {j : ℕ} (hj : j ∈ certificateSupport) :
    0 ≤ (certificate j : ℝ) := by
  simp [certificateSupport] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [Erdos542.certificate]

noncomputable def certificateError (q : ℕ) : ℝ :=
  ∑ j ∈ certificateSupport,
    (certificate j : ℝ) * (((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ))

lemma certificateError_le_lower (q : ℕ) (hq : 660 ≤ q) :
    certificateError q ≤ (17 : ℝ) / 1000 := by
  calc
    certificateError q ≤
        ∑ j ∈ certificateSupport,
          (certificate j : ℝ) *
            (((j + 1 : ℕ) : ℝ) / ((660 - j - 1 : ℕ) : ℝ)) := by
      dsimp [certificateError]
      apply Finset.sum_le_sum
      intro j hj
      have hjle : j ≤ 58 := by
        simp [certificateSupport] at hj
        omega
      have hbasepos : 0 < 660 - j - 1 := by omega
      have hden : 660 - j - 1 ≤ q - j - 1 := by omega
      apply mul_le_mul_of_nonneg_left _ (certificate_nonneg_on_support hj)
      exact div_le_div_of_nonneg_left (by positivity)
        (by exact_mod_cast hbasepos) (by exact_mod_cast hden)
    _ ≤ (17 : ℝ) / 1000 := by
      norm_num [certificateSupport, certificate]

lemma certificateError_le_upper (q : ℕ) (hq : 780 ≤ q) :
    certificateError q ≤ (43 : ℝ) / 3000 := by
  calc
    certificateError q ≤
        ∑ j ∈ certificateSupport,
          (certificate j : ℝ) *
            (((j + 1 : ℕ) : ℝ) / ((780 - j - 1 : ℕ) : ℝ)) := by
      dsimp [certificateError]
      apply Finset.sum_le_sum
      intro j hj
      have hjle : j ≤ 58 := by
        simp [certificateSupport] at hj
        omega
      have hbasepos : 0 < 780 - j - 1 := by omega
      have hden : 780 - j - 1 ≤ q - j - 1 := by omega
      apply mul_le_mul_of_nonneg_left _ (certificate_nonneg_on_support hj)
      exact div_le_div_of_nonneg_left (by positivity)
        (by exact_mod_cast hbasepos) (by exact_mod_cast hden)
    _ ≤ (43 : ℝ) / 3000 := by
      norm_num [certificateSupport, certificate]

lemma certificateSum_large_lower (q : ℕ) (hq : 660 ≤ q) :
    (1 : ℚ) ≤ certificateSum q := by
  have hsum :
      (∑ j ∈ certificateSupport,
          (certificate j : ℝ) *
            (logLower j - (((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ)))) ≤
        ((certificateSum q : ℚ) : ℝ) := by
    rw [certificateSum_cast_eq_bands]
    apply Finset.sum_le_sum
    intro j hj
    have hj1 := certificate_support_pos hj
    have hjle : j ≤ 58 := by
      simp [certificateSupport] at hj
      omega
    have hb := (certificateBand_log_bounds q j hj1 (by omega)).1
    have hl := (log_ratio_bounds j hj1).1
    exact mul_le_mul_of_nonneg_left (by linarith) (certificate_nonneg_on_support hj)
  have hrewrite :
      (∑ j ∈ certificateSupport,
          (certificate j : ℝ) *
            (logLower j - (((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ)))) =
        (∑ j ∈ certificateSupport, (certificate j : ℝ) * logLower j) -
          certificateError q := by
    dsimp [certificateError]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hnum : (1 : ℝ) ≤ (1017 : ℝ) / 1000 - (17 : ℝ) / 1000 := by norm_num
  have hreal : (1 : ℝ) ≤ ((certificateSum q : ℚ) : ℝ) := by
    rw [hrewrite] at hsum
    linarith [certificate_log_bounds.1, certificateError_le_lower q hq]
  exact (Rat.cast_le (K := ℝ)).mp (by norm_num; exact hreal)

lemma certificateSum_large_upper (q : ℕ) (hq : 780 ≤ q) :
    certificateSum q ≤ (31 : ℚ) / 30 := by
  have hsum :
      ((certificateSum q : ℚ) : ℝ) ≤
        ∑ j ∈ certificateSupport,
          (certificate j : ℝ) *
            (logUpper j + (((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ))) := by
    rw [certificateSum_cast_eq_bands]
    apply Finset.sum_le_sum
    intro j hj
    have hj1 := certificate_support_pos hj
    have hjle : j ≤ 58 := by
      simp [certificateSupport] at hj
      omega
    have hb := (certificateBand_log_bounds q j hj1 (by omega)).2
    have hu := (log_ratio_bounds j hj1).2
    exact mul_le_mul_of_nonneg_left (by linarith) (certificate_nonneg_on_support hj)
  have hrewrite :
      (∑ j ∈ certificateSupport,
          (certificate j : ℝ) *
            (logUpper j + (((j + 1 : ℕ) : ℝ) / ((q - j - 1 : ℕ) : ℝ)))) =
        (∑ j ∈ certificateSupport, (certificate j : ℝ) * logUpper j) +
          certificateError q := by
    dsimp [certificateError]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hnum : (1019 : ℝ) / 1000 + (43 : ℝ) / 3000 ≤ (31 : ℝ) / 30 := by norm_num
  have hreal : ((certificateSum q : ℚ) : ℝ) ≤ (31 : ℝ) / 30 := by
    rw [hrewrite] at hsum
    linarith [certificate_log_bounds.2, certificateError_le_upper q hq]
  exact (Rat.cast_le (K := ℝ)).mp (by norm_num; exact hreal)

def certificateNumerator : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 6 => 2
  | 10 => 31
  | 15 => 2021
  | 16 => 2021
  | 22 => 3565609
  | 28 => 148279331
  | 35 => 17694671471
  | 36 => 104205434239
  | 58 => 77337724377074022791
  | _ => 0

def certificateDenominator : ℕ → ℕ
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 6
  | 6 => 15
  | 10 => 420
  | 15 => 45045
  | 16 => 45045
  | 22 => 116396280
  | 28 => 6692786100
  | 35 => 1504203675975
  | 36 => 6016814703900
  | 58 => 13687446560419818786600
  | _ => 1

def certificateCommonDenominator : ℕ :=
  2 * 6 * 6 * 15 * 420 * 45045 * 45045 * 116396280 * 6692786100 *
    1504203675975 * 6016814703900 * 13687446560419818786600

def factorialChunk (lo hi : ℕ) : ℕ := ∏ k ∈ Finset.Ico lo hi, k

def certificateCut (q i : ℕ) : ℕ := min (20 * i + 1) (q + 1)

/-- A chunked evaluator of `q !`, for kernel-safe finite verification. -/
def certificateFactorial (q : ℕ) : ℕ :=
  ∏ i ∈ Finset.range 40,
    factorialChunk (certificateCut q i) (certificateCut q (i + 1))

def scaledCertificateTerm (q k : ℕ) : ℕ :=
  certificateNumerator (q / k) *
    (certificateCommonDenominator / certificateDenominator (q / k)) *
      (certificateFactorial q / k)

def scaledCertificateChunk (q lo hi : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico lo hi, scaledCertificateTerm q k

/-- A chunked evaluator for the exact scaled certificate.  The chunks keep
kernel reduction within Lean's ordinary recursion-depth bound. -/
def scaledCertificateSum (q : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 40,
    scaledCertificateChunk q (certificateCut q i) (certificateCut q (i + 1))

def ScaledCertificateBounds (q : ℕ) : Prop :=
  certificateCommonDenominator * certificateFactorial q ≤ scaledCertificateSum q ∧
    (q ∉ certificateExceptions →
      30 * scaledCertificateSum q ≤
        31 * (certificateCommonDenominator * certificateFactorial q))

instance (q : ℕ) : Decidable (ScaledCertificateBounds q) := by
  unfold ScaledCertificateBounds
  infer_instance

lemma scaledCertificateBounds_1_19 :
    ∀ q ∈ Finset.Icc 1 19, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_20_39 :
    ∀ q ∈ Finset.Icc 20 39, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_40_59 :
    ∀ q ∈ Finset.Icc 40 59, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_60_79 :
    ∀ q ∈ Finset.Icc 60 79, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_80_99 :
    ∀ q ∈ Finset.Icc 80 99, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_100_119 :
    ∀ q ∈ Finset.Icc 100 119, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_120_139 :
    ∀ q ∈ Finset.Icc 120 139, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_140_159 :
    ∀ q ∈ Finset.Icc 140 159, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_160_179 :
    ∀ q ∈ Finset.Icc 160 179, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_180_199 :
    ∀ q ∈ Finset.Icc 180 199, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_200_219 :
    ∀ q ∈ Finset.Icc 200 219, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_220_239 :
    ∀ q ∈ Finset.Icc 220 239, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_240_259 :
    ∀ q ∈ Finset.Icc 240 259, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_260_279 :
    ∀ q ∈ Finset.Icc 260 279, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_280_299 :
    ∀ q ∈ Finset.Icc 280 299, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_300_319 :
    ∀ q ∈ Finset.Icc 300 319, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_320_339 :
    ∀ q ∈ Finset.Icc 320 339, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_340_359 :
    ∀ q ∈ Finset.Icc 340 359, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_360_379 :
    ∀ q ∈ Finset.Icc 360 379, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_380_399 :
    ∀ q ∈ Finset.Icc 380 399, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_400_419 :
    ∀ q ∈ Finset.Icc 400 419, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_420_439 :
    ∀ q ∈ Finset.Icc 420 439, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_440_459 :
    ∀ q ∈ Finset.Icc 440 459, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_460_479 :
    ∀ q ∈ Finset.Icc 460 479, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_480_499 :
    ∀ q ∈ Finset.Icc 480 499, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_500_519 :
    ∀ q ∈ Finset.Icc 500 519, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_520_539 :
    ∀ q ∈ Finset.Icc 520 539, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_540_559 :
    ∀ q ∈ Finset.Icc 540 559, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_560_579 :
    ∀ q ∈ Finset.Icc 560 579, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_580_599 :
    ∀ q ∈ Finset.Icc 580 599, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_600_619 :
    ∀ q ∈ Finset.Icc 600 619, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_620_639 :
    ∀ q ∈ Finset.Icc 620 639, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_640_659 :
    ∀ q ∈ Finset.Icc 640 659, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_660_679 :
    ∀ q ∈ Finset.Icc 660 679, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_680_699 :
    ∀ q ∈ Finset.Icc 680 699, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_700_719 :
    ∀ q ∈ Finset.Icc 700 719, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_720_739 :
    ∀ q ∈ Finset.Icc 720 739, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_740_759 :
    ∀ q ∈ Finset.Icc 740 759, ScaledCertificateBounds q := by decide
lemma scaledCertificateBounds_760_779 :
    ∀ q ∈ Finset.Icc 760 779, ScaledCertificateBounds q := by decide

lemma certificateCut_mono (q i : ℕ) :
    certificateCut q i ≤ certificateCut q (i + 1) := by
  rw [certificateCut, certificateCut]
  exact min_le_min (by omega) le_rfl

lemma sum_certificateChunks {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (q r : ℕ) :
    (∑ i ∈ Finset.range r,
      ∑ k ∈ Finset.Ico (certificateCut q i) (certificateCut q (i + 1)), f k) =
      ∑ k ∈ Finset.Ico 1 (certificateCut q r), f k := by
  induction r with
  | zero => simp [certificateCut]
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      exact Finset.sum_Ico_consecutive f
        (by simp [certificateCut]) (certificateCut_mono q r)

lemma prod_certificateChunks {M : Type*} [CommMonoid M]
    (f : ℕ → M) (q r : ℕ) :
    (∏ i ∈ Finset.range r,
      ∏ k ∈ Finset.Ico (certificateCut q i) (certificateCut q (i + 1)), f k) =
      ∏ k ∈ Finset.Ico 1 (certificateCut q r), f k := by
  induction r with
  | zero => simp [certificateCut]
  | succ r ih =>
      rw [Finset.prod_range_succ, ih]
      exact Finset.prod_Ico_consecutive f
        (by simp [certificateCut]) (certificateCut_mono q r)

lemma certificateCut_forty {q : ℕ} (hq : q ≤ 779) :
    certificateCut q 40 = q + 1 := by
  simp [certificateCut]
  omega

lemma certificateFactorial_eq (q : ℕ) (hq : q ≤ 779) :
    certificateFactorial q = q.factorial := by
  simp only [certificateFactorial, factorialChunk]
  rw [prod_certificateChunks (fun k : ℕ => k) q 40,
    certificateCut_forty hq, Finset.prod_Ico_id_eq_factorial]

lemma scaledCertificateSum_eq_finset (q : ℕ) (hq : q ≤ 779) :
    scaledCertificateSum q =
      ∑ k ∈ Finset.Icc 1 q, scaledCertificateTerm q k := by
  simp only [scaledCertificateSum, scaledCertificateChunk]
  rw [sum_certificateChunks (scaledCertificateTerm q) q 40,
    certificateCut_forty hq, Finset.Ico_add_one_right_eq_Icc]

lemma certificate_scaled_coeff (x : ℕ) :
    ((certificateNumerator x : ℕ) : ℚ) *
        ((certificateCommonDenominator / certificateDenominator x : ℕ) : ℚ) =
      (certificateCommonDenominator : ℚ) * certificate x := by
  by_cases hx : x < 59
  · interval_cases x <;>
      norm_num [certificateNumerator, certificateDenominator,
        certificateCommonDenominator, certificate]
  · have hx1 : x ≠ 1 := by omega
    have hx2 : x ≠ 2 := by omega
    have hx3 : x ≠ 3 := by omega
    have hx4 : x ≠ 4 := by omega
    have hx6 : x ≠ 6 := by omega
    have hx10 : x ≠ 10 := by omega
    have hx15 : x ≠ 15 := by omega
    have hx16 : x ≠ 16 := by omega
    have hx22 : x ≠ 22 := by omega
    have hx28 : x ≠ 28 := by omega
    have hx35 : x ≠ 35 := by omega
    have hx36 : x ≠ 36 := by omega
    have hx58 : x ≠ 58 := by omega
    simp [certificateNumerator, certificateDenominator, certificate,
      hx1, hx2, hx3, hx4, hx6, hx10, hx15, hx16, hx22, hx28, hx35, hx36, hx58]

lemma scaledCertificateTerm_cast (q k : ℕ) (hq : q ≤ 779)
    (hkpos : 0 < k) (hkle : k ≤ q) :
    ((scaledCertificateTerm q k : ℕ) : ℚ) =
      ((certificateCommonDenominator * certificateFactorial q : ℕ) : ℚ) *
        (certificate (q / k) / (k : ℚ)) := by
  have hkfac : k ∣ q.factorial := Nat.dvd_factorial hkpos hkle
  rw [scaledCertificateTerm, certificateFactorial_eq q hq]
  push_cast
  rw [Nat.cast_div hkfac (by exact_mod_cast (ne_of_gt hkpos))]
  generalize hx : q / k = x
  rw [certificate_scaled_coeff x]
  ring

lemma scaledCertificateSum_cast (q : ℕ) (hq : q ≤ 779) :
    ((scaledCertificateSum q : ℕ) : ℚ) =
      ((certificateCommonDenominator * certificateFactorial q : ℕ) : ℚ) *
        certificateSum q := by
  rw [scaledCertificateSum_eq_finset q hq, certificateSum, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  simpa only [Nat.cast_mul] using
    scaledCertificateTerm_cast q k hq (by omega) hk'.2

lemma combineScaledCertificateBounds {a b c : ℕ}
    (h₁ : ∀ q ∈ Finset.Icc a b, ScaledCertificateBounds q)
    (h₂ : ∀ q ∈ Finset.Icc (b + 1) c, ScaledCertificateBounds q) :
    ∀ q ∈ Finset.Icc a c, ScaledCertificateBounds q := by
  intro q hq
  rw [Finset.mem_Icc] at hq
  by_cases hqb : q ≤ b
  · exact h₁ q (Finset.mem_Icc.mpr ⟨hq.1, hqb⟩)
  · exact h₂ q (Finset.mem_Icc.mpr ⟨by omega, hq.2⟩)

lemma scaledCertificateBounds_1_779 :
    ∀ q ∈ Finset.Icc 1 779, ScaledCertificateBounds q := by
  apply combineScaledCertificateBounds scaledCertificateBounds_1_19
  apply combineScaledCertificateBounds scaledCertificateBounds_20_39
  apply combineScaledCertificateBounds scaledCertificateBounds_40_59
  apply combineScaledCertificateBounds scaledCertificateBounds_60_79
  apply combineScaledCertificateBounds scaledCertificateBounds_80_99
  apply combineScaledCertificateBounds scaledCertificateBounds_100_119
  apply combineScaledCertificateBounds scaledCertificateBounds_120_139
  apply combineScaledCertificateBounds scaledCertificateBounds_140_159
  apply combineScaledCertificateBounds scaledCertificateBounds_160_179
  apply combineScaledCertificateBounds scaledCertificateBounds_180_199
  apply combineScaledCertificateBounds scaledCertificateBounds_200_219
  apply combineScaledCertificateBounds scaledCertificateBounds_220_239
  apply combineScaledCertificateBounds scaledCertificateBounds_240_259
  apply combineScaledCertificateBounds scaledCertificateBounds_260_279
  apply combineScaledCertificateBounds scaledCertificateBounds_280_299
  apply combineScaledCertificateBounds scaledCertificateBounds_300_319
  apply combineScaledCertificateBounds scaledCertificateBounds_320_339
  apply combineScaledCertificateBounds scaledCertificateBounds_340_359
  apply combineScaledCertificateBounds scaledCertificateBounds_360_379
  apply combineScaledCertificateBounds scaledCertificateBounds_380_399
  apply combineScaledCertificateBounds scaledCertificateBounds_400_419
  apply combineScaledCertificateBounds scaledCertificateBounds_420_439
  apply combineScaledCertificateBounds scaledCertificateBounds_440_459
  apply combineScaledCertificateBounds scaledCertificateBounds_460_479
  apply combineScaledCertificateBounds scaledCertificateBounds_480_499
  apply combineScaledCertificateBounds scaledCertificateBounds_500_519
  apply combineScaledCertificateBounds scaledCertificateBounds_520_539
  apply combineScaledCertificateBounds scaledCertificateBounds_540_559
  apply combineScaledCertificateBounds scaledCertificateBounds_560_579
  apply combineScaledCertificateBounds scaledCertificateBounds_580_599
  apply combineScaledCertificateBounds scaledCertificateBounds_600_619
  apply combineScaledCertificateBounds scaledCertificateBounds_620_639
  apply combineScaledCertificateBounds scaledCertificateBounds_640_659
  apply combineScaledCertificateBounds scaledCertificateBounds_660_679
  apply combineScaledCertificateBounds scaledCertificateBounds_680_699
  apply combineScaledCertificateBounds scaledCertificateBounds_700_719
  apply combineScaledCertificateBounds scaledCertificateBounds_720_739
  exact combineScaledCertificateBounds scaledCertificateBounds_740_759
    scaledCertificateBounds_760_779

lemma scaledCertificateBounds_small (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ 779) :
    ScaledCertificateBounds q :=
  scaledCertificateBounds_1_779 q (Finset.mem_Icc.mpr ⟨hq1, hq⟩)

lemma certificateBounds_small (q : ℕ) (hq1 : 1 ≤ q) (hq : q ≤ 779) :
    (1 : ℚ) ≤ certificateSum q ∧
      (q ∉ certificateExceptions → certificateSum q ≤ (31 : ℚ) / 30) := by
  have hs := scaledCertificateBounds_small q hq1 hq
  have hfact := certificateFactorial_eq q hq
  have hDnat : 0 < certificateCommonDenominator * certificateFactorial q := by
    rw [hfact]
    exact Nat.mul_pos (by norm_num [certificateCommonDenominator]) (Nat.factorial_pos q)
  have hD : (0 : ℚ) <
      ((certificateCommonDenominator * certificateFactorial q : ℕ) : ℚ) := by
    exact_mod_cast hDnat
  constructor
  · have hc :
        (((certificateCommonDenominator * certificateFactorial q : ℕ) : ℕ) : ℚ) ≤
          (scaledCertificateSum q : ℕ) := by
      exact_mod_cast hs.1
    rw [scaledCertificateSum_cast q hq] at hc
    exact (le_mul_iff_one_le_right hD).mp hc
  · intro hex
    have hcNat := hs.2 hex
    have hc : ((30 * scaledCertificateSum q : ℕ) : ℚ) ≤
        (31 * (certificateCommonDenominator * certificateFactorial q) : ℕ) := by
      exact_mod_cast hcNat
    push_cast at hc
    rw [scaledCertificateSum_cast q hq] at hc
    apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 30)).2
    have hc' :
        ((certificateCommonDenominator * certificateFactorial q : ℕ) : ℚ) *
            (30 * certificateSum q) ≤
          ((certificateCommonDenominator * certificateFactorial q : ℕ) : ℚ) * 31 := by
      calc
        _ = 30 *
            (((certificateCommonDenominator * certificateFactorial q : ℕ) : ℚ) *
              certificateSum q) := by ring
        _ ≤ 31 *
            ((certificateCommonDenominator * certificateFactorial q : ℕ) : ℚ) := by
          simpa only [Nat.cast_mul] using hc
        _ = _ := by ring
    simpa [mul_comm] using (mul_le_mul_iff_of_pos_left hD).mp hc'

lemma certificateSum_lower (q : ℕ) (hq : 1 ≤ q) : (1 : ℚ) ≤ certificateSum q := by
  by_cases hsmall : q ≤ 659
  · exact (certificateBounds_small q hq (by omega)).1
  · exact certificateSum_large_lower q (by omega)

lemma certificateSum_upper (q : ℕ) (hq : 1 ≤ q) (hex : q ∉ certificateExceptions) :
    certificateSum q ≤ (31 : ℚ) / 30 := by
  by_cases hsmall : q ≤ 779
  · exact (certificateBounds_small q hq hsmall).2 hex
  · exact certificateSum_large_upper q (by omega)

def multiples (n a : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m => a ∣ m

lemma multiples_subset (n a : ℕ) : multiples n a ⊆ Finset.Icc 1 n := by
  intro m hm
  exact (Finset.mem_filter.mp hm).1

lemma multiples_disjoint {n a b : ℕ} (hab : a ≠ b) (hlcm : n < Nat.lcm a b) :
    Disjoint (multiples n a) (multiples n b) := by
  rw [Finset.disjoint_left]
  intro m hma hmb
  have hma' := Finset.mem_filter.mp hma
  have hmb' := Finset.mem_filter.mp hmb
  have hlcmDvd : Nat.lcm a b ∣ m := (Nat.lcm_dvd_iff).2 ⟨hma'.2, hmb'.2⟩
  have hmIcc := multiples_subset n a hma
  have hmIcc' := Finset.mem_Icc.mp hmIcc
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmIcc'.1
  have hle := Nat.le_of_dvd hmpos hlcmDvd
  exact (not_lt_of_ge (hle.trans hmIcc'.2)) hlcm

lemma multiples_charge (n a : ℕ) (ha : 1 ≤ a) :
    (∑ m ∈ multiples n a, certificate (n / m) / (m : ℚ)) =
      certificateSum (n / a) / (a : ℚ) := by
  classical
  rw [certificateSum, Finset.sum_div]
  symm
  apply Finset.sum_bij (fun k _ => a * k)
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [multiples, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · constructor
      · nlinarith
      · have := (Nat.le_div_iff_mul_le (by omega)).mp hk.2
        simpa [mul_comm] using this
    · exact dvd_mul_right a k
  · intro k hk l hl hkl
    exact Nat.eq_of_mul_eq_mul_left (by omega) hkl
  · intro m hm
    rw [multiples, Finset.mem_filter] at hm
    rcases hm.2 with ⟨k, rfl⟩
    refine ⟨k, ?_, ?_⟩
    · rw [Finset.mem_Icc] at hm ⊢
      constructor
      · have : 0 < k := by
          by_contra hk
          simp_all
        omega
      · rw [Nat.le_div_iff_mul_le (by omega)]
        simpa [mul_comm] using hm.1.2
    · rfl
  · intro k hk
    rw [Nat.div_div_eq_div_mul]
    push_cast
    field_simp

lemma certificate_nonneg_all (j : ℕ) : 0 ≤ certificate j := by
  rw [certificate_eq_support_sum]
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact_mod_cast certificate_nonneg_on_support hi
  · norm_num

lemma certificate_weight_nonneg (n m : ℕ) :
    0 ≤ certificate (n / m) / (m : ℚ) := by
  exact div_nonneg (certificate_nonneg_all _) (by positivity)

lemma reciprocalSumRat_le_certificateSum
    {n : ℕ} {A : Finset ℕ} (hA : PairwiseLCMExceeds n A) :
    reciprocalSumRat A ≤ certificateSum n := by
  classical
  by_cases hn : n = 0
  · subst n
    have hEmpty : A = ∅ := by
      ext a
      constructor
      · intro ha
        have := hA.1 a ha
        omega
      · intro ha
        simp at ha
    simp [hEmpty, reciprocalSumRat, certificateSum]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  calc
    reciprocalSumRat A ≤
        ∑ a ∈ A, certificateSum (n / a) / (a : ℚ) := by
      dsimp [reciprocalSumRat]
      apply Finset.sum_le_sum
      intro a ha
      have haBounds := hA.1 a ha
      have hq1 : 1 ≤ n / a := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        simpa using haBounds.2
      have hcert := certificateSum_lower (n / a) hq1
      have haQ : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
      exact div_le_div_of_nonneg_right hcert haQ.le
    _ = ∑ a ∈ A, ∑ m ∈ multiples n a,
          certificate (n / m) / (m : ℚ) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (multiples_charge n a (hA.1 a ha).1).symm
    _ = ∑ m ∈ A.biUnion (multiples n),
          certificate (n / m) / (m : ℚ) := by
      symm
      apply Finset.sum_biUnion
      intro a ha b hb hab
      exact multiples_disjoint hab (hA.2 a ha b hb hab)
    _ ≤ ∑ m ∈ Finset.Icc 1 n, certificate (n / m) / (m : ℚ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · rw [Finset.biUnion_subset_iff_forall_subset]
        intro a ha
        exact multiples_subset n a
      · intro m hm hnmem
        exact certificate_weight_nonneg n m
    _ = certificateSum n := rfl

def covered (n : ℕ) (A : Finset ℕ) : Finset ℕ := A.biUnion (multiples n)

lemma reciprocalSumRat_le_covered
    {n : ℕ} {A : Finset ℕ} (hA : PairwiseLCMExceeds n A) :
    reciprocalSumRat A ≤
      ∑ m ∈ covered n A, certificate (n / m) / (m : ℚ) := by
  classical
  dsimp [reciprocalSumRat, covered]
  calc
    (∑ a ∈ A, (1 : ℚ) / a) ≤
        ∑ a ∈ A, certificateSum (n / a) / (a : ℚ) := by
      apply Finset.sum_le_sum
      intro a ha
      have haBounds := hA.1 a ha
      have hq1 : 1 ≤ n / a := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        simpa using haBounds.2
      have hcert := certificateSum_lower (n / a) hq1
      exact div_le_div_of_nonneg_right hcert (by positivity)
    _ = ∑ a ∈ A, ∑ m ∈ multiples n a,
          certificate (n / m) / (m : ℚ) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (multiples_charge n a (hA.1 a ha).1).symm
    _ = ∑ m ∈ A.biUnion (multiples n),
          certificate (n / m) / (m : ℚ) := by
      symm
      apply Finset.sum_biUnion
      intro a ha b hb hab
      exact multiples_disjoint hab (hA.2 a ha b hb hab)

def exceptionPair : ℕ → ℕ × ℕ
  | 13 => (2, 3)
  | 19 => (3, 4)
  | 20 => (2, 9)
  | 31 => (3, 5)
  | 32 => (3, 5)
  | 61 => (4, 15)
  | 62 => (4, 15)
  | _ => (1, 1)

lemma exceptionPair_data : ∀ n ∈ certificateExceptions,
    let x := (exceptionPair n).1
    let y := (exceptionPair n).2
    x ∈ Finset.Icc 1 n ∧ y ∈ Finset.Icc 1 n ∧ Nat.Coprime x y ∧
      Nat.lcm x y ≤ n ∧
      certificateSum n - (31 : ℚ) / 30 ≤ certificate (n / x) / (x : ℚ) ∧
      certificateSum n - (31 : ℚ) / 30 ≤ certificate (n / y) / (y : ℚ) := by
  intro n hn
  simp [certificateExceptions] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [exceptionPair, certificateSum, certificate, sum_Icc_succ_top]

lemma one_mem_forces_singleton
    {n : ℕ} {A : Finset ℕ} (hA : PairwiseLCMExceeds n A) (h1 : 1 ∈ A) :
    A = {1} := by
  ext a
  simp only [Finset.mem_singleton]
  constructor
  · intro ha
    by_contra hne
    have hlcm := hA.2 1 h1 a ha (Ne.symm hne)
    simp [Nat.lcm_comm] at hlcm
    exact (not_lt_of_ge (hA.1 a ha).2) hlcm
  · rintro rfl
    exact h1

lemma exception_pair_not_both_covered
    {n : ℕ} {A : Finset ℕ} (hA : PairwiseLCMExceeds n A) (h1 : 1 ∉ A)
    {x y : ℕ} (hxpos : 0 < x) (hypos : 0 < y)
    (hc : Nat.Coprime x y) (hlxy : Nat.lcm x y ≤ n) :
    x ∉ covered n A ∨ y ∉ covered n A := by
  classical
  by_contra h
  push_neg at h
  rw [covered] at h
  rcases Finset.mem_biUnion.mp h.1 with ⟨a, haA, hax⟩
  rcases Finset.mem_biUnion.mp h.2 with ⟨b, hbA, hby⟩
  have hax' := (Finset.mem_filter.mp hax).2
  have hby' := (Finset.mem_filter.mp hby).2
  by_cases hab : a = b
  · subst b
    have ha_gcd : a ∣ Nat.gcd x y := (Nat.dvd_gcd hax' hby')
    rw [hc.gcd_eq_one] at ha_gcd
    have : a = 1 := Nat.dvd_one.mp ha_gcd
    exact h1 (this ▸ haA)
  · have ha_lcmxy : a ∣ Nat.lcm x y := dvd_trans hax' (Nat.dvd_lcm_left x y)
    have hb_lcmxy : b ∣ Nat.lcm x y := dvd_trans hby' (Nat.dvd_lcm_right x y)
    have habDvd : Nat.lcm a b ∣ Nat.lcm x y := Nat.lcm_dvd ha_lcmxy hb_lcmxy
    have hpos : 0 < Nat.lcm x y := Nat.lcm_pos hxpos hypos
    have habLe : Nat.lcm a b ≤ n := (Nat.le_of_dvd hpos habDvd).trans hlxy
    exact (not_lt_of_ge habLe) (hA.2 a haA b hbA hab)

lemma covered_sum_le_sub_of_missing
    {n : ℕ} {A : Finset ℕ} {z : ℕ}
    (hzIcc : z ∈ Finset.Icc 1 n) (hz : z ∉ covered n A) :
    (∑ m ∈ covered n A, certificate (n / m) / (m : ℚ)) ≤
      certificateSum n - certificate (n / z) / (z : ℚ) := by
  have hsub : insert z (covered n A) ⊆ Finset.Icc 1 n := by
    intro m hm
    rw [Finset.mem_insert] at hm
    rcases hm with rfl | hm
    · exact hzIcc
    · rw [covered, Finset.mem_biUnion] at hm
      rcases hm with ⟨a, ha, hma⟩
      exact multiples_subset n a hma
  have hsum :
      (∑ m ∈ insert z (covered n A), certificate (n / m) / (m : ℚ)) ≤
        ∑ m ∈ Finset.Icc 1 n, certificate (n / m) / (m : ℚ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro m hm hnot
    exact certificate_weight_nonneg n m
  have hsum' : certificate (n / z) / (z : ℚ) +
        (∑ m ∈ covered n A, certificate (n / m) / (m : ℚ)) ≤ certificateSum n := by
    simpa [certificateSum, Finset.sum_insert hz] using hsum
  linarith

lemma reciprocalSumRat_le_on_exception
    {n : ℕ} {A : Finset ℕ} (hA : PairwiseLCMExceeds n A)
    (hnex : n ∈ certificateExceptions) :
    reciprocalSumRat A ≤ (31 : ℚ) / 30 := by
  classical
  by_cases h1 : 1 ∈ A
  · rw [one_mem_forces_singleton hA h1]
    norm_num [reciprocalSumRat]
  · let x := (exceptionPair n).1
    let y := (exceptionPair n).2
    have hd := exceptionPair_data n hnex
    dsimp only at hd
    have hmissing := exception_pair_not_both_covered hA h1
      (by have := (Finset.mem_Icc.mp hd.1).1; omega)
      (by have := (Finset.mem_Icc.mp hd.2.1).1; omega)
      hd.2.2.1 hd.2.2.2.1
    rcases hmissing with hx | hy
    · calc
        reciprocalSumRat A ≤
            ∑ m ∈ covered n A, certificate (n / m) / (m : ℚ) :=
          reciprocalSumRat_le_covered hA
        _ ≤ certificateSum n - certificate (n / x) / (x : ℚ) :=
          covered_sum_le_sub_of_missing hd.1 hx
        _ ≤ (31 : ℚ) / 30 := by linarith [hd.2.2.2.2.1]
    · calc
        reciprocalSumRat A ≤
            ∑ m ∈ covered n A, certificate (n / m) / (m : ℚ) :=
          reciprocalSumRat_le_covered hA
        _ ≤ certificateSum n - certificate (n / y) / (y : ℚ) :=
          covered_sum_le_sub_of_missing hd.2.1 hy
        _ ≤ (31 : ℚ) / 30 := by linarith [hd.2.2.2.2.2]

lemma reciprocalSumRat_le_of_not_exception
    {n : ℕ} {A : Finset ℕ} (hA : PairwiseLCMExceeds n A)
    (hnex : n ∉ certificateExceptions) :
    reciprocalSumRat A ≤ (31 : ℚ) / 30 := by
  by_cases hn : n = 0
  · subst n
    have hEmpty : A = ∅ := by
      ext a
      constructor
      · intro ha
        have := hA.1 a ha
        omega
      · intro ha
        simp at ha
    norm_num [hEmpty, reciprocalSumRat]
  exact (reciprocalSumRat_le_certificateSum hA).trans
    (certificateSum_upper n (Nat.one_le_iff_ne_zero.mpr hn) hnex)

/-- The sharp affirmative answer to the reciprocal-sum part of Problem 542. -/
theorem erdos542_reciprocal_bound
    {n : ℕ} {A : Finset ℕ} (hA : PairwiseLCMExceeds n A) :
    reciprocalSum A ≤ (31 : ℝ) / 30 := by
  have hrat : reciprocalSumRat A ≤ (31 : ℚ) / 30 := by
    by_cases hn : n ∈ certificateExceptions
    · exact reciprocalSumRat_le_on_exception hA hn
    · exact reciprocalSumRat_le_of_not_exception hA hn
  have hcast : reciprocalSum A = ((reciprocalSumRat A : ℚ) : ℝ) := by
    simp [reciprocalSum, reciprocalSumRat]
  rw [hcast]
  calc
    ((reciprocalSumRat A : ℚ) : ℝ) ≤ (((31 : ℚ) / 30 : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr hrat
    _ = (31 : ℝ) / 30 := by norm_num

/-- The set `{2,3,5}` at `n=5` attains the bound. -/
theorem erdos542_sharp_example :
    PairwiseLCMExceeds 5 {2, 3, 5} ∧
      reciprocalSum {2, 3, 5} = (31 : ℝ) / 30 := by
  constructor
  · norm_num [PairwiseLCMExceeds, Nat.lcm]
  · norm_num [reciprocalSum]

noncomputable def omegaPower (z : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else z ^ Ω n, by simp⟩

lemma omegaPower_apply {z : ℝ} {n : ℕ} (hn : n ≠ 0) :
    omegaPower z n = z ^ Ω n := by simp [omegaPower, hn]

lemma omegaPower_multiplicative (z : ℝ) : (omegaPower z).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [omegaPower]
  · intro m n hm hn hcop
    simp [omegaPower, hm, hn, mul_ne_zero hm hn,
      ArithmeticFunction.cardFactors_mul hm hn, pow_add]

noncomputable def omegaIncrement (z : ℝ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * omegaPower z

lemma omegaIncrement_multiplicative (z : ℝ) : (omegaIncrement z).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul (omegaPower_multiplicative z)

lemma omegaIncrement_mul_zeta (z : ℝ) :
    omegaIncrement z * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = omegaPower z := by
  calc
    omegaIncrement z * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
        omegaPower z * ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
      rw [omegaIncrement]
      ac_rfl
    _ = omegaPower z := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]

lemma omegaIncrement_prime_pow_succ (z : ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    omegaIncrement z (p ^ (e + 1)) = (z - 1) * z ^ e := by
  have hsum (r : ℕ) :
      (∑ k ∈ Finset.range (r + 1), omegaIncrement z (p ^ k)) = z ^ r := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f (p ^ r))
      (omegaIncrement_mul_zeta z)
    rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp] at h
    rw [omegaPower_apply (pow_ne_zero r hp.ne_zero),
      ArithmeticFunction.cardFactors_apply_prime_pow hp] at h
    exact h
  have hnext := hsum (e + 1)
  have hprev := hsum e
  rw [Finset.sum_range_succ] at hnext
  calc
    omegaIncrement z (p ^ (e + 1)) = z ^ (e + 1) - z ^ e := by linarith
    _ = (z - 1) * z ^ e := by rw [pow_succ]; ring

lemma omegaIncrement_nonneg (z : ℝ) (hz : 1 ≤ z) (n : ℕ) :
    0 ≤ omegaIncrement z n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [(omegaIncrement_multiplicative z).multiplicative_factorization _ hn]
  apply Finset.prod_nonneg
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hePos : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hePos)
  change 0 ≤ omegaIncrement z (p ^ n.factorization p)
  rw [he, omegaIncrement_prime_pow_succ z hpPrime e]
  positivity

lemma omegaPower_eq_sum_divisors (z : ℝ) {n : ℕ} (hn : n ≠ 0) :
    z ^ Ω n = ∑ d ∈ n.divisors, omegaIncrement z d := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (omegaIncrement_mul_zeta z)
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  rw [omegaPower_apply hn] at h
  exact h.symm

lemma omega_weighted_sum_le_increment_recip (N : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (∑ m ∈ Finset.Icc 1 N, z ^ Ω m) ≤
      (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, omegaIncrement z d / (d : ℝ) := by
  classical
  calc
    (∑ m ∈ Finset.Icc 1 N, z ^ Ω m) =
        ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ m.divisors, omegaIncrement z d := by
      apply Finset.sum_congr rfl
      intro m hm
      exact omegaPower_eq_sum_divisors z (by
        have := (Finset.mem_Icc.mp hm).1
        omega)
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
        ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ m), omegaIncrement z d := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc]
        have hd' := Nat.mem_divisors.mp hd
        have hmpos : 0 < m := by omega
        exact ⟨⟨Nat.succ_le_iff.mpr (Nat.pos_of_mem_divisors hd),
          (Nat.le_of_dvd hmpos hd'.1).trans (Finset.mem_Icc.mp hm).2⟩, hd'.1⟩
      · intro d hd hnot
        exact omegaIncrement_nonneg z hz d
    _ = ∑ d ∈ Finset.Icc 1 N,
        (((Finset.Icc 1 N).filter fun m => d ∣ m).card : ℝ) * omegaIncrement z d := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ((N : ℝ) / d) * omegaIncrement z d := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1
      have hcard := Erdos202.card_Icc_filter_dvd_le_div N d hdpos
      have hcardR : (((Finset.Icc 1 N).filter fun m => d ∣ m).card : ℝ) ≤
          (N : ℝ) / d := (Nat.cast_le.mpr hcard).trans Nat.cast_div_le
      exact mul_le_mul_of_nonneg_right hcardR (omegaIncrement_nonneg z hz d)
    _ = (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, omegaIncrement z d / (d : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
      field_simp

noncomputable def incrementDiv (z : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else omegaIncrement z n / (n : ℝ), by simp⟩

lemma incrementDiv_apply {z : ℝ} {n : ℕ} (hn : n ≠ 0) :
    incrementDiv z n = omegaIncrement z n / (n : ℝ) := by simp [incrementDiv, hn]

lemma incrementDiv_multiplicative (z : ℝ) : (incrementDiv z).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [incrementDiv, omegaIncrement_multiplicative z |>.map_one]
  · intro m n hm hn hcop
    rw [incrementDiv_apply hm, incrementDiv_apply hn, incrementDiv_apply (mul_ne_zero hm hn),
      (omegaIncrement_multiplicative z).map_mul_of_coprime hcop]
    push_cast
    field_simp

lemma incrementDiv_prime_pow_succ (z : ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    incrementDiv z (p ^ (e + 1)) =
      (z - 1) / (p : ℝ) * (z / (p : ℝ)) ^ e := by
  rw [incrementDiv_apply (pow_ne_zero _ hp.ne_zero), omegaIncrement_prime_pow_succ z hp]
  push_cast
  rw [pow_succ]
  field_simp
  ring

lemma incrementDiv_nonneg (z : ℝ) (hz : 1 ≤ z) (n : ℕ) : 0 ≤ incrementDiv z n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [incrementDiv_apply hn]
  exact div_nonneg (omegaIncrement_nonneg z hz n) (by positivity)

lemma increment_recip_le_factorial_divisors (N : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (∑ d ∈ Finset.Icc 1 N, omegaIncrement z d / (d : ℝ)) ≤
      ∑ d ∈ N.factorial.divisors, incrementDiv z d := by
  calc
    (∑ d ∈ Finset.Icc 1 N, omegaIncrement z d / (d : ℝ)) =
        ∑ d ∈ Finset.Icc 1 N, incrementDiv z d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [incrementDiv_apply]
      exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1)
    _ ≤ ∑ d ∈ N.factorial.divisors, incrementDiv z d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Nat.mem_divisors]
        exact ⟨Nat.dvd_factorial
          (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1)
          (Finset.mem_Icc.mp hd).2,
          ne_of_gt (Nat.factorial_pos N)⟩
      · intro d hd hnot
        rw [incrementDiv_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
        exact div_nonneg (omegaIncrement_nonneg z hz d) (by positivity)

lemma factorial_divisor_sum_eq_euler (N : ℕ) (z : ℝ) :
    (∑ d ∈ N.factorial.divisors, incrementDiv z d) =
      ∏ p ∈ N.factorial.primeFactors,
        ∑ k ∈ Finset.range (N.factorial.factorization p + 1), incrementDiv z (p ^ k) := by
  let h := incrementDiv z * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  calc
    (∑ d ∈ N.factorial.divisors, incrementDiv z d) = h N.factorial := by
      change (∑ d ∈ N.factorial.divisors, incrementDiv z d) =
        (incrementDiv z * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) N.factorial
      exact ArithmeticFunction.coe_mul_zeta_apply.symm
    _ = ∏ p ∈ N.factorial.primeFactors, h (p ^ N.factorial.factorization p) := by
      rw [((incrementDiv_multiplicative z).mul
        ArithmeticFunction.isMultiplicative_zeta.natCast).multiplicative_factorization h
          (ne_of_gt (Nat.factorial_pos N))]
      rfl
    _ = ∏ p ∈ N.factorial.primeFactors,
          ∑ k ∈ Finset.range (N.factorial.factorization p + 1), incrementDiv z (p ^ k) := by
      apply Finset.prod_congr rfl
      intro p hp
      change (incrementDiv z * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
          (p ^ N.factorial.factorization p) = _
      rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow
        (Nat.prime_of_mem_primeFactors hp)]

lemma incrementDiv_euler_factor_le (z : ℝ) {p E : ℕ}
    (hz1 : 1 ≤ z) (hp : p.Prime) (hzp : z < p) :
    (∑ k ∈ Finset.range (E + 1), incrementDiv z (p ^ k)) ≤
      1 + (z - 1) / ((p : ℝ) - z) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr0 : 0 ≤ z / (p : ℝ) := div_nonneg (by linarith) hpR.le
  have hr1 : z / (p : ℝ) < 1 := (div_lt_one hpR).2 hzp
  rw [Finset.sum_range_succ']
  have hterms :
      (∑ k ∈ Finset.range E, incrementDiv z (p ^ (k + 1))) =
        (z - 1) / (p : ℝ) * ∑ k ∈ Finset.range E, (z / (p : ℝ)) ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact incrementDiv_prime_pow_succ z hp k
  rw [hterms]
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 0) (n := E) hr0 hr1
  simp only [Nat.Ico_zero_eq_range, pow_zero, one_div] at hgeom
  have hcoef : 0 ≤ (z - 1) / (p : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hgeom hcoef
  have hzero : incrementDiv z (p ^ 0) = 1 := by
    simpa using (incrementDiv_multiplicative z).map_one
  rw [hzero]
  calc
    (z - 1) / (p : ℝ) * ∑ k ∈ Finset.range E, (z / (p : ℝ)) ^ k + 1 ≤
        (z - 1) / (p : ℝ) * (1 - z / (p : ℝ))⁻¹ + 1 := by linarith
    _ = 1 + (z - 1) / ((p : ℝ) - z) := by
      field_simp
      ring

lemma small_euler_factor_le_two {p E : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.range (E + 1), incrementDiv ((21 : ℝ) / 20) (p ^ k)) ≤ 2 := by
  have hb := incrementDiv_euler_factor_le ((21 : ℝ) / 20) (E := E)
    (by norm_num) hp (by
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : ((21 : ℝ) / 20 - 1) / ((p : ℝ) - 21 / 20) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  linarith

lemma large_euler_factor_le_exp {p E : ℕ} (hp : p.Prime) (hp13 : 13 ≤ p) :
    (∑ k ∈ Finset.range (E + 1), incrementDiv ((21 : ℝ) / 20) (p ^ k)) ≤
      Real.exp ((11 : ℝ) / 200 / p) := by
  have hb := incrementDiv_euler_factor_le ((21 : ℝ) / 20) (E := E)
    (by norm_num) hp (by
      have hpR : (13 : ℝ) ≤ p := by exact_mod_cast hp13
      linarith)
  have hpR : (13 : ℝ) ≤ p := by exact_mod_cast hp13
  have hfrac : (((21 : ℝ) / 20 - 1) / ((p : ℝ) - 21 / 20)) ≤
      (11 : ℝ) / 200 / p := by
    have hpPos : (0 : ℝ) < p := by positivity
    have hden : (0 : ℝ) < (p : ℝ) - 21 / 20 := by linarith
    rw [div_le_div_iff₀ hden hpPos]
    norm_num
    nlinarith
  exact hb.trans (by linarith [hfrac, Real.add_one_le_exp ((11 : ℝ) / 200 / p)])

lemma factorial_euler_product_bound (N : ℕ) :
    (∏ p ∈ N.factorial.primeFactors,
        ∑ k ∈ Finset.range (N.factorial.factorization p + 1),
          incrementDiv ((21 : ℝ) / 20) (p ^ k)) ≤
      32 * Real.exp ((11 : ℝ) / 200 *
        ∑ p ∈ N.factorial.primeFactors, (1 : ℝ) / p) := by
  let P := N.factorial.primeFactors
  let f : ℕ → ℝ := fun p =>
    ∑ k ∈ Finset.range (N.factorial.factorization p + 1),
      incrementDiv ((21 : ℝ) / 20) (p ^ k)
  have hsplit :
      (∏ p ∈ P, f p) = (∏ p ∈ P.filter (fun p => p < 13), f p) *
        ∏ p ∈ P.filter (fun p => ¬p < 13), f p := by
    exact (Finset.prod_filter_mul_prod_filter_not P (fun p => p < 13) f).symm
  have hf0 (p : ℕ) : 0 ≤ f p := by
    dsimp [f]
    apply Finset.sum_nonneg
    intro k hk
    exact incrementDiv_nonneg ((21 : ℝ) / 20) (by norm_num) _
  rw [hsplit]
  have hsmall : (∏ p ∈ P.filter (fun p => p < 13), f p) ≤ 32 := by
    calc
      (∏ p ∈ P.filter (fun p => p < 13), f p) ≤
          ∏ p ∈ P.filter (fun p => p < 13), (2 : ℝ) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact hf0 p
        · intro p hp
          exact small_euler_factor_le_two (Nat.prime_of_mem_primeFactors
            (Finset.mem_filter.mp hp).1)
      _ = 2 ^ (P.filter (fun p => p < 13)).card := by simp
      _ ≤ 2 ^ 5 := by
        have hsub : P.filter (fun p => p < 13) ⊆ ({2, 3, 5, 7, 11} : Finset ℕ) := by
          intro p hp
          have hp' := Finset.mem_filter.mp hp
          have hpPrime := Nat.prime_of_mem_primeFactors hp'.1
          have hp2 := hpPrime.two_le
          have hple : p ≤ 12 := by omega
          interval_cases p <;> norm_num at hpPrime
          all_goals simp
        have hc := Finset.card_le_card hsub
        norm_num at hc
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hc
      _ = 32 := by norm_num
  have hlarge : (∏ p ∈ P.filter (fun p => ¬p < 13), f p) ≤
      Real.exp ((11 : ℝ) / 200 * ∑ p ∈ P, (1 : ℝ) / p) := by
    calc
      (∏ p ∈ P.filter (fun p => ¬p < 13), f p) ≤
          ∏ p ∈ P.filter (fun p => ¬p < 13),
            Real.exp ((11 : ℝ) / 200 / p) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact hf0 p
        · intro p hp
          have hpnot := (Finset.mem_filter.mp hp).2
          exact large_euler_factor_le_exp
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1) (by omega)
      _ = Real.exp (∑ p ∈ P.filter (fun p => ¬p < 13),
            (11 : ℝ) / 200 / p) := by rw [← Real.exp_sum]
      _ ≤ Real.exp ((11 : ℝ) / 200 * ∑ p ∈ P, (1 : ℝ) / p) := by
        apply Real.exp_le_exp.mpr
        calc
          (∑ p ∈ P.filter (fun p => ¬p < 13), (11 : ℝ) / 200 / p) ≤
              ∑ p ∈ P, (11 : ℝ) / 200 / p := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro p hp hnot
            have hpPrime := Nat.prime_of_mem_primeFactors hp
            exact div_nonneg (by norm_num) (by exact_mod_cast hpPrime.pos.le)
          _ = (11 : ℝ) / 200 * ∑ p ∈ P, (1 : ℝ) / p := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            ring
  have hnonnegLarge : 0 ≤ ∏ p ∈ P.filter (fun p => ¬p < 13), f p := by
    apply Finset.prod_nonneg
    intro p hp
    exact hf0 p
  exact (mul_le_mul hsmall hlarge hnonnegLarge (by norm_num)).trans_eq (by ring)

lemma factorial_prime_reciprocal_mertens :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∑ p ∈ N.factorial.primeFactors, (1 : ℝ) / p) ≤
        Real.log (Real.log (N : ℝ)) + C := by
  obtain ⟨C, hC⟩ := Mertens.sum_prime_div_eq_log_log
  refine ⟨C, ?_⟩
  intro N hN
  have hM := hC (N : ℝ) (by exact_mod_cast hN)
  have hsub : N.factorial.primeFactors ⊆
      (Finset.Ioc 0 ⌊(N : ℝ)⌋₊).filter Nat.Prime := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    rw [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · constructor
      · exact hpPrime.pos
      · rw [Nat.floor_natCast]
        exact (hpPrime.dvd_factorial).mp (Nat.dvd_of_mem_primeFactors hp)
    · exact hpPrime
  have hsum : (∑ p ∈ N.factorial.primeFactors, (1 : ℝ) / p) ≤
      ∑ p ∈ (Finset.Ioc 0 ⌊(N : ℝ)⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp hnot
    have hpPrime := (Finset.mem_filter.mp hp).2
    exact div_nonneg zero_le_one (by exact_mod_cast hpPrime.pos.le)
  linarith [abs_le.mp hM |>.2]

theorem omega_weighted_sum_bound :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m) ≤
        32 * (N : ℝ) * Real.exp ((11 : ℝ) / 200 *
          (Real.log (Real.log (N : ℝ)) + C)) := by
  obtain ⟨C, hC⟩ := factorial_prime_reciprocal_mertens
  refine ⟨C, ?_⟩
  intro N hN
  calc
    (∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m) ≤
        (N : ℝ) * ∑ d ∈ Finset.Icc 1 N,
          omegaIncrement ((21 : ℝ) / 20) d / (d : ℝ) :=
      omega_weighted_sum_le_increment_recip N _ (by norm_num)
    _ ≤ (N : ℝ) * ∑ d ∈ N.factorial.divisors,
          incrementDiv ((21 : ℝ) / 20) d := by
      gcongr
      exact increment_recip_le_factorial_divisors N _ (by norm_num)
    _ = (N : ℝ) * ∏ p ∈ N.factorial.primeFactors,
          ∑ k ∈ Finset.range (N.factorial.factorization p + 1),
            incrementDiv ((21 : ℝ) / 20) (p ^ k) := by
      rw [factorial_divisor_sum_eq_euler]
    _ ≤ (N : ℝ) * (32 * Real.exp ((11 : ℝ) / 200 *
          ∑ p ∈ N.factorial.primeFactors, (1 : ℝ) / p)) := by
      gcongr
      exact factorial_euler_product_bound N
    _ ≤ (N : ℝ) * (32 * Real.exp ((11 : ℝ) / 200 *
          (Real.log (Real.log (N : ℝ)) + C))) := by
      gcongr
      exact hC N hN
    _ = 32 * (N : ℝ) * Real.exp ((11 : ℝ) / 200 *
          (Real.log (Real.log (N : ℝ)) + C)) := by ring

def thresholdSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun r => n < r * r.minFac

def minimalThresholdSet (n : ℕ) : Finset ℕ :=
  (thresholdSet n).filter fun a =>
    ∀ c ∈ thresholdSet n, c ∣ a → a ∣ c

lemma threshold_minimal_cover {n r : ℕ} (hr : r ∈ thresholdSet n) :
    ∃ a ∈ minimalThresholdSet n, a ∣ r := by
  classical
  let D := (thresholdSet n).filter fun c => c ∣ r
  have hD : D.Nonempty := ⟨r, Finset.mem_filter.mpr ⟨hr, dvd_rfl⟩⟩
  let a := D.min' hD
  have haD : a ∈ D := Finset.min'_mem D hD
  have haParts := Finset.mem_filter.mp haD
  refine ⟨a, ?_, haParts.2⟩
  rw [minimalThresholdSet, Finset.mem_filter]
  refine ⟨haParts.1, ?_⟩
  intro c hc hca
  have hcr : c ∣ r := dvd_trans hca haParts.2
  have hcD : c ∈ D := Finset.mem_filter.mpr ⟨hc, hcr⟩
  have hac : a ≤ c := Finset.min'_le D c hcD
  have hcpos : 0 < c := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1
    omega
  have hapos : 0 < a := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp haParts.1).1).1
    omega
  have hcaLe : c ≤ a := Nat.le_of_dvd hapos hca
  exact (Nat.le_antisymm hcaLe hac) ▸ dvd_rfl

lemma minimalThreshold_antichain {n a b : ℕ}
    (ha : a ∈ minimalThresholdSet n) (hb : b ∈ minimalThresholdSet n)
    (hab : a ≠ b) : ¬a ∣ b := by
  intro hdvd
  have hbparts := Finset.mem_filter.mp hb
  have haparts := Finset.mem_filter.mp ha
  have hba := hbparts.2 a haparts.1 hdvd
  exact hab (Nat.dvd_antisymm hdvd hba)

lemma minimalThreshold_lcm_gt_of_lt {n a b : ℕ}
    (ha : a ∈ minimalThresholdSet n) (hb : b ∈ minimalThresholdSet n)
    (hab : a < b) : n < Nat.lcm a b := by
  have haT := (Finset.mem_filter.mp ha).1
  have hbT := (Finset.mem_filter.mp hb).1
  have haIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp haT).1
  have hbIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hbT).1
  have hapos : 0 < a := by omega
  have hbpos : 0 < b := by omega
  let g := Nat.gcd a b
  let q₁ := a / g
  let q₂ := b / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b hapos
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have haeq : g * q₁ = a := by
    dsimp [q₁]
    simpa [mul_comm] using Nat.div_mul_cancel hga
  have hbeq : g * q₂ = b := by
    dsimp [q₂]
    simpa [mul_comm] using Nat.div_mul_cancel hgb
  have hq_lt : q₁ < q₂ := by
    rw [← (Nat.mul_lt_mul_left hgpos)]
    simpa [haeq, hbeq] using hab
  have hq1ne : q₁ ≠ 1 := by
    intro hq
    rw [hq, mul_one] at haeq
    have hag : a = g := haeq.symm
    have habDvd : a ∣ b := hag ▸ hgb
    exact minimalThreshold_antichain ha hb (ne_of_lt hab) habDvd
  have hq1two : 2 ≤ q₁ := by
    have hqpos : 0 < q₁ := by
      have : 0 < g * q₁ := haeq.symm ▸ hapos
      exact Nat.pos_of_mul_pos_left this
    omega
  have hq1dvd : q₁ ∣ a := ⟨g, by simpa [mul_comm] using haeq.symm⟩
  have hmin : a.minFac ≤ q₁ := Nat.minFac_le_of_dvd hq1two hq1dvd
  have hlcmEq : Nat.lcm a b = g * q₁ * q₂ := by
    have hprod := Nat.gcd_mul_lcm a b
    have hcancel : Nat.lcm a b = g * q₁ * q₂ := by
      apply Nat.eq_of_mul_eq_mul_left hgpos
      change g * Nat.lcm a b = g * (g * q₁ * q₂)
      calc
        g * Nat.lcm a b = a * b := by simpa [g] using hprod
        _ = (g * q₁) * (g * q₂) := by rw [haeq, hbeq]
        _ = g * (g * q₁ * q₂) := by ring
    exact hcancel
  have haThresh : n < a * a.minFac := (Finset.mem_filter.mp haT).2
  calc
    n < a * a.minFac := haThresh
    _ ≤ a * q₁ := Nat.mul_le_mul_left a hmin
    _ < a * q₂ := (Nat.mul_lt_mul_left hapos).2 hq_lt
    _ = Nat.lcm a b := by rw [hlcmEq, ← haeq]

lemma minimalThreshold_admissible (n : ℕ) :
    PairwiseLCMExceeds n (minimalThresholdSet n) := by
  constructor
  · intro a ha
    have haT := (Finset.mem_filter.mp ha).1
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp haT).1
  · intro a ha b hb hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact minimalThreshold_lcm_gt_of_lt ha hb hlt
    · rw [Nat.lcm_comm]
      exact minimalThreshold_lcm_gt_of_lt hb ha hgt

lemma uncovered_not_threshold {n b : ℕ}
    (hb : b ∈ uncovered n (minimalThresholdSet n)) : b ∉ thresholdSet n := by
  intro hbT
  obtain ⟨a, ha, hab⟩ := threshold_minimal_cover hbT
  have hb' := Finset.mem_filter.mp hb
  exact hb'.2 a ha hab

lemma uncovered_power_bound {n b : ℕ}
    (hb : b ∈ uncovered n (minimalThresholdSet n)) :
    b ^ (2 ^ Ω b) ≤ n ^ (2 ^ Ω b - 1) := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
      have hbParts := Finset.mem_filter.mp hb
      have hbIcc := Finset.mem_Icc.mp hbParts.1
      by_cases hb1 : b = 1
      · subst b
        simp
      · have hbgt : 1 < b := by omega
        let p := b.minFac
        let c := b / p
        have hpPrime : p.Prime := Nat.minFac_prime hb1
        have hp2 : 2 ≤ p := hpPrime.two_le
        have hpdvd : p ∣ b := Nat.minFac_dvd b
        have hceq : c * p = b := by
          dsimp [c]
          exact Nat.div_mul_cancel hpdvd
        have hcpos : 0 < c := by
          dsimp [c]
          exact Nat.div_pos (Nat.minFac_le (by omega)) hpPrime.pos
        have hclt : c < b := by
          dsimp [c]
          exact Nat.div_lt_self (by omega) (by omega)
        have hcIcc : c ∈ Finset.Icc 1 n := by
          rw [Finset.mem_Icc]
          exact ⟨hcpos, (Nat.le_of_dvd (by omega) ⟨p, hceq.symm⟩).trans hbIcc.2⟩
        have hcUncovered : c ∈ uncovered n (minimalThresholdSet n) := by
          rw [uncovered, Finset.mem_filter]
          refine ⟨hcIcc, ?_⟩
          intro a ha hac
          exact hbParts.2 a ha (dvd_trans hac ⟨p, hceq.symm⟩)
        have hOmega : Ω b = Ω c + 1 := by
          rw [← hceq, ArithmeticFunction.cardFactors_mul (ne_of_gt hcpos) hpPrime.ne_zero,
            ArithmeticFunction.cardFactors_apply_prime hpPrime]
        have hnotT := uncovered_not_threshold hb
        have hbp : b * p ≤ n := by
          rw [thresholdSet, Finset.mem_filter] at hnotT
          push_neg at hnotT
          exact hnotT hbParts.1
        have hbSq : b ^ 2 ≤ n * c := by
          have hmul := Nat.mul_le_mul_left c hbp
          calc
            b ^ 2 = c * (b * p) := by rw [pow_two, ← hceq]; ring
            _ ≤ c * n := hmul
            _ = n * c := by ring
        have hIH := ih c hclt hcUncovered
        rw [hOmega]
        let E := 2 ^ Ω c
        have hpow := Nat.pow_le_pow_left hbSq E
        have hmulIH := Nat.mul_le_mul_left (n ^ E) hIH
        dsimp [E] at hpow hmulIH ⊢
        calc
          b ^ (2 ^ (Ω c + 1)) = (b ^ 2) ^ (2 ^ Ω c) := by
            rw [← pow_mul]
            congr 1
            rw [pow_succ]
            omega
          _ ≤ (n * c) ^ (2 ^ Ω c) := hpow
          _ = n ^ (2 ^ Ω c) * c ^ (2 ^ Ω c) := by rw [mul_pow]
          _ ≤ n ^ (2 ^ Ω c) * n ^ (2 ^ Ω c - 1) := hmulIH
          _ = n ^ (2 ^ (Ω c + 1) - 1) := by
            rw [← pow_add, pow_succ]
            congr 1
            have hpos : 0 < 2 ^ Ω c := pow_pos (by omega) _
            have : 1 ≤ 2 ^ Ω c := by omega
            omega

/-! ### The explicit sparse subsequence -/

/-- The exponent used for the ambient interval at stage `t`. -/
def constructionExponent (t : ℕ) : ℕ := 2 ^ (6 * t)

/-- The ambient endpoint at stage `t`. -/
def constructionAmbient (t : ℕ) : ℕ := 2 ^ constructionExponent t

/-- The minimal-threshold family at stage `t`. -/
def constructionFamily (t : ℕ) : Finset ℕ :=
  minimalThresholdSet (constructionAmbient t)

lemma constructionFamily_admissible (t : ℕ) :
    PairwiseLCMExceeds (constructionAmbient t) (constructionFamily t) := by
  exact minimalThreshold_admissible _

lemma pow_two_le_constructionExponent {t e : ℕ} (he : e ≤ 5 * t) :
    2 ^ t * 2 ^ e ≤ constructionExponent t := by
  calc
    2 ^ t * 2 ^ e ≤ 2 ^ t * 2 ^ (5 * t) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) he)
    _ = constructionExponent t := by
      rw [← pow_add]
      simp only [constructionExponent]
      congr 1
      omega

lemma lowOmega_uncovered_le {t b : ℕ}
    (hb : b ∈ uncovered (constructionAmbient t) (constructionFamily t))
    (hΩ : Ω b ≤ 5 * t) :
    b ≤ 2 ^ (constructionExponent t - 2 ^ t) := by
  have hpow := uncovered_power_bound hb
  let E := 2 ^ Ω b
  let R := constructionExponent t
  let D := 2 ^ t
  have hEpos : 0 < E := by positivity
  have hDE : D * E ≤ R := by
    exact pow_two_le_constructionExponent hΩ
  have hDR : D ≤ R := le_trans (Nat.le_mul_of_pos_right D (by positivity)) hDE
  have hexp : R * (E - 1) ≤ (R - D) * E := by
    rw [Nat.mul_sub_left_distrib, Nat.sub_mul]
    simpa using Nat.sub_le_sub_left hDE (R * E)
  have htarget : b ^ E ≤ (2 ^ (R - D)) ^ E := by
    calc
      b ^ E ≤ (2 ^ R) ^ (E - 1) := by
        simpa [constructionAmbient, R, E] using hpow
      _ = 2 ^ (R * (E - 1)) := by rw [pow_mul]
      _ ≤ 2 ^ ((R - D) * E) := Nat.pow_le_pow_right (by omega) hexp
      _ = (2 ^ (R - D)) ^ E := by rw [pow_mul]
  simpa [D, R] using (Nat.pow_le_pow_iff_left hEpos.ne').mp htarget

def highOmegaUpTo (N K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun m => K < Ω m

lemma uncovered_card_le_low_add_high (t : ℕ) :
    (uncovered (constructionAmbient t) (constructionFamily t)).card ≤
      2 ^ (constructionExponent t - 2 ^ t) +
        (highOmegaUpTo (constructionAmbient t) (5 * t)).card := by
  let B := 2 ^ (constructionExponent t - 2 ^ t)
  let H := highOmegaUpTo (constructionAmbient t) (5 * t)
  have hsub : uncovered (constructionAmbient t) (constructionFamily t) ⊆
      Finset.Icc 1 B ∪ H := by
    intro b hb
    by_cases hΩ : Ω b ≤ 5 * t
    · rw [Finset.mem_union]
      exact Or.inl (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1,
          lowOmega_uncovered_le hb hΩ⟩)
    · rw [Finset.mem_union]
      exact Or.inr (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hb).1, Nat.lt_of_not_ge hΩ⟩)
  calc
    (uncovered (constructionAmbient t) (constructionFamily t)).card ≤
        (Finset.Icc 1 B ∪ H).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 B).card + H.card := Finset.card_union_le _ _
    _ = B + H.card := by simp [B]

lemma highOmega_card_weight_le (N K : ℕ) :
    ((highOmegaUpTo N K).card : ℝ) * ((21 : ℝ) / 20) ^ (K + 1) ≤
      ∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m := by
  calc
    ((highOmegaUpTo N K).card : ℝ) * ((21 : ℝ) / 20) ^ (K + 1) =
        ∑ m ∈ highOmegaUpTo N K, ((21 : ℝ) / 20) ^ (K + 1) := by simp
    _ ≤ ∑ m ∈ highOmegaUpTo N K, ((21 : ℝ) / 20) ^ Ω m := by
      apply Finset.sum_le_sum
      intro m hm
      exact pow_le_pow_right₀ (by norm_num) (Finset.mem_filter.mp hm).2
    _ ≤ ∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro m hm hnot
      positivity

lemma log_log_constructionAmbient_le (t : ℕ) :
    Real.log (Real.log (constructionAmbient t : ℝ)) ≤
      (21 : ℝ) / 5 * t := by
  have hRpos : (0 : ℝ) < constructionExponent t := by
    exact_mod_cast (show 0 < constructionExponent t by
      simp [constructionExponent])
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hloglog2 : Real.log (Real.log (2 : ℝ)) ≤ 0 :=
    Real.log_nonpos hlog2pos.le (by
      linarith [Real.log_two_lt_d9])
  have hmain : ((6 * t : ℕ) : ℝ) * Real.log (2 : ℝ) ≤
      (21 : ℝ) / 5 * t := by
    push_cast
    have ht : (0 : ℝ) ≤ t := by positivity
    nlinarith [Real.log_two_lt_d9]
  rw [constructionAmbient, Nat.cast_pow, Real.log_pow,
    Real.log_mul hRpos.ne' (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))]
  have hRlog : Real.log (constructionExponent t : ℝ) =
      ((6 * t : ℕ) : ℝ) * Real.log (2 : ℝ) := by
    rw [constructionExponent, Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hRlog]
  linarith

lemma highOmega_density_le_geometric (C : ℝ)
    (hC : ∀ N : ℕ, 2 ≤ N →
      (∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m) ≤
        32 * (N : ℝ) * Real.exp ((11 : ℝ) / 200 *
          (Real.log (Real.log (N : ℝ)) + C))) (t : ℕ) :
    ((highOmegaUpTo (constructionAmbient t) (5 * t)).card : ℝ) /
        constructionAmbient t ≤
      (32 * Real.exp ((11 : ℝ) / 200 * C)) *
        (Real.exp (-(149 : ℝ) / 21000)) ^ t := by
  let N := constructionAmbient t
  let K := 5 * t + 1
  let z : ℝ := 21 / 20
  let A : ℝ := (11 : ℝ) / 200 * (Real.log (Real.log (N : ℝ)) + C)
  have hN2 : 2 ≤ N := by
    dsimp [N, constructionAmbient, constructionExponent]
    exact Nat.one_lt_pow (by positivity) (by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN2)
  have hzpos : 0 < z := by norm_num [z]
  have hzpowpos : 0 < z ^ K := pow_pos hzpos _
  have hweighted := hC N hN2
  have hmark := highOmega_card_weight_le N (5 * t)
  have hcardWeighted :
      ((highOmegaUpTo N (5 * t)).card : ℝ) * z ^ K ≤
        32 * (N : ℝ) * Real.exp A := by
    exact hmark.trans (by simpa [z, K, A] using hweighted)
  have hraw :
      ((highOmegaUpTo N (5 * t)).card : ℝ) / (N : ℝ) ≤
        32 * Real.exp A / z ^ K := by
    apply (div_le_iff₀ hNpos).2
    calc
      ((highOmegaUpTo N (5 * t)).card : ℝ) ≤
          (32 * (N : ℝ) * Real.exp A) / z ^ K :=
        (le_div_iff₀ hzpowpos).2 hcardWeighted
      _ = (32 * Real.exp A / z ^ K) * (N : ℝ) := by ring
  have hlogz : (1 : ℝ) / 21 ≤ Real.log z := by
    dsimp [z]
    convert Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 21 / 20 by norm_num) using 1 <;>
      norm_num
  have hAexp :
      A - (K : ℝ) * Real.log z ≤
        -(149 : ℝ) / 21000 * t + (11 : ℝ) / 200 * C := by
    have hloglog := log_log_constructionAmbient_le t
    have ht : (0 : ℝ) ≤ t := by positivity
    dsimp [A, K, N]
    push_cast
    nlinarith
  calc
    ((highOmegaUpTo (constructionAmbient t) (5 * t)).card : ℝ) /
        constructionAmbient t ≤ 32 * Real.exp A / z ^ K := by
      simpa [N] using hraw
    _ = 32 * Real.exp (A - (K : ℝ) * Real.log z) := by
      rw [Real.exp_sub]
      have hzexp : Real.exp ((K : ℝ) * Real.log z) = z ^ K := by
        rw [Real.exp_nat_mul, Real.exp_log hzpos]
      rw [hzexp]
      ring
    _ ≤ 32 * Real.exp (-(149 : ℝ) / 21000 * t + (11 : ℝ) / 200 * C) := by
      gcongr
    _ = (32 * Real.exp ((11 : ℝ) / 200 * C)) *
        (Real.exp (-(149 : ℝ) / 21000)) ^ t := by
      rw [Real.exp_add]
      have hexp : Real.exp (-(149 : ℝ) / 21000 * (t : ℝ)) =
          (Real.exp (-(149 : ℝ) / 21000)) ^ t := by
        rw [mul_comm, Real.exp_nat_mul]
      rw [hexp]
      ring

lemma self_le_two_pow (t : ℕ) : t ≤ 2 ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
      omega

lemma lowPart_density_le_geometric (t : ℕ) :
    ((2 ^ (constructionExponent t - 2 ^ t) : ℕ) : ℝ) /
        constructionAmbient t ≤ ((1 : ℝ) / 2) ^ t := by
  let R := constructionExponent t
  let D := 2 ^ t
  have hDR : D ≤ R := by
    dsimp [D, R, constructionExponent]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hR : R - D + D = R := Nat.sub_add_cancel hDR
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have heq : ((2 : ℝ) ^ (R - D)) / (2 : ℝ) ^ R = ((1 : ℝ) / 2) ^ D := by
    have hden : (2 : ℝ) ^ R = (2 : ℝ) ^ (R - D) * (2 : ℝ) ^ D := by
      rw [← pow_add, hR]
    rw [hden, div_pow]
    field_simp
    simp
  calc
    ((2 ^ (constructionExponent t - 2 ^ t) : ℕ) : ℝ) /
        constructionAmbient t = ((1 : ℝ) / 2) ^ D := by
      simpa [constructionAmbient, R, D] using heq
    _ ≤ ((1 : ℝ) / 2) ^ t :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (self_le_two_pow t)

lemma uncovered_density_le_geometric (C : ℝ)
    (hC : ∀ N : ℕ, 2 ≤ N →
      (∑ m ∈ Finset.Icc 1 N, ((21 : ℝ) / 20) ^ Ω m) ≤
        32 * (N : ℝ) * Real.exp ((11 : ℝ) / 200 *
          (Real.log (Real.log (N : ℝ)) + C))) (t : ℕ) :
    ((uncovered (constructionAmbient t) (constructionFamily t)).card : ℝ) /
        constructionAmbient t ≤
      ((1 : ℝ) / 2) ^ t +
        (32 * Real.exp ((11 : ℝ) / 200 * C)) *
          (Real.exp (-(149 : ℝ) / 21000)) ^ t := by
  have hcard := uncovered_card_le_low_add_high t
  have hcast :
      ((uncovered (constructionAmbient t) (constructionFamily t)).card : ℝ) ≤
        (2 ^ (constructionExponent t - 2 ^ t) : ℕ) +
          ((highOmegaUpTo (constructionAmbient t) (5 * t)).card : ℝ) := by
    exact_mod_cast hcard
  have hNpos : (0 : ℝ) < constructionAmbient t := by
    exact_mod_cast (show 0 < constructionAmbient t by
      simp [constructionAmbient])
  calc
    ((uncovered (constructionAmbient t) (constructionFamily t)).card : ℝ) /
        constructionAmbient t ≤
      (((2 ^ (constructionExponent t - 2 ^ t) : ℕ) : ℝ) +
        (highOmegaUpTo (constructionAmbient t) (5 * t)).card) /
          constructionAmbient t := (div_le_div_iff_of_pos_right hNpos).2 hcast
    _ = (((2 ^ (constructionExponent t - 2 ^ t) : ℕ) : ℝ) /
          constructionAmbient t) +
        (((highOmegaUpTo (constructionAmbient t) (5 * t)).card : ℝ) /
          constructionAmbient t) := by rw [add_div]
    _ ≤ ((1 : ℝ) / 2) ^ t +
        (32 * Real.exp ((11 : ℝ) / 200 * C)) *
          (Real.exp (-(149 : ℝ) / 21000)) ^ t := by
      gcongr
      · exact lowPart_density_le_geometric t
      · exact highOmega_density_le_geometric C hC t

/-- Along the explicit Schinzel--Szekeres subsequence, the proportion of integers
not dividing a selected member tends to zero. -/
theorem erdos542_uncovered_density_tendsto_zero :
    Filter.Tendsto
      (fun t : ℕ =>
        ((uncovered (constructionAmbient t) (constructionFamily t)).card : ℝ) /
          constructionAmbient t)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := omega_weighted_sum_bound
  let B : ℝ := 32 * Real.exp ((11 : ℝ) / 200 * C)
  let q : ℝ := Real.exp (-(149 : ℝ) / 21000)
  have hhalf : Filter.Tendsto (fun t : ℕ => ((1 : ℝ) / 2) ^ t)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hq0 : 0 ≤ q := Real.exp_pos _ |>.le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    norm_num
  have hq : Filter.Tendsto (fun t : ℕ => q ^ t)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hmajorant : Filter.Tendsto
      (fun t : ℕ => ((1 : ℝ) / 2) ^ t + B * q ^ t)
      Filter.atTop (nhds 0) := by
    simpa using hhalf.add (hq.const_mul B)
  refine squeeze_zero (g := fun t : ℕ => ((1 : ℝ) / 2) ^ t + B * q ^ t) ?_ ?_ hmajorant
  · intro t
    positivity
  · intro t
    simpa only [B, q] using uncovered_density_le_geometric C hC t

lemma covered_union_uncovered (n : ℕ) (A : Finset ℕ) :
    covered n A ∪ uncovered n A = Finset.Icc 1 n := by
  classical
  ext m
  simp only [covered, uncovered, multiples, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro (⟨a, ha, hmn, hdiv⟩ | ⟨hmn, _⟩)
    · exact hmn
    · exact hmn
  · intro hmn
    by_cases h : ∃ a ∈ A, a ∣ m
    · obtain ⟨a, ha, ham⟩ := h
      exact Or.inl ⟨a, ha, hmn, ham⟩
    · exact Or.inr ⟨hmn, by simpa only [not_exists, not_and] using h⟩

lemma covered_card_le_reciprocal (n : ℕ) (A : Finset ℕ)
    (hpos : ∀ a ∈ A, 1 ≤ a) :
    ((covered n A).card : ℝ) ≤ (n : ℝ) * reciprocalSum A := by
  classical
  calc
    ((covered n A).card : ℝ) ≤
        ∑ a ∈ A, ((multiples n a).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := A) (t := multiples n))
    _ ≤ ∑ a ∈ A, (n : ℝ) / a := by
      apply Finset.sum_le_sum
      intro a ha
      have ha0 : 0 < a := lt_of_lt_of_le Nat.zero_lt_one (hpos a ha)
      have hc := Erdos202.card_Icc_filter_dvd_le_div n a ha0
      calc
        ((multiples n a).card : ℝ) ≤ (n / a : ℕ) := by
          exact_mod_cast hc
        _ ≤ (n : ℝ) / a := Nat.cast_div_le
    _ = (n : ℝ) * reciprocalSum A := by
      rw [reciprocalSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

lemma reciprocalSum_lower_of_uncovered {n : ℕ} {A : Finset ℕ}
    (hn : 1 ≤ n) (hA : PairwiseLCMExceeds n A) :
    1 - ((uncovered n A).card : ℝ) / n ≤ reciprocalSum A := by
  have hunion := congrArg Finset.card (covered_union_uncovered n A)
  have hcardUnion := Finset.card_union_le (covered n A) (uncovered n A)
  have hcoverNat : n ≤ (covered n A).card + (uncovered n A).card := by
    have hIcc : (Finset.Icc 1 n).card = n := by simp
    omega
  have hcoverReal : (n : ℝ) ≤
      ((covered n A).card : ℝ) + (uncovered n A).card := by
    exact_mod_cast hcoverNat
  have hcovered := covered_card_le_reciprocal n A (fun a ha => (hA.1 a ha).1)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  calc
    1 - ((uncovered n A).card : ℝ) / n =
        ((n : ℝ) - (uncovered n A).card) / n := by field_simp
    _ ≤ reciprocalSum A := by
      apply (div_le_iff₀ hnR).2
      calc
        (n : ℝ) - (uncovered n A).card ≤ (covered n A).card := by linarith
        _ ≤ reciprocalSum A * (n : ℝ) := by simpa [mul_comm] using hcovered

/-- The same examples have reciprocal sum arbitrarily close to `1` from below. -/
theorem erdos542_construction_reciprocal_eventually
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℕ in Filter.atTop,
      1 - ε < reciprocalSum (constructionFamily t) := by
  have hd := (tendsto_order.1 erdos542_uncovered_density_tendsto_zero).2 (0 + ε) (by simpa)
  filter_upwards [hd] with t ht
  have hlower := reciprocalSum_lower_of_uncovered
    (n := constructionAmbient t) (A := constructionFamily t)
    (Nat.one_le_pow _ _ (by omega)) (constructionFamily_admissible t)
  linarith

/-- A precise formalization of the failed `\gg n` assertion in Problem 542. -/
def HasUniformLinearUncoveredLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ A : Finset ℕ,
    PairwiseLCMExceeds n A → c * n ≤ ((uncovered n A).card : ℝ)

/-- The second question in Problem 542 has a negative answer. -/
theorem erdos542_no_uniform_linear_uncovered_bound :
    ¬HasUniformLinearUncoveredLowerBound := by
  rintro ⟨c, hc, hbound⟩
  have hd := (tendsto_order.1 erdos542_uncovered_density_tendsto_zero).2 c hc
  obtain ⟨t, ht⟩ := hd.exists
  have hlin := hbound (constructionAmbient t) (constructionFamily t)
    (constructionFamily_admissible t)
  have hNpos : (0 : ℝ) < constructionAmbient t := by
    exact_mod_cast (show 0 < constructionAmbient t by simp [constructionAmbient])
  have hc_le : c ≤
      ((uncovered (constructionAmbient t) (constructionFamily t)).card : ℝ) /
        constructionAmbient t := by
    exact (le_div_iff₀ hNpos).2 (by simpa [mul_comm] using hlin)
  linarith

/-- The complete formal resolution of Erdős Problem 542: the first assertion is
true with sharp constant `31/30`, while the proposed linear lower bound in the
second assertion is false.  The exhibited counterexamples also have reciprocal
sum arbitrarily close to `1`. -/
theorem erdos_542 :
    (∀ n : ℕ, ∀ A : Finset ℕ,
      PairwiseLCMExceeds n A → reciprocalSum A ≤ (31 : ℝ) / 30) ∧
    (PairwiseLCMExceeds 5 {2, 3, 5} ∧
      reciprocalSum {2, 3, 5} = (31 : ℝ) / 30) ∧
    (∀ t : ℕ, PairwiseLCMExceeds (constructionAmbient t) (constructionFamily t)) ∧
    Filter.Tendsto
      (fun t : ℕ =>
        ((uncovered (constructionAmbient t) (constructionFamily t)).card : ℝ) /
          constructionAmbient t)
      Filter.atTop (nhds 0) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in Filter.atTop,
      1 - ε < reciprocalSum (constructionFamily t)) ∧
    ¬(∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ A : Finset ℕ,
  Erdos542.PairwiseLCMExceeds n A → c * n ≤ ((Erdos542.uncovered n A).card : ℝ)) := by
  refine ⟨?_, erdos542_sharp_example, constructionFamily_admissible,
    erdos542_uncovered_density_tendsto_zero, ?_,
    erdos542_no_uniform_linear_uncovered_bound⟩
  · intro n A hA
    exact erdos542_reciprocal_bound hA
  · intro ε hε
    exact erdos542_construction_reciprocal_eventually hε

end Erdos542

#print axioms Erdos542.erdos_542

alias _root_.Erdos542.erdos542_resolution := _root_.Erdos542.erdos_542
