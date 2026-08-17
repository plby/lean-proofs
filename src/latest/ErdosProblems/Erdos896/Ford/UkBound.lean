import ErdosProblems.Erdos896.Ford.Uk
import ErdosProblems.Erdos896.Ford.Cluster

/-!
# Ford's bound for `U_k(v)`

This downstream module combines the dependency-light integral and measurable
stratification in `Uk` with the clustered volume estimate in `Cluster`.  The
finite series argument below is the last analytic step in Ford's proof of
Lemma 3.6.
-/

namespace Erdos896.Ford

open MeasureTheory
open scoped BigOperators

noncomputable def ukSeriesTerm (k v m : ℕ) : ℝ :=
  (2 / (2 : ℝ) ^ m) *
    (orderStatisticY k v (m + 1) / orderStatisticDoubleExp k v (m + 1))

noncomputable def ukTargetDenominator (k v : ℕ) : ℝ :=
  (2 : ℝ) ^ ((orderStatisticExcess k v : ℤ) : ℝ) + 1

noncomputable def ukSeriesMajorant (d : ℕ) : ℝ :=
  ((d : ℝ) + 6) ^ 3 * ((1 : ℝ) / 2) ^ d

lemma ukSeriesMajorant_nonneg (d : ℕ) : 0 ≤ ukSeriesMajorant d := by
  unfold ukSeriesMajorant
  positivity

lemma summable_ukSeriesMajorant : Summable ukSeriesMajorant := by
  have hnorm : ‖(1 : ℝ) / 2‖ < 1 := by norm_num
  have h0 : Summable (fun d : ℕ ↦ ((1 : ℝ) / 2) ^ d) :=
    summable_geometric_of_norm_lt_one hnorm
  have h1 : Summable (fun d : ℕ ↦ (d : ℝ) * ((1 : ℝ) / 2) ^ d) :=
    by simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm)
  have h2 : Summable (fun d : ℕ ↦ (d : ℝ) ^ 2 * ((1 : ℝ) / 2) ^ d) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  have h3 : Summable (fun d : ℕ ↦ (d : ℝ) ^ 3 * ((1 : ℝ) / 2) ^ d) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 hnorm
  have h := h3.add (h2.mul_left 18) |>.add (h1.mul_left 108) |>.add
    (h0.mul_left 216)
  convert h using 1
  funext d
  simp only [ukSeriesMajorant]
  ring

noncomputable def ukSeriesConstant : ℝ :=
  10000 * (1 + ∑' d : ℕ, ukSeriesMajorant d)

lemma ukSeriesConstant_pos : 0 < ukSeriesConstant := by
  unfold ukSeriesConstant
  have : 0 ≤ ∑' d : ℕ, ukSeriesMajorant d :=
    tsum_nonneg ukSeriesMajorant_nonneg
  positivity

lemma orderStatisticExcess_eq_of_ge {k v : ℕ} (hvk : v ≤ k) :
    orderStatisticExcess k v = ((k - v : ℕ) : ℤ) := by
  unfold orderStatisticExcess
  omega

lemma orderStatisticY_eq_low {k v m : ℕ} (hvk : v ≤ k)
    (hlow : m + 6 ≤ k - v) :
    orderStatisticY k v (m + 1) = ((k - v : ℕ) : ℝ) := by
  rw [orderStatisticY, orderStatisticExcess_eq_of_ge hvk, if_pos]
  · norm_num
  · exact_mod_cast hlow

lemma orderStatisticY_eq_high {k v m : ℕ} (hvk : v ≤ k)
    (hhigh : k - v < m + 6) :
    orderStatisticY k v (m + 1) =
      (((m + 6 - (k - v) : ℕ) : ℝ) ^ 2 * (m + 2 : ℕ)) := by
  rw [orderStatisticY, orderStatisticExcess_eq_of_ge hvk, if_neg]
  · have hd : k - v ≤ m + 6 := by omega
    norm_num only [Nat.cast_add, Nat.cast_ofNat, Int.cast_add, Int.cast_ofNat,
      Int.cast_sub, Int.cast_natCast, Nat.cast_sub hd]
    ring
  · exact_mod_cast (show ¬m + 6 ≤ k - v by omega)

private lemma two_mul_le_two_pow_pred {e : ℕ} (he : 4 ≤ e) :
    2 * e ≤ 2 ^ (e - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le he
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show 4 + (n + 1) - 1 = (4 + n - 1) + 1 by omega, pow_succ]
      have hp : 2 ≤ 2 ^ (4 + n - 1) := by
        rw [show 4 + n - 1 = n + 3 by omega, pow_add]
        have hone : 1 ≤ 2 ^ n :=
          Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
        norm_num
        omega
      omega

lemma orderStatisticDoubleExp_eq_low {k v m : ℕ} (hvk : v ≤ k)
    (hlow : m + 6 ≤ k - v) :
    orderStatisticDoubleExp k v (m + 1) =
      (2 : ℝ) ^ ((2 : ℝ) ^ (((k - v) - m - 1 : ℕ) : ℝ)) := by
  unfold orderStatisticDoubleExp
  rw [orderStatisticExcess_eq_of_ge hvk]
  rw [show ((k - v : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) =
      (((k - v) - m - 1 : ℕ) : ℤ) by omega]
  norm_num only [Int.cast_natCast]

lemma pow_two_distance_le_orderStatisticDoubleExp_of_low
    {k v m : ℕ} (hvk : v ≤ k) (hlow : m + 6 ≤ k - v) :
    (2 : ℝ) ^ (2 * ((k - v) - m)) ≤
      orderStatisticDoubleExp k v (m + 1) := by
  let d := k - v
  let e := d - m
  have he : 6 ≤ e := by omega
  have hde : d - m - 1 = e - 1 := by omega
  have hexp : 2 * e ≤ 2 ^ (e - 1) :=
    two_mul_le_two_pow_pred (by omega)
  rw [orderStatisticDoubleExp_eq_low hvk hlow,
    show k - v - m = e by rfl, hde]
  calc
    (2 : ℝ) ^ (2 * e) =
        (2 : ℝ) ^ (((2 * e : ℕ) : ℝ)) :=
      (Real.rpow_natCast 2 (2 * e)).symm
    _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (((e - 1 : ℕ) : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        rw [Real.rpow_natCast]
        exact_mod_cast hexp)

lemma ukSeriesTerm_le_low {k v m : ℕ} (hvk : v ≤ k)
    (hlow : m + 6 ≤ k - v) :
    ukSeriesTerm k v m ≤
      (2 * ((k - v : ℕ) : ℝ) / (2 : ℝ) ^ (k - v)) *
        ukSeriesMajorant ((k - v) - m) := by
  let d := k - v
  let e := d - m
  have he : 6 ≤ e := by omega
  have hdm : d = m + e := by omega
  have hY := orderStatisticY_eq_low hvk hlow
  have hD := pow_two_distance_le_orderStatisticDoubleExp_of_low hvk hlow
  have hDpos := orderStatisticDoubleExp_pos k v (m + 1)
  have hdiv : orderStatisticY k v (m + 1) /
      orderStatisticDoubleExp k v (m + 1) ≤
        (d : ℝ) / (2 : ℝ) ^ (2 * e) := by
    rw [hY]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hD
  unfold ukSeriesTerm ukSeriesMajorant
  change (2 / (2 : ℝ) ^ m) *
      (orderStatisticY k v (m + 1) /
        orderStatisticDoubleExp k v (m + 1)) ≤
    (2 * (d : ℝ) / (2 : ℝ) ^ d) *
      (((e : ℝ) + 6) ^ 3 * ((1 : ℝ) / 2) ^ e)
  calc
    (2 / (2 : ℝ) ^ m) *
        (orderStatisticY k v (m + 1) / orderStatisticDoubleExp k v (m + 1)) ≤
      (2 / (2 : ℝ) ^ m) * ((d : ℝ) / (2 : ℝ) ^ (2 * e)) := by
        gcongr
    _ = (2 * (d : ℝ) / (2 : ℝ) ^ d) * ((1 : ℝ) / 2) ^ e := by
      rw [hdm, pow_add, show 2 * e = e * 2 by omega, pow_mul, div_pow]
      field_simp
      ring
    _ ≤ (2 * (d : ℝ) / (2 : ℝ) ^ d) *
        (((e : ℝ) + 6) ^ 3 * ((1 : ℝ) / 2) ^ e) := by
      have hfac : 0 ≤ 2 * (d : ℝ) / (2 : ℝ) ^ d := by positivity
      have hgeom : 0 ≤ ((1 : ℝ) / 2) ^ e := by positivity
      have hpoly : 1 ≤ ((e : ℝ) + 6) ^ 3 := by
        have he0 : 0 ≤ (e : ℝ) := Nat.cast_nonneg e
        nlinarith [sq_nonneg ((e : ℝ) + 6)]
      apply mul_le_mul_of_nonneg_left _ hfac
      exact le_mul_of_one_le_left hgeom hpoly

lemma one_le_orderStatisticDoubleExp (k v gamma : ℕ) :
    1 ≤ orderStatisticDoubleExp k v gamma := by
  unfold orderStatisticDoubleExp
  exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)

lemma ukSeriesTerm_le_tail {k v m : ℕ} (hvk : v ≤ k)
    (htail : k - v ≤ m) :
    ukSeriesTerm k v m ≤
      (2 * (((k - v : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (k - v)) *
        ukSeriesMajorant (m - (k - v)) := by
  let d := k - v
  let e := m - d
  have hhigh : d < m + 6 := by omega
  have hY := orderStatisticY_eq_high hvk hhigh
  have hme : m = d + e := by omega
  have hsub : m + 6 - d = e + 6 := by omega
  have hY0 : 0 ≤ orderStatisticY k v (m + 1) := by
    rw [hY]
    positivity
  have hD : 1 ≤ orderStatisticDoubleExp k v (m + 1) :=
    one_le_orderStatisticDoubleExp _ _ _
  have hdiv : orderStatisticY k v (m + 1) /
      orderStatisticDoubleExp k v (m + 1) ≤ orderStatisticY k v (m + 1) :=
    div_le_self hY0 hD
  have hYbound : orderStatisticY k v (m + 1) ≤
      ((d : ℝ) + 1) * ((e : ℝ) + 6) ^ 3 := by
    rw [hY, hsub, hme]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    have hlin : (d : ℝ) + e + 2 ≤ ((d : ℝ) + 1) * ((e : ℝ) + 6) := by
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg e
      nlinarith
    have hsquare : 0 ≤ ((e : ℝ) + 6) ^ 2 := sq_nonneg _
    nlinarith
  unfold ukSeriesTerm ukSeriesMajorant
  change (2 / (2 : ℝ) ^ m) *
      (orderStatisticY k v (m + 1) / orderStatisticDoubleExp k v (m + 1)) ≤
    (2 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) *
      (((e : ℝ) + 6) ^ 3 * ((1 : ℝ) / 2) ^ e)
  calc
    (2 / (2 : ℝ) ^ m) *
        (orderStatisticY k v (m + 1) / orderStatisticDoubleExp k v (m + 1)) ≤
      (2 / (2 : ℝ) ^ m) * orderStatisticY k v (m + 1) := by gcongr
    _ ≤ (2 / (2 : ℝ) ^ m) *
        (((d : ℝ) + 1) * ((e : ℝ) + 6) ^ 3) := by gcongr
    _ = (2 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) *
        (((e : ℝ) + 6) ^ 3 * ((1 : ℝ) / 2) ^ e) := by
      rw [hme, pow_add, div_pow]
      field_simp
      ring

lemma ukSeriesTerm_le_near {k v m : ℕ} (hvk : v ≤ k)
    (hm : m < k - v) (hnear : k - v < m + 6) :
    ukSeriesTerm k v m ≤
      (2304 * (((k - v : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (k - v)) *
        ukSeriesMajorant ((k - v) - m) := by
  let d := k - v
  let e := d - m
  have hepos : 1 ≤ e := by omega
  have hele : e ≤ 5 := by omega
  have hme : d = m + e := by omega
  have hsub : m + 6 - d = 6 - e := by omega
  have hY := orderStatisticY_eq_high hvk hnear
  have hY0 : 0 ≤ orderStatisticY k v (m + 1) := by
    rw [hY]
    positivity
  have hD : 1 ≤ orderStatisticDoubleExp k v (m + 1) :=
    one_le_orderStatisticDoubleExp _ _ _
  have hdiv : orderStatisticY k v (m + 1) /
      orderStatisticDoubleExp k v (m + 1) ≤ orderStatisticY k v (m + 1) :=
    div_le_self hY0 hD
  have hYbound : orderStatisticY k v (m + 1) ≤ 36 * ((d : ℝ) + 1) := by
    rw [hY, hsub]
    have hfirst : (((6 - e : ℕ) : ℝ) ^ 2) ≤ 36 := by
      interval_cases e <;> norm_num
    have hsecond : ((m + 2 : ℕ) : ℝ) ≤ (d : ℝ) + 1 := by
      exact_mod_cast (show m + 2 ≤ d + 1 by omega)
    exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
  have hpow_e : (2 : ℝ) ^ e ≤ 32 := by
    interval_cases e <;> norm_num
  have hmaj : 1 ≤ ukSeriesMajorant e := by
    interval_cases e <;> norm_num [ukSeriesMajorant]
  unfold ukSeriesTerm
  change (2 / (2 : ℝ) ^ m) *
      (orderStatisticY k v (m + 1) / orderStatisticDoubleExp k v (m + 1)) ≤
    (2304 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) * ukSeriesMajorant e
  calc
    (2 / (2 : ℝ) ^ m) *
        (orderStatisticY k v (m + 1) / orderStatisticDoubleExp k v (m + 1)) ≤
      (2 / (2 : ℝ) ^ m) * orderStatisticY k v (m + 1) := by gcongr
    _ ≤ (2 / (2 : ℝ) ^ m) * (36 * ((d : ℝ) + 1)) := by gcongr
    _ = (72 * ((d : ℝ) + 1) * (2 : ℝ) ^ e) / (2 : ℝ) ^ d := by
      rw [hme, pow_add]
      field_simp
      ring
    _ ≤ 2304 * ((d : ℝ) + 1) / (2 : ℝ) ^ d := by
      have hd : 0 ≤ (d : ℝ) + 1 := by positivity
      have hp : 0 < (2 : ℝ) ^ d := by positivity
      apply (div_le_div_iff_of_pos_right hp).2
      nlinarith
    _ ≤ (2304 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) * ukSeriesMajorant e := by
      have hfac : 0 ≤ 2304 * ((d : ℝ) + 1) / (2 : ℝ) ^ d := by positivity
      nlinarith

private lemma sum_reindexed_le_tsum
    (s : Finset ℕ) (f : ℕ → ℕ) (g : ℕ → ℝ)
    (hf : Set.InjOn f s) (hg : Summable g) (hg0 : ∀ n, 0 ≤ g n) :
    ∑ k ∈ s, g (f k) ≤ ∑' d, g d := by
  let t := s.image f
  have hsum : ∑ k ∈ s, g (f k) = ∑ d ∈ t, g d := by
    apply Finset.sum_bij (fun k _ ↦ f k)
    · intro k hk
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    · intro k₁ hk₁ k₂ hk₂ h
      exact hf hk₁ hk₂ h
    · intro d hd
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
      exact ⟨k, hk, rfl⟩
    · intros
      rfl
  rw [hsum]
  exact hg.sum_le_tsum t (fun _ _ ↦ hg0 _)

lemma ukSeries_sum_le_of_ge {k v n : ℕ} (hvk : v ≤ k) :
    ∑ m ∈ Finset.range n, ukSeriesTerm k v m ≤
      ukSeriesConstant * (1 + ((k - v : ℕ) : ℝ) ^ 2) /
        ukTargetDenominator k v := by
  let d := k - v
  let low := (Finset.range n).filter fun m ↦ m + 6 ≤ d
  let near := (Finset.range n).filter fun m ↦ m < d ∧ d < m + 6
  let tail := (Finset.range n).filter fun m ↦ d ≤ m
  let A := ∑' e : ℕ, ukSeriesMajorant e
  have hA0 : 0 ≤ A := tsum_nonneg ukSeriesMajorant_nonneg
  have hsplit :
      ∑ m ∈ Finset.range n, ukSeriesTerm k v m =
        (∑ m ∈ low, ukSeriesTerm k v m) +
        (∑ m ∈ near, ukSeriesTerm k v m) +
        ∑ m ∈ tail, ukSeriesTerm k v m := by
    simp only [low, near, tail, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hlow : m + 6 ≤ d
    · have hmd : m < d := by omega
      have hnnear : ¬d < m + 6 := not_lt_of_ge hlow
      have hntail : ¬d ≤ m := not_le_of_gt hmd
      simp [hlow, hmd, hnnear, hntail]
    · by_cases hmd : m < d
      · have hnear : d < m + 6 := by omega
        simp [hlow, hmd, hnear]
      · have htail : d ≤ m := by omega
        simp [hlow, hmd, htail]
  have hlowMaj : ∑ m ∈ low, ukSeriesMajorant (d - m) ≤ A := by
    apply sum_reindexed_le_tsum low (fun m ↦ d - m) ukSeriesMajorant
    · intro m₁ hm₁ m₂ hm₂ heq
      have hm₁d : m₁ < d := by
        have := (Finset.mem_filter.mp hm₁).2
        omega
      have hm₂d : m₂ < d := by
        have := (Finset.mem_filter.mp hm₂).2
        omega
      change d - m₁ = d - m₂ at heq
      omega
    · exact summable_ukSeriesMajorant
    · exact ukSeriesMajorant_nonneg
  have hlowSum : ∑ m ∈ low, ukSeriesTerm k v m ≤
      (2 * (d : ℝ) / (2 : ℝ) ^ d) * A := by
    calc
      ∑ m ∈ low, ukSeriesTerm k v m ≤
          ∑ m ∈ low, (2 * (d : ℝ) / (2 : ℝ) ^ d) *
            ukSeriesMajorant (d - m) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmlow := (Finset.mem_filter.mp hm).2
        exact ukSeriesTerm_le_low hvk hmlow
      _ = (2 * (d : ℝ) / (2 : ℝ) ^ d) *
          ∑ m ∈ low, ukSeriesMajorant (d - m) := by rw [Finset.mul_sum]
      _ ≤ (2 * (d : ℝ) / (2 : ℝ) ^ d) * A := by
        gcongr
  have hnearMaj : ∑ m ∈ near, ukSeriesMajorant (d - m) ≤ A := by
    apply sum_reindexed_le_tsum near (fun m ↦ d - m) ukSeriesMajorant
    · intro m₁ hm₁ m₂ hm₂ heq
      have hm₁d := (Finset.mem_filter.mp hm₁).2.1
      have hm₂d := (Finset.mem_filter.mp hm₂).2.1
      change d - m₁ = d - m₂ at heq
      omega
    · exact summable_ukSeriesMajorant
    · exact ukSeriesMajorant_nonneg
  have hnearSum : ∑ m ∈ near, ukSeriesTerm k v m ≤
      (2304 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) * A := by
    calc
      ∑ m ∈ near, ukSeriesTerm k v m ≤
          ∑ m ∈ near, (2304 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) *
            ukSeriesMajorant (d - m) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmnear := (Finset.mem_filter.mp hm).2
        exact ukSeriesTerm_le_near hvk hmnear.1 hmnear.2
      _ = (2304 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) *
          ∑ m ∈ near, ukSeriesMajorant (d - m) := by rw [Finset.mul_sum]
      _ ≤ (2304 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) * A := by
        gcongr
  have htailMaj : ∑ m ∈ tail, ukSeriesMajorant (m - d) ≤ A := by
    apply sum_reindexed_le_tsum tail (fun m ↦ m - d) ukSeriesMajorant
    · intro m₁ hm₁ m₂ hm₂ heq
      have hdm₁ := (Finset.mem_filter.mp hm₁).2
      have hdm₂ := (Finset.mem_filter.mp hm₂).2
      change m₁ - d = m₂ - d at heq
      omega
    · exact summable_ukSeriesMajorant
    · exact ukSeriesMajorant_nonneg
  have htailSum : ∑ m ∈ tail, ukSeriesTerm k v m ≤
      (2 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) * A := by
    calc
      ∑ m ∈ tail, ukSeriesTerm k v m ≤
          ∑ m ∈ tail, (2 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) *
            ukSeriesMajorant (m - d) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmtail := (Finset.mem_filter.mp hm).2
        exact ukSeriesTerm_le_tail hvk hmtail
      _ = (2 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) *
          ∑ m ∈ tail, ukSeriesMajorant (m - d) := by rw [Finset.mul_sum]
      _ ≤ (2 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) * A := by
        gcongr
  have hDform : ukTargetDenominator k v = (2 : ℝ) ^ d + 1 := by
    unfold ukTargetDenominator
    rw [orderStatisticExcess_eq_of_ge hvk, Int.cast_natCast, Real.rpow_natCast]
  have hDpos : 0 < ukTargetDenominator k v := by
    unfold ukTargetDenominator
    positivity
  have hDone : ukTargetDenominator k v ≤ 2 * (2 : ℝ) ^ d := by
    rw [hDform]
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    linarith
  rw [hsplit]
  calc
    (∑ m ∈ low, ukSeriesTerm k v m) +
        (∑ m ∈ near, ukSeriesTerm k v m) +
        ∑ m ∈ tail, ukSeriesTerm k v m ≤
      (2 * (d : ℝ) / (2 : ℝ) ^ d) * A +
        (2304 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) * A +
        (2 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) * A := by linarith
    _ ≤ (4616 * (1 + (d : ℝ) ^ 2) / (2 : ℝ) ^ d) * A := by
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hp : 0 < (2 : ℝ) ^ d := by positivity
      rw [show
        (2 * (d : ℝ) / (2 : ℝ) ^ d) * A +
            (2304 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) * A +
            (2 * ((d : ℝ) + 1) / (2 : ℝ) ^ d) * A =
          ((2 * (d : ℝ) + 2304 * ((d : ℝ) + 1) + 2 * ((d : ℝ) + 1)) /
            (2 : ℝ) ^ d) * A by ring]
      apply mul_le_mul_of_nonneg_right _ hA0
      apply (div_le_div_iff_of_pos_right hp).2
      nlinarith [sq_nonneg ((d : ℝ) - 1)]
    _ ≤ ukSeriesConstant * (1 + (d : ℝ) ^ 2) /
        ukTargetDenominator k v := by
      apply (le_div_iff₀ hDpos).2
      unfold ukSeriesConstant
      have hnum : 0 ≤ 1 + (d : ℝ) ^ 2 := by positivity
      have hp : 0 < (2 : ℝ) ^ d := by positivity
      have honeA : A ≤ 1 + A := by linarith
      have hmulD := mul_le_mul_of_nonneg_left hDone
        (mul_nonneg (mul_nonneg (by positivity) hnum) hA0)
      field_simp
      nlinarith

lemma orderStatisticExcess_eq_neg_of_le {k v : ℕ} (hkv : k ≤ v) :
    orderStatisticExcess k v = -((v - k : ℕ) : ℤ) := by
  unfold orderStatisticExcess
  omega

lemma orderStatisticY_eq_of_le {k v m : ℕ} (hkv : k ≤ v) :
    orderStatisticY k v (m + 1) =
      ((m + 6 + (v - k) : ℕ) : ℝ) ^ 2 * (m + 2 : ℕ) := by
  have hex := orderStatisticExcess_eq_neg_of_le hkv
  rw [orderStatisticY, hex, if_neg]
  norm_num only [Nat.cast_add, Nat.cast_ofNat, Int.cast_add, Int.cast_ofNat,
    Int.cast_sub, Int.cast_neg, Int.cast_natCast]
  ring
  omega

lemma ukSeriesTerm_le_of_le {k v m : ℕ} (hkv : k ≤ v) :
    ukSeriesTerm k v m ≤
      4 * (1 + ((v - k : ℕ) : ℝ) ^ 2) * ukSeriesMajorant m := by
  let d : ℕ := v - k
  have hY : orderStatisticY k v (m + 1) =
      ((m + 6 + d : ℕ) : ℝ) ^ 2 * (m + 2 : ℕ) := by
    simpa [d] using orderStatisticY_eq_of_le (m := m) hkv
  have hY0 : 0 ≤ orderStatisticY k v (m + 1) := by
    rw [hY]
    positivity
  have hD : 1 ≤ orderStatisticDoubleExp k v (m + 1) :=
    one_le_orderStatisticDoubleExp _ _ _
  have hdiv : orderStatisticY k v (m + 1) /
      orderStatisticDoubleExp k v (m + 1) ≤ orderStatisticY k v (m + 1) :=
    div_le_self hY0 hD
  have hm6 : (0 : ℝ) ≤ m + 6 := by positivity
  have hd1 : (0 : ℝ) ≤ d + 1 := by positivity
  have hsum : (m : ℝ) + 6 + d ≤
      ((m : ℝ) + 6) * ((d : ℝ) + 1) := by
    nlinarith
  have hd_sq : ((d : ℝ) + 1) ^ 2 ≤ 2 * (1 + (d : ℝ) ^ 2) := by
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hYbound : orderStatisticY k v (m + 1) ≤
      2 * (1 + (d : ℝ) ^ 2) * ((m : ℝ) + 6) ^ 3 := by
    rw [hY]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    calc
      ((m + 6 + d : ℝ) ^ 2) * (m + 2) ≤
          (((m + 6 : ℝ) * (d + 1)) ^ 2) * (m + 6) := by
        exact mul_le_mul
          (show (m + 6 + d : ℝ) ^ 2 ≤
            ((m + 6 : ℝ) * (d + 1)) ^ 2 by nlinarith [hsum])
          (by linarith) (by positivity) (sq_nonneg _)
      _ = ((d + 1 : ℝ) ^ 2) * (m + 6) ^ 3 := by ring
      _ ≤ 2 * (1 + (d : ℝ) ^ 2) * (m + 6) ^ 3 := by
        gcongr
  unfold ukSeriesTerm ukSeriesMajorant
  calc
    (2 / (2 : ℝ) ^ m) *
        (orderStatisticY k v (m + 1) / orderStatisticDoubleExp k v (m + 1)) ≤
      (2 / (2 : ℝ) ^ m) * orderStatisticY k v (m + 1) := by
        gcongr
    _ ≤ (2 / (2 : ℝ) ^ m) *
        (2 * (1 + (d : ℝ) ^ 2) * ((m : ℝ) + 6) ^ 3) := by
      gcongr
    _ = 4 * (1 + (d : ℝ) ^ 2) *
        (((m : ℝ) + 6) ^ 3 * ((1 : ℝ) / 2) ^ m) := by
      rw [div_pow]
      ring

lemma ukTargetDenominator_le_two_of_le {k v : ℕ} (hkv : k ≤ v) :
    ukTargetDenominator k v ≤ 2 := by
  unfold ukTargetDenominator
  have hex : ((orderStatisticExcess k v : ℤ) : ℝ) ≤ 0 := by
    rw [orderStatisticExcess_eq_neg_of_le hkv]
    push_cast
    exact neg_nonpos.mpr (Nat.cast_nonneg _)
  have hp : (2 : ℝ) ^ ((orderStatisticExcess k v : ℤ) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hex
  linarith

lemma ukTargetDenominator_pos (k v : ℕ) : 0 < ukTargetDenominator k v := by
  unfold ukTargetDenominator
  positivity

lemma ukSeries_sum_le_of_le {k v n : ℕ} (hkv : k ≤ v) :
    ∑ m ∈ Finset.range n, ukSeriesTerm k v m ≤
      (8 * ∑' d : ℕ, ukSeriesMajorant d) *
        (1 + ((v - k : ℕ) : ℝ) ^ 2) / ukTargetDenominator k v := by
  have hpoint : ∑ m ∈ Finset.range n, ukSeriesTerm k v m ≤
      ∑ m ∈ Finset.range n,
        4 * (1 + ((v - k : ℕ) : ℝ) ^ 2) * ukSeriesMajorant m := by
    exact Finset.sum_le_sum fun m hm ↦ ukSeriesTerm_le_of_le hkv
  have hfinite : ∑ m ∈ Finset.range n, ukSeriesMajorant m ≤
      ∑' d : ℕ, ukSeriesMajorant d :=
    summable_ukSeriesMajorant.sum_le_tsum _
      (fun m hm ↦ ukSeriesMajorant_nonneg m)
  have hfac : 0 ≤ 4 * (1 + ((v - k : ℕ) : ℝ) ^ 2) := by positivity
  have hD := ukTargetDenominator_le_two_of_le hkv
  have hDpos := ukTargetDenominator_pos k v
  calc
    ∑ m ∈ Finset.range n, ukSeriesTerm k v m ≤
        ∑ m ∈ Finset.range n,
          4 * (1 + ((v - k : ℕ) : ℝ) ^ 2) * ukSeriesMajorant m := hpoint
    _ = (4 * (1 + ((v - k : ℕ) : ℝ) ^ 2)) *
        ∑ m ∈ Finset.range n, ukSeriesMajorant m := by
      rw [Finset.mul_sum]
    _ ≤ (4 * (1 + ((v - k : ℕ) : ℝ) ^ 2)) *
        ∑' d : ℕ, ukSeriesMajorant d := by gcongr
    _ ≤ (8 * ∑' d : ℕ, ukSeriesMajorant d) *
        (1 + ((v - k : ℕ) : ℝ) ^ 2) / ukTargetDenominator k v := by
      apply (le_div_iff₀ hDpos).2
      have htsum : 0 ≤ ∑' d : ℕ, ukSeriesMajorant d :=
        tsum_nonneg ukSeriesMajorant_nonneg
      have hA : 0 ≤ (1 + ((v - k : ℕ) : ℝ) ^ 2) *
          ∑' d : ℕ, ukSeriesMajorant d := by positivity
      have hmul := mul_nonneg hA (sub_nonneg.mpr hD)
      nlinarith

/-- Uniform geometric-series estimate which closes the summation in Ford's
proof of Lemma 3.6. -/
theorem ukSeries_sum_bound (k v n : ℕ) :
    ∑ m ∈ Finset.range n, ukSeriesTerm k v m ≤
      ukSeriesConstant * (1 + |(k : ℝ) - (v : ℝ)| ^ 2) /
        ukTargetDenominator k v := by
  by_cases hkv : k ≤ v
  · have h := ukSeries_sum_le_of_le (n := n) hkv
    have hA0 : 0 ≤ ∑' d : ℕ, ukSeriesMajorant d :=
      tsum_nonneg ukSeriesMajorant_nonneg
    have hDpos : 0 < ukTargetDenominator k v := by
      unfold ukTargetDenominator
      positivity
    have hdist : |(k : ℝ) - (v : ℝ)| ^ 2 = ((v - k : ℕ) : ℝ) ^ 2 := by
      rw [sq_abs]
      norm_num only [Nat.cast_sub hkv]
      ring
    rw [hdist]
    refine h.trans ?_
    apply (div_le_div_iff_of_pos_right hDpos).2
    unfold ukSeriesConstant
    have hnum : 0 ≤ 1 + ((v - k : ℕ) : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg hnum hA0]
  · have hvk : v ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hkv)
    have h := ukSeries_sum_le_of_ge (n := n) hvk
    have hdist : |(k : ℝ) - (v : ℝ)| ^ 2 = ((k - v : ℕ) : ℝ) ^ 2 := by
      rw [sq_abs]
      norm_num only [Nat.cast_sub hvk]
    simpa only [hdist] using h

/-! ## Assembly with the clustered volume estimate -/

/-- The final integration step of Lemma 3.6, factored from the geometric
proof of Lemma 4.4.  This theorem is useful while the latter is compiled in
`Cluster`: once supplied with its uniform volume constant, no analytic or
limiting step remains. -/
theorem uk_bound_of_fordT_volume_bound
    (C : ℝ) (hC : 0 ≤ C)
    (hvolume : ∀ k v gamma : ℕ, 1 ≤ k → k ≤ 10 * v →
      (volume (fordT k v gamma)).toReal ≤
        C * orderStatisticY k v gamma /
          (orderStatisticDoubleExp k v gamma * ((k + 1).factorial : ℝ)))
    {k v : ℕ} (hk : 1 ≤ k) (hkv : k ≤ 10 * v) :
    uk k v ≤
      (C * ukSeriesConstant) * (1 + |(k : ℝ) - (v : ℝ)| ^ 2) /
        (((k + 1).factorial : ℝ) * ukTargetDenominator k v) := by
  have hfacpos : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have hDpos : 0 < ukTargetDenominator k v := by
    unfold ukTargetDenominator
    positivity
  have hseries := ukSeries_sum_bound k v (k + 1)
  have hprefixTop (m : ℕ) : volume (ukPrefixRegion k v (m + 1)) ≠ ⊤ := by
    rw [ukPrefixRegion_eq_fordT]
    apply lt_top_iff_ne_top.mp
    calc
      volume (fordT k v (m + 1)) ≤ volume (orderedSimplex k 0 1) :=
        volume_fordT_le_orderedSimplex k v (m + 1)
      _ < ⊤ := by
        rw [volume_orderedSimplex k (by norm_num)]
        simp
  have hsuperPrefix (m : ℕ) :
      (volume (ukSuperlevel k v m)).toReal ≤
        (volume (ukPrefixRegion k v (m + 1))).toReal := by
    apply ENNReal.toReal_mono (hprefixTop m)
    exact measure_mono (ukSuperlevel_subset_ukPrefixRegion k v m)
  have hstrata :
      ∑ m ∈ Finset.range (k + 1),
          (volume (ukSuperlevel k v m)).toReal * (2 / (2 : ℝ) ^ m) ≤
        (C / ((k + 1).factorial : ℝ)) *
          ∑ m ∈ Finset.range (k + 1), ukSeriesTerm k v m := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hlayer : 0 ≤ 2 / (2 : ℝ) ^ m := by positivity
    have hregion :
        (volume (ukPrefixRegion k v (m + 1))).toReal ≤
          C * orderStatisticY k v (m + 1) /
            (orderStatisticDoubleExp k v (m + 1) *
              ((k + 1).factorial : ℝ)) := by
      rw [ukPrefixRegion_eq_fordT]
      exact hvolume k v (m + 1) hk hkv
    calc
      (volume (ukSuperlevel k v m)).toReal * (2 / (2 : ℝ) ^ m) ≤
          (volume (ukPrefixRegion k v (m + 1))).toReal *
            (2 / (2 : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_right (hsuperPrefix m) hlayer
      _ ≤ (C * orderStatisticY k v (m + 1) /
            (orderStatisticDoubleExp k v (m + 1) *
              ((k + 1).factorial : ℝ))) * (2 / (2 : ℝ) ^ m) := by
        exact mul_le_mul_of_nonneg_right hregion hlayer
      _ = (C / ((k + 1).factorial : ℝ)) * ukSeriesTerm k v m := by
        unfold ukSeriesTerm
        have hstatD := orderStatisticDoubleExp_pos k v (m + 1)
        field_simp
  calc
    uk k v ≤ ∑ m ∈ Finset.range (k + 1),
        (volume (ukSuperlevel k v m)).toReal * (2 / (2 : ℝ) ^ m) :=
      uk_le_sum_superlevel_volume k v
    _ ≤ (C / ((k + 1).factorial : ℝ)) *
        ∑ m ∈ Finset.range (k + 1), ukSeriesTerm k v m := hstrata
    _ ≤ (C / ((k + 1).factorial : ℝ)) *
        (ukSeriesConstant * (1 + |(k : ℝ) - (v : ℝ)| ^ 2) /
          ukTargetDenominator k v) := by
      exact mul_le_mul_of_nonneg_left hseries (div_nonneg hC hfacpos.le)
    _ = (C * ukSeriesConstant) * (1 + |(k : ℝ) - (v : ℝ)| ^ 2) /
        (((k + 1).factorial : ℝ) * ukTargetDenominator k v) := by
      field_simp

/-- Existential, all-`k` form of the preceding assembly theorem.  The added
`2` absorbs the exactly computed zero-dimensional endpoint. -/
theorem ford_uk_bound_of_fordT_volume_bound
    (hvolume : ∃ C : ℝ, 0 < C ∧
      ∀ k v gamma : ℕ, 1 ≤ k → k ≤ 10 * v →
        (volume (fordT k v gamma)).toReal ≤
          C * orderStatisticY k v gamma /
            (orderStatisticDoubleExp k v gamma * ((k + 1).factorial : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ k v : ℕ, k ≤ 10 * v →
      uk k v ≤ C * (1 + |(k : ℝ) - (v : ℝ)| ^ 2) /
        (((k + 1).factorial : ℝ) * ukTargetDenominator k v) := by
  obtain ⟨C, hC, hvolume⟩ := hvolume
  refine ⟨C * ukSeriesConstant + 2,
    add_pos (mul_pos hC ukSeriesConstant_pos) (by norm_num), ?_⟩
  intro k v hkv
  by_cases hk0 : k = 0
  · subst k
    rw [uk_zero]
    have hDpos : 0 < ukTargetDenominator 0 v := by
      unfold ukTargetDenominator
      positivity
    have hDle : ukTargetDenominator 0 v ≤ 2 :=
      ukTargetDenominator_le_two_of_le (Nat.zero_le v)
    apply (le_div_iff₀ (mul_pos (by positivity) hDpos)).2
    norm_num only [Nat.zero_eq, Nat.cast_zero, zero_sub, abs_neg, Nat.factorial_one,
      Nat.cast_one, one_mul]
    have hK : 0 < ukSeriesConstant := ukSeriesConstant_pos
    have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
    have hprod : 0 ≤ C * ukSeriesConstant := mul_nonneg hC.le hK.le
    nlinarith [sq_nonneg (v : ℝ)]
  · have hk : 1 ≤ k := by omega
    have hbase := uk_bound_of_fordT_volume_bound C hC.le hvolume hk hkv
    refine hbase.trans ?_
    have hden : 0 < ((k + 1).factorial : ℝ) * ukTargetDenominator k v := by
      exact mul_pos (by positivity) (by unfold ukTargetDenominator; positivity)
    apply (div_le_div_iff_of_pos_right hden).2
    have hnum : 0 ≤ 1 + |(k : ℝ) - (v : ℝ)| ^ 2 := by positivity
    nlinarith [mul_nonneg hnum (by norm_num : (0 : ℝ) ≤ 2)]

/-! ## Power-only interface for the `T_k` summation -/

/-- The piecewise envelope obtained by replacing `2^(k-v)+1` with the
equivalent one-sided power.  This is the form used in the subsequent sum over
`k`. -/
noncomputable def ukEnvelope (k v : ℕ) : ℝ :=
  if k ≤ v then
    (1 + ((v - k : ℕ) : ℝ) ^ 2) / ((k + 1).factorial : ℝ)
  else
    (1 + ((k - v : ℕ) : ℝ) ^ 2) /
      (((k + 1).factorial : ℝ) * (2 : ℝ) ^ (k - v))

lemma ukEnvelope_nonneg (k v : ℕ) : 0 ≤ ukEnvelope k v := by
  unfold ukEnvelope
  split_ifs <;> positivity

lemma exactUkEnvelope_le_piecewise (C : ℝ) (hC : 0 ≤ C) (k v : ℕ) :
    C * (1 + |(k : ℝ) - (v : ℝ)| ^ 2) /
        (((k + 1).factorial : ℝ) * ukTargetDenominator k v) ≤
      C * ukEnvelope k v := by
  have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  by_cases hkv : k ≤ v
  · rw [ukEnvelope, if_pos hkv]
    have hdist : |(k : ℝ) - (v : ℝ)| ^ 2 = ((v - k : ℕ) : ℝ) ^ 2 := by
      rw [sq_abs]
      norm_num only [Nat.cast_sub hkv]
      ring
    rw [hdist]
    have hD : 1 ≤ ukTargetDenominator k v := by
      unfold ukTargetDenominator
      have hp : 0 ≤ (2 : ℝ) ^ ((orderStatisticExcess k v : ℤ) : ℝ) :=
        Real.rpow_nonneg (by norm_num) _
      linarith
    have hDpos := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hD
    have hnum : 0 ≤ C * (1 + ((v - k : ℕ) : ℝ) ^ 2) /
        ((k + 1).factorial : ℝ) := by positivity
    calc
      C * (1 + ((v - k : ℕ) : ℝ) ^ 2) /
          (((k + 1).factorial : ℝ) * ukTargetDenominator k v) =
        (C * (1 + ((v - k : ℕ) : ℝ) ^ 2) /
          ((k + 1).factorial : ℝ)) / ukTargetDenominator k v := by ring
      _ ≤ C * (1 + ((v - k : ℕ) : ℝ) ^ 2) /
          ((k + 1).factorial : ℝ) := div_le_self hnum hD
      _ = C * ((1 + ((v - k : ℕ) : ℝ) ^ 2) /
          ((k + 1).factorial : ℝ)) := by ring
  · have hvk : v ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hkv)
    rw [ukEnvelope, if_neg hkv]
    have hdist : |(k : ℝ) - (v : ℝ)| ^ 2 = ((k - v : ℕ) : ℝ) ^ 2 := by
      rw [sq_abs]
      norm_num only [Nat.cast_sub hvk]
    rw [hdist]
    have hDform : ukTargetDenominator k v = (2 : ℝ) ^ (k - v) + 1 := by
      unfold ukTargetDenominator
      rw [orderStatisticExcess_eq_of_ge hvk, Int.cast_natCast,
        Real.rpow_natCast]
    have hpow : (0 : ℝ) < (2 : ℝ) ^ (k - v) := by positivity
    have hD : (2 : ℝ) ^ (k - v) ≤ ukTargetDenominator k v := by
      rw [hDform]
      linarith
    have hleft : 0 ≤ C * (1 + ((k - v : ℕ) : ℝ) ^ 2) := by positivity
    calc
      C * (1 + ((k - v : ℕ) : ℝ) ^ 2) /
          (((k + 1).factorial : ℝ) * ukTargetDenominator k v) ≤
        C * (1 + ((k - v : ℕ) : ℝ) ^ 2) /
          (((k + 1).factorial : ℝ) * (2 : ℝ) ^ (k - v)) := by
        apply div_le_div_of_nonneg_left hleft
        · exact mul_pos hfac hpow
        · exact mul_le_mul_of_nonneg_left hD hfac.le
      _ = C * ((1 + ((k - v : ℕ) : ℝ) ^ 2) /
          (((k + 1).factorial : ℝ) * (2 : ℝ) ^ (k - v))) := by ring

/-- Piecewise summation interface, conditional only on the already isolated
cluster-volume theorem. -/
theorem ford_uk_piecewise_bound_of_fordT_volume_bound
    (hvolume : ∃ C : ℝ, 0 < C ∧
      ∀ k v gamma : ℕ, 1 ≤ k → k ≤ 10 * v →
        (volume (fordT k v gamma)).toReal ≤
          C * orderStatisticY k v gamma /
            (orderStatisticDoubleExp k v gamma * ((k + 1).factorial : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ k v : ℕ, k ≤ 10 * v →
      uk k v ≤ C * ukEnvelope k v := by
  obtain ⟨C, hC, hbound⟩ := ford_uk_bound_of_fordT_volume_bound hvolume
  refine ⟨C, hC, ?_⟩
  intro k v hkv
  exact (hbound k v hkv).trans (exactUkEnvelope_le_piecewise C hC.le k v)

/-- Ford's Lemma 3.6 in the power-only form used for the subsequent
summation over `k`. -/
theorem ford_uk_piecewise_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ k v : ℕ, k ≤ 10 * v →
      uk k v ≤ C * ukEnvelope k v :=
  ford_uk_piecewise_bound_of_fordT_volume_bound fordT_volume_bound

end Erdos896.Ford
