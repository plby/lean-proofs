import ErdosProblems.Erdos4.ConditionalProductMoments

/-! Mixed moments through order three, needed to discard atypical full-tuple normalizers. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical RandomResidueSieve AffineTuples TupleCollisionMass
open ConditionalTupleMoments ConditionalProductMoments

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime] {k : ℕ}

theorem tuple_extension_mean_upper (h : Fin k → ℕ) (p Y q : ℕ) (μ : ℕ → ℝ)
    (hμ0 : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (hμsum : ∑ n ∈ Finset.Icc 1 Y, μ n = 1)
    {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α) (T : Finset ℕ)
    (hlocal : ∀ n ∈ Finset.Icc 1 Y, Disjoint (tuple h p n) T →
      mean ell q (fun a => indicator ell a (tuple h p n ∪ T)) ≤ L) :
    (∑ n ∈ Finset.Icc 1 Y, μ n *
      mean ell q (fun a => indicator ell a (tuple h p n ∪ T))) ≤ L + (T.card : ℝ) * k * α := by
  have hpoint : ∀ n ∈ Finset.Icc 1 Y,
      mean ell q (fun a => indicator ell a (tuple h p n ∪ T)) ≤
        L + if ¬Disjoint (tuple h p n) T then 1 else 0 := by
    intro n hn
    by_cases hd : Disjoint (tuple h p n) T
    · simpa only [hd, not_true_eq_false, if_false, add_zero] using hlocal n hn hd
    · rw [if_pos hd]
      exact (mean_indicator_le_one ell q _).trans (by linarith)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Y, μ n *
        (L + if ¬Disjoint (tuple h p n) T then 1 else 0) :=
      Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hpoint n hn) (hμ0 n hn))
    _ = L + ∑ n ∈ Finset.Icc 1 Y, if ¬Disjoint (tuple h p n) T then μ n else 0 := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hμsum, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> simp
    _ ≤ _ := add_le_add le_rfl (meeting_mass_le h p Y T μ hα hμ)

theorem tuple_extension_mean_lower (h : Fin k → ℕ) (p Y q : ℕ) (μ : ℕ → ℝ)
    (hμ0 : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (hμsum : ∑ n ∈ Finset.Icc 1 Y, μ n = 1)
    {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α) (T : Finset ℕ)
    (hlocal : ∀ n ∈ Finset.Icc 1 Y, Disjoint (tuple h p n) T →
      L ≤ mean ell q (fun a => indicator ell a (tuple h p n ∪ T))) :
    L * (1 - (T.card : ℝ) * k * α) ≤
      ∑ n ∈ Finset.Icc 1 Y, μ n * mean ell q (fun a => indicator ell a (tuple h p n ∪ T)) := by
  have hpoint : ∀ n ∈ Finset.Icc 1 Y,
      L * (1 - if ¬Disjoint (tuple h p n) T then 1 else 0) ≤
        mean ell q (fun a => indicator ell a (tuple h p n ∪ T)) := by
    intro n hn
    by_cases hd : Disjoint (tuple h p n) T
    · simpa only [hd, not_true_eq_false, if_false, sub_zero, mul_one] using hlocal n hn hd
    · rw [if_pos hd, sub_self, mul_zero]
      exact mean_nonneg ell q _ (fun a => indicator_nonneg ell a _)
  have hmass := meeting_mass_le h p Y T μ hα hμ
  calc
    _ ≤ L * (1 - ∑ n ∈ Finset.Icc 1 Y, if ¬Disjoint (tuple h p n) T then μ n else 0) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hmass 1) hL
    _ = ∑ n ∈ Finset.Icc 1 Y, μ n *
        (L * (1 - if ¬Disjoint (tuple h p n) T then 1 else 0)) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, ← Finset.sum_mul, hμsum, one_mul,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> ring
    _ ≤ _ := Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hpoint n hn) (hμ0 n hn))

theorem mixed_product_lower (h : Fin k → ℕ) (hh : Function.Injective h)
    {p : ℕ} (hp : 0 < p) (Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    (hμ0 : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (hμsum : ∑ n ∈ Finset.Icc 1 Y, μ n = 1)
    {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α)
    (hlocal : ∀ n ∈ Finset.Icc 1 Y, ∀ m ∈ Finset.Icc 1 Y, q ∈ tuple h p m →
      Disjoint (tuple h p n) (tuple h p m) →
        L ≤ mean ell q (fun a => indicator ell a (tuple h p n ∪ tuple h p m))) :
    (L * (1 - (k : ℝ) ^ 2 * α)) * hitMass h p Y μ q ≤
      mean ell q (fun a => tupleMass ell h p Y μ a * hittingMass ell h p Y μ q a) := by
  rw [mean_mixed_product]
  unfold hitMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  by_cases hqm : q ∈ tuple h p m
  · simp only [if_pos hqm]
    have hbound := tuple_extension_mean_lower ell h p Y q μ hμ0 hμsum hα hL hμ
      (tuple h p m) (fun n hn hd => hlocal n hn m hm hqm hd)
    rw [card_tuple h hh hp m] at hbound
    have heq : (k : ℝ) * k * α = (k : ℝ) ^ 2 * α := by ring
    rw [heq] at hbound
    calc
      _ = μ m * (L * (1 - (k : ℝ) ^ 2 * α)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (hμ0 m hm)
  · simp [hqm]

theorem mean_mixed_square_product (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ) :
    mean ell q (fun a => tupleMass ell h p Y μ a ^ 2 * hittingMass ell h p Y μ q a) =
      ∑ m ∈ Finset.Icc 1 Y, (if q ∈ tuple h p m then μ m else 0) *
        ∑ n ∈ Finset.Icc 1 Y, μ n * ∑ r ∈ Finset.Icc 1 Y, μ r *
          mean ell q (fun a => indicator ell a (tuple h p r ∪ (tuple h p n ∪ tuple h p m))) := by
  have hpoint (a : ∀ l, ZMod (ell l)) :
      tupleMass ell h p Y μ a ^ 2 * hittingMass ell h p Y μ q a =
        ∑ m ∈ Finset.Icc 1 Y, (if q ∈ tuple h p m then μ m else 0) *
          ∑ n ∈ Finset.Icc 1 Y, μ n * ∑ r ∈ Finset.Icc 1 Y, μ r *
            indicator ell a (tuple h p r ∪ (tuple h p n ∪ tuple h p m)) := by
    have hsquare : tupleMass ell h p Y μ a * tupleMass ell h p Y μ a =
        ∑ n ∈ Finset.Icc 1 Y, ∑ r ∈ Finset.Icc 1 Y,
          μ n * μ r * indicator ell a (tuple h p n ∪ tuple h p r) := by
      unfold tupleMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [← indicator_mul]
      ring
    calc
      _ = hittingMass ell h p Y μ q a * (tupleMass ell h p Y μ a * tupleMass ell h p Y μ a) := by ring
      _ = _ := by
        rw [hsquare, hittingMass, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        apply Finset.sum_congr rfl
        intro r _
        simp only [← indicator_mul]
        ring
  simp only [hpoint, mean_sum, mean_const_mul]

theorem mixed_square_product_upper (h : Fin k → ℕ) (hh : Function.Injective h)
    {p : ℕ} (hp : 0 < p) (Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    (hμ0 : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (hμsum : ∑ n ∈ Finset.Icc 1 Y, μ n = 1)
    {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α)
    (hlocal : ∀ m ∈ Finset.Icc 1 Y, q ∈ tuple h p m →
      ∀ n ∈ Finset.Icc 1 Y, Disjoint (tuple h p n) (tuple h p m) →
      ∀ r ∈ Finset.Icc 1 Y, Disjoint (tuple h p r) (tuple h p n ∪ tuple h p m) →
      mean ell q (fun a => indicator ell a (tuple h p r ∪ (tuple h p n ∪ tuple h p m))) ≤ L) :
    mean ell q (fun a => tupleMass ell h p Y μ a ^ 2 * hittingMass ell h p Y μ q a) ≤
      (L + 3 * (k : ℝ) ^ 2 * α) * hitMass h p Y μ q := by
  have hinner : ∀ m ∈ Finset.Icc 1 Y, q ∈ tuple h p m →
      (∑ n ∈ Finset.Icc 1 Y, μ n * ∑ r ∈ Finset.Icc 1 Y, μ r *
        mean ell q (fun a => indicator ell a (tuple h p r ∪ (tuple h p n ∪ tuple h p m)))) ≤
        L + 3 * (k : ℝ) ^ 2 * α := by
    intro m hm hqm
    have hpoint : ∀ n ∈ Finset.Icc 1 Y,
        (∑ r ∈ Finset.Icc 1 Y, μ r * mean ell q
          (fun a => indicator ell a (tuple h p r ∪ (tuple h p n ∪ tuple h p m)))) ≤
          (L + 2 * (k : ℝ) ^ 2 * α) + if ¬Disjoint (tuple h p n) (tuple h p m) then 1 else 0 := by
      intro n hn
      by_cases hd : Disjoint (tuple h p n) (tuple h p m)
      · rw [if_neg (not_not.mpr hd), add_zero]
        have hb := tuple_extension_mean_upper ell h p Y q μ hμ0 hμsum hα hL hμ
          (tuple h p n ∪ tuple h p m) (fun r hr hdr => hlocal m hm hqm n hn hd r hr hdr)
        have hc : (tuple h p n ∪ tuple h p m).card ≤ 2 * k := by
          have hc := Finset.card_union_le (tuple h p n) (tuple h p m)
          rw [card_tuple h hh hp n, card_tuple h hh hp m] at hc
          omega
        have hcR : ((tuple h p n ∪ tuple h p m).card : ℝ) ≤ 2 * k := by exact_mod_cast hc
        have hmul := mul_le_mul_of_nonneg_right hcR (mul_nonneg (Nat.cast_nonneg k) hα)
        exact hb.trans (by nlinarith)
      · rw [if_pos hd]
        have hb : (∑ r ∈ Finset.Icc 1 Y, μ r * mean ell q
            (fun a => indicator ell a (tuple h p r ∪ (tuple h p n ∪ tuple h p m)))) ≤ 1 := by
          calc
            _ ≤ ∑ r ∈ Finset.Icc 1 Y, μ r * 1 :=
              Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left
                (mean_indicator_le_one ell q _) (hμ0 r hr))
            _ = _ := by simpa only [mul_one] using hμsum
        exact hb.trans (by nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hα])
    have hcollision := meeting_mass_le h p Y (tuple h p m) μ hα hμ
    rw [card_tuple h hh hp m] at hcollision
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 Y, μ n * ((L + 2 * (k : ℝ) ^ 2 * α) +
          if ¬Disjoint (tuple h p n) (tuple h p m) then 1 else 0) :=
        Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hpoint n hn) (hμ0 n hn))
      _ = L + 2 * (k : ℝ) ^ 2 * α +
          ∑ n ∈ Finset.Icc 1 Y, if ¬Disjoint (tuple h p n) (tuple h p m) then μ n else 0 := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hμsum, one_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro n _
        split_ifs <;> simp
      _ ≤ _ := by nlinarith
  rw [mean_mixed_square_product]
  unfold hitMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  by_cases hqm : q ∈ tuple h p m
  · simp only [if_pos hqm]
    exact (mul_le_mul_of_nonneg_left (hinner m hm hqm) (hμ0 m hm)).trans_eq (by ring)
  · simp [hqm]

end Erdos4.FGKMT
