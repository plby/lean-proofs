import ErdosProblems.Erdos491.Growth

/-! # Finite affine valuation counts -/

open scoped BigOperators

namespace Erdos491

noncomputable section

private def affineResidue (a d : ℕ) : ℕ :=
  (-(a : ZMod d)⁻¹ * (a + 1)).val

private lemma affine_dvd_modEq (a d t : ℕ) (hd : d ≠ 0) (h : a.Coprime d) :
    d ∣ a * (t + 1) + 1 ↔ t ≡ affineResidue a d [MOD d] := by
  letI : NeZero d := ⟨hd⟩
  rw [← Nat.modEq_zero_iff_dvd, ← ZMod.natCast_eq_natCast_iff,
    ← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, affineResidue,
    ZMod.natCast_zmod_val]
  have hunit : (a : ZMod d)⁻¹ * (a : ZMod d) = 1 := by
    rw [mul_comm]
    exact ZMod.coe_mul_inv_eq_one a h
  constructor
  · intro ht
    have ht' : (t : ZMod d) + 1 + (a : ZMod d)⁻¹ = 0 := by
      calc
        _ = (a : ZMod d)⁻¹ * ((a : ZMod d) * (t + 1) + 1) := by
          rw [mul_add, ← mul_assoc, hunit, one_mul, mul_one]
        _ = 0 := by rw [ht]; simp
    calc
      (t : ZMod d) = -1 - (a : ZMod d)⁻¹ := by linear_combination ht'
      _ = -((a : ZMod d)⁻¹ * (a : ZMod d)) - (a : ZMod d)⁻¹ := by rw [hunit]
      _ = -(a : ZMod d)⁻¹ * ((a : ZMod d) + 1) := by ring
  · intro ht
    rw [ht]
    simp only [Nat.cast_zero]
    calc
      _ = -((a : ZMod d)⁻¹ * (a : ZMod d)) * ((a : ZMod d) + 1) +
          (a : ZMod d) + 1 := by ring
      _ = (0 : ZMod d) := by rw [hunit]; ring

def affineCount (a d N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun m ↦ d ∣ a * m + 1)).card

private lemma affineCount_eq_count (a d N : ℕ) (hd : d ≠ 0)
    (h : a.Coprime d) :
    affineCount a d N = N.count (fun t ↦ t ≡ affineResidue a d [MOD d]) := by
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun m _hm ↦ m - 1)
  · intro m hm
    rw [Finset.mem_filter] at hm ⊢
    have hmI := Finset.mem_Icc.mp hm.1
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [← affine_dvd_modEq a d (m - 1) hd h]
    simpa [Nat.sub_add_cancel hmI.1] using hm.2
  · intro m₁ hm₁ m₂ hm₂ heq
    have h₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₁).1).1
    have h₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
    omega
  · intro t ht
    rw [Finset.mem_filter] at ht
    refine ⟨t + 1, ?_, by omega⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by
      have := Finset.mem_range.mp ht.1
      omega⟩, ?_⟩
    rw [affine_dvd_modEq a d t hd h]
    exact ht.2

/-- The affine count differs from the ordinary multiples count by at most
one, without an asymptotic limit or a geometric-tail estimate. -/
lemma affineCount_sub_div_bound (a d N : ℕ) (hd : 0 < d)
    (h : a.Coprime d) :
    |(affineCount a d N : ℝ) - ((N / d : ℕ) : ℝ)| ≤ 1 := by
  rw [affineCount_eq_count a d N hd.ne' h, Nat.count_modEq_card N hd]
  split_ifs <;> push_cast <;> norm_num

lemma affineCount_le_one (a d N : ℕ) (hd : 0 < d)
    (h : a.Coprime d) (hNd : N < d) : affineCount a d N ≤ 1 := by
  rw [affineCount_eq_count a d N hd.ne' h, Nat.count_modEq_card N hd,
    Nat.div_eq_of_lt hNd]
  split_ifs <;> omega

lemma coprime_affine (a m : ℕ) : a.Coprime (a * m + 1) := by
  rw [mul_comm a m, add_comm]
  simpa using (Nat.coprime_add_mul_left_right a 1 m).mpr (Nat.coprime_one_right a)

lemma affineCount_eq_zero (a d N : ℕ) (h : ¬ a.Coprime d) :
    affineCount a d N = 0 := by
  rw [affineCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ hdvd
  exact h ((coprime_affine a m).coprime_dvd_right hdvd)

lemma factorization_sum_layers {p n Y : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hnY : n ≤ Y) :
    (n.factorization p : ℝ) =
      ∑ j ∈ Finset.Icc 1 (Nat.log p Y), if p ^ j ∣ n then (1 : ℝ) else 0 := by
  have hf : n.factorization p ≤ Nat.log p Y := by
    apply Nat.le_log_of_pow_le hp.one_lt
    exact (Nat.le_of_dvd hn ((hp.pow_dvd_iff_le_factorization hn.ne').mpr le_rfl)).trans hnY
  have heq : (Finset.Icc 1 (Nat.log p Y)).filter (fun j ↦ p ^ j ∣ n) =
      Finset.Icc 1 (n.factorization p) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, hp.pow_dvd_iff_le_factorization hn.ne']
    omega
  rw [← Finset.sum_filter, heq]
  simp

lemma sum_affine_factorization {a p N Y : ℕ} (hp : p.Prime)
    (hY : a * N + 1 ≤ Y) :
    (∑ m ∈ Finset.Icc 1 N, ((a * m + 1).factorization p : ℝ)) =
      ∑ j ∈ Finset.Icc 1 (Nat.log p Y), (affineCount a (p ^ j) N : ℝ) := by
  calc
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 (Nat.log p Y),
        if p ^ j ∣ a * m + 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      apply factorization_sum_layers hp (by omega)
      exact (Nat.add_le_add_right (Nat.mul_le_mul_left a (Finset.mem_Icc.mp hm).2) 1).trans hY
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, affineCount]

lemma sum_factorization {p N Y : ℕ} (hp : p.Prime) (hY : N ≤ Y) :
    (∑ m ∈ Finset.Icc 1 N, (m.factorization p : ℝ)) =
      ∑ j ∈ Finset.Icc 1 (Nat.log p Y), ((N / p ^ j : ℕ) : ℝ) := by
  calc
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 (Nat.log p Y),
        if p ^ j ∣ m then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      exact factorization_sum_layers hp (Finset.mem_Icc.mp hm).1
        ((Finset.mem_Icc.mp hm).2.trans hY)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      have heq : (Finset.Icc 1 N).filter (fun m ↦ p ^ j ∣ m) =
          (Finset.range (N + 1)).filter (fun m ↦ p ^ j ∣ m ∧ m ≠ 0) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
        omega
      rw [← Finset.sum_filter, Finset.sum_const, heq]
      simp only [nsmul_eq_mul, mul_one]
      congr 1
      simpa [and_comm] using Nat.card_multiples' N (p ^ j)

lemma sum_affine_factorization_sub_bound {a p N Y : ℕ} (hp : p.Prime)
    (hcop : a.Coprime p) (haY : a * N + 1 ≤ Y) (hNY : N ≤ Y) :
    |∑ m ∈ Finset.Icc 1 N,
        (((a * m + 1).factorization p : ℝ) - (m.factorization p : ℝ))| ≤
      (Nat.log p Y : ℝ) := by
  rw [Finset.sum_sub_distrib, sum_affine_factorization hp haY,
    sum_factorization hp hNY, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 (Nat.log p Y),
        |(affineCount a (p ^ j) N : ℝ) - ((N / p ^ j : ℕ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Icc 1 (Nat.log p Y), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact affineCount_sub_div_bound a (p ^ j) N (pow_pos hp.pos _) (hcop.pow_right _)
    _ = _ := by simp

end

end Erdos491
