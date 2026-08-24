import ErdosProblems.Erdos587.NVDevelopment

/-!
The mixed-sum growth tree needs only logarithmic depth in reciprocal
density: its cardinalities grow like `3^s`, while the ambient interval
grows like `2^s`. This sharpens the existing exponential row count to a
polynomial one without changing the combinatorial growth theorem.
-/

open scoped Pointwise

namespace Erdos587.CFP

def denseBinaryDepth (D : ℕ) : ℕ := 4 * (Nat.log 2 D + 1)

theorem density_pow_comparison (D : ℕ) :
    2 * D * 2 ^ denseBinaryDepth D < 3 ^ denseBinaryDepth D := by
  let t := Nat.log 2 D + 1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hDlt : D < 2 ^ t := Nat.lt_pow_succ_log_self (by omega) D
  have htwo : 2 ≤ 2 ^ t := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
  have hcore : 2 * D * 16 ^ t < 81 ^ t := by
    calc
      2 * D * 16 ^ t < (2 * 2 ^ t) * 16 ^ t :=
        Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hDlt (by omega))
          (pow_pos (by omega) _)
      _ ≤ (2 ^ t * 2 ^ t) * 16 ^ t :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ htwo)
      _ = 64 ^ t := by rw [← mul_pow, ← mul_pow]; norm_num
      _ ≤ 81 ^ t := Nat.pow_le_pow_left (by omega) t
  change 2 * D * 2 ^ (4 * t) < 3 ^ (4 * t)
  simpa only [pow_mul, show (2 : ℕ) ^ 4 = 16 by norm_num,
    show (3 : ℕ) ^ 4 = 81 by norm_num] using hcore

theorem denseBinaryDepth_count_le {D : ℕ} (hD : 0 < D) :
    2 ^ denseBinaryDepth D ≤ 16 * D ^ 4 := by
  have hpow : 2 ^ (Nat.log 2 D + 1) ≤ 2 * D := by
    rw [pow_succ]
    calc
      2 ^ Nat.log 2 D * 2 ≤ D * 2 :=
        Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 hD.ne')
      _ = 2 * D := by ring
  calc
    2 ^ denseBinaryDepth D = (2 ^ (Nat.log 2 D + 1)) ^ 4 := by
      rw [← pow_mul]
      congr 1
      dsimp [denseBinaryDepth]
      ring
    _ ≤ (2 * D) ^ 4 := Nat.pow_le_pow_left hpow 4
    _ = 16 * D ^ 4 := by ring

theorem mixedGrowth_exceeds_of_density_logarithmic
    {D k H : ℕ} (hk : 4 ≤ k) (hdense : H + 1 ≤ D * k) :
    2 ^ denseBinaryDepth D * H + 1 < nvMixedGrowth k (denseBinaryDepth D) := by
  have hHlt : H < D * k := lt_of_lt_of_le (Nat.lt_succ_self H) hdense
  have hk2 : 0 < k - 2 := by omega
  have hkfactor : k ≤ 2 * (k - 2) := by omega
  have hpow := density_pow_comparison D
  have hfirst : 2 ^ denseBinaryDepth D * H < 2 ^ denseBinaryDepth D * (D * k) :=
    Nat.mul_lt_mul_of_pos_left hHlt (pow_pos (by omega) _)
  have hmiddle : 2 ^ denseBinaryDepth D * (D * k) ≤
      (2 * D * 2 ^ denseBinaryDepth D) * (k - 2) := by
    calc
      2 ^ denseBinaryDepth D * (D * k) = (D * 2 ^ denseBinaryDepth D) * k := by ring
      _ ≤ (D * 2 ^ denseBinaryDepth D) * (2 * (k - 2)) :=
        Nat.mul_le_mul_left _ hkfactor
      _ = (2 * D * 2 ^ denseBinaryDepth D) * (k - 2) := by ring
  have hlast : (2 * D * 2 ^ denseBinaryDepth D) * (k - 2) <
      3 ^ denseBinaryDepth D * (k - 2) := Nat.mul_lt_mul_of_pos_right hpow hk2
  have hgrowth := nvMixedGrowth_ge_pow_mul (show 2 ≤ k by omega) (denseBinaryDepth D)
  omega

/-- Polynomially many different dense summands suffice for the same long
arithmetic progression as in the older exponential-count theorem. -/
theorem exists_long_natAP_of_dense_different_summands_polynomial
    {D k H : ℕ} (hk : 4 ≤ k) (sums : List (Finset ℕ))
    (hlen : sums.length = 2 ^ denseBinaryDepth D)
    (hcard : ∀ S ∈ sums, k ≤ S.card)
    (hbounded : ∀ S ∈ sums, S ⊆ Finset.Icc 0 H)
    (hdense : H + 1 ≤ D * k) :
    ∃ a d : ℕ, 0 < d ∧
      Erdos13Additive.natAP a d (2 * k - 1) ⊆ finsetListSum sums := by
  exact exists_long_natAP_of_mixed_growth_exceeds (by omega) sums hlen hcard hbounded
    (mixedGrowth_exceeds_of_density_logarithmic hk hdense)

def denseRowCount (D : ℕ) : ℕ := 2 ^ denseBinaryDepth (2 * D)

theorem denseRowCount_le {D : ℕ} (hD : 0 < D) : denseRowCount D ≤ 256 * D ^ 4 := by
  calc
    denseRowCount D ≤ 16 * (2 * D) ^ 4 := denseBinaryDepth_count_le (by omega)
    _ = 256 * D ^ 4 := by ring

/-- Integer-row form, ready for induction on the dimension of a coefficient
box. The row count is at most `256 * D^4`. -/
theorem exists_dense_intAP_of_different_rows_polynomial
    {D H : ℕ} (hD : 0 < D) (rows : List (Finset ℤ))
    (hlen : rows.length = denseRowCount D)
    (hrows : ∀ row ∈ rows,
      row ⊆ Finset.Icc 0 (H : ℤ) ∧ H + 1 ≤ D * row.card) :
    ∃ a q : ℤ, ∃ L : ℕ,
      q ≠ 0 ∧ H + 1 ≤ 4 * D * (L + 1) ∧
      ∀ y ≤ L, a + (y : ℤ) * q ∈ nvFinsetListSum rows := by
  by_cases hlong : 4 * D ≤ H + 1
  · let k := (H + 1) / D
    have hk : 4 ≤ k := by
      dsimp [k]
      apply (Nat.le_div_iff_mul_le hD).mpr
      simpa [mul_comm] using hlong
    let natRows := rows.map nvNatRow
    have hnatLen : natRows.length = 2 ^ denseBinaryDepth (2 * D) := by
      dsimp [natRows]
      rw [List.length_map]
      exact hlen
    have hnatCard : ∀ S ∈ natRows, k ≤ S.card := by
      intro S hS
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hS
      rw [card_nvNatRow (hrows row hrow).1]
      exact Nat.div_le_of_le_mul (hrows row hrow).2
    have hnatBounded : ∀ S ∈ natRows, S ⊆ Finset.Icc 0 H := by
      intro S hS
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hS
      exact nvNatRow_subset_Icc (hrows row hrow).1
    have hdivUpper : H + 1 ≤ 2 * D * k := by
      have hlt : H + 1 < D * (k + 1) := by
        simpa only [k] using Nat.lt_mul_div_succ (H + 1) hD
      have hkone : 1 ≤ k := by omega
      calc
        H + 1 ≤ D * (k + 1) := hlt.le
        _ ≤ D * (2 * k) := Nat.mul_le_mul_left D (by omega)
        _ = 2 * D * k := by ring
    obtain ⟨a, q, hq, hAP⟩ :=
      exists_long_natAP_of_dense_different_summands_polynomial
        hk natRows hnatLen hnatCard hnatBounded hdivUpper
    refine ⟨(a : ℤ), (q : ℤ), 2 * k - 2, ?_, ?_, ?_⟩
    · exact_mod_cast hq.ne'
    · have hLcard : (2 * k - 2) + 1 = 2 * k - 1 := by omega
      rw [hLcard]
      calc
        H + 1 ≤ 2 * D * k := hdivUpper
        _ ≤ 4 * D * (2 * k - 1) := by
          have hk' : k ≤ 2 * (2 * k - 1) := by omega
          calc
            2 * D * k ≤ (2 * D) * (2 * (2 * k - 1)) :=
              Nat.mul_le_mul_left (2 * D) hk'
            _ = 4 * D * (2 * k - 1) := by ring
    · intro y hy
      have hylt : y < 2 * k - 1 := by omega
      have hnatAP : a + q * y ∈ Erdos13Additive.natAP a q (2 * k - 1) :=
        Erdos13Additive.mem_natAP.mpr ⟨y, hylt, rfl⟩
      have hnatSum : a + q * y ∈ nvFinsetListSum natRows := by
        rw [nvFinsetListSum_nat_eq]
        exact hAP hnatAP
      have hcastMem : ((a + q * y : ℕ) : ℤ) ∈
          (nvFinsetListSum natRows).image Int.ofNatHom.toAddMonoidHom :=
        Finset.mem_image.mpr ⟨a + q * y, hnatSum, rfl⟩
      have hcastSub := cast_nvFinsetListSum_natRows_subset
        (rows := rows) (H := H) (fun row hrow => (hrows row hrow).1)
      have := hcastSub hcastMem
      simpa only [natRows, Nat.cast_add, Nat.cast_mul, mul_comm] using this
  · have hrowNonempty : ∀ row ∈ rows, row.Nonempty := by
      intro row hrow
      apply Finset.card_pos.mp
      have hdense := (hrows row hrow).2
      by_contra hzero
      have : row.card = 0 := Nat.eq_zero_of_not_pos hzero
      rw [this] at hdense
      simp at hdense
    obtain ⟨a, ha⟩ := nvFinsetListSum_nonempty hrowNonempty
    refine ⟨a, 1, 0, by norm_num, ?_, ?_⟩
    · simp only [Nat.zero_add, Nat.mul_one]
      omega
    · intro y hy
      have hy0 : y = 0 := by omega
      simpa [hy0] using ha

end Erdos587.CFP
