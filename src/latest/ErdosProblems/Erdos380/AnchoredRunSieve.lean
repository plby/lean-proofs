import ErdosProblems.Erdos380.DyadicShiftSieve

/-! # Sieve bounds for smooth runs starting at a prime-square multiple -/

namespace Erdos380

def anchorShiftValue (p m j : ℕ) (left : Bool) : ℕ :=
  if left then p ^ 2 * m - j else p ^ 2 * m + j

def anchoredSmoothRunStarts (p M H : ℕ) (left : Bool) : Finset ℕ :=
  (Finset.Icc 1 M).filter fun m => ∀ j ∈ Finset.range H,
    largestPrimeFactor (anchorShiftValue p m j left) ≤ p

lemma anchorShiftValue_pos {p m j H : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hj : j < H) (hH : H ≤ p) (left : Bool) : 0 < anchorShiftValue p m j left := by
  have hpm : p ≤ p ^ 2 * m := by nlinarith [hp.two_le]
  cases left <;> simp only [anchorShiftValue, Bool.false_eq_true, ↓reduceIte] <;> omega

noncomputable def anchorSieveUnit {p : ℕ} (hp : p.Prime)
    (q : dyadicPrimes p) (left : Bool) : (ZMod q.1)ˣ := by
  have hq := (Finset.mem_filter.mp q.2).2
  have hpq : p < q.1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp q.2).1).1
  let u := ZMod.unitOfCoprime (p ^ 2) (((Nat.coprime_primes hp hq).mpr hpq.ne).pow_left 2)
  exact if left then -u else u

lemma anchorSieveUnit_coe {p : ℕ} (hp : p.Prime) (q : dyadicPrimes p) (left : Bool) :
    (anchorSieveUnit hp q left : ZMod q.1) =
      if left then -((p ^ 2 : ℕ) : ZMod q.1) else ((p ^ 2 : ℕ) : ZMod q.1) := by
  cases left <;> simp [anchorSieveUnit]

lemma anchoredSmoothRunStarts_subset_survivors {p M H : ℕ} (hp : p.Prime)
    (hH : H ≤ p) (left : Bool) :
    letI : ∀ q : dyadicPrimes p, NeZero q.1 :=
      fun q => ⟨(Finset.mem_filter.mp q.2).2.ne_zero⟩
    anchoredSmoothRunStarts p M H left ⊆
      residueClassSurvivors (fun q => unitShiftResidues (anchorSieveUnit hp q left) H) 0 M := by
  classical
  let : ∀ q : dyadicPrimes p, NeZero q.1 :=
    fun q => ⟨(Finset.mem_filter.mp q.2).2.ne_zero⟩
  intro m hm
  obtain ⟨hmrange, hmsmooth⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hmrange
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
  intro q hres
  obtain ⟨j, hj, hz⟩ := mem_unitShiftResidues_iff (anchorSieveUnit hp q left) |>.mp hres
  have hjH := Finset.mem_range.mp hj
  have hpos := anchorShiftValue_pos hp hm1 hjH hH left
  have hpm : j ≤ p ^ 2 * m := by nlinarith [hp.two_le]
  have hzero : (anchorShiftValue p m j left : ZMod q.1) = 0 := by
    rw [anchorSieveUnit_coe] at hz
    cases left
    · simpa [anchorShiftValue, Nat.cast_add, Nat.cast_mul] using hz
    · simp only [↓reduceIte] at hz
      simp only [anchorShiftValue, ↓reduceIte, Nat.cast_sub hpm, Nat.cast_mul]
      linear_combination -hz
  have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hle := (prime_le_largestPrimeFactor hpos.ne' (Finset.mem_filter.mp q.2).2 hdiv).trans
    (hmsmooth j hj)
  exact (not_le_of_gt (Finset.mem_Ioc.mp (Finset.mem_filter.mp q.2).1).1) hle

theorem exists_uniform_anchoredSmoothRunStarts_bound : ∃ P₀ : ℕ, ∀ p ≥ P₀,
    p.Prime → ∀ k H : ℕ, 0 < k → 0 < H → H ≤ p →
    20 * (k : ℝ) * Real.log p ≤ p → ∀ M : ℕ, (2 * p) ^ (2 * k) ≤ M →
    ∀ left : Bool, ((anchoredSmoothRunStarts p M H left).card : ℝ) ≤
      ((M : ℝ) + M) / (((H : ℝ) / (40 * k * Real.log p)) ^ k) := by
  obtain ⟨P₀, hP₀⟩ := exists_uniform_dyadicShiftSieve_bound
  refine ⟨P₀, ?_⟩
  intro p hp₀ hp k H hk hH hHp hkp M hpower left
  let : ∀ q : dyadicPrimes p, NeZero q.1 :=
    fun q => ⟨(Finset.mem_filter.mp q.2).2.ne_zero⟩
  have hsieve := hP₀ p hp₀ k H hk hH hHp hkp 0 M hpower (fun q => anchorSieveUnit hp q left)
  have hsub := anchoredSmoothRunStarts_subset_survivors (M := M) hp hHp left
  exact (show ((anchoredSmoothRunStarts p M H left).card : ℝ) ≤
      (residueClassSurvivors (fun q => unitShiftResidues (anchorSieveUnit hp q left) H) 0 M).card by
    exact_mod_cast Finset.card_le_card hsub).trans hsieve

end Erdos380
