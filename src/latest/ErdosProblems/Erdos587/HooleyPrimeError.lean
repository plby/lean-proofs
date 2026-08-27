import ErdosProblems.Erdos587.HooleyHarmonicRecursion
import ErdosProblems.Erdos587.HooleyPrimeMean

/-!
# Bounding a block of largest-prime increments

The prime-averaged mixed-moment inequality is applied after enlarging the
cofactor sets to a common smooth cutoff. This is the analytic step in the
recursive bound for the accumulated prime error.
-/

open scoped BigOperators

namespace Erdos587

lemma deltaPrimeIncrement_eq_sum (n p q : ℕ) :
    deltaPrimeIncrement n p q = ∑ b ∈ Finset.Icc 1 (q / 2),
      ((q.choose b : ℝ) / ((n.divisors.card : ℝ) * n)) *
        ((1 : ℝ) / p * deltaMixedMoment n (q - b) b (Real.log p)) := by
  unfold deltaPrimeIncrement
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem sum_deltaPrimeIncrement_le (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) {Y : ℝ} (hY : 1 < Y)
    (hmin : ∀ p ∈ P, Y ≤ (p : ℝ)) (n q : ℕ) :
    (∑ p ∈ P, deltaPrimeIncrement n p q) ≤
      (deltaPrimeWindowConstant / Real.log Y) *
        ∑ b ∈ Finset.Icc 1 (q / 2), 2 ^ b * (q.choose b : ℝ) *
          (deltaMoment n (q - b) * deltaMoment n b) / ((n.divisors.card : ℝ) * n) := by
  simp_rw [deltaPrimeIncrement_eq_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hb' := Finset.mem_Icc.mp hb
  rw [← Finset.mul_sum]
  have hmean := sum_prime_deltaMixedMoment_le P hprime hY hmin n
    (a := q - b) (b := b) (by omega) (by omega)
  calc
    _ ≤ ((q.choose b : ℝ) / ((n.divisors.card : ℝ) * n)) *
        ((deltaPrimeWindowConstant / Real.log Y) * 2 ^ b *
          deltaMoment n (q - b) * deltaMoment n b) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by ring

lemma restrictedDeltaPrimeError_split (G : ℕ → Prop) [DecidablePred G]
    (q : ℕ) {y x : ℕ} (hyx : y ≤ x) :
    restrictedDeltaPrimeError G q x = restrictedDeltaPrimeError G q y +
      ∑ p ∈ x.primesBelow \ y.primesBelow,
        ∑ n ∈ (deltaSmoothNumbers p).filter G, deltaPrimeIncrement n p q := by
  have hsub : y.primesBelow ⊆ x.primesBelow := by
    intro p hp
    obtain ⟨hpy, hp⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨hpy.trans_le hyx, hp⟩
  unfold restrictedDeltaPrimeError
  rw [Finset.sum_sdiff_eq_sub hsub]
  ring

/-- The high-prime error is controlled by ordinary moments on one common
smooth set. No regularity of `G` is needed for this enlargement step. -/
theorem restrictedDeltaPrimeError_block_le (G : ℕ → Prop) [DecidablePred G]
    (q : ℕ) {y x : ℕ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    restrictedDeltaPrimeError G q x ≤ restrictedDeltaPrimeError G q y +
      (deltaPrimeWindowConstant / Real.log (y : ℝ)) *
        ∑ n ∈ (deltaSmoothNumbers x).filter G,
          ∑ b ∈ Finset.Icc 1 (q / 2), 2 ^ b * (q.choose b : ℝ) *
            (deltaMoment n (q - b) * deltaMoment n b) / ((n.divisors.card : ℝ) * n) := by
  classical
  let P := x.primesBelow \ y.primesBelow
  have hprime : ∀ p ∈ P, p.Prime := fun p hp =>
    (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).2
  have hmin : ∀ p ∈ P, (y : ℝ) ≤ p := by
    intro p hp
    obtain ⟨hpx, hpy⟩ := Finset.mem_sdiff.mp hp
    have hpp := (Nat.mem_primesBelow.mp hpx).2
    have hyp : y ≤ p := by
      by_contra h
      exact hpy (Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩)
    exact_mod_cast hyp
  rw [restrictedDeltaPrimeError_split G q hyx]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ p ∈ P, ∑ n ∈ (deltaSmoothNumbers x).filter G, deltaPrimeIncrement n p q := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn, hGn⟩ := Finset.mem_filter.mp hn
        have hpx := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).1
        exact Finset.mem_filter.mpr ⟨deltaSmoothNumbers_mono hpx.le hn, hGn⟩
      · exact fun n _ _ => deltaPrimeIncrement_nonneg n p q
    _ = ∑ n ∈ (deltaSmoothNumbers x).filter G, ∑ p ∈ P, deltaPrimeIncrement n p q :=
      Finset.sum_comm
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      exact sum_deltaPrimeIncrement_le P hprime
        (by exact_mod_cast (show 1 < y by omega)) hmin n q

end Erdos587
