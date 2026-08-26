import ErdosProblems.Erdos380.Intervals

/-!
# Exact smooth-number formula for the singleton count

The smoothness cutoff is inclusive: `smoothCount N y` counts positive
integers at most `N` with all prime divisors at most `y`. Mathlib's strict
smoothness convention is therefore used with parameter `y + 1`.
-/

open scoped BigOperators

namespace Erdos380

lemma mem_smoothNumbers_iff_largestPrimeFactor {n y : ℕ} (hy : 1 ≤ y) :
    n ∈ Nat.smoothNumbers (y + 1) ↔ n ≠ 0 ∧ largestPrimeFactor n ≤ y := by
  constructor
  · intro hn
    refine ⟨hn.1, largestPrimeFactor_le hy ?_⟩
    intro p hp hpn
    exact Nat.lt_succ_iff.mp (Nat.mem_smoothNumbers'.mp hn p hp hpn)
  · rintro ⟨hn0, hny⟩
    apply Nat.mem_smoothNumbers'.mpr
    intro p hp hpn
    exact Nat.lt_succ_iff.mpr ((prime_le_largestPrimeFactor hn0 hp hpn).trans hny)

/-- The number of positive, inclusively `y`-smooth integers at most `N`. -/
def smoothCount (N y : ℕ) : ℕ := (Nat.smoothNumbersUpTo N (y + 1)).card

noncomputable section

def singletonPrimeFiber (N p : ℕ) : Finset ℕ := by
  classical
  exact (singletonBadUpTo N).filter fun n => largestPrimeFactor n = p

lemma mem_singletonPrimeFiber {N p n : ℕ} :
    n ∈ singletonPrimeFiber N p ↔
      1 ≤ n ∧ n ≤ N ∧ SingletonBad n ∧ largestPrimeFactor n = p := by
  classical
  simp [singletonPrimeFiber, and_assoc]

lemma prime_square_smooth_largest {p m : ℕ} (hp : p.Prime)
    (hm : m ∈ Nat.smoothNumbers (p + 1)) : largestPrimeFactor (p ^ 2 * m) = p := by
  have hml := (mem_smoothNumbers_iff_largestPrimeFactor hp.one_le).mp hm
  rw [largestPrimeFactor_mul (pow_ne_zero _ hp.ne_zero) hml.1,
    largestPrimeFactor_pow p (by decide), largestPrimeFactor_of_prime hp,
    max_eq_left hml.2]

lemma prime_square_smooth_mem_fiber {N p m : ℕ} (hp : p.Prime)
    (hm : m ∈ Nat.smoothNumbersUpTo (N / p ^ 2) (p + 1)) :
    p ^ 2 * m ∈ singletonPrimeFiber N p := by
  obtain ⟨hmN, hm⟩ := Nat.mem_smoothNumbersUpTo.mp hm
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm.1
  have hn2 : 2 ≤ p ^ 2 * m := by nlinarith [hp.two_le]
  have hnN : p ^ 2 * m ≤ N := by
    have h := (Nat.le_div_iff_mul_le (pow_pos hp.pos 2)).mp hmN
    simpa [mul_comm] using h
  have hlpf := prime_square_smooth_largest hp hm
  exact mem_singletonPrimeFiber.mpr ⟨by omega, hnN, ⟨hn2, by rw [hlpf]; exact dvd_mul_right _ _⟩,
    hlpf⟩

lemma singletonPrimeFiber_card {N p : ℕ} (hp : p.Prime) :
    (singletonPrimeFiber N p).card = smoothCount (N / p ^ 2) p := by
  classical
  symm
  apply Finset.card_bij (fun m _ => p ^ 2 * m)
  · intro m hm
    exact prime_square_smooth_mem_fiber hp hm
  · intro m hm n hn hmn
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) hmn
  · intro n hn
    obtain ⟨hn1, hnN, hnBad, hlpf⟩ := mem_singletonPrimeFiber.mp hn
    have hsquare : p ^ 2 ∣ n := by simpa [hlpf] using hnBad.2
    obtain ⟨m, hnm⟩ := hsquare
    have hm0 : m ≠ 0 := by
      intro hm0
      simp [hm0] at hnm
      omega
    have hmlpf : largestPrimeFactor m ≤ p := by
      rw [← hlpf]
      apply largestPrimeFactor_mono_dvd (by omega : n ≠ 0)
      exact ⟨p ^ 2, by simpa [mul_comm] using hnm⟩
    have hmSmooth := (mem_smoothNumbers_iff_largestPrimeFactor hp.one_le).mpr ⟨hm0, hmlpf⟩
    have hmN : m ≤ N / p ^ 2 := by
      apply (Nat.le_div_iff_mul_le (pow_pos hp.pos 2)).mpr
      simpa [hnm, mul_comm] using hnN
    exact ⟨m, Nat.mem_smoothNumbersUpTo.mpr ⟨hmN, hmSmooth⟩, hnm.symm⟩

/-- The exact identity `A(N) = sum_p Psi(N/p^2,p)`, before taking real casts. -/
theorem singletonBadUpTo_card_eq_sum_smoothCount (N : ℕ) :
    (singletonBadUpTo N).card =
      ∑ p ∈ (N + 1).primesBelow, smoothCount (N / p ^ 2) p := by
  classical
  have hf : ∀ n ∈ singletonBadUpTo N, largestPrimeFactor n ∈ (N + 1).primesBelow := by
    intro n hn
    obtain ⟨hn1, hnN, hnBad⟩ := mem_singletonBadUpTo.mp hn
    exact Nat.mem_primesBelow.mpr
      ⟨Nat.lt_succ_iff.mpr ((largestPrimeFactor_le_self hn1).trans hnN),
        largestPrimeFactor_prime (by have := hnBad.1; omega)⟩
  have h := Finset.card_eq_sum_card_fiberwise hf
  calc
    _ = ∑ p ∈ (N + 1).primesBelow, (singletonPrimeFiber N p).card := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      exact singletonPrimeFiber_card (Nat.prime_of_mem_primesBelow hp)

theorem A_eq_sum_smoothCount (x : ℝ) :
    A x = ∑ p ∈ (⌊x⌋₊ + 1).primesBelow, (smoothCount (⌊x⌋₊ / p ^ 2) p : ℝ) := by
  unfold A
  rw [singletonBadUpTo_card_eq_sum_smoothCount, Nat.cast_sum]

end

end Erdos380
