import ErdosProblems.Erdos587.ShortDifferencing
import ErdosProblems.Erdos587.FullPeriodDensity

/-! Embed a finite interval in a cycle with no wraparound for the selected shifts. -/

open scoped BigOperators ComplexConjugate

namespace Erdos587

def cyclicCutoffSequence {R : Type*} [Zero R] (z : ℕ → R) (q N : ℕ) (x : ZMod q) : R :=
  if x.val < N then z x.val else 0

lemma sum_range_cutoff {R : Type*} [AddCommMonoid R] (z : ℕ → R) {N M : ℕ} (hNM : N ≤ M) :
    (∑ n ∈ Finset.range M, if n < N then z n else 0) = ∑ n ∈ Finset.range N, z n := by
  calc
    _ = ∑ n ∈ Finset.range N, if n < N then z n else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hNM)
      intro n hn hnot
      simp only [Finset.mem_range] at hnot
      exact if_neg hnot
    _ = _ := Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_range.mp hn))

lemma sum_cyclicCutoffSequence {R : Type*} [AddCommMonoid R]
    (z : ℕ → R) (q N : ℕ) [NeZero q] (hNq : N ≤ q) :
    (∑ x : ZMod q, cyclicCutoffSequence z q N x) = ∑ n ∈ Finset.range N, z n := by
  rw [← sum_range_natCast_zmod]
  calc
    _ = ∑ n ∈ Finset.range q, if n < N then z n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [cyclicCutoffSequence, ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)]
    _ = _ := sum_range_cutoff z hNq

lemma cyclicCutoffSequence_map {R S : Type*} [Zero R] [Zero S]
    (z : ℕ → R) (φ : R → S) (hφ : φ 0 = 0) (q N : ℕ) (x : ZMod q) :
    φ (cyclicCutoffSequence z q N x) = cyclicCutoffSequence (fun n => φ (z n)) q N x := by
  unfold cyclicCutoffSequence
  split_ifs <;> simp only [hφ]

lemma cyclicCutoffSequence_correlation (z : ℕ → ℂ) {N r : ℕ}
    (hN : 0 < N) (hr : r ≤ N) (x : ZMod (2 * N)) :
    cyclicCutoffSequence z (2 * N) N (x + r • (1 : ZMod (2 * N))) *
        conj (cyclicCutoffSequence z (2 * N) N x) =
      cyclicCutoffSequence (fun n => z (n + r) * conj (z n)) (2 * N) (N - r) x := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  by_cases hx : x.val < N
  · have hrq : r < 2 * N := by omega
    have hval : (x + r • (1 : ZMod (2 * N))).val = x.val + r := by
      rw [nsmul_one, ZMod.val_add, ZMod.val_natCast_of_lt hrq,
        Nat.mod_eq_of_lt (show x.val + r < 2 * N by omega)]
    by_cases hxr : x.val + r < N
    · have hcut : x.val < N - r := by omega
      simp only [cyclicCutoffSequence, hval, if_pos hx, if_pos hxr, if_pos hcut]
    · have hcut : ¬ x.val < N - r := by omega
      simp only [cyclicCutoffSequence, hval, if_pos hx, if_neg hxr, if_neg hcut, zero_mul]
  · have hcut : ¬ x.val < N - r := by omega
    simp only [cyclicCutoffSequence, if_neg hx, if_neg hcut, map_zero, mul_zero]

lemma finiteShiftCorrelation_cyclicCutoff (z : ℕ → ℂ) {N r : ℕ}
    (hN : 0 < N) (hr : r ≤ N) :
    letI : NeZero (2 * N) := ⟨by omega⟩
    finiteShiftCorrelation (cyclicCutoffSequence z (2 * N) N) (1 : ZMod (2 * N)) r =
      ∑ n ∈ Finset.range (N - r), z (n + r) * conj (z n) := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  change (∑ x : ZMod (2 * N), cyclicCutoffSequence z (2 * N) N (x + r • 1) *
    conj (cyclicCutoffSequence z (2 * N) N x)) = _
  simp_rw [cyclicCutoffSequence_correlation z hN hr]
  exact sum_cyclicCutoffSequence _ _ _ (by omega)

theorem interval_short_shift_differencing (z : ℕ → ℂ) {N K : ℕ}
    (hN : 0 < N) (hK : K ≤ N) (hz : ∀ n < N, ‖z n‖ ≤ 1) :
    (K : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 ≤
      2 * N * ((K : ℝ) * N + 2 * K * ∑ r ∈ Finset.range K,
        ‖∑ n ∈ Finset.range (N - (r + 1)), z (n + r + 1) * conj (z n)‖) := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  have hh := finite_short_shift_differencing (cyclicCutoffSequence z (2 * N) N)
    (1 : ZMod (2 * N)) K
  rw [sum_cyclicCutoffSequence z (2 * N) N (by omega), ZMod.card] at hh
  have henergy : (∑ x : ZMod (2 * N), ‖cyclicCutoffSequence z (2 * N) N x‖ ^ 2) ≤ N := by
    simp_rw [cyclicCutoffSequence_map z (fun w : ℂ => ‖w‖ ^ 2) (by simp)]
    rw [sum_cyclicCutoffSequence _ _ _ (by omega)]
    calc
      _ ≤ ∑ n ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        simpa only [one_pow] using
          pow_le_pow_left₀ (norm_nonneg (z n)) (hz n (Finset.mem_range.mp hn)) 2
      _ = N := by simp
  have hcorr : (∑ r ∈ Finset.range K,
      ‖finiteShiftCorrelation (cyclicCutoffSequence z (2 * N) N) (1 : ZMod (2 * N)) (r + 1)‖) =
      ∑ r ∈ Finset.range K, ‖∑ n ∈ Finset.range (N - (r + 1)), z (n + r + 1) * conj (z n)‖ := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [finiteShiftCorrelation_cyclicCutoff z hN (by have := Finset.mem_range.mp hr; omega)]
    simp only [Nat.add_assoc]
  rw [hcorr, Nat.cast_mul, Nat.cast_ofNat] at hh
  apply hh.trans
  gcongr

end Erdos587
