import ErdosProblems.Erdos421.ResidueQuotient

/-! # The complete-system mean-value step

The prime and residue selection, nonsingular congruence count,
zero-representation bound, and interval parametrization are all proved
in the imported modules. The shorter interval keeps its rounding term.
-/

namespace Erdos421

theorem exists_prime_vinogradov_step (s k N M : ℕ)
    (hks : 2 ≤ k + s) (hk : 0 < k) (hs : 0 < s)
    (hN : (4 * ((k + s) * (k + s - 1))) ^ 2 < N)
    (hM : 1 < M) (hkM : k ≤ M) (hNM : N ≤ M ^ k) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ 2 ^ (2 * k ^ 3) * M ∧ N < p ^ k ∧
      vinogradovCount (k + s) k N ≤
        (4 * k ^ 3 * k.factorial) * N ^ k * p ^ (2 * s + k * (k - 1) / 2) *
          vinogradovCount s k (N / p + 1) := by
  obtain ⟨p, hp, hMp, hup, hNp, c, hcount⟩ := exists_prime_and_residue_at_root_scale
    s k N M hks hk hs hN hM hNM
  have hm := mixedIntegerCount_residue_le s k N p hp hk (hkM.trans_lt hMp) hNp.le c
  have hr := restrictedResidueCount_le s k N p hs hp.pos c
  have hmr : mixedIntegerCount (primeDistinctTuples k N p) (integerResidueClass N p c) s k ≤
      N ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
        vinogradovCount s k (N / p + 1) :=
    hm.trans (Nat.mul_le_mul_left _ hr)
  refine ⟨p, hp, hMp, hup, hNp, ?_⟩
  calc
    _ ≤ 4 * k ^ 3 * p ^ (2 * s) *
        mixedIntegerCount (primeDistinctTuples k N p) (integerResidueClass N p c) s k := hcount
    _ ≤ 4 * k ^ 3 * p ^ (2 * s) *
        (N ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) *
          vinogradovCount s k (N / p + 1)) := Nat.mul_le_mul_left _ hmr
    _ = _ := by rw [pow_add]; ring

end Erdos421
