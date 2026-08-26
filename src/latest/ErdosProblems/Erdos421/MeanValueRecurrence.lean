import ErdosProblems.Erdos421.MeanValueStep
import ErdosProblems.Erdos421.VinogradovMonotone

/-! # A quantitative complete-system recurrence with an integer scale -/

namespace Erdos421

theorem vinogradovCount_scale_recurrence (s k N M : ℕ)
    (hks : 2 ≤ k + s) (hk : 0 < k) (hs : 0 < s)
    (hN : (4 * ((k + s) * (k + s - 1))) ^ 2 < N)
    (hM : 1 < M) (hkM : k ≤ M) (hNM : N ≤ M ^ k) :
    vinogradovCount (k + s) k N ≤
      (4 * k ^ 3 * k.factorial) * N ^ k *
        (2 ^ (2 * k ^ 3) * M) ^ (2 * s + k * (k - 1) / 2) *
          vinogradovCount s k (N / M + 1) := by
  obtain ⟨p, _, hMp, hup, _, hcount⟩ := exists_prime_vinogradov_step s k N M
    hks hk hs hN hM hkM hNM
  have hq : N / p + 1 ≤ N / M + 1 :=
    Nat.add_le_add_right (Nat.div_le_div_left hMp.le (Nat.zero_lt_of_lt hM)) 1
  calc
    _ ≤ (4 * k ^ 3 * k.factorial) * N ^ k * p ^ (2 * s + k * (k - 1) / 2) *
        vinogradovCount s k (N / p + 1) := hcount
    _ ≤ (4 * k ^ 3 * k.factorial) * N ^ k *
        (2 ^ (2 * k ^ 3) * M) ^ (2 * s + k * (k - 1) / 2) *
          vinogradovCount s k (N / M + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hup _))
        (vinogradovCount_mono hq s k)

end Erdos421
