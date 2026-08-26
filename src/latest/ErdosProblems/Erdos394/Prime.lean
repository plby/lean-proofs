import ErdosProblems.Erdos394.Structural

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Nat Finset

namespace Erdos394

/-- For a prime modulus, divisibility of the block product comes from one factor. -/
theorem prime_dvd_consecutiveProduct_iff {p k m : ℕ} (hp : p.Prime) :
    p ∣ consecutiveProduct k m ↔ ∃ i < k, p ∣ m + i := by
  rw [consecutiveProduct]
  simpa only [Finset.mem_range] using
    (Prime.dvd_finsetProd_iff (S := Finset.range k)
      (Nat.prime_iff.mp hp) (fun i : ℕ ↦ m + i))

/-- Exact value at primes longer than the block: `t_k(p)=p+1-k`. -/
theorem t_prime {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hkp : k ≤ p) :
    t k p = p + 1 - k := by
  have hcand_pos : 0 < p + 1 - k := by omega
  have hi_mem : k - 1 ∈ Finset.range k := by simp [hk]
  have hfactor : (p + 1 - k) + (k - 1) = p := by omega
  have hcand_div : p ∣ consecutiveProduct k (p + 1 - k) := by
    unfold consecutiveProduct
    simpa [hfactor] using
      (Finset.dvd_prod_of_mem (fun i : ℕ ↦ (p + 1 - k) + i) hi_mem)
  apply Nat.le_antisymm
  · exact t_min hcand_pos hcand_div
  · have htpos : 0 < t k p := t_pos hk hp.pos
    have hpdiv : p ∣ consecutiveProduct k (t k p) := t_dvd hk hp.pos
    obtain ⟨i, hi, hpi⟩ := (prime_dvd_consecutiveProduct_iff hp).mp hpdiv
    have hsum_pos : 0 < t k p + i := by omega
    have hple : p ≤ t k p + i := Nat.le_of_dvd hsum_pos hpi
    omega

/-- In particular, the familiar two-term value is `t₂(p)=p-1`. -/
theorem t_two_prime {p : ℕ} (hp : p.Prime) : t 2 p = p - 1 := by
  have h2p : 2 ≤ p := hp.two_le
  rw [t_prime hp (by omega) h2p]
  omega

end Erdos394
