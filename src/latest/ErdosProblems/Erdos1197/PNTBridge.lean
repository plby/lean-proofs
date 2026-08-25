import PrimeNumberTheoremAnd.Consequences

open Chebyshev
open scoped Asymptotics Chebyshev

namespace Erdos1197

/-- A positive increment of Chebyshev's theta function contains a prime.
This is the elementary bridge from the proved PNT asymptotic to the interval
form used by the Buczolich--Mauldin construction. -/
lemma theta_pos_implies_prime_in_interval {x y : ℝ}
    (_hxy : y < x) (h : θ x - θ y > 0) :
    HasPrimeInInterval y (x - y) := by
  by_contra hnone
  have hle : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → (p : ℝ) ≤ y := by
    intro p hp hpx
    by_contra hpy
    apply hnone
    refine ⟨p, hp, lt_of_not_ge hpy, ?_⟩
    linarith
  have htheta : θ x = θ y := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    congr 1
    ext p
    simp only [Nat.mem_primesLE]
    constructor
    · rintro ⟨hpx, hp⟩
      refine ⟨?_, hp⟩
      exact Nat.le_floor (hle p hp ((Nat.le_floor_iff' hp.ne_zero).mp hpx))
    · rintro ⟨hpy, hp⟩
      refine ⟨?_, hp⟩
      exact Nat.le_floor (by
        have : (p : ℝ) ≤ y := (Nat.le_floor_iff' hp.ne_zero).mp hpy
        linarith)
  linarith

end Erdos1197
