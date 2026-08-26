import ErdosProblems.Erdos520.ThinScheduleChebyshev
import Mathlib.NumberTheory.Harmonic.Bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset
open scoped BigOperators Nat.Prime Topology

namespace Erdos
namespace Problem520

/-!
# Elementary aggregate estimates for the Caich `W` split

The small-prime branch only needs the crude harmonic estimate for reciprocal
primes.  The single-atom branch only needs the unconditional Chebyshev upper
bound for the total number of primes.  Both estimates below are uniform in
the lower endpoint of the fresh-prime block.
-/

/-- A fresh-prime reciprocal sum is bounded by the full harmonic sum at its
upper endpoint. -/
theorem freshReciprocalSum_le_harmonic (a x : ℕ) :
    freshReciprocalSum a x ≤ (harmonic x : ℝ) := by
  classical
  have hsub : freshPrimes a x ⊆ Finset.Icc 1 x := by
    intro p hp
    have hpInfo := mem_freshPrimes.mp hp
    exact Finset.mem_Icc.mpr ⟨by omega, hpInfo.2.2⟩
  unfold freshReciprocalSum
  calc
    (∑ p ∈ freshPrimes a x, (p : ℝ)⁻¹) ≤
        ∑ p ∈ Finset.Icc 1 x, (p : ℝ)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p hp hnot ↦ by positivity)
    _ = (harmonic x : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]

/-- The convenient logarithmic consequence of the harmonic majorant. -/
theorem freshReciprocalSum_le_one_add_log (a x : ℕ) :
    freshReciprocalSum a x ≤ 1 + Real.log (x : ℝ) :=
  (freshReciprocalSum_le_harmonic a x).trans (harmonic_le_one_add_log x)

/-- The fresh-prime block is a subset of all primes up to its upper
endpoint. -/
theorem card_freshPrimes_le_primeCounting (a x : ℕ) :
    #(freshPrimes a x) ≤ Nat.primeCounting x := by
  have hsub : freshPrimes a x ⊆ (x + 1).primesBelow := by
    intro p hp
    have hpInfo := mem_freshPrimes.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, hpInfo.1⟩
  calc
    #(freshPrimes a x) ≤ #((x + 1).primesBelow) :=
      Finset.card_le_card hsub
    _ = Nat.primeCounting x := by
      rw [Nat.primesBelow_card_eq_primeCounting']
      rfl

/-- An explicit prime-counting upper bound immediately controls every
fresh-prime block, uniformly in its lower endpoint. -/
theorem card_freshPrimes_cast_le_of_primeCountingUpperBound
    {C : ℝ} {N x : ℕ} (hP : PrimeCountingUpperBound C N)
    (hx : N ≤ x) (a : ℕ) :
    (#(freshPrimes a x) : ℝ) ≤
      C * (x : ℝ) / Real.log (x : ℝ) := by
  calc
    (#(freshPrimes a x) : ℝ) ≤ (Nat.primeCounting x : ℝ) := by
      exact_mod_cast card_freshPrimes_le_primeCounting a x
    _ ≤ C * (x : ℝ) / Real.log (x : ℝ) := by
      simpa only [Nat.floor_natCast] using!
        hP (x : ℝ) (by exact_mod_cast hx)

/-- Unconditionally, a single absolute constant bounds the cardinality of
every fresh-prime block by `C x / log x` for all sufficiently large `x`.
The quantifier over the lower endpoint remains inside the eventuality. -/
theorem exists_eventually_uniform_card_freshPrimes_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∀ a : ℕ,
        (#(freshPrimes a x) : ℝ) ≤
          C * (x : ℝ) / Real.log (x : ℝ) := by
  obtain ⟨C, hC, N, hN, hP⟩ := exists_primeCountingUpperBound
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop N] with x hx
  intro a
  exact card_freshPrimes_cast_le_of_primeCountingUpperBound hP hx a

end Problem520
end Erdos
