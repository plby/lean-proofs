import ErdosProblems.Erdos4.ChebyshevIntervals
import ErdosProblems.Erdos4.CoverBudget

/-!
# Residual set for the zero-residue initial sieve

Residue zero is assigned to primes at most `w` and to primes in `(z,x]`.
If `Y ≤ w*x`, every survivor in `[1,Y]` is either `z`-smooth or a prime
larger than `x`. The cofactor of a nonsmooth survivor is eliminated by
one of the small zero residues.
-/

open scoped BigOperators

namespace Erdos4.ZeroSieveResidual

open ChebyshevIntervals

def zeroPrimes (w z x : ℕ) : Finset ℕ := w.primesLE ∪ primeInterval z x

theorem zeroPrimes_prime (w z x : ℕ) : ∀ p ∈ zeroPrimes w z x, p.Prime := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Nat.prime_of_mem_primesLE hp
  · exact (mem_primeInterval.mp hp).1

def survivors (Y w z x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter (fun n => ∀ p ∈ zeroPrimes w z x, ¬p ∣ n)

theorem mem_survivors {Y w z x n : ℕ} :
    n ∈ survivors Y w z x ↔ 1 ≤ n ∧ n ≤ Y ∧ ∀ p ∈ zeroPrimes w z x, ¬p ∣ n := by
  simp only [survivors, Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem smooth_or_prime {Y w z x n : ℕ} (hx : 0 < x) (hY : Y ≤ w * x)
    (hn : n ∈ survivors Y w z x) :
    n ∈ Nat.smoothNumbersUpTo Y (z + 1) ∨ (n.Prime ∧ x < n) := by
  have hdata := mem_survivors.mp hn
  have hnpos : 0 < n := by omega
  by_cases hs : n ∈ Nat.smoothNumbers (z + 1)
  · exact Or.inl (Nat.mem_smoothNumbersUpTo.mpr ⟨hdata.2.1, hs⟩)
  · right
    rw [Nat.mem_smoothNumbers'] at hs
    push Not at hs
    obtain ⟨p, hp, hpn, hpz⟩ := hs
    have hzp : z < p := by omega
    have hxp : x < p := by
      by_contra hpx
      have hpzero : p ∈ zeroPrimes w z x :=
        Finset.mem_union_right _ (mem_primeInterval.mpr ⟨hp, hzp, by omega⟩)
      exact hdata.2.2 p hpzero hpn
    obtain ⟨m, hm⟩ := hpn
    have hmpos : 0 < m := by
      by_contra hm0
      have hz : m = 0 := by omega
      simp [hz] at hm
      omega
    have hmw : m ≤ w := by
      have hxm : x * m ≤ x * w := by
        calc
          x * m ≤ p * m := Nat.mul_le_mul_right m hxp.le
          _ = n := hm.symm
          _ ≤ w * x := hdata.2.1.trans hY
          _ = x * w := Nat.mul_comm _ _
      nlinarith
    have hmone : m = 1 := by
      by_contra hm1
      obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
      have hqw : q ≤ w := (Nat.le_of_dvd hmpos hqm).trans hmw
      have hqzero : q ∈ zeroPrimes w z x :=
        Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨hqw, hq⟩)
      have hqn : q ∣ n := by
        rw [hm]
        exact dvd_mul_of_dvd_right hqm p
      exact hdata.2.2 q hqzero hqn
    have hnp : n = p := by simpa only [hmone, mul_one] using hm
    simpa only [hnp] using And.intro hp hxp

theorem survivors_subset {Y w z x : ℕ} (hx : 0 < x) (hY : Y ≤ w * x) :
    survivors Y w z x ⊆ Nat.smoothNumbersUpTo Y (z + 1) ∪ primeInterval x Y := by
  intro n hn
  rcases smooth_or_prime hx hY hn with hs | hp
  · exact Finset.mem_union_left _ hs
  · exact Finset.mem_union_right _ (mem_primeInterval.mpr ⟨hp.1, hp.2, (mem_survivors.mp hn).2.1⟩)

theorem exists_zero_cover (Y w z x : ℕ) :
    ∃ cover : Erdos4.PartialResidueCover (Finset.Icc 1 Y \ survivors Y w z x),
      cover.primes = zeroPrimes w z x := by
  classical
  refine ⟨⟨zeroPrimes w z x, fun _ => 0, zeroPrimes_prime w z x, ?_⟩, rfl⟩
  intro n hn
  have hnI := (Finset.mem_sdiff.mp hn).1
  have hnot := (Finset.mem_sdiff.mp hn).2
  have hex : ∃ p ∈ zeroPrimes w z x, p ∣ n := by
    by_contra hh
    push Not at hh
    exact hnot (Finset.mem_filter.mpr ⟨hnI, hh⟩)
  obtain ⟨p, hp, hpn⟩ := hex
  exact ⟨p, hp, Nat.modEq_zero_iff_dvd.mpr hpn⟩

end Erdos4.ZeroSieveResidual
