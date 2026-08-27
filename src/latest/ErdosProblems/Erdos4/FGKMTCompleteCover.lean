import ErdosProblems.Erdos4.FGKMTResidueChoices
import ErdosProblems.Erdos4.ZeroSieveResidual

/-! Combine the shifted prime cover, zero residues, and fresh-prime cleanup. -/

namespace Erdos4.FGKMT

open Classical ChebyshevIntervals ZeroSieveResidual

theorem exists_complete_cover_from_choices
    (sieve sources reserve : Finset ℕ) [∀ l : sieve, Fact l.val.Prime]
    {w z base x Y R : ℕ} (hbase : 0 < base) (hwbase : w ≤ base)
    (hzbase : z ≤ base) (hbasex : base ≤ x) (hxR : x ≤ R) (hY : Y ≤ w * base)
    (hrandom : ∀ p ∈ sieve, w < p ∧ p ≤ z)
    (hsource : ∀ p ∈ sources, p.Prime ∧ base < p ∧ p ≤ x)
    (hreserve : ∀ p ∈ reserve, p.Prime ∧ x < p ∧ p ≤ R)
    (a : ∀ l : sieve, ZMod l.val) (b : ∀ p : sources, ZMod p.val)
    (hcard : (remainingPrimeTargets sieve sources (primeInterval x Y) Y a b ∪
      (Nat.smoothNumbersUpTo Y (z + 1) ∪ x.primesLE)).card ≤ reserve.card) :
    ∃ cover : Erdos4.ResidueCover Y, cover.modulus ≤ primorial R := by
  have hdisjoint : Disjoint sieve sources := by
    apply Finset.disjoint_left.mpr
    intro p hp hs
    have hh := (hrandom p hp).2.trans hzbase
    have hh' := (hsource p hs).2.1
    omega
  have hfresh : Disjoint (sieve ∪ sources) reserve := by
    apply Finset.disjoint_left.mpr
    intro p hp hs
    have hh := (hreserve p hs).2.1
    rcases Finset.mem_union.mp hp with hp | hp
    · have hh' := ((hrandom p hp).2.trans hzbase).trans hbasex
      omega
    · have hh' := (hsource p hp).2.2
      omega
  obtain ⟨other, hother⟩ := exists_cover_of_residue_choices_with_reserve
    sieve sources (primeInterval x Y) Y a b
    (Nat.smoothNumbersUpTo Y (z + 1) ∪ x.primesLE) reserve
    (fun p hp => (hsource p hp).1) (fun p hp => (hreserve p hp).1)
    hdisjoint hfresh hcard
  let S := survivors Y w z base
  have hS : S ⊆ primeInterval x Y ∪ (Nat.smoothNumbersUpTo Y (z + 1) ∪ x.primesLE) := by
    intro n hn
    rcases smooth_or_prime hbase hY hn with hs | hp
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hs)
    · by_cases hnx : n ≤ x
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Nat.mem_primesLE.mpr ⟨hnx, hp.1⟩))
      · exact Finset.mem_union_left _ (mem_primeInterval.mpr
          ⟨hp.1, by omega, (mem_survivors.mp hn).2.1⟩)
  let rest : Erdos4.PartialResidueCover S :=
    ⟨other.primes, other.residue, other.prime, fun n hn => other.covers n (hS hn)⟩
  obtain ⟨initial, hinitial⟩ := exists_zero_cover Y w z base
  have hzeroBound : ∀ p ∈ zeroPrimes w z base, p ≤ base := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Nat.mem_primesLE.mp hp).1.trans hwbase
    · exact (mem_primeInterval.mp hp).2.2
  have hzeroRandom : Disjoint (zeroPrimes w z base) sieve := by
    apply Finset.disjoint_left.mpr
    intro p hp hs
    obtain ⟨hlow, hhigh⟩ := hrandom p hs
    rcases Finset.mem_union.mp hp with hp | hp
    · have hh := (Nat.mem_primesLE.mp hp).1
      omega
    · have hh := (mem_primeInterval.mp hp).2.1
      omega
  have hd : Disjoint initial.primes rest.primes := by
    change Disjoint initial.primes other.primes
    rw [hinitial, hother]
    apply Finset.disjoint_left.mpr
    intro p hp hs
    have hpb := hzeroBound p hp
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases Finset.mem_union.mp hs with hs | hs
      · exact Finset.disjoint_left.mp hzeroRandom hp hs
      · have hh := (hsource p hs).2.1
        omega
    · have hh := (hreserve p hs).2.1
      omega
  have hsub : S ⊆ Finset.Icc 1 Y := Finset.filter_subset _ _
  let combined := (initial.union rest hd).reindex (Finset.sdiff_union_of_subset hsub)
  let cover := combined.toResidueCover
  have hsupport : cover.primes = zeroPrimes w z base ∪ ((sieve ∪ sources) ∪ reserve) := by
    change initial.primes ∪ other.primes = _
    rw [hinitial, hother]
  have hbound : cover.primes ⊆ R.primesLE := by
    intro p hp
    have hpprime := cover.prime p hp
    apply Nat.mem_primesLE.mpr
    refine ⟨?_, hpprime⟩
    rw [hsupport] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ((hzeroBound p hp).trans hbasex).trans hxR
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact (((hrandom p hp).2.trans hzbase).trans hbasex).trans hxR
        · exact ((hsource p hp).2.2).trans hxR
      · exact (hreserve p hp).2.2
  exact ⟨cover, Erdos4.primeProduct_le_primorial hbound⟩

end Erdos4.FGKMT
