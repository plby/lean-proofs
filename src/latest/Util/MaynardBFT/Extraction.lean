import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Int.ModEq

/-!
# Extracting indexed runs of consecutive primes

The interval hypothesis concerns every prime in the interval, not just the
members of a prime cluster. This is the elementary last step in the BFT
argument. The starting index is the number of primes strictly below the
lower endpoint.
-/

namespace MaynardBFT

theorem count_add_card_filter_Icc (P : ℕ → Prop) [DecidablePred P]
    {L U : ℕ} (hLU : L ≤ U) :
    Nat.count P L + ((Finset.Icc L U).filter P).card = Nat.count P (U + 1) := by
  have hpartition : (Finset.range (U + 1)).filter P =
      ((Finset.range L).filter P) ∪ ((Finset.Icc L U).filter P) := by
    ext x
    by_cases hx : P x
    · simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Icc,
        hx, and_true]
      omega
    · simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Icc,
        hx, and_false, or_self]
  have hdisjoint : Disjoint ((Finset.range L).filter P)
      ((Finset.Icc L U).filter P) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxL := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hLx := (Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1).1
    omega
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    hpartition, Finset.card_union_of_disjoint hdisjoint]

theorem nth_prime_mem_interval {L U m j : ℕ}
    (hcount : m ≤ ((Finset.Icc L U).filter Nat.Prime).card) (hj : j < m) :
    L ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime L + j) ∧
      Nat.nth Nat.Prime (Nat.count Nat.Prime L + j) ≤ U := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega :
    0 < ((Finset.Icc L U).filter Nat.Prime).card)
  have hpI := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
  have hpartition := count_add_card_filter_Icc Nat.Prime (hpI.1.trans hpI.2)
  constructor
  · exact (Nat.le_nth_count Nat.infinite_setOfPred_prime L).trans
      (Nat.nth_monotone Nat.infinite_setOfPred_prime (Nat.le_add_right _ _))
  · have hindex : Nat.count Nat.Prime L + j < Nat.count Nat.Prime (U + 1) := by
      omega
    exact Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count hindex)

/-- An interval containing enough primes, all in one residue class, supplies
the exact consecutive indices and preserves its length bound. -/
theorem consecutive_run_of_interval {m q C N L U : ℕ} {a : ℤ}
    (hm : 0 < m)
    (hlate : Nat.nth Nat.Prime N ≤ L)
    (hcount : m ≤ ((Finset.Icc L U).filter Nat.Prime).card)
    (hresidue : ∀ p ∈ Finset.Icc L U, p.Prime →
      (p : ℤ) ≡ a [ZMOD (q : ℤ)])
    (hspan : U - L ≤ q * C) :
    ∃ r : ℕ, N ≤ r ∧
      (∀ j, j < m → (Nat.nth Nat.Prime (r + j) : ℤ) ≡ a [ZMOD (q : ℤ)]) ∧
      Nat.nth Nat.Prime (r + m - 1) - Nat.nth Nat.Prime r ≤ q * C := by
  let r := Nat.count Nat.Prime L
  have hNr : N ≤ r := by
    have hc := Nat.count_monotone Nat.Prime hlate
    simpa only [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] using hc
  have hrun (j : ℕ) (hj : j < m) :
      L ≤ Nat.nth Nat.Prime (r + j) ∧ Nat.nth Nat.Prime (r + j) ≤ U :=
    nth_prime_mem_interval hcount hj
  refine ⟨r, hNr, ?_, ?_⟩
  · intro j hj
    exact hresidue _ (Finset.mem_Icc.mpr (hrun j hj)) (Nat.prime_nth_prime _)
  · have hfirst : L ≤ Nat.nth Nat.Prime r := by
      simpa only [Nat.add_zero] using (hrun 0 hm).1
    have hlast : Nat.nth Nat.Prime (r + m - 1) ≤ U := by
      have hindex : r + (m - 1) = r + m - 1 := by omega
      simpa only [hindex] using (hrun (m - 1) (by omega)).2
    omega

end MaynardBFT
