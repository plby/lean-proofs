import ErdosProblems.Erdos1058.Erdos1058Core

namespace Erdos1058

open Nat

namespace PrimeGap210Certificate

/-- The local spacing condition used by the finite prime cover. -/
def GapStep (a b : ℕ) : Prop := b ≤ a + 210

/-- The compact interface exported by each piece of the finite prime cover.  It
records primality, the gap condition, and the two endpoints without requiring
later aggregation proofs to unfold the (very large) underlying lists. -/
structure CertifiedSegment (xs : List ℕ) (first last : ℕ) : Prop where
  primes : xs.Forall Nat.Prime
  chain : xs.IsChain GapStep
  head_eq : xs.head? = some first
  last_eq : xs.getLast? = some last

/-- Adjacent certified pieces concatenate to another certified piece. -/
lemma CertifiedSegment.append {xs ys : List ℕ} {a b c d : ℕ}
    (hx : CertifiedSegment xs a b) (hy : CertifiedSegment ys c d)
    (hbc : GapStep b c) : CertifiedSegment (xs ++ ys) a d := by
  have hxs : xs ≠ [] := by
    intro h
    have hhead := hx.head_eq
    simp [h] at hhead
  have hys : ys ≠ [] := by
    intro h
    have hhead := hy.head_eq
    simp [h] at hhead
  refine ⟨List.forall_append.mpr ⟨hx.primes, hy.primes⟩, ?_, ?_, ?_⟩
  · exact hx.chain.append hy.chain (by
      intro x hxlast y hyhead
      have hbx : b = x := by simpa [hx.last_eq] using hxlast
      have hcy : c = y := by simpa [hy.head_eq] using hyhead
      subst x
      subst y
      exact hbc)
  · simpa only [List.head?_append_of_ne_nil _ hxs] using hx.head_eq
  · simpa only [List.getLast?_append_of_ne_nil _ hys] using hy.last_eq

/-- A prime chain with gaps at most `210` supplies a prime in `(p,p+210]`
as soon as its first element is at most `p+210` and some element is above
`p`. -/
lemma exists_prime_in_chain {p a : ℕ} {xs : List ℕ}
    (hprime : (a :: xs).Forall Nat.Prime)
    (hchain : (a :: xs).IsChain GapStep)
    (habound : a ≤ p + 210)
    (hfuture : ∃ z ∈ a :: xs, p < z) :
    ∃ r ∈ a :: xs, r.Prime ∧ p < r ∧ r ≤ p + 210 := by
  induction xs generalizing a with
  | nil =>
      obtain ⟨z, hz, hpz⟩ := hfuture
      simp only [List.mem_singleton] at hz
      subst z
      exact ⟨a, by simp, by simpa using hprime, hpz, habound⟩
  | cons b xs ih =>
      have haPrime : a.Prime := hprime.1
      by_cases hpa : p < a
      · exact ⟨a, by simp, haPrime, hpa, habound⟩
      have hfuture' : ∃ z ∈ b :: xs, p < z := by
        obtain ⟨z, hz, hpz⟩ := hfuture
        rcases List.mem_cons.mp hz with rfl | hz
        · omega
        · exact ⟨z, hz, hpz⟩
      have hab : GapStep a b := hchain.rel
      obtain ⟨r, hrmem, hrprime, hpr, hrbound⟩ :=
        ih hprime.2 hchain.tail (by unfold GapStep at hab; omega) hfuture'
      exact ⟨r, by simp [hrmem], hrprime, hpr, hrbound⟩

/-- A certified segment whose last entry lies above `p` supplies a prime in
`(p,p+210]`.  Keeping this lemma polymorphic in the list prevents later uses
from unfolding the full finite cover. -/
lemma CertifiedSegment.exists_prime_after {xs : List ℕ} {first last p : ℕ}
    (hcert : CertifiedSegment xs first last)
    (hfirst : first ≤ p + 210) (hlast : p < last) :
    ∃ r ∈ xs, r.Prime ∧ p < r ∧ r ≤ p + 210 := by
  have hheadMem : first ∈ xs.head? := by
    rw [hcert.head_eq]
    simp
  have hshape : xs = first :: xs.tail :=
    List.eq_cons_of_mem_head? hheadMem
  have hprime := hcert.primes
  have hchain := hcert.chain
  rw [hshape] at hprime hchain
  have hlastOpt : last ∈ xs.getLast? := by
    rw [hcert.last_eq]
    simp
  have hlastMem : last ∈ xs := List.mem_of_mem_getLast? hlastOpt
  have hfuture : ∃ z ∈ first :: xs.tail, p < z := by
    refine ⟨last, ?_, hlast⟩
    rw [← hshape]
    exact hlastMem
  obtain ⟨r, hrmem, hrprime, hpr, hrbound⟩ :=
    exists_prime_in_chain hprime hchain hfirst hfuture
  refine ⟨r, ?_, hrprime, hpr, hrbound⟩
  rw [hshape]
  exact hrmem

end PrimeGap210Certificate

end Erdos1058
