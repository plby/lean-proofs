import ErdosProblems.Erdos796.SemiprimeIdentity
import Mathlib.Tactic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A prime-summatory formula for the semiprime count

Grouping a semiprime pair by its smaller prime gives an exact finite formula
in terms of the prime-counting function.  This is the natural starting point
for deriving the second-order semiprime asymptotic from PNT and the prime
harmonic sum.
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

/-- Admissible larger prime partners of a fixed smaller prime. -/
def semiprimePartners (n p : ℕ) : Finset ℕ :=
  (Nat.primesLE (n / p)).filter fun q => p ≤ q

@[simp]
theorem mem_semiprimePartners {n p q : ℕ} :
    q ∈ semiprimePartners n p ↔ q.Prime ∧ q ≤ n / p ∧ p ≤ q := by
  constructor
  · intro hq
    have hq' := Finset.mem_filter.mp hq
    have hp := Nat.mem_primesLE.mp hq'.1
    exact ⟨hp.2, hp.1, hq'.2⟩
  · rintro ⟨hqprime, hqle, hpq⟩
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hqle, hqprime⟩, hpq⟩

theorem smaller_prime_le_sqrt {n p q : ℕ}
    (hpq : (p, q) ∈ semiprimePairs n) : p ≤ n.sqrt := by
  have h := Finset.mem_filter.mp hpq
  have hmem := Finset.mem_product.mp h.1
  have hcond := h.2
  rw [Nat.le_sqrt]
  exact (Nat.mul_le_mul_left p hcond.1).trans hcond.2

theorem semiprimePairs_fst_mapsTo (n : ℕ) :
    Set.MapsTo Prod.fst (semiprimePairs n : Set (ℕ × ℕ))
      (Nat.primesLE n.sqrt : Set ℕ) := by
  intro pq hpq
  have h := Finset.mem_filter.mp hpq
  have hmem := Finset.mem_product.mp h.1
  exact Nat.mem_primesLE.mpr
    ⟨smaller_prime_le_sqrt hpq, (Nat.mem_primesLE.mp hmem.1).2⟩

/-- The fibre over the smaller prime is in bijection with its partner set. -/
theorem card_semiprimePairs_fiber_eq_partners
    {n p : ℕ} (hp : p ∈ Nat.primesLE n.sqrt) :
    ((semiprimePairs n).filter fun pq => pq.1 = p).card =
      (semiprimePartners n p).card := by
  have hp' := Nat.mem_primesLE.mp hp
  have hppos := hp'.2.pos
  refine Finset.card_bij (fun pq _ => pq.2) ?_ ?_ ?_
  · intro pq hpq
    have hpq' := Finset.mem_filter.mp hpq
    have hpair := Finset.mem_filter.mp hpq'.1
    have hmem := Finset.mem_product.mp hpair.1
    have hcond := hpair.2
    have hpEq : pq.1 = p := hpq'.2
    apply mem_semiprimePartners.mpr
    refine ⟨(Nat.mem_primesLE.mp hmem.2).2, ?_, ?_⟩
    · apply (Nat.le_div_iff_mul_le hppos).mpr
      simpa [hpEq, Nat.mul_comm] using! hcond.2
    · simpa [hpEq] using! hcond.1
  · intro a ha b hb hsnd
    apply Prod.ext
    · exact (Finset.mem_filter.mp ha).2.trans
        (Finset.mem_filter.mp hb).2.symm
    · exact hsnd
  · intro q hq
    have hq' := mem_semiprimePartners.mp hq
    have hqle : q ≤ n := by
      have hdivle : n / p ≤ n := Nat.div_le_self _ _
      exact hq'.2.1.trans hdivle
    have hple : p ≤ n :=
      hp'.1.trans (Nat.sqrt_le_self n)
    refine ⟨(p, q), Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨Nat.mem_primesLE.mpr ⟨hple, hp'.2⟩,
          Nat.mem_primesLE.mpr ⟨hqle, hq'.1⟩⟩
    · exact ⟨hq'.2.2, by
        simpa [Nat.mul_comm] using!
          (Nat.le_div_iff_mul_le hppos).mp hq'.2.1⟩

theorem primesBelow_fixed_eq {p n : ℕ}
    (hp : p ∈ Nat.primesLE n.sqrt) :
    ((Nat.primesLE (n / p)).filter fun q => ¬p ≤ q) =
      Nat.primesLE (p - 1) := by
  have hp' := Nat.mem_primesLE.mp hp
  have hppos := hp'.2.pos
  have hpsq : p * p ≤ n := Nat.le_sqrt.mp hp'.1
  have hpdiv : p ≤ n / p := (Nat.le_div_iff_mul_le hppos).mpr hpsq
  ext q
  simp only [Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hqn, hqprime⟩, hnot⟩
    exact ⟨by omega, hqprime⟩
  · rintro ⟨hqp, hqprime⟩
    have hqle : q ≤ n / p := hqp.trans (by omega)
    exact ⟨⟨hqle, hqprime⟩, by omega⟩

/-- Exact cardinality of the partner set. -/
theorem card_semiprimePartners {n p : ℕ}
    (hp : p ∈ Nat.primesLE n.sqrt) :
    (semiprimePartners n p).card =
      Nat.primeCounting (n / p) - Nat.primeCounting (p - 1) := by
  have hpartition := (Nat.primesLE (n / p)).card_filter_add_card_filter_not
    (fun q => p ≤ q)
  change (semiprimePartners n p).card +
      ((Nat.primesLE (n / p)).filter fun q => ¬p ≤ q).card =
        (Nat.primesLE (n / p)).card at hpartition
  rw [primesBelow_fixed_eq hp, Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting] at hpartition
  omega

theorem primesLE_prime_eq_insert_predecessor {p : ℕ} (hp : p.Prime) :
    Nat.primesLE p = insert p (Nat.primesLE (p - 1)) := by
  ext q
  simp only [Nat.mem_primesLE, Finset.mem_insert]
  constructor
  · rintro ⟨hqp, hqprime⟩
    by_cases h : q = p
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hqprime⟩
  · rintro (rfl | ⟨hqp, hqprime⟩)
    · exact ⟨Nat.le_refl _, hp⟩
    · exact ⟨by omega, hqprime⟩

theorem primeCounting_pred_prime {p : ℕ} (hp : p.Prime) :
    Nat.primeCounting (p - 1) = Nat.primeCounting p - 1 := by
  have hnot : p ∉ Nat.primesLE (p - 1) := by
    intro hmem
    have hle := (Nat.mem_primesLE.mp hmem).1
    have hpPos := hp.pos
    omega
  have hcard := congrArg Finset.card (primesLE_prime_eq_insert_predecessor hp)
  simp only [Nat.primesLE_card_eq_primeCounting,
    Finset.card_insert_of_notMem hnot] at hcard
  omega

theorem card_semiprimePartners_eq_sub_add_one {n p : ℕ}
    (hp : p ∈ Nat.primesLE n.sqrt) :
    (semiprimePartners n p).card =
      Nat.primeCounting (n / p) - Nat.primeCounting p + 1 := by
  have hp' := Nat.mem_primesLE.mp hp
  have hppos := hp'.2.pos
  have hpdiv : p ≤ n / p :=
    (Nat.le_div_iff_mul_le hppos).mpr (Nat.le_sqrt.mp hp'.1)
  have hcount : Nat.primeCounting p ≤ Nat.primeCounting (n / p) :=
    Nat.monotone_primeCounting hpdiv
  have hcountPos : 0 < Nat.primeCounting p := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_pos.mpr
      ⟨p, Nat.mem_primesLE.mpr ⟨Nat.le_refl _, hp'.2⟩⟩
  calc
    (semiprimePartners n p).card =
        Nat.primeCounting (n / p) - Nat.primeCounting (p - 1) :=
      card_semiprimePartners hp
    _ = Nat.primeCounting (n / p) -
        (Nat.primeCounting p - 1) := by
      rw [primeCounting_pred_prime hp'.2]
    _ = Nat.primeCounting (n / p) - Nat.primeCounting p + 1 := by
      omega

/-- Exact prime-summatory formula for semiprimes, including squares. -/
theorem semiprimeCount_eq_sum_primeCounting_sub (n : ℕ) :
    semiprimeCount n =
      ∑ p ∈ Nat.primesLE n.sqrt,
        (Nat.primeCounting (n / p) - Nat.primeCounting (p - 1)) := by
  rw [semiprimeCount]
  calc
    (semiprimePairs n).card =
        ∑ p ∈ Nat.primesLE n.sqrt,
          ((semiprimePairs n).filter fun pq => pq.1 = p).card :=
      Finset.card_eq_sum_card_fiberwise (semiprimePairs_fst_mapsTo n)
    _ = ∑ p ∈ Nat.primesLE n.sqrt, (semiprimePartners n p).card := by
      apply Finset.sum_congr rfl
      intro p hp
      exact card_semiprimePairs_fiber_eq_partners hp
    _ = ∑ p ∈ Nat.primesLE n.sqrt,
        (Nat.primeCounting (n / p) - Nat.primeCounting (p - 1)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact card_semiprimePartners hp

/-- Equivalent conventional form of the summatory identity. -/
theorem semiprimeCount_eq_sum_primeCounting_sub_add_one (n : ℕ) :
    semiprimeCount n =
      ∑ p ∈ Nat.primesLE n.sqrt,
        (Nat.primeCounting (n / p) - Nat.primeCounting p + 1) := by
  rw [semiprimeCount_eq_sum_primeCounting_sub]
  apply Finset.sum_congr rfl
  intro p hp
  have h₁ := card_semiprimePartners hp
  have h₂ := card_semiprimePartners_eq_sub_add_one hp
  omega

end Erdos796
