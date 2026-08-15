import ErdosProblems.Erdos888.Foundations
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
# Erdős 888: the prime and squarefree-semiprime construction

This file supplies the elementary rigidity input for the lower bound.  The
construction consists of all primes and all products of two *distinct*
primes up to `n`.  Equivalently, these are the squarefree positive integers
having one or two prime factors.

The main point is a small incidence lemma.  Regard the prime factors of a
squarefree integer as a set of size one or two.  If the product of four such
integers is a square, every prime has even total incidence.  Four nonempty
sets of size at most two with this property have one of the three pairings
whose multisets of incidences agree.  Unique factorization gives equality of
the corresponding pair-products.  Finally, monotonicity of the sorted four
integers forces the pairing to be the outside-versus-inside pairing.
-/

namespace Erdos888

open scoped BigOperators

/-- A squarefree integer with exactly one or two distinct prime factors.
These are precisely primes and squarefree semiprimes. -/
def IsPrimeOrSquarefreeSemiprime (m : ℕ) : Prop :=
  Squarefree m ∧ (m.primeFactors.card = 1 ∨ m.primeFactors.card = 2)

/-- The factor-support definition is exactly the advertised union of the
primes and products of two distinct primes. -/
theorem isPrimeOrSquarefreeSemiprime_iff {m : ℕ} :
    IsPrimeOrSquarefreeSemiprime m ↔
      m.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ m = p * q := by
  constructor
  · intro hm
    rcases hm.2 with hcard | hcard
    · obtain ⟨p, hpFactors⟩ := Finset.card_eq_one.mp hcard
      have hpMem : p ∈ m.primeFactors := by simp [hpFactors]
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
      left
      have heq : p = m := by
        rw [← Nat.prod_primeFactors_of_squarefree hm.1, hpFactors]
        simp
      simpa [← heq] using hp
    · obtain ⟨p, q, hpq, hpFactors⟩ := Finset.card_eq_two.mp hcard
      have hpMem : p ∈ m.primeFactors := by simp [hpFactors]
      have hqMem : q ∈ m.primeFactors := by simp [hpFactors]
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
      have hq : q.Prime := Nat.prime_of_mem_primeFactors hqMem
      have hmprod : m = p * q := by
        rw [← Nat.prod_primeFactors_of_squarefree hm.1, hpFactors]
        simp [hpq]
      rcases lt_or_gt_of_ne hpq with hpqlt | hqplt
      · exact Or.inr ⟨p, q, hp, hq, hpqlt, hmprod⟩
      · exact Or.inr ⟨q, p, hq, hp, hqplt, by simpa [Nat.mul_comm] using hmprod⟩
  · rintro (hm | ⟨p, q, hp, hq, hpq, rfl⟩)
    · refine ⟨hm.squarefree, Or.inl ?_⟩
      simp [hm]
    · have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq.ne
      refine ⟨(Nat.squarefree_mul hcop).2 ⟨hp.squarefree, hq.squarefree⟩, Or.inr ?_⟩
      rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero]
      simp [hp, hq, hpq.ne]

/-- The prime-plus-squarefree-semiprime construction, truncated at `n`. -/
noncomputable def lowerBoundSet (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 0 n).filter IsPrimeOrSquarefreeSemiprime

@[simp] theorem mem_lowerBoundSet {n m : ℕ} :
    m ∈ lowerBoundSet n ↔
      0 < m ∧ m ≤ n ∧ IsPrimeOrSquarefreeSemiprime m := by
  classical
  simp [lowerBoundSet, and_assoc]

private theorem support_nonempty_of_card_pos {f : α →₀ ℕ}
    (h : 0 < f.support.card) : ∃ x, 0 < f x := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  exact ⟨x, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)⟩

private theorem no_three_of_support_card_le_two {f : α →₀ ℕ}
    (hcard : f.support.card ≤ 2) {x y z : α}
    (hx : 0 < f x) (hy : 0 < f y) (hz : 0 < f z) :
    x = y ∨ x = z ∨ y = z := by
  classical
  by_contra h
  push Not at h
  have hmemx : x ∈ f.support := Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hx)
  have hmemy : y ∈ f.support := Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hy)
  have hmemz : z ∈ f.support := Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hz)
  have hsub : ({x, y, z} : Finset α) ⊆ f.support := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact hmemx
    · exact hmemy
    · exact hmemz
  have hthree : ({x, y, z} : Finset α).card = 3 := by
    simp [h.1, h.2.1, h.2.2]
  have := Finset.card_le_card hsub
  omega

/-- The combinatorial core of the construction.  A binary vector of support
size one or two is an edge (a singleton is allowed).  If four such edges
have even total degree at every vertex, then one of the three pairings has
the same integer incidence vector on both sides. -/
private theorem four_small_binary_vectors_pair
    {f₁ f₂ f₃ f₄ : α →₀ ℕ}
    (hbin₁ : ∀ x, f₁ x ≤ 1) (hbin₂ : ∀ x, f₂ x ≤ 1)
    (hbin₃ : ∀ x, f₃ x ≤ 1) (hbin₄ : ∀ x, f₄ x ≤ 1)
    (hnon₁ : ∃ x, 0 < f₁ x) (hnon₂ : ∃ x, 0 < f₂ x)
    (hnon₃ : ∃ x, 0 < f₃ x) (hnon₄ : ∃ x, 0 < f₄ x)
    (hsmall₁ : ∀ {x y z}, 0 < f₁ x → 0 < f₁ y → 0 < f₁ z →
      x = y ∨ x = z ∨ y = z)
    (hsmall₂ : ∀ {x y z}, 0 < f₂ x → 0 < f₂ y → 0 < f₂ z →
      x = y ∨ x = z ∨ y = z)
    (hsmall₃ : ∀ {x y z}, 0 < f₃ x → 0 < f₃ y → 0 < f₃ z →
      x = y ∨ x = z ∨ y = z)
    (hsmall₄ : ∀ {x y z}, 0 < f₄ x → 0 < f₄ y → 0 < f₄ z →
      x = y ∨ x = z ∨ y = z)
    (heven : ∀ x, Even (f₁ x + f₂ x + f₃ x + f₄ x)) :
    (∀ x, f₁ x + f₂ x = f₃ x + f₄ x) ∨
      (∀ x, f₁ x + f₃ x = f₂ x + f₄ x) ∨
      (∀ x, f₁ x + f₄ x = f₂ x + f₃ x) := by
  by_contra hpair
  push Not at hpair
  obtain ⟨x, hx⟩ := hpair.1
  obtain ⟨y, hy⟩ := hpair.2.1
  obtain ⟨z, hz⟩ := hpair.2.2
  have pattern_x :
      (f₁ x = 1 ∧ f₂ x = 1 ∧ f₃ x = 0 ∧ f₄ x = 0) ∨
      (f₁ x = 0 ∧ f₂ x = 0 ∧ f₃ x = 1 ∧ f₄ x = 1) := by
    obtain ⟨k, hk⟩ := heven x
    have h₁ := hbin₁ x
    have h₂ := hbin₂ x
    have h₃ := hbin₃ x
    have h₄ := hbin₄ x
    omega
  have pattern_y :
      (f₁ y = 1 ∧ f₃ y = 1 ∧ f₂ y = 0 ∧ f₄ y = 0) ∨
      (f₁ y = 0 ∧ f₃ y = 0 ∧ f₂ y = 1 ∧ f₄ y = 1) := by
    obtain ⟨k, hk⟩ := heven y
    have h₁ := hbin₁ y
    have h₂ := hbin₂ y
    have h₃ := hbin₃ y
    have h₄ := hbin₄ y
    omega
  have pattern_z :
      (f₁ z = 1 ∧ f₄ z = 1 ∧ f₂ z = 0 ∧ f₃ z = 0) ∨
      (f₁ z = 0 ∧ f₄ z = 0 ∧ f₂ z = 1 ∧ f₃ z = 1) := by
    obtain ⟨k, hk⟩ := heven z
    have h₁ := hbin₁ z
    have h₂ := hbin₂ z
    have h₃ := hbin₃ z
    have h₄ := hbin₄ z
    omega
  /- A star among the three selected matching edges puts three distinct
  vertices in one support.  A triangle fills three supports with two
  vertices each; nonemptiness of the fourth support then overfills one of
  the first three.  The eight branches below are exactly these cases. -/
  rcases pattern_x with hxP | hxP <;>
    rcases pattern_y with hyP | hyP <;>
      rcases pattern_z with hzP | hzP
  · -- star at `f₁`
    have hxy : x ≠ y := by intro h; subst y; omega
    have hxz : x ≠ z := by intro h; subst z; omega
    have hyz : y ≠ z := by intro h; subst z; omega
    rcases hsmall₁ (x := x) (y := y) (z := z) (by omega) (by omega) (by omega) with h | h | h
    all_goals contradiction
  · -- triangle on `f₁,f₂,f₃`; `f₄` is the missing support
    obtain ⟨w, hw⟩ := hnon₄
    have hw₄ : f₄ w = 1 := by have := hbin₄ w; omega
    obtain hw₁ | hw₂ | hw₃ : 0 < f₁ w ∨ 0 < f₂ w ∨ 0 < f₃ w := by
      obtain ⟨k, hk⟩ := heven w
      have h₁ := hbin₁ w
      have h₂ := hbin₂ w
      have h₃ := hbin₃ w
      omega
    · have hxy : x ≠ y := by intro h; subst y; omega
      have hxw : x ≠ w := by intro h; subst w; omega
      have hyw : y ≠ w := by intro h; subst w; omega
      rcases hsmall₁ (x := x) (y := y) (z := w) (by omega) (by omega) hw₁ with h | h | h
      all_goals contradiction
    · have hxz : x ≠ z := by intro h; subst z; omega
      have hxw : x ≠ w := by intro h; subst w; omega
      have hzw : z ≠ w := by intro h; subst w; omega
      rcases hsmall₂ (x := x) (y := z) (z := w) (by omega) (by omega) hw₂ with h | h | h
      all_goals contradiction
    · have hyz : y ≠ z := by intro h; subst z; omega
      have hyw : y ≠ w := by intro h; subst w; omega
      have hzw : z ≠ w := by intro h; subst w; omega
      rcases hsmall₃ (x := y) (y := z) (z := w) (by omega) (by omega) hw₃ with h | h | h
      all_goals contradiction
  · -- triangle on `f₁,f₂,f₄`; `f₃` is missing
    obtain ⟨w, hw⟩ := hnon₃
    have hw₃ : f₃ w = 1 := by have := hbin₃ w; omega
    obtain hw₁ | hw₂ | hw₄ : 0 < f₁ w ∨ 0 < f₂ w ∨ 0 < f₄ w := by
      obtain ⟨k, hk⟩ := heven w
      have h₁ := hbin₁ w
      have h₂ := hbin₂ w
      have h₄ := hbin₄ w
      omega
    · have hxz : x ≠ z := by intro h; subst z; omega
      have hxw : x ≠ w := by intro h; subst w; omega
      have hzw : z ≠ w := by intro h; subst w; omega
      rcases hsmall₁ (x := x) (y := z) (z := w) (by omega) (by omega) hw₁ with h | h | h
      all_goals contradiction
    · have hxy : x ≠ y := by intro h; subst y; omega
      have hxw : x ≠ w := by intro h; subst w; omega
      have hyw : y ≠ w := by intro h; subst w; omega
      rcases hsmall₂ (x := x) (y := y) (z := w) (by omega) (by omega) hw₂ with h | h | h
      all_goals contradiction
    · have hyz : y ≠ z := by intro h; subst z; omega
      have hyw : y ≠ w := by intro h; subst w; omega
      have hzw : z ≠ w := by intro h; subst w; omega
      rcases hsmall₄ (x := y) (y := z) (z := w) (by omega) (by omega) hw₄ with h | h | h
      all_goals contradiction
  · -- star at `f₂`
    have hxy : x ≠ y := by intro h; subst y; omega
    have hxz : x ≠ z := by intro h; subst z; omega
    have hyz : y ≠ z := by intro h; subst z; omega
    rcases hsmall₂ (x := x) (y := y) (z := z) (by omega) (by omega) (by omega) with h | h | h
    all_goals contradiction
  · -- triangle on `f₁,f₃,f₄`; `f₂` is missing
    obtain ⟨w, hw⟩ := hnon₂
    have hw₂ : f₂ w = 1 := by have := hbin₂ w; omega
    obtain hw₁ | hw₃ | hw₄ : 0 < f₁ w ∨ 0 < f₃ w ∨ 0 < f₄ w := by
      obtain ⟨k, hk⟩ := heven w
      have h₁ := hbin₁ w
      have h₃ := hbin₃ w
      have h₄ := hbin₄ w
      omega
    · have hyz : y ≠ z := by intro h; subst z; omega
      have hyw : y ≠ w := by intro h; subst w; omega
      have hzw : z ≠ w := by intro h; subst w; omega
      rcases hsmall₁ (x := y) (y := z) (z := w) (by omega) (by omega) hw₁ with h | h | h
      all_goals contradiction
    · have hxy : x ≠ y := by intro h; subst y; omega
      have hxw : x ≠ w := by intro h; subst w; omega
      have hyw : y ≠ w := by intro h; subst w; omega
      rcases hsmall₃ (x := x) (y := y) (z := w) (by omega) (by omega) hw₃ with h | h | h
      all_goals contradiction
    · have hxz : x ≠ z := by intro h; subst z; omega
      have hxw : x ≠ w := by intro h; subst w; omega
      have hzw : z ≠ w := by intro h; subst w; omega
      rcases hsmall₄ (x := x) (y := z) (z := w) (by omega) (by omega) hw₄ with h | h | h
      all_goals contradiction
  · -- star at `f₃`
    have hxy : x ≠ y := by intro h; subst y; omega
    have hxz : x ≠ z := by intro h; subst z; omega
    have hyz : y ≠ z := by intro h; subst z; omega
    rcases hsmall₃ (x := x) (y := y) (z := z) (by omega) (by omega) (by omega) with h | h | h
    all_goals contradiction
  · -- star at `f₄`
    have hxy : x ≠ y := by intro h; subst y; omega
    have hxz : x ≠ z := by intro h; subst z; omega
    have hyz : y ≠ z := by intro h; subst z; omega
    rcases hsmall₄ (x := x) (y := y) (z := z) (by omega) (by omega) (by omega) with h | h | h
    all_goals contradiction
  · -- triangle on `f₂,f₃,f₄`; `f₁` is missing
    obtain ⟨w, hw⟩ := hnon₁
    have hw₁ : f₁ w = 1 := by have := hbin₁ w; omega
    obtain hw₂ | hw₃ | hw₄ : 0 < f₂ w ∨ 0 < f₃ w ∨ 0 < f₄ w := by
      obtain ⟨k, hk⟩ := heven w
      have h₂ := hbin₂ w
      have h₃ := hbin₃ w
      have h₄ := hbin₄ w
      omega
    · have hyz : y ≠ z := by intro h; subst z; omega
      have hyw : y ≠ w := by intro h; subst w; omega
      have hzw : z ≠ w := by intro h; subst w; omega
      rcases hsmall₂ (x := y) (y := z) (z := w) (by omega) (by omega) hw₂ with h | h | h
      all_goals contradiction
    · have hxz : x ≠ z := by intro h; subst z; omega
      have hxw : x ≠ w := by intro h; subst w; omega
      have hzw : z ≠ w := by intro h; subst w; omega
      rcases hsmall₃ (x := x) (y := z) (z := w) (by omega) (by omega) hw₃ with h | h | h
      all_goals contradiction
    · have hxy : x ≠ y := by intro h; subst y; omega
      have hxw : x ≠ w := by intro h; subst w; omega
      have hyw : y ≠ w := by intro h; subst w; omega
      rcases hsmall₄ (x := x) (y := y) (z := w) (by omega) (by omega) hw₄ with h | h | h
      all_goals contradiction

/-- Four positive squarefree integers with at most two (and at least one)
prime factors each have equal pair-products in one of the three possible
pairings whenever their total product is a square. -/
theorem small_squarefree_pairing {a b c d : ℕ}
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d)
    (ha : IsPrimeOrSquarefreeSemiprime a)
    (hb : IsPrimeOrSquarefreeSemiprime b)
    (hc : IsPrimeOrSquarefreeSemiprime c)
    (hd : IsPrimeOrSquarefreeSemiprime d)
    (hsquare : IsSquare (a * b * c * d)) :
    a * b = c * d ∨ a * c = b * d ∨ a * d = b * c := by
  have ha_ne : a ≠ 0 := Nat.ne_of_gt ha0
  have hb_ne : b ≠ 0 := Nat.ne_of_gt hb0
  have hc_ne : c ≠ 0 := Nat.ne_of_gt hc0
  have hd_ne : d ≠ 0 := Nat.ne_of_gt hd0
  have hab_ne : a * b ≠ 0 := Nat.mul_ne_zero ha_ne hb_ne
  have habc_ne : a * b * c ≠ 0 := Nat.mul_ne_zero hab_ne hc_ne
  have hfac : (a * b * c * d).factorization =
      a.factorization + b.factorization + c.factorization + d.factorization := by
    rw [Nat.factorization_mul habc_ne hd_ne,
      Nat.factorization_mul hab_ne hc_ne, Nat.factorization_mul ha_ne hb_ne]
  obtain ⟨r, hr⟩ := hsquare.exists_sq
  have heven : ∀ p, Even
      (a.factorization p + b.factorization p +
        c.factorization p + d.factorization p) := by
    intro p
    refine ⟨r.factorization p, ?_⟩
    have hp := congrArg (fun f : ℕ →₀ ℕ => f p)
      (hfac.symm.trans (hr ▸ Nat.factorization_pow r 2))
    simpa [add_assoc, two_mul] using hp
  have hcarda_pos : 0 < a.factorization.support.card := by
    rw [Nat.support_factorization]
    rcases ha.2 with h | h <;> omega
  have hcardb_pos : 0 < b.factorization.support.card := by
    rw [Nat.support_factorization]
    rcases hb.2 with h | h <;> omega
  have hcardc_pos : 0 < c.factorization.support.card := by
    rw [Nat.support_factorization]
    rcases hc.2 with h | h <;> omega
  have hcardd_pos : 0 < d.factorization.support.card := by
    rw [Nat.support_factorization]
    rcases hd.2 with h | h <;> omega
  have hcarda_le : a.factorization.support.card ≤ 2 := by
    rw [Nat.support_factorization]
    rcases ha.2 with h | h <;> omega
  have hcardb_le : b.factorization.support.card ≤ 2 := by
    rw [Nat.support_factorization]
    rcases hb.2 with h | h <;> omega
  have hcardc_le : c.factorization.support.card ≤ 2 := by
    rw [Nat.support_factorization]
    rcases hc.2 with h | h <;> omega
  have hcardd_le : d.factorization.support.card ≤ 2 := by
    rw [Nat.support_factorization]
    rcases hd.2 with h | h <;> omega
  have hpairs := four_small_binary_vectors_pair
    (f₁ := a.factorization) (f₂ := b.factorization)
    (f₃ := c.factorization) (f₄ := d.factorization)
    ha.1.natFactorization_le_one hb.1.natFactorization_le_one
    hc.1.natFactorization_le_one hd.1.natFactorization_le_one
    (support_nonempty_of_card_pos hcarda_pos)
    (support_nonempty_of_card_pos hcardb_pos)
    (support_nonempty_of_card_pos hcardc_pos)
    (support_nonempty_of_card_pos hcardd_pos)
    (fun hx hy hz => no_three_of_support_card_le_two hcarda_le hx hy hz)
    (fun hx hy hz => no_three_of_support_card_le_two hcardb_le hx hy hz)
    (fun hx hy hz => no_three_of_support_card_le_two hcardc_le hx hy hz)
    (fun hx hy hz => no_three_of_support_card_le_two hcardd_le hx hy hz)
    heven
  rcases hpairs with hpair | hpair | hpair
  · left
    apply Nat.eq_of_factorization_eq hab_ne (Nat.mul_ne_zero hc_ne hd_ne)
    intro p
    rw [Nat.factorization_mul ha_ne hb_ne, Nat.factorization_mul hc_ne hd_ne]
    exact hpair p
  · right; left
    apply Nat.eq_of_factorization_eq (Nat.mul_ne_zero ha_ne hc_ne)
      (Nat.mul_ne_zero hb_ne hd_ne)
    intro p
    rw [Nat.factorization_mul ha_ne hc_ne, Nat.factorization_mul hb_ne hd_ne]
    exact hpair p
  · right; right
    apply Nat.eq_of_factorization_eq (Nat.mul_ne_zero ha_ne hd_ne)
      (Nat.mul_ne_zero hb_ne hc_ne)
    intro p
    rw [Nat.factorization_mul ha_ne hd_ne, Nat.factorization_mul hb_ne hc_ne]
    exact hpair p

/-- Among a sorted positive quadruple, either of the two non-required
pairings can only be equal when cancellation collapses it to the required
outside-versus-inside pairing. -/
private theorem sorted_pairing_forces_outside {a b c d : ℕ}
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hpair : a * b = c * d ∨ a * c = b * d ∨ a * d = b * c) :
    a * d = b * c := by
  rcases hpair with hpair | hpair | hpair
  · have hac : a = c := by
      apply le_antisymm (hab.trans hbc)
      by_contra hnot
      have haclt : a < c := Nat.lt_of_not_ge hnot
      have hlt : a * b < c * d :=
        (Nat.mul_lt_mul_of_pos_right haclt hb0).trans_le
          (Nat.mul_le_mul_left c (hbc.trans hcd))
      omega
    subst c
    have hbd : b = d := Nat.eq_of_mul_eq_mul_left ha0 hpair
    subst d
    simp [Nat.mul_comm]
  · have hab_eq : a = b := by
      apply le_antisymm hab
      by_contra hnot
      have hablt : a < b := Nat.lt_of_not_ge hnot
      have hlt : a * c < b * d :=
        (Nat.mul_lt_mul_of_pos_right hablt hc0).trans_le
          (Nat.mul_le_mul_left b hcd)
      omega
    subst b
    have hcd_eq : c = d := Nat.eq_of_mul_eq_mul_left ha0 hpair
    subst d
    rfl
  · exact hpair

/-- The prime-plus-squarefree-semiprime construction satisfies the Erdős
888 rigidity condition. -/
theorem lowerBoundSet_requiredCondition (n : ℕ) :
    RequiredCondition (lowerBoundSet n) n := by
  refine ⟨?_, ?_⟩
  · intro m hm
    exact Finset.mem_Ioc.mpr ⟨(mem_lowerBoundSet.mp hm).1,
      (mem_lowerBoundSet.mp hm).2.1⟩
  · intro a ha_mem b hb_mem c hc_mem d hd_mem hab hbc hcd hsquare
    have ha_data := mem_lowerBoundSet.mp ha_mem
    have hb_data := mem_lowerBoundSet.mp hb_mem
    have hc_data := mem_lowerBoundSet.mp hc_mem
    have hd_data := mem_lowerBoundSet.mp hd_mem
    apply sorted_pairing_forces_outside
      ha_data.1 hb_data.1 hc_data.1 hd_data.1 hab hbc hcd
    exact small_squarefree_pairing
      ha_data.1 hb_data.1 hc_data.1 hd_data.1
      ha_data.2.2 hb_data.2.2 hc_data.2.2 hd_data.2.2 hsquare

/-- Consequently, the cardinality of `lowerBoundSet n` is attained by the
extremal predicate `p n`. -/
theorem p_lowerBoundSet (n : ℕ) : p n (lowerBoundSet n).card :=
  ⟨lowerBoundSet n, lowerBoundSet_requiredCondition n, rfl⟩

/-- The construction gives a direct finite lower bound for the extremal
cardinality. -/
theorem card_lowerBoundSet_le_extremalSize (n : ℕ) :
    (lowerBoundSet n).card ≤ extremalSize n :=
  le_extremalSize_of_p (p_lowerBoundSet n)

end Erdos888
