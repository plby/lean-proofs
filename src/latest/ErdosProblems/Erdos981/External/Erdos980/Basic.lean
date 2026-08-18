import Mathlib

/-!
# Erdős Problem 980: the least `k`-th-power nonresidue

This file fixes the total normalization used in the problem and proves the
elementary facts about the least nonresidue.  When `p` is not a prime congruent
to `1` modulo `k` (or when `k < 2`) the value is defined to be zero.
-/

namespace Erdos980

open scoped Classical

/-- The primes for which the `k`-th-power map on nonzero residues need not be
surjective, in the normalization used by Elliott. -/
def Eligible (k p : ℕ) : Prop := p.Prime ∧ p ≡ 1 [MOD k]

/-- A natural number represents a nonzero `k`-th-power nonresidue modulo `p`.

The `IsUnit` condition makes the definition meaningful for every modulus.  At
a prime modulus it is equivalent to saying that the residue is nonzero. -/
def IsKthPowerNonresidue (k p a : ℕ) : Prop :=
  IsUnit (a : ZMod p) ∧ ¬ ∃ b : ZMod p, b ^ k = (a : ZMod p)

theorem eligible_prime {k p : ℕ} (h : Eligible k p) : p.Prime := h.1

theorem eligible_modEq {k p : ℕ} (h : Eligible k p) : p ≡ 1 [MOD k] := h.2

theorem dvd_prime_sub_one_of_eligible {k p : ℕ} (h : Eligible k p) :
    k ∣ p - 1 := by
  exact h.2.symm.dvd'

/-- In a finite cyclic commutative group, the `k`-th-power map is not
surjective when `k` is a nontrivial divisor of the group order. -/
theorem exists_not_mem_powMonoidHom_range
    (G : Type*) [CommGroup G] [Finite G] [IsCyclic G]
    {k : ℕ} (hk : 2 ≤ k) (hdiv : k ∣ Nat.card G) :
    ∃ u : G, u ∉ (powMonoidHom k : G →* G).range := by
  have hgcd : (Nat.card G).gcd k = k := Nat.gcd_eq_right_iff_dvd.mpr hdiv
  have hindex : (powMonoidHom k : G →* G).range.index = k := by
    rw [IsCyclic.index_powMonoidHom_range, hgcd]
  have hne : (powMonoidHom k : G →* G).range ≠ ⊤ := by
    intro htop
    have hone : (powMonoidHom k : G →* G).range.index = 1 :=
      Subgroup.index_eq_one.mpr htop
    omega
  exact SetLike.exists_not_mem_of_ne_top _ hne

/-- An eligible prime has a nonzero `k`-th-power nonresidue represented by a
natural number smaller than the modulus. -/
theorem exists_kthPowerNonresidue_lt {k p : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) :
    ∃ a : ℕ, a < p ∧ IsKthPowerNonresidue k p a := by
  letI : Fact p.Prime := ⟨hp.1⟩
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp.1
  have hdiv : k ∣ Nat.card (ZMod p)ˣ := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
    exact dvd_prime_sub_one_of_eligible hp
  obtain ⟨u, hu⟩ := exists_not_mem_powMonoidHom_range (ZMod p)ˣ hk hdiv
  refine ⟨(u : ZMod p).val, ZMod.val_lt (u : ZMod p), ?_⟩
  have hcast : ((u : ZMod p).val : ZMod p) = (u : ZMod p) :=
    ZMod.natCast_zmod_val (u : ZMod p)
  refine ⟨?_, ?_⟩
  · rw [hcast]
    exact u.isUnit
  · rintro ⟨b, hb⟩
    have hbunit : IsUnit b := by
      rw [← isUnit_pow_iff (show k ≠ 0 by omega), hb, hcast]
      exact u.isUnit
    let v : (ZMod p)ˣ := hbunit.unit
    apply hu
    refine ⟨v, ?_⟩
    apply Units.ext
    simpa [v, IsUnit.unit_spec, hcast] using hb

/-- An eligible prime has a nonzero `k`-th-power nonresidue. -/
theorem exists_kthPowerNonresidue {k p : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) : ∃ a : ℕ, IsKthPowerNonresidue k p a := by
  obtain ⟨a, _, ha⟩ := exists_kthPowerNonresidue_lt hk hp
  exact ⟨a, ha⟩

/-- Elliott's total normalization of the least `k`-th-power nonresidue. -/
noncomputable def leastKthPowerNonresidue (k p : ℕ) : ℕ :=
  if h : 2 ≤ k ∧ Eligible k p then
    Nat.find (exists_kthPowerNonresidue h.1 h.2)
  else 0

theorem leastKthPowerNonresidue_eq_zero_of_not_eligible {k p : ℕ}
    (h : ¬ (2 ≤ k ∧ Eligible k p)) :
    leastKthPowerNonresidue k p = 0 := by
  simp [leastKthPowerNonresidue, h]

theorem leastKthPowerNonresidue_spec {k p : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) :
    IsKthPowerNonresidue k p (leastKthPowerNonresidue k p) := by
  rw [leastKthPowerNonresidue, dif_pos ⟨hk, hp⟩]
  exact Nat.find_spec (exists_kthPowerNonresidue hk hp)

theorem leastKthPowerNonresidue_minimal {k p a : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) (ha : IsKthPowerNonresidue k p a) :
    leastKthPowerNonresidue k p ≤ a := by
  rw [leastKthPowerNonresidue, dif_pos ⟨hk, hp⟩]
  exact Nat.find_min' (exists_kthPowerNonresidue hk hp) ha

theorem leastKthPowerNonresidue_lt {k p : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) : leastKthPowerNonresidue k p < p := by
  obtain ⟨a, hap, ha⟩ := exists_kthPowerNonresidue_lt hk hp
  exact (leastKthPowerNonresidue_minimal hk hp ha).trans_lt hap

theorem leastKthPowerNonresidue_lt_modulus {k p : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) : leastKthPowerNonresidue k p < p :=
  leastKthPowerNonresidue_lt hk hp

theorem zero_not_kthPowerNonresidue (k : ℕ) {p : ℕ} (hp : p.Prime) :
    ¬ IsKthPowerNonresidue k p 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp [IsKthPowerNonresidue]

theorem leastKthPowerNonresidue_pos {k p : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) : 0 < leastKthPowerNonresidue k p := by
  exact Nat.pos_of_ne_zero fun hzero ↦
    zero_not_kthPowerNonresidue k hp.1 <|
      hzero ▸ leastKthPowerNonresidue_spec hk hp

theorem leastKthPowerNonresidue_eq_zero_iff (k p : ℕ) :
    leastKthPowerNonresidue k p = 0 ↔ ¬ (2 ≤ k ∧ Eligible k p) := by
  constructor
  · intro hzero helig
    have hpos := leastKthPowerNonresidue_pos helig.1 helig.2
    omega
  · exact leastKthPowerNonresidue_eq_zero_of_not_eligible

theorem not_kthPowerNonresidue_of_lt_least {k p a : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) (ha : a < leastKthPowerNonresidue k p) :
    ¬ IsKthPowerNonresidue k p a := by
  intro hnon
  exact (leastKthPowerNonresidue_minimal hk hp hnon).not_gt ha

theorem one_not_kthPowerNonresidue (k p : ℕ) :
    ¬ IsKthPowerNonresidue k p 1 := by
  rintro ⟨_, hnot⟩
  apply hnot
  exact ⟨1, by simp⟩

/-- A root in `ZMod p` is the same thing as an ordinary natural-number
congruence.  This bridge is useful when applying elementary factorization. -/
theorem exists_zmod_pow_eq_iff_exists_modEq {k p a : ℕ} (hp : p.Prime) :
    (∃ b : ZMod p, b ^ k = (a : ZMod p)) ↔
      ∃ b : ℕ, b ^ k ≡ a [MOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.val, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, ZMod.natCast_zmod_val]
    exact hb
  · rintro ⟨b, hb⟩
    refine ⟨(b : ZMod p), ?_⟩
    simpa only [Nat.cast_pow] using
      (ZMod.natCast_eq_natCast_iff (b ^ k) a p).mpr hb

/-- A minimal failure of a multiplicatively closed predicate is prime. -/
theorem prime_of_minimal_failure_of_mul_closed
    {good : ℕ → Prop} {n : ℕ}
    (hn : 2 ≤ n)
    (hbad : ¬ good n)
    (hminimal : ∀ m < n, good m)
    (hmul : ∀ a b, good a → good b → good (a * b)) :
    n.Prime := by
  by_contra hnotPrime
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (Nat.not_prime_iff_exists_mul_eq hn).mp hnotPrime
  apply hbad
  rw [← hab]
  exact hmul a b (hminimal a ha) (hminimal b hb)

theorem exists_pow_modEq_mul_closed (k p a b : ℕ)
    (ha : ∃ x : ℕ, x ^ k ≡ a [MOD p])
    (hb : ∃ y : ℕ, y ^ k ≡ b [MOD p]) :
    ∃ z : ℕ, z ^ k ≡ a * b [MOD p] := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x * y, ?_⟩
  simpa only [mul_pow] using hx.mul hy

/-- The least nonresidue in the total normalization is a rational prime at
every eligible modulus. -/
theorem leastKthPowerNonresidue_prime {k p : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) :
    (leastKthPowerNonresidue k p).Prime := by
  letI : Fact p.Prime := ⟨hp.1⟩
  let n := leastKthPowerNonresidue k p
  have hspec : IsKthPowerNonresidue k p n := leastKthPowerNonresidue_spec hk hp
  have hnpos : 0 < n := leastKthPowerNonresidue_pos hk hp
  have hn_ne_one : n ≠ 1 := by
    intro hn
    exact one_not_kthPowerNonresidue k p (hn ▸ hspec)
  have hn : 2 ≤ n := by omega
  apply prime_of_minimal_failure_of_mul_closed
    (good := fun a ↦ ∃ x : ℕ, x ^ k ≡ a [MOD p]) hn
  · intro hpow
    exact hspec.2 <| (exists_zmod_pow_eq_iff_exists_modEq hp.1).mpr hpow
  · intro m hm
    apply (exists_zmod_pow_eq_iff_exists_modEq hp.1).mp
    by_cases hunit : IsUnit (m : ZMod p)
    · by_contra hpow
      exact not_kthPowerNonresidue_of_lt_least hk hp hm ⟨hunit, hpow⟩
    · have hmzero : (m : ZMod p) = 0 := by
        exact not_ne_iff.mp ((isUnit_iff_ne_zero.not).mp hunit)
      exact ⟨0, by simp [hmzero, show k ≠ 0 by omega]⟩
  · exact exists_pow_modEq_mul_closed k p

end Erdos980
