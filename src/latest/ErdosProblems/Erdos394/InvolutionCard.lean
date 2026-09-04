import ErdosProblems.Erdos394.CyclicGap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Counting square roots of one modulo odd squarefree moduli
-/

open Nat Finset

namespace Erdos394

noncomputable local instance zmodUnitsFintype' (q : ℕ) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- Transport square roots of one across an equality of moduli. -/
noncomputable def involutionCongr {m n : ℕ} (h : m = n) :
    involutionSubgroup m ≃ involutionSubgroup n := by
  subst n
  exact Equiv.refl _

/-- Chinese remainder equivalence on unit groups. -/
noncomputable def unitsChineseRemainder {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- Chinese remainder equivalence restricted to square roots of one. -/
noncomputable def involutionChineseRemainder {m n : ℕ} (h : m.Coprime n) :
    involutionSubgroup (m * n) ≃
      involutionSubgroup m × involutionSubgroup n where
  toFun u := by
    let z := unitsChineseRemainder h u.1
    refine (⟨z.1, ?_⟩, ⟨z.2, ?_⟩)
    · have hz := congrArg (unitsChineseRemainder h) u.2
      simp only [map_pow, map_one] at hz
      exact congrArg Prod.fst hz
    · have hz := congrArg (unitsChineseRemainder h) u.2
      simp only [map_pow, map_one] at hz
      exact congrArg Prod.snd hz
  invFun z := by
    refine ⟨(unitsChineseRemainder h).symm (z.1.1, z.2.1), ?_⟩
    apply (unitsChineseRemainder h).injective
    rw [map_pow, map_one, (unitsChineseRemainder h).apply_symm_apply]
    exact Prod.ext z.1.2 z.2.2
  left_inv u := by
    apply Subtype.ext
    exact (unitsChineseRemainder h).symm_apply_apply u.1
  right_inv z := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((unitsChineseRemainder h).apply_symm_apply (z.1.1, z.2.1))
    · exact congrArg Prod.snd ((unitsChineseRemainder h).apply_symm_apply (z.1.1, z.2.1))

/-- The number of square roots of one is multiplicative on coprime moduli. -/
theorem card_involutionSubgroup_mul {m n : ℕ} (h : m.Coprime n) :
    Fintype.card (involutionSubgroup (m * n)) =
      Fintype.card (involutionSubgroup m) * Fintype.card (involutionSubgroup n) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr (involutionChineseRemainder h)

/-- Modulo one there is one square root of one. -/
theorem card_involutionSubgroup_one :
    Fintype.card (involutionSubgroup 1) = 1 := by
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨1, by simp [involutionSubgroup]⟩, fun _ ↦ Subsingleton.elim _ _⟩

/-- The distinguished square root `-1`. -/
def negOneInvolution (q : ℕ) : involutionSubgroup q :=
  ⟨(-1 : (ZMod q)ˣ), by simp [involutionSubgroup]⟩

/-- Over a prime field, every square root of one is `1` or `-1`. -/
theorem involution_eq_one_or_neg_one_of_prime {p : ℕ} (hp : p.Prime)
    (u : involutionSubgroup p) :
    u = 1 ∨ u = negOneInvolution p := by
  let : Fact p.Prime := ⟨hp⟩
  have hu : ((u.1 : (ZMod p)ˣ) : ZMod p) ^ 2 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun z : (ZMod p)ˣ ↦ (z : ZMod p)) u.2
  rcases (sq_eq_one_iff.mp hu) with h | h
  · left
    apply Subtype.ext
    apply Units.ext
    exact h
  · right
    apply Subtype.ext
    apply Units.ext
    simpa [negOneInvolution] using h

/-- For an odd prime, the two roots `1` and `-1` are distinct. -/
theorem one_ne_negOneInvolution_of_prime {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : (1 : involutionSubgroup p) ≠ negOneInvolution p := by
  intro heq
  have hone : (1 : ZMod p) = -1 := by
    have h := congrArg (fun u : involutionSubgroup p ↦ ((u.1 : (ZMod p)ˣ) : ZMod p)) heq
    simpa [negOneInvolution] using h
  have htwo : (2 : ZMod p) = 0 := by
    calc
      (2 : ZMod p) = 1 + 1 := by norm_num
      _ = -1 + 1 := congrArg (fun z : ZMod p ↦ z + 1) hone
      _ = 0 := by ring
  have hpd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwo
  rcases (Nat.dvd_prime Nat.prime_two).mp hpd with hp1 | hp2eq
  · exact hp.ne_one hp1
  · exact hp2 hp2eq

/-- An odd prime modulus has exactly two square roots of one. -/
theorem card_involutionSubgroup_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Fintype.card (involutionSubgroup p) = 2 := by
  let oneRoot : involutionSubgroup p := 1
  let negRoot : involutionSubgroup p := negOneInvolution p
  have huniv : (Finset.univ : Finset (involutionSubgroup p)) =
      {oneRoot, negRoot} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    simpa [oneRoot, negRoot] using involution_eq_one_or_neg_one_of_prime hp u
  rw [← Finset.card_univ, huniv]
  exact Finset.card_pair_eq_two_iff.mpr <| by
    simpa [oneRoot, negRoot] using one_ne_negOneInvolution_of_prime hp hp2

/-- Instance-independent cardinal form of CRT multiplicativity. -/
theorem natCard_involutionSubgroup_mul {m n : ℕ} (h : m.Coprime n) :
    Nat.card (involutionSubgroup (m * n)) =
      Nat.card (involutionSubgroup m) * Nat.card (involutionSubgroup n) := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (involutionChineseRemainder h)

/-- Instance-independent cardinality at an odd prime. -/
theorem natCard_involutionSubgroup_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (involutionSubgroup p) = 2 := by
  rw [Nat.card_eq_fintype_card]
  exact card_involutionSubgroup_prime hp hp2

/-- A product of distinct odd primes has two independent choices of square
root of one at every prime. -/
theorem natCard_involutionSubgroup_prod_primes (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≠ 2) :
    Nat.card (involutionSubgroup (∏ p ∈ s, p)) = 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hprod : (∏ p ∈ (∅ : Finset ℕ), p) = 1 := by simp
      calc
        Nat.card (involutionSubgroup (∏ p ∈ (∅ : Finset ℕ), p)) =
            Nat.card (involutionSubgroup 1) := Nat.card_congr (involutionCongr hprod)
        _ = 1 := Nat.card_unique
        _ = 2 ^ (∅ : Finset ℕ).card := by simp
  | @insert p s hps ih =>
      have hp : p.Prime ∧ p ≠ 2 := hs p (Finset.mem_insert_self p s)
      have hs' : ∀ r ∈ s, r.Prime ∧ r ≠ 2 := by
        intro r hr
        exact hs r (Finset.mem_insert_of_mem hr)
      have hcop : p.Coprime (∏ r ∈ s, r) := by
        apply Nat.Coprime.prod_right
        intro r hr
        rw [hp.1.coprime_iff_not_dvd]
        intro hpr
        rcases (Nat.dvd_prime (hs' r hr).1).mp hpr with hp1 | hpeq
        · exact hp.1.ne_one hp1
        · apply hps
          simpa [hpeq] using hr
      have hprod : (∏ r ∈ insert p s, r) = p * ∏ r ∈ s, r :=
        Finset.prod_insert hps
      calc
        Nat.card (involutionSubgroup (∏ r ∈ insert p s, r)) =
            Nat.card (involutionSubgroup (p * ∏ r ∈ s, r)) :=
              Nat.card_congr (involutionCongr hprod)
        _ = Nat.card (involutionSubgroup p) *
              Nat.card (involutionSubgroup (∏ r ∈ s, r)) :=
                natCard_involutionSubgroup_mul hcop
        _ = 2 * 2 ^ s.card := by rw [natCard_involutionSubgroup_prime hp.1 hp.2, ih hs']
        _ = 2 ^ (insert p s).card := by simp [hps, pow_succ, Nat.mul_comm]

/-- For every odd squarefree modulus `q`, the subgroup of square roots of one
has cardinality `2^(number of prime factors of q)`. -/
theorem card_involutionSubgroup_odd_squarefree {q : ℕ}
    (hsq : Squarefree q) (hodd : Odd q) :
    Fintype.card (involutionSubgroup q) = 2 ^ q.primeFactors.card := by
  rw [← Nat.card_eq_fintype_card]
  calc
    Nat.card (involutionSubgroup q) =
        Nat.card (involutionSubgroup (∏ p ∈ q.primeFactors, p)) :=
          Nat.card_congr (involutionCongr (Nat.prod_primeFactors_of_squarefree hsq).symm)
    _ = 2 ^ q.primeFactors.card := by
      apply natCard_involutionSubgroup_prod_primes
      intro p hpq
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpq
      refine ⟨hp, ?_⟩
      intro hp2
      apply hodd.not_two_dvd_nat
      exact hp2 ▸ Nat.dvd_of_mem_primeFactors hpq

/-- Exact coset-gap total for an odd squarefree modulus, now with the subgroup
cardinality evaluated explicitly. -/
theorem odd_squarefree_involution_coset_gap_identity {q : ℕ}
    (hsq : Squarefree q) (hodd : Odd q) :
    2 ^ q.primeFactors.card *
        (∑ a : (ZMod q)ˣ,
          abstractCosetGap q (unitResidue q) (involutionSubgroup q) a) =
      q * q.totient := by
  rw [← card_involutionSubgroup_odd_squarefree hsq hodd]
  exact involution_coset_gap_identity q hodd.pos

end Erdos394
