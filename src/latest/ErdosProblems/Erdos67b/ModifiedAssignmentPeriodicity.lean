import ErdosProblems.Erdos67b.BCCDecomposition

/-!
# Periodicity of a modified character on good residue classes

An assignment which agrees with a Dirichlet character away from its
conductor is not periodic on all natural numbers: its values at conductor
primes are arbitrary.  It is, however, periodic modulo `q ^ k` after one
excludes integers divisible by `p ^ k` for a conductor prime `p`.  This is
the precise pointwise statement needed when the Section 4 weighted sum is
grouped by residue classes.
-/

namespace Erdos67b

noncomputable section

/-- A scaled character of level `q * d` is periodic modulo `q ^ k` whenever
`d ∣ q ^ (k-1)`. -/
theorem naturalScaledCharacter_eq_of_modEq_pow
    {q k d x y : ℕ} [NeZero q] (hk : 0 < k)
    (chi : DirichletCharacter ℂ q) (hd : d ∣ q ^ (k - 1))
    (hxy : x ≡ y [MOD q ^ k]) :
    naturalScaledCharacter chi d x = naturalScaledCharacter chi d y := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hpow : q * q ^ (k - 1) = q ^ k := by
    calc
      q * q ^ (k - 1) = q ^ (k - 1) * q := Nat.mul_comm _ _
      _ = q ^ ((k - 1) + 1) := (pow_succ q (k - 1)).symm
      _ = q ^ k := by congr 1; omega
  have hdqk : d ∣ q ^ k := hd.trans (by
    rw [← hpow]
    exact dvd_mul_left _ _)
  have hdxy : x ≡ y [MOD d] := hxy.of_dvd hdqk
  have hdvd_iff : d ∣ x ↔ d ∣ y := by
    constructor
    · intro hdx
      rw [Nat.dvd_iff_mod_eq_zero, ← hdxy]
      exact Nat.mod_eq_zero_of_dvd hdx
    · intro hdy
      rw [Nat.dvd_iff_mod_eq_zero, hdxy]
      exact Nat.mod_eq_zero_of_dvd hdy
  by_cases hdx : d ∣ x
  · have hdy : d ∣ y := hdvd_iff.mp hdx
    rw [naturalScaledCharacter_of_dvd chi hdx,
      naturalScaledCharacter_of_dvd chi hdy]
    have hd0 : d ≠ 0 := by
      intro hdzero
      subst d
      have hz : q ^ (k - 1) = 0 := by simpa using hd
      exact (pow_ne_zero (k - 1) hq0) hz
    have hdq : d * q ∣ q ^ k := by
      obtain ⟨c, hc⟩ := hd
      refine ⟨c, ?_⟩
      rw [← hpow, hc]
      ring
    have hmul : d * (x / d) ≡ d * (y / d) [MOD d * q] := by
      simpa only [Nat.mul_div_cancel' hdx, Nat.mul_div_cancel' hdy] using
        hxy.of_dvd hdq
    have hquot : x / d ≡ y / d [MOD q] :=
      (Nat.ModEq.mul_left_cancel_iff' hd0).1 hmul
    exact congrArg chi
      ((ZMod.natCast_eq_natCast_iff (x / d) (y / d) q).2 hquot)
  · have hdy : ¬d ∣ y := not_congr hdvd_iff |>.mp hdx
    rw [naturalScaledCharacter_of_not_dvd chi hdx,
      naturalScaledCharacter_of_not_dvd chi hdy]

/-- On the prime-power-avoiding locus, a modified assignment agreeing with
`chi` away from `q` is genuinely periodic modulo `q ^ k`. -/
theorem primeExtension_eq_of_modEq_pow_of_avoids
    (z : PrimeAssignment) {q k x y : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hagree : AgreesWithCharacterAway z chi)
    (hk : 0 < k) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : AvoidsConductorPrimePowers q k x)
    (hy : AvoidsConductorPrimePowers q k y)
    (hxy : x ≡ y [MOD q ^ k]) :
    (primeExtension z x : ℂ) = (primeExtension z y : ℂ) := by
  rw [primeExtension_eq_sum_scaledCharacter_of_avoids z chi hagree hx0 hx,
    primeExtension_eq_sum_scaledCharacter_of_avoids z chi hagree hy0 hy]
  apply Finset.sum_congr rfl
  intro d hd
  rw [naturalScaledCharacter_eq_of_modEq_pow hk chi
    (Nat.dvd_of_mem_divisors hd) hxy]

/-- Concrete good-class form: every positive natural representative of the
shifted class has the same modified-character value as its canonical `ZMod`
representative. -/
theorem primeExtension_eq_shiftVal_of_mem_cyclicGoodResidues
    (z : PrimeAssignment) {q k H : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hagree : AgreesWithCharacterAway z chi)
    (hq : 1 < q) (hk : 0 < k) {a : ZMod (q ^ k)}
    (ha : a ∈ cyclicGoodResidues q k H)
    {m : ℕ} (hm : m ∈ Finset.Icc 1 (2 * H))
    {x : ℕ} (hx0 : x ≠ 0)
    (hx : (x : ZMod (q ^ k)) = a + (m : ZMod (q ^ k))) :
    (primeExtension z x : ℂ) =
      (primeExtension z (a + (m : ZMod (q ^ k))).val : ℂ) := by
  let y := (a + (m : ZMod (q ^ k))).val
  have hyAvoid : AvoidsConductorPrimePowers q k y :=
    avoids_of_mem_cyclicGoodResidues ha hm
  have hy0 : y ≠ 0 := by
    intro hyzero
    have hp : q.minFac.Prime := Nat.minFac_prime hq.ne'
    have hpq : q.minFac ∈ q.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd q, NeZero.ne q⟩
    exact (hyAvoid q.minFac hpq) (by simp [y, hyzero])
  have hxy : x ≡ y [MOD q ^ k] := by
    apply (ZMod.natCast_eq_natCast_iff x y (q ^ k)).1
    simpa only [y, ZMod.natCast_zmod_val] using hx
  have hxAvoid : AvoidsConductorPrimePowers q k x := by
    intro p hp hpx
    have hpkqk : p ^ k ∣ q ^ k :=
      pow_dvd_pow_of_dvd (Nat.dvd_of_mem_primeFactors hp) k
    have hpmod : x ≡ y [MOD p ^ k] := hxy.of_dvd hpkqk
    apply hyAvoid p hp
    rw [Nat.dvd_iff_mod_eq_zero, ← hpmod]
    exact Nat.mod_eq_zero_of_dvd hpx
  exact primeExtension_eq_of_modEq_pow_of_avoids z chi hagree hk
    hx0 hy0 hxAvoid hyAvoid hxy

end

end Erdos67b
