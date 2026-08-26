import Mathlib

/-!
# Elementary reductions for Erdős problem 1148

These results do not prove the eventual assertion. They prove the bound for
all nonnegative integers congruent to `0` or `1` modulo `4`, and reduce the
remaining assertion to an explicit family of prime candidates. All proofs
use the default computational limits.
-/

namespace Erdos1148

/-- The bounded representation sought in Erdős problem 1148. -/
def HasBoundedRepresentation (n : ℤ) : Prop :=
  ∃ x y z : ℤ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    max (x ^ 2) (max (y ^ 2) (z ^ 2)) ≤ n

lemma boundedRepresentation_of_coordinates {n s x z : ℤ}
    (hs : s ^ 2 ≤ n) (hx : 0 ≤ x) (hxs : x ≤ s)
    (hz : 0 ≤ z) (hzs : z ≤ s)
    (heq : n = x ^ 2 + s ^ 2 - z ^ 2) : HasBoundedRepresentation n := by
  refine ⟨x, s, z, heq, max_le ?_ (max_le hs ?_)⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hxs) (show 0 ≤ s + x by omega)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hzs) (show 0 ≤ s + z by omega)]

lemma boundedRepresentation_of_odd_remainder {n s : ℤ}
    (hs : s ^ 2 ≤ n) (hn : n < (s + 1) ^ 2)
    (hodd : (n - s ^ 2) % 2 = 1) : HasBoundedRepresentation n := by
  let d := n - s ^ 2
  have hd : 0 ≤ d := by dsimp [d]; omega
  have hds : d ≤ 2 * s := by dsimp [d]; nlinarith
  have hdodd : d % 2 = 1 := hodd
  have hx : 2 * ((d + 1) / 2) = d + 1 := by omega
  have hz : 2 * ((d - 1) / 2) = d - 1 := by omega
  apply boundedRepresentation_of_coordinates hs
    (x := (d + 1) / 2) (z := (d - 1) / 2) <;> try omega
  have hdrel : d = n - s ^ 2 := rfl
  nlinarith [sq_nonneg ((d + 1) / 2 - (d - 1) / 2)]

lemma boundedRepresentation_of_four_dvd_remainder {n s : ℤ}
    (hs0 : 0 ≤ s) (hs : s ^ 2 ≤ n) (hn : n < (s + 1) ^ 2)
    (hfour : (n - s ^ 2) % 4 = 0) : HasBoundedRepresentation n := by
  let d := n - s ^ 2
  have hd : 0 ≤ d := by dsimp [d]; omega
  have hds : d ≤ 2 * s := by dsimp [d]; nlinarith
  have hdfour : d % 4 = 0 := hfour
  by_cases hd0 : d = 0
  · have heq : n = s ^ 2 := by dsimp [d] at hd0; omega
    refine ⟨0, s, 0, by simpa using heq, ?_⟩
    simpa only [zero_pow (by decide : 2 ≠ 0)] using
      max_le (le_trans (sq_nonneg s) hs) (max_le hs (le_trans (sq_nonneg s) hs))
  have hdpos : 0 < d := by omega
  have hdiv : 4 * (d / 4) = d := by omega
  apply boundedRepresentation_of_coordinates hs
    (x := d / 4 + 1) (z := d / 4 - 1) <;> try omega
  have hdrel : d = n - s ^ 2 := rfl
  nlinarith

lemma int_sq_mod_four (s : ℤ) : s ^ 2 % 4 = 0 ∨ s ^ 2 % 4 = 1 := by
  have hmod : s ^ 2 % 4 = (s % 4) ^ 2 % 4 := by
    simpa only [pow_two] using Int.mul_emod s s 4
  have hs0 : 0 ≤ s % 4 := Int.emod_nonneg _ (by norm_num)
  have hs4 : s % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases h : s % 4 <;> norm_num [h] at hmod ⊢ <;> omega

lemma exists_square_interval {n : ℤ} (hn : 0 ≤ n) :
    ∃ s : ℤ, 0 ≤ s ∧ s ^ 2 ≤ n ∧ n < (s + 1) ^ 2 := by
  refine ⟨Nat.sqrt n.toNat, Int.natCast_nonneg _, ?_, ?_⟩
  · have hcast : (Nat.sqrt n.toNat : ℤ) ^ 2 ≤ (n.toNat : ℤ) := by
      exact_mod_cast Nat.sqrt_le' n.toNat
    simpa [Int.toNat_of_nonneg hn] using hcast
  · have hcast : (n.toNat : ℤ) < ((Nat.sqrt n.toNat : ℤ) + 1) ^ 2 := by
      exact_mod_cast Nat.lt_succ_sqrt' n.toNat
    simpa [Int.toNat_of_nonneg hn] using hcast

/-- The only remainder not handled by consecutive squares is `2` modulo `4`. -/
theorem boundedRepresentation_of_remainder_ne_two {n s : ℤ}
    (hs0 : 0 ≤ s) (hs : s ^ 2 ≤ n) (hnlt : n < (s + 1) ^ 2)
    (hmod : (n - s ^ 2) % 4 ≠ 2) : HasBoundedRepresentation n := by
  by_cases hodd : (n - s ^ 2) % 2 = 1
  · exact boundedRepresentation_of_odd_remainder hs hnlt hodd
  · exact boundedRepresentation_of_four_dvd_remainder hs0 hs hnlt (by omega)

/-- An elementary construction covers both discriminant residue classes. -/
theorem boundedRepresentation_of_mod_four {n : ℤ} (hn : 0 ≤ n)
    (hmod : n % 4 = 0 ∨ n % 4 = 1) : HasBoundedRepresentation n := by
  obtain ⟨s, hs0, hs, hnlt⟩ := exists_square_interval hn
  have hsq := int_sq_mod_four s
  exact boundedRepresentation_of_remainder_ne_two hs0 hs hnlt (by omega)

/-- All perfect squares are covered, with no size restriction. -/
theorem boundedRepresentation_of_isSquare {n : ℤ} (hn : IsSquare n) :
    HasBoundedRepresentation n := by
  obtain ⟨s, rfl⟩ := hn
  refine ⟨s, 0, 0, by ring, ?_⟩
  simp only [zero_pow (by decide : 2 ≠ 0), max_self, pow_two]
  exact max_le le_rfl (mul_self_nonneg s)

/-- A representation scales by any integer square. -/
theorem HasBoundedRepresentation.mul_sq {n : ℤ} (hn : HasBoundedRepresentation n)
    (k : ℤ) : HasBoundedRepresentation (n * k ^ 2) := by
  obtain ⟨x, y, z, heq, hmax⟩ := hn
  have hx := (max_le_iff.mp hmax).1
  have hy := (max_le_iff.mp (max_le_iff.mp hmax).2).1
  have hz := (max_le_iff.mp (max_le_iff.mp hmax).2).2
  refine ⟨x * k, y * k, z * k, ?_, max_le ?_ (max_le ?_ ?_)⟩
  · rw [heq]; ring
  · simpa only [mul_pow] using mul_le_mul_of_nonneg_right hx (sq_nonneg k)
  · simpa only [mul_pow] using mul_le_mul_of_nonneg_right hy (sq_nonneg k)
  · simpa only [mul_pow] using mul_le_mul_of_nonneg_right hz (sq_nonneg k)

/-- The eventual assertion is equivalent to just its two remaining residue classes. -/
theorem eventually_boundedRepresentation_iff_mod_four :
    (∃ N : ℤ, ∀ n : ℤ, N ≤ n → HasBoundedRepresentation n) ↔
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n → n % 4 = 2 ∨ n % 4 = 3 →
        HasBoundedRepresentation n := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn _ ↦ hN n hn⟩
  · rintro ⟨N, hN⟩
    refine ⟨max N 0, fun n hn ↦ ?_⟩
    by_cases hmod : n % 4 = 0 ∨ n % 4 = 1
    · exact boundedRepresentation_of_mod_four (by omega) hmod
    · exact hN n (by omega) (by omega)

/-- An exact reduction to the exceptional remainder, retaining the original threshold. -/
theorem eventually_boundedRepresentation_iff_remainder_two :
    (∃ N : ℤ, ∀ n : ℤ, N ≤ n → HasBoundedRepresentation n) ↔
      ∃ N : ℤ, ∀ s d : ℤ, 0 ≤ s → 0 ≤ d → d ≤ 2 * s → d % 4 = 2 →
        N ≤ s ^ 2 + d → HasBoundedRepresentation (s ^ 2 + d) := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun s d _ _ _ _ hn ↦ hN _ hn⟩
  · rintro ⟨N, hN⟩
    refine ⟨max N 0, fun n hn ↦ ?_⟩
    obtain ⟨s, hs0, hs, hnlt⟩ := exists_square_interval (show 0 ≤ n by omega)
    by_cases hmod : (n - s ^ 2) % 4 = 2
    · have h := hN s (n - s ^ 2) hs0 (by omega) (by nlinarith) hmod (by omega)
      simpa using h
    · exact boundedRepresentation_of_remainder_ne_two hs0 hs hnlt hmod

/-- The exact arithmetic form of the problem: a square with a balanced
factorization of its nonnegative remainder. No primitivity is needed. -/
theorem boundedRepresentation_iff_balanced_factors (n : ℤ) :
    HasBoundedRepresentation n ↔
      ∃ y u v : ℤ, 0 ≤ u ∧ 0 ≤ v ∧ u % 2 = v % 2 ∧
        n = y ^ 2 + u * v ∧ y ^ 2 ≤ n ∧ (u + v) ^ 2 ≤ 4 * n := by
  constructor
  · rintro ⟨x, y, z, heq, hmax⟩
    have hx := (max_le_iff.mp hmax).1
    have hy := (max_le_iff.mp (max_le_iff.mp hmax).2).1
    have hzx : z ^ 2 ≤ x ^ 2 := by linarith
    have habs : |z| ≤ |x| := (sq_le_sq).mp hzx
    refine ⟨y, |x| - |z|, |x| + |z|, sub_nonneg.mpr habs,
      add_nonneg (abs_nonneg _) (abs_nonneg _), by omega, ?_, hy, ?_⟩
    · nlinarith [sq_abs x, sq_abs z]
    · nlinarith [sq_abs x, sq_abs z]
  · rintro ⟨y, u, v, hu, hv, hpar, heq, hy, hsum⟩
    have hxu : 2 * ((u + v) / 2) = u + v := by omega
    have hzu : 2 * ((v - u) / 2) = v - u := by omega
    have hrepr : n = ((u + v) / 2) ^ 2 + y ^ 2 - ((v - u) / 2) ^ 2 := by
      nlinarith [sq_nonneg (u + v), sq_nonneg (v - u)]
    have hx : ((u + v) / 2) ^ 2 ≤ n := by nlinarith
    have hz : ((v - u) / 2) ^ 2 ≤ n := by nlinarith [mul_nonneg hu hv]
    exact ⟨(u + v) / 2, y, (v - u) / 2, hrepr, max_le hx (max_le hy hz)⟩

/-- Factoring the remainder after the next smaller square often also covers
the exceptional residue class. The factors need only be odd and nontrivial. -/
theorem boundedRepresentation_of_shifted_factors {s d u v : ℤ}
    (hs : 4 ≤ s) (hd : 0 ≤ d) (hds : d ≤ 2 * s)
    (hu : 3 ≤ u) (hv : 3 ≤ v) (hpar : u % 2 = v % 2)
    (hmul : u * v = d + 2 * s - 1) : HasBoundedRepresentation (s ^ 2 + d) := by
  have hsum : u + v ≤ 2 * s := by
    nlinarith [mul_nonneg (show 0 ≤ u - 3 by omega) (show 0 ≤ v - 3 by omega)]
  apply (boundedRepresentation_iff_balanced_factors _).mpr
  refine ⟨s - 1, u, v, by omega, by omega, hpar, by nlinarith, by nlinarith, ?_⟩
  nlinarith [mul_nonneg (show 0 ≤ 2 * s - (u + v) by omega)
    (show 0 ≤ 2 * s + (u + v) by omega)]

/-- For a counterexample in a square interval, the remainder after the next
smaller square must be prime. This is necessary, not sufficient. -/
theorem prime_shifted_remainder_of_not_boundedRepresentation {s d : ℤ}
    (hs : 4 ≤ s) (hd : 0 ≤ d) (hds : d ≤ 2 * s) (hdmod : d % 4 = 2)
    (hno : ¬ HasBoundedRepresentation (s ^ 2 + d)) :
    Nat.Prime (d + 2 * s - 1).toNat := by
  have hmpos : 0 ≤ d + 2 * s - 1 := by omega
  have hmcast : ((d + 2 * s - 1).toNat : ℤ) = d + 2 * s - 1 :=
    Int.toNat_of_nonneg hmpos
  by_contra hprime
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (Nat.not_prime_iff_exists_mul_eq (show 2 ≤ (d + 2 * s - 1).toNat by omega)).mp hprime
  have ha' : (2 : ℤ) ≤ a := by
    by_contra h
    have hsmall : a = 0 ∨ a = 1 := by omega
    rcases hsmall with h0 | h1
    · simp [h0] at hab; omega
    · simp [h1] at hab; omega
  have hb' : (2 : ℤ) ≤ b := by
    by_contra h
    have hsmall : b = 0 ∨ b = 1 := by omega
    rcases hsmall with h0 | h1
    · simp [h0] at hab; omega
    · simp [h1] at hab; omega
  have hab' : (a : ℤ) * b = d + 2 * s - 1 := by
    have hc : (a : ℤ) * b = ((d + 2 * s - 1).toNat : ℤ) := by exact_mod_cast hab
    omega
  have hmod : ((a : ℤ) % 2) * ((b : ℤ) % 2) % 2 = 1 := by
    rw [← Int.mul_emod, hab']
    omega
  have hpa : (a : ℤ) % 2 = 1 := by
    have h0 : (a : ℤ) % 2 = 0 ∨ (a : ℤ) % 2 = 1 := by omega
    rcases h0 with h0 | h1
    · simp [h0] at hmod
    · exact h1
  have hpb : (b : ℤ) % 2 = 1 := by simpa [hpa] using hmod
  apply hno
  exact boundedRepresentation_of_shifted_factors hs hd hds (by omega) (by omega)
    (by omega) hab'

/-- A version of the original eventual assertion in which only the remaining
prime candidates need to be considered. This is a reduction, not a proof of
either side of the equivalence. -/
theorem erdos_1148_iff_prime_candidates :
    (∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∃ x y z : ℤ,
      n = x ^ 2 + y ^ 2 - z ^ 2 ∧ max (x ^ 2) (max (y ^ 2) (z ^ 2)) ≤ n) ↔
      ∃ N : ℤ, ∀ s d : ℤ, 4 ≤ s → 0 ≤ d → d ≤ 2 * s → d % 4 = 2 →
        Nat.Prime (d + 2 * s - 1).toNat → N ≤ s ^ 2 + d →
          HasBoundedRepresentation (s ^ 2 + d) := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun s d _ _ _ _ _ hn ↦ hN _ hn⟩
  · rintro ⟨N, hN⟩
    refine ⟨max N 16, fun n hn ↦ ?_⟩
    obtain ⟨s, hs0, hs, hnlt⟩ := exists_square_interval (show 0 ≤ n by omega)
    have hs4 : 4 ≤ s := by
      by_contra h
      have hsle : s ≤ 3 := by omega
      have hn16 : 16 ≤ n := by omega
      nlinarith [mul_nonneg (show 0 ≤ 3 - s by omega) (show 0 ≤ s + 5 by omega)]
    have hd : 0 ≤ n - s ^ 2 := by omega
    have hds : n - s ^ 2 ≤ 2 * s := by nlinarith
    by_cases hmod : (n - s ^ 2) % 4 = 2
    · by_cases hp : Nat.Prime (n - s ^ 2 + 2 * s - 1).toNat
      · have h := hN s (n - s ^ 2) hs4 hd hds hmod hp (by omega)
        simpa [HasBoundedRepresentation] using h
      · have hrepr : HasBoundedRepresentation (s ^ 2 + (n - s ^ 2)) := by
          by_contra hno
          exact hp (prime_shifted_remainder_of_not_boundedRepresentation hs4 hd hds hmod hno)
        simpa [HasBoundedRepresentation] using hrepr
    · exact boundedRepresentation_of_remainder_ne_two hs0 hs hnlt hmod

/-- The prime-candidate reduction cannot be closed by proving that the
candidate set is eventually empty: even the subfamily `d = 2` is unbounded.
This does not assert that any of these candidates is a counterexample. -/
theorem unbounded_prime_candidates (N : ℤ) :
    ∃ s : ℤ, 4 ≤ s ∧ N ≤ s ^ 2 + 2 ∧ Nat.Prime (2 * s + 1).toNat := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (2 * (N.toNat + 5) + 1)
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hpdiv : 2 * (p / 2) + 1 = p := by omega
  let s : ℤ := (p / 2 : ℕ)
  have hs : (N.toNat : ℤ) + 5 ≤ s := by
    have hnat : N.toNat + 5 ≤ p / 2 := by omega
    dsimp [s]
    exact_mod_cast hnat
  have hs4 : 4 ≤ s := by omega
  have hsp : 2 * s + 1 = (p : ℤ) := by
    dsimp [s]
    exact_mod_cast hpdiv
  refine ⟨s, hs4, ?_, ?_⟩
  · have hN : N ≤ (N.toNat : ℤ) := by omega
    nlinarith [mul_nonneg (show 0 ≤ s by omega) (show 0 ≤ s - 1 by omega)]
  · simpa only [hsp, Int.toNat_natCast] using hp

end Erdos1148
