import Util.Bernays.QuadraticPrimeIdeals
import Util.Bernays.DiscriminantCharacter

/-!
# The character and ideal-theoretic splitting criteria agree
-/

namespace Bernays

theorem quadratic_conjugate_root {K : Type*} [CommRing K] (d b r : K)
    (hr : r ^ 2 = d + b * r) : (b - r) ^ 2 = d + b * (b - r) := by
  linear_combination hr

theorem quadratic_roots_distinct {K : Type*} [Field K] (d b r : K)
    (hr : r ^ 2 = d + b * r) (hD : b ^ 2 + 4 * d ≠ 0) : r ≠ b - r := by
  intro heq
  apply hD
  linear_combination -4 * hr + (2 * r - b) * heq

theorem quadratic_has_root_iff_isSquare {K : Type*} [Field K] [NeZero (2 : K)] (d b : K) :
    (∃ r : K, r ^ 2 = d + b * r) ↔ IsSquare (b ^ 2 + 4 * d) := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨2 * r - b, ?_⟩
    linear_combination -4 * hr
  · rintro ⟨s, hs⟩
    refine ⟨(b + s) / 2, ?_⟩
    have ht : (2 : K) ≠ 0 := NeZero.ne 2
    field_simp
    linear_combination -hs

theorem discriminantCharacter_prime_eq_neg_one_iff {D : ℤ} (hD : D ≠ 0)
    {q : ℕ} [Fact q.Prime] (hq : q.Coprime (discriminantLevel D)) :
    discriminantCharacter D hD q = -1 ↔ ¬ IsSquare (D : ZMod q) := by
  rw [discriminantCharacter_apply_of_coprime D hD hq, ← ZMod.nonsquare_iff_jacobiSym_eq_neg_one]
  norm_cast

theorem discriminantCharacter_root_iff {d b : ℤ} {q : ℕ} [Fact q.Prime]
    (hD : b ^ 2 + 4 * d ≠ 0) (hq : q.Coprime (discriminantLevel (b ^ 2 + 4 * d))) :
    (∃ r : ZMod q, r ^ 2 = (d : ZMod q) + (b : ZMod q) * r) ↔
      discriminantCharacter (b ^ 2 + 4 * d) hD q ≠ -1 := by
  have hq₂ : q ≠ 2 := by
    have ho := Nat.odd_iff.mp (odd_of_coprime_discriminantLevel hq)
    omega
  haveI : NeZero (2 : ZMod q) := ⟨by
    intro hz
    have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    exact hq₂ ((Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left (Fact.out : q.Prime).ne_one)⟩
  rw [quadratic_has_root_iff_isSquare, ne_eq, discriminantCharacter_prime_eq_neg_one_iff hD hq,
    not_not]
  simp only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]

end Bernays
