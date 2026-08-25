import ErdosProblems.Erdos1141b.WeakBurgess
import ErdosProblems.Erdos1141b.TwistedCharacterSums

/-!
# Weak Burgess cancellation with the factors at four and eight
-/

open scoped BigOperators

namespace Erdos1141b

open CharacterSums

/-- The auxiliary modulus may be any positive integer at most eight. -/
theorem exists_twisted_weak_burgess_cutoff :
    ∃ q0 : ℕ, ∀ (t : ℕ) [NeZero t], t ≤ 8 →
      ∀ {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
        (hc : Pairwise fun i j ↦ (p i).Coprime (p j))
        (ht : t.Coprime (∏ i, p i)) (ψ : DirichletCharacter ℤ t),
        ψ.IsQuadratic → (∀ i, p i ≠ 2) → q0 ≤ t * ∏ i, p i →
        ∀ N : ℕ, (t * ∏ i, p i : ℕ) ^ (15 / 32 : ℝ) ≤ (N : ℝ) →
          (N : ℝ) ≤ (t * ∏ i, p i : ℕ) ^ (5 / 8 : ℝ) →
          |∑ n ∈ Finset.Icc 1 N,
            (crtMulChar ht ψ (primeProductMulChar p hc) (n : ZMod (t * ∏ i, p i)) : ℝ)| ≤
            (N : ℝ) * (t * ∏ i, p i : ℕ) ^ (-1 / 256 : ℝ) := by
  obtain ⟨q0, hcut⟩ := exists_weak_burgess_cutoff_of_moment
  obtain ⟨q1, hq1⟩ := Filter.eventually_atTop.mp
    (eventually_const_le_rpow 8 (1 / 8) (by norm_num))
  refine ⟨max q0 q1, ?_⟩
  intro t _ ht8 ι _ p _ hc ht ψ hψ hodd hq N hNlo hNhi
  let r := ∏ i, p i
  let q := t * r
  let χ := crtMulChar ht ψ (primeProductMulChar p hc)
  have hχ : χ.IsQuadratic :=
    crtMulChar_isQuadratic ht ψ (primeProductMulChar p hc) hψ (primeProductMulChar_isQuadratic p hc)
  have hq0 : q0 ≤ q := (le_max_left _ _).trans hq
  have hq1' : q1 ≤ q := (le_max_right _ _).trans hq
  have htpos : (0 : ℝ) < t := by exact_mod_cast NeZero.pos t
  have hrpos : (0 : ℝ) < r := by
    exact_mod_cast (Finset.prod_pos (fun i _ ↦ (Fact.out : (p i).Prime).pos))
  have hqpos : (0 : ℝ) < q := by
    dsimp [q]
    rw [Nat.cast_mul]
    exact mul_pos htpos hrpos
  have hsmall : (t : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ) :=
    (by exact_mod_cast ht8 : (t : ℝ) ≤ 8).trans (hq1 q hq1')
  apply hcut q hq0 (fun x ↦ (χ x : ℝ))
    (fun x y ↦ by rw [map_mul, Int.cast_mul])
    (fun a ha ↦ abs_mulChar_of_isUnit χ hχ _ ((ZMod.isUnit_iff_coprime _ _).mpr ha))
    (abs_mulChar_le_one χ hχ) ?_ N hNlo hNhi
  let B := ⌊(q : ℝ) ^ (1 / 8 : ℝ)⌋₊
  have hBhi : (B : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ) := Nat.floor_le (by positivity)
  have hB7 : B ^ 7 ≤ r := by
    have hprod : (B : ℝ) ^ 7 * t ≤ q := by
      calc
        _ ≤ ((q : ℝ) ^ (1 / 8 : ℝ)) ^ 7 * (q : ℝ) ^ (1 / 8 : ℝ) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hBhi 7) hsmall
            htpos.le (by positivity)
        _ = (q : ℝ) ^ (1 : ℝ) := by
          rw [← Real.rpow_mul_natCast hqpos.le, ← Real.rpow_add hqpos]; norm_num
        _ = _ := Real.rpow_one _
    have hr : (B : ℝ) ^ 7 ≤ r := by
      apply (mul_le_mul_iff_of_pos_right htpos).mp
      simpa only [q, Nat.cast_mul, mul_comm (t : ℝ)] using hprod
    exact_mod_cast hr
  have htwo : (2 : ℝ) ^ Fintype.card ι ≤ (q.divisors.card : ℝ) := by
    rw [← primeProduct_primeFactors_card p hc]
    have hr0 : r ≠ 0 := by exact_mod_cast hrpos.ne'
    have hfirst : (2 : ℝ) ^ r.primeFactors.card ≤ (r.divisors.card : ℝ) := by
      exact_mod_cast two_pow_primeFactors_card_le_divisors_card r hr0
    apply hfirst.trans
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd
      (show q ≠ 0 by exact_mod_cast hqpos.ne') (dvd_mul_left r t))
  have hthree : (3 : ℝ) ^ Fintype.card ι ≤ (q.divisors.card : ℝ) ^ 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ 2) ^ Fintype.card ι := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = ((2 : ℝ) ^ Fintype.card ι) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) htwo 2
  apply (crt_primeProduct_fourth_moment_short_le p hc ht ψ hψ hodd B hB7).trans
  gcongr

/-- Pólya–Vinogradov covers longer intervals, so the upper endpoint restriction disappears. -/
theorem exists_twisted_prefix_bound_cutoff :
    ∃ q0 : ℕ, ∀ (t : ℕ) [NeZero t], t ≤ 8 →
      ∀ {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
        (hc : Pairwise fun i j ↦ (p i).Coprime (p j))
        (ht : t.Coprime (∏ i, p i)) (ψ : DirichletCharacter ℤ t),
        ψ.IsQuadratic → (∀ i, p i ≠ 2) → q0 ≤ t * ∏ i, p i →
        (crtMulChar ht ψ (primeProductMulChar p hc)).ringHomComp (Int.castRingHom ℂ) ≠ 1 →
        ∀ N : ℕ, (t * ∏ i, p i : ℕ) ^ (15 / 32 : ℝ) ≤ (N : ℝ) →
          |∑ n ∈ Finset.Icc 1 N,
            (crtMulChar ht ψ (primeProductMulChar p hc) (n : ZMod (t * ∏ i, p i)) : ℝ)| ≤
            (N : ℝ) * (t * ∏ i, p i : ℕ) ^ (-1 / 256 : ℝ) := by
  obtain ⟨q0, hshort⟩ := exists_twisted_weak_burgess_cutoff
  obtain ⟨q1, hlong⟩ := Filter.eventually_atTop.mp eventually_polyaVinogradov_scale_le
  refine ⟨max (max q0 q1) 2, ?_⟩
  intro t _ ht8 ι _ p _ hc ht ψ hψ hodd hq hχ N hNlo
  let q := t * ∏ i, p i
  have hq0 : q0 ≤ q := (le_max_left q0 q1).trans ((le_max_left _ _).trans hq)
  have hq1 : q1 ≤ q := (le_max_right q0 q1).trans ((le_max_left _ _).trans hq)
  have hq2 : 2 ≤ q := (le_max_right _ _).trans hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  by_cases hNhi : (N : ℝ) ≤ (q : ℝ) ^ (5 / 8 : ℝ)
  · exact hshort t ht8 p hc ht ψ hψ hodd hq0 N hNlo hNhi
  · have hlong' := mulChar_prefix_polyaVinogradov_bound (by omega : 1 < q)
      (crtMulChar ht ψ (primeProductMulChar p hc)) hχ N
    apply hlong'.trans
    calc
      _ ≤ (q : ℝ) ^ (159 / 256 : ℝ) := hlong q hq1
      _ = (q : ℝ) ^ (5 / 8 : ℝ) * (q : ℝ) ^ (-1 / 256 : ℝ) := by
        rw [← Real.rpow_add hqpos]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right (lt_of_not_ge hNhi).le (by positivity)

end Erdos1141b
