import ErdosProblems.Erdos380.SmoothLogLower
import ErdosProblems.Erdos380.SingletonCount

/-! # Lower bounds for the singleton contribution -/

open scoped BigOperators

namespace Erdos380

theorem singletonBadUpTo_card_ge_prime_band_smooth {N M y : ℕ}
    (hy : 1 ≤ y) (hsize : (2 * y) ^ 2 * M ≤ N) :
    (dyadicPrimes y).card * smoothCount M y ≤ (singletonBadUpTo N).card := by
  classical
  let s := (dyadicPrimes y).product (Nat.smoothNumbersUpTo M (y + 1))
  have hmem (pm : ℕ × ℕ) (hpm : pm ∈ s) :
      pm.1 ^ 2 * pm.2 ∈ singletonBadUpTo N ∧
        largestPrimeFactor (pm.1 ^ 2 * pm.2) = pm.1 := by
    obtain ⟨hp, hm⟩ := Finset.mem_product.mp hpm
    obtain ⟨hprange, hpprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hyp, hpy⟩ := Finset.mem_Ioc.mp hprange
    obtain ⟨hmM, hmsmooth⟩ := Nat.mem_smoothNumbersUpTo.mp hm
    obtain ⟨hm0, hmP⟩ := (mem_smoothNumbers_iff_largestPrimeFactor hy).mp hmsmooth
    have hmp := (mem_smoothNumbers_iff_largestPrimeFactor hpprime.one_le).mpr
      ⟨hm0, hmP.trans hyp.le⟩
    have hP := prime_square_smooth_largest hpprime hmp
    have hnN : pm.1 ^ 2 * pm.2 ≤ N :=
      (Nat.mul_le_mul (Nat.pow_le_pow_left hpy 2) hmM).trans hsize
    have hn2 : 2 ≤ pm.1 ^ 2 * pm.2 := by
      have := hpprime.two_le
      have := Nat.pos_of_ne_zero hm0
      nlinarith
    exact ⟨mem_singletonBadUpTo.mpr ⟨by omega, hnN,
      hn2, by rw [hP]; exact dvd_mul_right _ _⟩, hP⟩
  have hcard : s.card ≤ (singletonBadUpTo N).card := by
    apply Finset.card_le_card_of_injOn (fun pm : ℕ × ℕ => pm.1 ^ 2 * pm.2)
    · exact fun pm hpm => (hmem pm hpm).1
    · intro pm hpm qn hqn heq
      dsimp only at heq
      have hpq : pm.1 = qn.1 := by
        rw [← (hmem pm hpm).2, ← (hmem qn hqn).2, heq]
      have hp : pm.1.Prime := (Finset.mem_filter.mp (Finset.mem_product.mp hpm).1).2
      have hmn : pm.2 = qn.2 := by
        rw [← hpq] at heq
        exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) heq
      exact Prod.ext hpq hmn
  simpa [s, smoothCount] using hcard

lemma dyadic_singletonLower_size (X Y : ℕ) :
    (2 * 2 ^ Y) ^ 2 * 2 ^ X = 2 ^ (X + 2 * (Y + 1)) := by
  rw [← pow_succ', ← pow_mul, ← pow_add]
  congr 1
  omega

/-- A fully explicit lower bound, with freely chosen dyadic exponents. -/
theorem exists_singletonBadUpTo_dyadic_exponential_lower : ∃ Y₀ : ℕ, ∀ X Y : ℕ,
    Y₀ ≤ Y → ∀ ε u : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ u → (X : ℝ) = u * Y →
    4 ≤ ε * Y → 8 * X ≤ ε * (Y : ℝ) ^ 2 →
    Real.log (20 * Y : ℝ) ≤ (1 + ε) * Real.log u →
      (2 : ℝ) ^ (X + Y) * Real.exp (-(1 + 3 * ε) * u * Real.log u) / (10 * Y) ≤
        ((singletonBadUpTo (2 ^ (X + 2 * (Y + 1)))).card : ℝ) := by
  obtain ⟨Y₁, hY₁⟩ := exists_smoothCount_dyadic_exponential_lower
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp eventually_dyadicPrimes_card_bounds
  refine ⟨max 1 (max Y₁ P₀), ?_⟩
  intro X Y hY ε u hε hε1 hu hX hεY hXY hlog
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYY₁ : Y₁ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYP₀ : P₀ ≤ 2 ^ Y :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans hY)).trans
      (Nat.le_of_lt (show Y < 2 ^ Y from Nat.lt_two_pow_self))
  have hsmooth := hY₁ X Y hYY₁ ε u hε hε1 hu hX hεY hXY hlog
  have hpool := (hP₀ (2 ^ Y) hYP₀).1
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hpool' : (2 : ℝ) ^ Y / (10 * Y) ≤ ((dyadicPrimes (2 ^ Y)).card : ℝ) := by
    have hlogpow : Real.log ((2 ^ Y : ℕ) : ℝ) = Y * Real.log 2 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    rw [hlogpow] at hpool
    push_cast at hpool
    have hratio : (2 : ℝ) ^ Y / (10 * Y) ≤ ((2 : ℝ) ^ Y / (Y * Real.log 2)) / 10 := by
      rw [div_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    exact hratio.trans hpool
  have hcount := singletonBadUpTo_card_ge_prime_band_smooth
    (Nat.one_le_pow Y 2 (by omega)) (dyadic_singletonLower_size X Y).le
  have hcountR : ((dyadicPrimes (2 ^ Y)).card : ℝ) * smoothCount (2 ^ X) (2 ^ Y) ≤
      ((singletonBadUpTo (2 ^ (X + 2 * (Y + 1)))).card : ℝ) := by exact_mod_cast hcount
  calc
    _ = ((2 : ℝ) ^ Y / (10 * Y)) *
        ((2 : ℝ) ^ X * Real.exp (-(1 + 3 * ε) * u * Real.log u)) := by
      rw [pow_add]
      ring
    _ ≤ ((dyadicPrimes (2 ^ Y)).card : ℝ) * smoothCount (2 ^ X) (2 ^ Y) :=
      mul_le_mul hpool' hsmooth (by positivity) (Nat.cast_nonneg _)
    _ ≤ _ := hcountR

end Erdos380
