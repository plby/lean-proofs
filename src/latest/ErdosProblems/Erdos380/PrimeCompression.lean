import ErdosProblems.Erdos380.PrimeCounts

/-!
# Compressing primes with bounded fibers

Divide a prime's index by a fixed integer.  This preserves primality,
has bounded fibers, and, by the prime number theorem, reduces the prime
by a prescribed fixed factor while retaining a fixed lower size bound.
-/

open Filter

namespace Erdos380

noncomputable def compressedPrime (K p : ℕ) : ℕ :=
  Nat.nth Nat.Prime (Nat.primeCounting' p / K)

lemma compressedPrime_prime (K p : ℕ) : (compressedPrime K p).Prime := Nat.prime_nth_prime _

lemma compressedPrime_with_tag_injective {K p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hcomp : compressedPrime K p = compressedPrime K q)
    (htag : Nat.primeCounting' p % K = Nat.primeCounting' q % K) : p = q := by
  have hdiv := congrArg Nat.primeCounting' hcomp
  simp only [compressedPrime, Nat.primeCounting'_nth_eq] at hdiv
  have hindex : Nat.primeCounting' p = Nat.primeCounting' q := by
    have hp' := Nat.mod_add_div (Nat.primeCounting' p) K
    have hq' := Nat.mod_add_div (Nat.primeCounting' q) K
    rw [htag, hdiv] at hp'
    exact hp'.symm.trans hq'
  have hpn : Nat.nth Nat.Prime (Nat.primeCounting' p) = p := Nat.nth_count hp
  have hqn : Nat.nth Nat.Prime (Nat.primeCounting' q) = q := Nat.nth_count hq
  rw [← hpn, ← hqn, hindex]

lemma compressedPrime_fiber_card_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {K : ℕ} (hK : 0 < K) (r : ℕ) :
    (s.filter fun p => compressedPrime K p = r).card ≤ K := by
  classical
  calc
    (s.filter fun p => compressedPrime K p = r).card ≤ (Finset.range K).card := by
      apply Finset.card_le_card_of_injOn (fun p => Nat.primeCounting' p % K)
      · intro p _
        exact Finset.mem_range.mpr (Nat.mod_lt _ hK)
      · intro p hp q hq htag
        exact compressedPrime_with_tag_injective
          (hs p (Finset.mem_filter.mp hp).1) (hs q (Finset.mem_filter.mp hq).1)
          ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) htag
    _ = K := Finset.card_range _

lemma primeCounting_le_strict_add_one (n : ℕ) :
    Nat.primeCounting n ≤ Nat.primeCounting' n + 1 := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ]
  split_ifs <;> omega

theorem exists_strict_primeCounting_bounds : ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n ≥ n₀,
    ((n : ℝ) / Real.log n) / 2 ≤ Nat.primeCounting' n ∧
      (Nat.primeCounting' n : ℝ) ≤ 2 * ((n : ℝ) / Real.log n) := by
  have hlog := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 10)
  have hlogNat := tendsto_natCast_atTop_atTop.eventually hlog
  have hall : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) / Real.log n) / 2 ≤ Nat.primeCounting' n ∧
        (Nat.primeCounting' n : ℝ) ≤ 2 * ((n : ℝ) / Real.log n) := by
    filter_upwards [eventually_primeCounting_bounds, hlogNat, eventually_ge_atTop 2] with n hp hl hn
    have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hl' : Real.log (n : ℝ) ≤ (n : ℝ) / 10 := by
      simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, abs_of_pos hL,
        abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), one_div_mul_eq_div] using hl
    have hratio : 10 ≤ (n : ℝ) / Real.log n := (le_div_iff₀ hL).mpr (by linarith)
    have hinc : (Nat.primeCounting n : ℝ) ≤ Nat.primeCounting' n + 1 := by
      exact_mod_cast primeCounting_le_strict_add_one n
    have hmono : (Nat.primeCounting' n : ℝ) ≤ Nat.primeCounting n := by
      exact_mod_cast Nat.monotone_primeCounting' (show n ≤ n + 1 by omega)
    constructor <;> linarith
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp hall
  exact ⟨max 2 n₁, le_max_left _ _, fun n hn => hn₁ n ((le_max_right _ _).trans hn)⟩

lemma strict_primeCounting_dilation_bounds
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (hbase : ∀ n ≥ n₀, ((n : ℝ) / Real.log n) / 2 ≤ Nat.primeCounting' n ∧
      (Nat.primeCounting' n : ℝ) ≤ 2 * ((n : ℝ) / Real.log n))
    {c n : ℕ} (hc : 1 ≤ c) (hn : n₀ ≤ n) (hcn : c ≤ n) :
    (c : ℝ) * Nat.primeCounting' n ≤ 8 * Nat.primeCounting' (c * n) ∧
      (Nat.primeCounting' (c * n) : ℝ) ≤ 4 * c * Nat.primeCounting' n := by
  have hn2 : 2 ≤ n := hn₀.trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcR : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hnn : n ≤ c * n := Nat.le_mul_of_pos_left n (by omega)
  have hLC : 0 < Real.log (c * n : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c * n))
  have hloglo : Real.log (n : ℝ) ≤ Real.log (c * n : ℕ) :=
    Real.log_le_log hnR (by exact_mod_cast hnn)
  have hloghi : Real.log (c * n : ℕ) ≤ 2 * Real.log n := by
    rw [Nat.cast_mul, Real.log_mul hcR.ne' hnR.ne']
    have h := Real.log_le_log hcR (show (c : ℝ) ≤ (n : ℝ) by exact_mod_cast hcn)
    linarith
  obtain ⟨hlo, hhi⟩ := hbase n hn
  obtain ⟨hloC, hhiC⟩ := hbase (c * n) (hn.trans hnn)
  have hnl : (n : ℝ) ≤ 2 * Real.log n * Nat.primeCounting' n := by
    have h := (div_le_iff₀ hL).mp (show (n : ℝ) / Real.log n ≤ 2 * Nat.primeCounting' n by linarith)
    nlinarith
  have hnu : (Nat.primeCounting' n : ℝ) * Real.log n ≤ 2 * n := by
    have h := (le_div_iff₀ hL).mp (show (Nat.primeCounting' n : ℝ) ≤ (2 * n) / Real.log n by
      simpa only [mul_div_assoc] using hhi)
    exact h
  have hcl : (c : ℝ) * n ≤ 4 * Real.log n * Nat.primeCounting' (c * n) := by
    have h := (div_le_iff₀ hLC).mp (show ((c * n : ℕ) : ℝ) / Real.log (c * n : ℕ) ≤
      2 * Nat.primeCounting' (c * n) by linarith)
    have hm := mul_le_mul_of_nonneg_right hloghi (Nat.cast_nonneg (Nat.primeCounting' (c * n)) : (0 : ℝ) ≤ _)
    push_cast at h hm
    nlinarith
  have hcu : (Nat.primeCounting' (c * n) : ℝ) * Real.log n ≤ 2 * c * n := by
    have h := (le_div_iff₀ hLC).mp (show (Nat.primeCounting' (c * n) : ℝ) ≤
      (2 * ((c * n : ℕ) : ℝ)) / Real.log (c * n : ℕ) by simpa only [mul_div_assoc] using hhiC)
    have hm := mul_le_mul_of_nonneg_right hloglo (Nat.cast_nonneg (Nat.primeCounting' (c * n)) : (0 : ℝ) ≤ _)
    push_cast at h hm
    nlinarith
  constructor
  · apply le_of_mul_le_mul_right _ hL
    have hmul := mul_le_mul_of_nonneg_left hnu hcR.le
    nlinarith
  · apply le_of_mul_le_mul_right _ hL
    have hmul := mul_le_mul_of_nonneg_left hnl (show (0 : ℝ) ≤ 2 * c by positivity)
    nlinarith

lemma compressedPrime_le {K p : ℕ} (hp : p.Prime) :
    compressedPrime K p ≤ p := by
  calc
    compressedPrime K p ≤ Nat.nth Nat.Prime (Nat.primeCounting' p) :=
      (Nat.nth_monotone Nat.infinite_setOfPred_prime)
        (Nat.div_le_self (Nat.primeCounting' p) K)
    _ = p := Nat.nth_count hp

/-- A fixed compression factor reduces all sufficiently large primes by
the desired factor, without reducing them by more than another fixed factor. -/
theorem exists_compressedPrime_scale_bounds {C : ℕ} (hC : 1 ≤ C) :
    ∃ P₀ : ℕ, ∀ p ≥ P₀, p.Prime →
      C * compressedPrime (8 * C) p ≤ p ∧
        p ≤ 128 * C * compressedPrime (8 * C) p := by
  obtain ⟨n₀, hn₀, hbase⟩ := exists_strict_primeCounting_bounds
  let K := 8 * C
  let D := 128 * C
  let R := max n₀ D
  have hK : 0 < K := by dsimp [K]; omega
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hCD : C ≤ D := by dsimp [D]; omega
  have hR : 1 ≤ R := hD.trans (le_max_right _ _)
  refine ⟨Nat.nth Nat.Prime (K * R), ?_⟩
  intro p hp hpprime
  let i := Nat.primeCounting' p
  let j := i / K
  let r := compressedPrime K p
  have hi : K * R ≤ i := by
    have h := Nat.monotone_primeCounting' hp
    simpa only [Nat.primeCounting'_nth_eq] using h
  have hjR : R ≤ j := by
    apply (Nat.le_div_iff_mul_le hK).mpr
    simpa only [mul_comm] using hi
  have hj1 : 1 ≤ j := hR.trans hjR
  have hjr : j ≤ r := by
    have h := Nat.add_two_le_nth_prime j
    change j ≤ Nat.nth Nat.Prime j
    omega
  have hnr : n₀ ≤ r := (le_max_left n₀ D).trans (hjR.trans hjr)
  have hDr : D ≤ r := (le_max_right n₀ D).trans (hjR.trans hjr)
  have hcount : Nat.primeCounting' r = j := Nat.primeCounting'_nth_eq _
  have hij : K * j ≤ i := Nat.mul_div_le i K
  have hij' : i < K * (j + 1) := by
    have hmod := Nat.mod_lt i hK
    have hdecomp := Nat.mod_add_div i K
    dsimp [j]
    nlinarith
  obtain ⟨_, hupper⟩ := strict_primeCounting_dilation_bounds hn₀ hbase hC hnr
    (hCD.trans hDr)
  obtain ⟨hlower, _⟩ := strict_primeCounting_dilation_bounds hn₀ hbase hD hnr hDr
  have hupperN : Nat.primeCounting' (C * r) ≤ 4 * C * j := by
    rw [hcount] at hupper
    exact_mod_cast hupper
  have hlowerN : D * j ≤ 8 * Nat.primeCounting' (D * r) := by
    rw [hcount] at hlower
    exact_mod_cast hlower
  change C * r ≤ p ∧ p ≤ D * r
  constructor
  · by_contra h
    have hpi : i ≤ Nat.primeCounting' (C * r) :=
      Nat.monotone_primeCounting' (Nat.le_of_lt (Nat.lt_of_not_ge h))
    dsimp [K] at hij
    nlinarith
  · by_contra h
    have hpi : Nat.primeCounting' (D * r) ≤ i :=
      Nat.monotone_primeCounting' (Nat.le_of_lt (Nat.lt_of_not_ge h))
    dsimp [D] at hlowerN
    dsimp [K] at hij'
    nlinarith

end Erdos380
