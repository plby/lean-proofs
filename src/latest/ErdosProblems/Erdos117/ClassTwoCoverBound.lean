import ErdosProblems.Erdos117.SylowCover
import ErdosProblems.Erdos117.ProductArithmetic

/-!
# Removing the prime from the local error

The central-series length is bounded by a power-of-two bound on the
derived-subgroup order. Ceiling logarithms for all primes are dominated by
the ceiling logarithm at two.
-/

namespace Erdos117

open scoped BigOperators

/-- A common derived-subgroup size bound makes the local error independent
of the prime. This is only an arithmetic comparison of the proved bound. -/
theorem primeCoverLogBound_le_uniform {p c n L q : ℕ} [Fact p.Prime]
    (hcn : c ≤ n) (hsize : p ^ L ≤ 2 ^ q) :
    primeCoverLogBound p c L ≤ Real.log 2 / 2 * c + 2 * q +
      48 * Real.sqrt c * ((q : ℝ) + Nat.clog 2 ((2 * n) ^ 2) + 1) *
        Real.sqrt ((q : ℝ) + Nat.clog 2 ((2 * n) ^ 2) + 1) +
      (q : ℝ) * q * Nat.clog 2 ((2 * n) ^ 2) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hLq : L ≤ q := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    ((Nat.pow_le_pow_left hp L).trans hsize)
  have hLq' : (L : ℝ) ≤ q := by exact_mod_cast hLq
  have hell : Nat.clog p ((2 * c) ^ 2) ≤ Nat.clog 2 ((2 * n) ^ 2) :=
    Nat.clog_mono (by decide) hp (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hcn) 2)
  have hell' : (Nat.clog p ((2 * c) ^ 2) : ℝ) ≤ Nat.clog 2 ((2 * n) ^ 2) := by
    exact_mod_cast hell
  have hlogsize : (L : ℝ) * Real.log p ≤ (q : ℝ) * Real.log 2 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hsize' : (p : ℝ) ^ L ≤ 2 ^ q := by exact_mod_cast hsize
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos hp0 L) hsize'
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hweighted : Real.log p * L ≤ (q : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    nlinarith only [hlogsize, h]
  have htail : Real.log p * L * L * Nat.clog p ((2 * c) ^ 2) ≤
      (q : ℝ) * q * Nat.clog 2 ((2 * n) ^ 2) := by
    exact mul_le_mul
      (mul_le_mul hweighted hLq' (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      hell' (Nat.cast_nonneg _) (by positivity)
  unfold primeCoverLogBound
  have hroot :
      48 * Real.sqrt c * ((L : ℝ) + Nat.clog p ((2 * c) ^ 2) + 1) *
        Real.sqrt ((L : ℝ) + Nat.clog p ((2 * c) ^ 2) + 1) ≤
      48 * Real.sqrt c * ((q : ℝ) + Nat.clog 2 ((2 * n) ^ 2) + 1) *
        Real.sqrt ((q : ℝ) + Nat.clog 2 ((2 * n) ^ 2) + 1) := by
    gcongr
  linarith only [hLq', hroot, htail]

open scoped Classical in
/-- A common bound on the actual Sylow derived orders controls the complete
cover error. The factor lengths and covers are constructed by the recursion. -/
theorem exists_class_two_cover_bound_of_sylow_card_le {G : Type*} [Group G] [Finite G]
    (hG : commutator G ≤ Subgroup.center G) {n q : ℕ} (hn : NoncommutingBound G n)
    (hsylow : ∀ p : (Nat.card G).primeFactors,
      Nat.card (commutator (default : Sylow p.val G)) ≤ 2 ^ q) :
    let ell := Nat.clog 2 ((2 * n) ^ 2)
    ∃ k : ℕ, HasAbelianCover G k ∧
      Real.log k ≤ Real.log 2 / 2 * n +
        96 * Real.sqrt n * ((q : ℝ) + ell + 1) * Real.sqrt ((q : ℝ) + ell + 1) +
        (2 * (q : ℝ) + (q : ℝ) * q * ell) * Nat.log 2 n := by
  classical
  let ell := Nat.clog 2 ((2 * n) ^ 2)
  let H : ℝ := (q : ℝ) + ell + 1
  change ∃ k : ℕ, HasAbelianCover G k ∧
    Real.log k ≤ Real.log 2 / 2 * n + 96 * Real.sqrt n * H * Real.sqrt H +
      (2 * (q : ℝ) + (q : ℝ) * q * ell) * Nat.log 2 n
  obtain ⟨c, L, k, hc, hc1, hc3, hprod, hcard, hcover, hlog⟩ :=
    exists_class_two_sylow_cover_exact hG hn
  let J : Finset (Nat.card G).primeFactors := Finset.univ.filter
    (fun p => ¬IsMulCommutative (default : Sylow p.val G))
  have hJ3 (p : (Nat.card G).primeFactors) (hp : p ∈ J) : 3 ≤ c p :=
    hc3 p (Finset.mem_filter.mp hp).2
  have hprodJ : (∏ p ∈ J, c p) ≤ n := by
    apply le_trans ?_ hprod
    exact Finset.prod_le_prod_of_subset_of_one_le' J.subset_univ (fun p _ _ => hc1 p)
  have hcn (p : (Nat.card G).primeFactors) : c p ≤ n :=
    (Finset.single_le_prod' (fun p _ => hc1 p) (Finset.mem_univ p)).trans hprod
  have hsize (p : (Nat.card G).primeFactors) : p.val ^ L p ≤ 2 ^ q :=
    (hcard p).le.trans (hsylow p)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hlocal (p : (Nat.card G).primeFactors) (_hp : p ∈ J) :
      primeCoverLogBound p.val (c p) (L p) ≤
        (Real.log 2 / 2) * c p + (48 * H * Real.sqrt H) * Real.sqrt (c p) +
          (2 * (q : ℝ) + (q : ℝ) * q * ell) := by
    have : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    have h := primeCoverLogBound_le_uniform (hcn p) (hsize p)
    calc
      _ ≤ Real.log 2 / 2 * c p + 2 * q + 48 * Real.sqrt (c p) * H * Real.sqrt H +
          (q : ℝ) * q * ell := h
      _ = _ := by ring
  have hsum := sum_factor_cost_le J c (fun p => primeCoverLogBound p.val (c p) (L p))
    hJ3 hprodJ (by positivity : 0 ≤ Real.log 2 / 2)
    (by positivity : 0 ≤ 48 * H * Real.sqrt H)
    (by positivity : 0 ≤ 2 * (q : ℝ) + (q : ℝ) * q * ell) hlocal
  refine ⟨∏ p, k p, hcover, ?_⟩
  calc
    _ ≤ ∑ p ∈ J, primeCoverLogBound p.val (c p) (L p) := by
      simpa only [J, Finset.sum_filter, ite_not] using hlog
    _ ≤ Real.log 2 / 2 * n + 2 * (48 * H * Real.sqrt H) * Real.sqrt n +
        (2 * (q : ℝ) + (q : ℝ) * q * ell) * Nat.log 2 n := hsum
    _ = _ := by ring

/-- A full cover of a finite class-two group, with an explicit error in the
ceiling logarithm of its derived-subgroup order. This theorem imposes no
bound on that order as an extra hypothesis. -/
theorem exists_class_two_cover_bound {G : Type*} [Group G] [Finite G]
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n) :
    let q := Nat.clog 2 (Nat.card (commutator G))
    let ell := Nat.clog 2 ((2 * n) ^ 2)
    ∃ k : ℕ, HasAbelianCover G k ∧
      Real.log k ≤ Real.log 2 / 2 * n +
        96 * Real.sqrt n * ((q : ℝ) + ell + 1) * Real.sqrt ((q : ℝ) + ell + 1) +
        (2 * (q : ℝ) + (q : ℝ) * q * ell) * Nat.log 2 n := by
  classical
  apply exists_class_two_cover_bound_of_sylow_card_le hG hn
  intro p
  exact (commutator_subgroup_card_le ((default : Sylow p.val G) : Subgroup G)).trans
    (Nat.le_pow_clog (by decide) _)

/-- The explicit class-two estimate is monotone in a supplied numerical
upper bound on its derived-subgroup order. -/
theorem exists_class_two_cover_bound_of_card_le {G : Type*} [Group G] [Finite G]
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n)
    {q : ℕ} (hsize : Nat.card (commutator G) ≤ 2 ^ q) :
    let ell := Nat.clog 2 ((2 * n) ^ 2)
    ∃ k : ℕ, HasAbelianCover G k ∧
      Real.log k ≤ Real.log 2 / 2 * n +
        96 * Real.sqrt n * ((q : ℝ) + ell + 1) * Real.sqrt ((q : ℝ) + ell + 1) +
        (2 * (q : ℝ) + (q : ℝ) * q * ell) * Nat.log 2 n := by
  obtain ⟨k, hk, hlog⟩ := exists_class_two_cover_bound hG hn
  have hq : Nat.clog 2 (Nat.card (commutator G)) ≤ q := Nat.clog_le_of_le_pow hsize
  have hq' : (Nat.clog 2 (Nat.card (commutator G)) : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨k, hk, hlog.trans ?_⟩
  gcongr

end Erdos117
