/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1141.
https://www.erdosproblems.com/forum/thread/1141

Formalization status:
- Unconditional; the final theorems use only Lean's standard axioms.

Informal authors:
- an internal model at OpenAI
- Boris Alexeev
- Moe Putterman
- Mehtaab Sawhney
- Mark Sellke
- Gregory Valiant

Formal authors:
- GPT-5.4 Pro
- Yuta Oriike

URLs:
- https://www.erdosproblems.com/forum/thread/1141#post-5335
- https://github.com/yuta0x89/ErdosProblems/blob/a1319f732cdee5140faf47d984e2c451c1184803/Erdos1141.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1141.lean
-/
import Mathlib
import Util.MertensThird
import ErdosProblems.Erdos1141b.CoprimeCounting
import ErdosProblems.Erdos1141b.SmallResiduePrime

/-!
# Erdős Problem 1141: proof avoiding Pollack

We formalize the `Pa`-variant of Erdős Problem 1141 from the paper
https://arxiv.org/abs/2604.06609 and then deduce the Formal
Conjectures statement.
Fix `a ≥ 1`. Let `Pa a n` denote the property that
`n - a*k^2` is prime for every positive integer `k` with `(k,n)=1` and `a*k^2 < n`.
Then only finitely many `n` satisfy `Pa a n`.

## Analytic inputs

The supporting modules prove a weak Burgess estimate from the Hasse bound,
a Siegel lower bound for quadratic L-values from the unconditional zero-free
region, and existence of one split prime outside a prescribed modulus.
The Mertens product estimate is also proved in the imported library.
This proof neither invokes nor imports Pollack's theorem. The Pollack-based proof is
in `ErdosProblems.Erdos1141`.

## Proof structure

Write `a*n = u^2*d` with `d` squarefree.

* If `d > 1`, the small-prime theorem gives an odd prime
  `p ≤ (8*a*n)^(31/64)`, with `p ∤ a*n`, at which `d` is a square.
  Thus `a*x^2 ≡ n [MOD p]` is solvable. Inclusion-exclusion in a root
  class provides two admissible values of `k` for large `n`.
* If `d = 1`, the test `k = 1` suffices: primality of `n-a`, together
  with `(u+a)*(u-a) = a*(n-a)`, contradicts `n > 4*a`.
-/

namespace Erdos1141b

open scoped BigOperators
open Finset Real

/-! ## Basic definitions -/

/-- `Pa a n` means that every positive `k` coprime to `n` with `a*k^2 < n`
produces a prime value `n - a*k^2`. -/
def Pa (a n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → Nat.Coprime k n → a * k ^ 2 < n → Nat.Prime (n - a * k ^ 2)

/-- `d` is a quadratic residue modulo `p`.  We use an elementary `Nat.ModEq` formulation,
which is enough for the formalization. -/
def QuadResidueMod (d p : ℕ) : Prop :=
  ∃ x : ℕ, Nat.ModEq p (x ^ 2) d

/-- The congruence `a*x^2 ≡ n [MOD p]` is solvable. -/
def SolvableAX2EqNMod (a n p : ℕ) : Prop :=
  ∃ x : ℕ, Nat.ModEq p (a * x ^ 2) n

/-- The small-prime cutoff used by the nonsquare case. -/
noncomputable def smallPrimeSizeBound (a n : ℕ) : ℝ :=
  Real.rpow ((8 * a * n : ℕ) : ℝ) ((31 : ℝ) / 64)

/-- Candidate values of `k` used in both cases of the proof.  We range over `k < n`; this is
harmless because `a*k^2 < n` and `a ≥ 1` automatically force `k < n`. -/
def candidateKs (a n p : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun k ↦
    1 ≤ k ∧ a * k ^ 2 < n ∧ Nat.Coprime k n ∧ Nat.ModEq p (a * k ^ 2) n

/-! ## Elementary setup -/

/-- Squarefree-part factorization of a natural number. -/
lemma exists_squarefree_factorization (m : ℕ) :
    ∃ u d : ℕ, u ^ 2 * d = m ∧ Squarefree d := by
  obtain ⟨d, u, h, hd⟩ := Nat.sq_mul_squarefree m
  exact ⟨u, d, h, hd⟩

/-- `1` is always a quadratic residue. -/
private lemma one_is_quad_residue (p : ℕ) : QuadResidueMod 1 p := by
  refine ⟨1, ?_⟩
  simpa using (Nat.ModEq.refl (1 : ℕ))

/-- A squarefree natural different from `1` is `> 1`. -/
lemma one_lt_of_squarefree_ne_one {d : ℕ} (hd : Squarefree d) (h : d ≠ 1) : 1 < d := by
  cases d with
  | zero => exact (hd.ne_zero rfl).elim
  | succ d =>
      cases d with
      | zero => exact (h rfl).elim
      | succ d => exact Nat.succ_lt_succ (Nat.succ_pos _)

/-- The size comparison needed to apply the residue-prime theorem with `m = 8*a*n`. -/
lemma le_residue_modulus {a n : ℕ} (ha : 1 ≤ a) : n ≤ 8 * a * n := by
  have hmul : 1 ≤ 8 * a := by
    nlinarith
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_right n hmul

/-- If `u^2*d = a*n`, then the conductor-relevant multiple `8*d` divides `8*a*n`. -/
private lemma squarefree_factor_dvd_residue_modulus {a n u d : ℕ}
    (hdecomp : u ^ 2 * d = a * n) : 8 * d ∣ 8 * a * n := by
  refine ⟨u ^ 2, ?_⟩
  calc
    8 * a * n = 8 * (a * n) := by ac_rfl
    _ = 8 * (u ^ 2 * d) := by rw [← hdecomp]
    _ = (8 * d) * (u ^ 2) := by ac_rfl

/-- A prime not dividing `8*a*n` certainly does not divide `a*n`. -/
lemma not_dvd_an_of_not_dvd_residue_modulus {a n p : ℕ}
    (h : ¬ p ∣ 8 * a * n) : ¬ p ∣ a * n := by
  intro hp
  apply h
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using dvd_mul_of_dvd_right hp 8

/-- A square root in `ZMod p` yields a witness for `QuadResidueMod d p`. -/
private lemma quadResidueMod_of_isSquare_zmod {d p : ℕ} (h : IsSquare (d : ZMod p)) :
    QuadResidueMod d p := by
  rcases h with ⟨x, hx⟩
  cases p with
  | zero =>
      refine ⟨x.val, ?_⟩
      rw [Nat.ModEq, Nat.mod_zero, Nat.mod_zero]
      simpa [pow_two] using congrArg ZMod.val hx.symm
  | succ p =>
      refine ⟨x.val, ?_⟩
      rw [← ZMod.natCast_eq_natCast_iff]
      calc
        (((x.val ^ 2 : ℕ) : ZMod (p + 1))) = (((x.val : ℕ) : ZMod (p + 1)) ^ 2) := by
          simp
        _ = x ^ 2 := by
          simp
        _ = (d : ZMod (p + 1)) := by
          simpa [pow_two] using hx.symm

/-! ## The unconditional small-prime input -/

lemma exists_small_residue_prime :
    ∃ M0 : ℕ, ∀ {m d : ℕ}, M0 ≤ m → Squarefree d → 1 < d → 8 * d ∣ m →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬p ∣ m ∧
        (p : ℝ) ≤ (m : ℝ) ^ (31 / 64 : ℝ) ∧ QuadResidueMod d p := by
  obtain ⟨M0, hprime⟩ := exists_small_quadratic_residue_prime_cutoff
  refine ⟨M0, ?_⟩
  intro m d hm hd hdgt hdvd
  obtain ⟨p, hp, hp2, hpm, hpbound, hJ⟩ := hprime hm hd hdgt hdvd
  have : Fact p.Prime := ⟨hp⟩
  have hsq : IsSquare (d : ZMod p) := by
    simpa only [Int.cast_natCast] using ZMod.isSquare_of_jacobiSym_eq_one hJ
  exact ⟨p, hp, hp2, hpm, hpbound, quadResidueMod_of_isSquare_zmod hsq⟩

/-! ## Turning quadratic residuosity into solvability of `a*x^2 ≡ n [MOD p]` -/

/-- In the non-square case, The small-prime theorem gives `d` as a quadratic residue.  Combined with
`u^2*d = a*n` and `p ∤ a*n`, this yields solvability of `a*x^2 ≡ n [MOD p]`. -/
lemma solvable_of_squarefree_part
    {a n u d p : ℕ}
    (hdecomp : u ^ 2 * d = a * n)
    (hp : p.Prime)
    (hpn : ¬ p ∣ a * n)
    (hres : QuadResidueMod d p) :
    SolvableAX2EqNMod a n p := by
  obtain ⟨y, hy⟩ := hres
  have hpa : ¬ p ∣ a := by
    intro hpa
    exact hpn (dvd_mul_of_dvd_left hpa n)
  have hcop : Nat.Coprime a p := (hp.coprime_iff_not_dvd.2 hpa).symm
  have hfermat : Nat.ModEq p (a ^ (p - 1)) 1 :=
    Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  let b : ℕ := a * a ^ (p - 2)
  have hp2le : 2 ≤ p := hp.two_le
  have hp_sub : p - 1 = (p - 2) + 1 := by
    omega
  have hb : Nat.ModEq p b 1 := by
    dsimp [b]
    simpa [hp_sub, Nat.pow_add, pow_one, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      hfermat
  have hb2 : Nat.ModEq p (b ^ 2) 1 := by
    simpa using Nat.ModEq.pow 2 hb
  have hsq : Nat.ModEq p ((u * y) ^ 2) (a * n) := by
    have hmul : Nat.ModEq p (u ^ 2 * y ^ 2) (u ^ 2 * d) := hy.mul_left (u ^ 2)
    have hmul' : Nat.ModEq p ((u * y) ^ 2) (u ^ 2 * d) := by
      simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    rw [← hdecomp]
    exact hmul'
  let x : ℕ := u * y * a ^ (p - 2)
  have hax : Nat.ModEq p (a * x ^ 2) (n * b ^ 2) := by
    have hmul :
        Nat.ModEq p (((u * y) ^ 2) * (a ^ (p - 2)) ^ 2)
          ((a * n) * (a ^ (p - 2)) ^ 2) :=
      hsq.mul_right ((a ^ (p - 2)) ^ 2)
    have hmul' :
        Nat.ModEq p (a * (((u * y) ^ 2) * (a ^ (p - 2)) ^ 2))
          (a * ((a * n) * (a ^ (p - 2)) ^ 2)) :=
      hmul.mul_left a
    simpa [x, b, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul'
  have hnb : Nat.ModEq p (n * b ^ 2) n := by
    simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hb2.mul_left n
  exact ⟨x, hax.trans hnb⟩

/-- In the square case `a*n = u^2`, every odd prime `p ∤ a*n` makes `a*x^2 ≡ n [MOD p]`
solvable. -/
private lemma solvable_of_square_case
    {a n u p : ℕ}
    (hsq : u ^ 2 = a * n)
    (hp : p.Prime)
    (hpn : ¬ p ∣ a * n) :
    SolvableAX2EqNMod a n p := by
  have hdecomp : u ^ 2 * 1 = a * n := by
    simpa using hsq
  exact solvable_of_squarefree_part hdecomp hp hpn (one_is_quad_residue p)

/-! ## Candidate set bounds -/

/-- If `Pa a n` holds, then for any prime `p` there is at most one candidate `k`.
Indeed, `p ∣ n - a*k^2` and primality force `n - a*k^2 = p`, and that equation has at most one
positive solution in `k`. -/
private lemma candidateKs_card_le_one
    {a n p : ℕ}
    (ha : 1 ≤ a)
    (hPa : Pa a n)
    (hp : p.Prime) :
    (candidateKs a n p).card ≤ 1 := by
  refine Finset.card_le_one.2 ?_
  intro k1 hk1 k2 hk2
  rw [candidateKs, Finset.mem_filter] at hk1 hk2
  rcases hk1 with ⟨_, hk1_pos, hk1_lt, hk1_coprime, hk1_mod⟩
  rcases hk2 with ⟨_, hk2_pos, hk2_lt, hk2_coprime, hk2_mod⟩
  have hprime1 : Nat.Prime (n - a * k1 ^ 2) := hPa k1 hk1_pos hk1_coprime hk1_lt
  have hprime2 : Nat.Prime (n - a * k2 ^ 2) := hPa k2 hk2_pos hk2_coprime hk2_lt
  have hdiv1 : p ∣ n - a * k1 ^ 2 :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hk1_lt)).1 hk1_mod
  have hdiv2 : p ∣ n - a * k2 ^ 2 :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hk2_lt)).1 hk2_mod
  have hEq1 : p = n - a * k1 ^ 2 := (Nat.prime_dvd_prime_iff_eq hp hprime1).1 hdiv1
  have hEq2 : p = n - a * k2 ^ 2 := (Nat.prime_dvd_prime_iff_eq hp hprime2).1 hdiv2
  let t1 : ℕ := a * k1 ^ 2
  let t2 : ℕ := a * k2 ^ 2
  have ht1lt : t1 < n := by
    simpa [t1] using hk1_lt
  have ht2lt : t2 < n := by
    simpa [t2] using hk2_lt
  have ht1eq : p = n - t1 := by
    simpa [t1] using hEq1
  have ht2eq : p = n - t2 := by
    simpa [t2] using hEq2
  have ht12 : t1 = t2 := by
    omega
  have hsq_eq : k1 ^ 2 = k2 ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_le_iff.mp ha)
    simpa [t1, t2] using ht12
  exact Nat.pow_left_injective (show (2 : ℕ) ≠ 0 by decide) hsq_eq

/-! ### Counting helpers for `many_candidates_of_small_prime_size` -/

private lemma two_pow_primeFactors_card_le_rpow_eventually :
    ∃ Nω : ℕ, ∀ {n : ℕ}, Nω ≤ n →
      (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) ^ ((1 : ℝ) / 128) := by
  have hbound := eventually_divisors_card_le_rpow_uniform 256 (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hbound
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by have := (le_max_right N 1).trans hn; omega
  have htwo : (2 : ℝ) ^ n.primeFactors.card ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast two_pow_primeFactors_card_le_divisors_card n hn0
  have hdiv := hN n ((le_max_left N 1).trans hn) n hn0 le_rfl
  norm_num at hdiv
  exact htwo.trans hdiv

private lemma nat_rpow_div_log_eventually_large (N : ℝ) :
    ∃ N0 : ℕ, 3 ≤ N0 ∧ ∀ n : ℕ, N0 ≤ n →
      N ≤ (n : ℝ) ^ ((1 : ℝ) / 128) / (3 * Real.log n) := by
  have h_tend : Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 128) / (3 * Real.log n))
      Filter.atTop Filter.atTop := by
    have h_aux : Filter.Tendsto (fun u : ℝ ↦ Real.exp u / (384 * u)) Filter.atTop Filter.atTop := by
      have h1 : Filter.Tendsto (fun u : ℝ ↦ Real.exp u / u) Filter.atTop Filter.atTop := by
        simpa using Real.tendsto_exp_div_pow_atTop 1
      convert Filter.Tendsto.atTop_div_const (show 0 < (384 : ℝ) by norm_num) h1 using 1 with u
      ring_nf
    have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log n / 128) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.atTop_div_const (show 0 < (128 : ℝ) by norm_num) <|
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact (h_aux.comp hlog).congr' (by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hlog128 : Real.log n / 128 = Real.log n * ((1 : ℝ) / 128) := by ring
      have hden' : 384 * (Real.log n * ((1 : ℝ) / 128)) = 3 * Real.log n := by ring
      simp only [Function.comp_apply]
      rw [Real.rpow_def_of_pos hn', hlog128, hden'])
  rcases Filter.eventually_atTop.1 (h_tend.eventually_ge_atTop N) with ⟨N0, hN0⟩
  refine ⟨max N0 3, le_max_right _ _, ?_⟩
  intro n hn
  exact hN0 n (le_trans (le_max_left _ _) hn)

private lemma mem_finset_inf_iff {ι α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset ι} {f : ι → Finset α} {a : α} :
    a ∈ s.inf f ↔ ∀ i ∈ s, a ∈ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert b s hb ih =>
      simp [Finset.inf_insert, ih]

private lemma mertens_primeFactors_lower_bound {n : ℕ} (hn3 : 3 ≤ n) :
    1 / (3 * Real.log n)
      ≤ ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
  let t : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime
  let f : ℕ → ℝ := fun q ↦ 1 - 1 / (q : ℝ)
  have hsubset : n.primeFactors ⊆ t := by
    intro q hq
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primeFactors hq)),
      Nat.prime_of_mem_primeFactors hq⟩
  have hfactor_nonneg : ∀ q ∈ t, 0 ≤ f q := by
    intro q hq
    have hqprime : Nat.Prime q := (Finset.mem_filter.mp hq).2
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
    have hq_ge1 : (1 : ℝ) ≤ q := by exact_mod_cast hqprime.one_le
    have hdiv_le : 1 / (q : ℝ) ≤ 1 :=
      by simpa using (one_div_le_one_div_of_le zero_lt_one hq_ge1)
    nlinarith
  have hfactor_le_one : ∀ q ∈ t, f q ≤ 1 := by
    intro q hq
    have hdiv_nonneg : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
    nlinarith
  have hs_nonneg : 0 ≤ ∏ q ∈ n.primeFactors, f q := by
    refine Finset.prod_nonneg ?_
    intro q hq
    exact hfactor_nonneg q (hsubset hq)
  have hextra_le_one : ∏ q ∈ t \ n.primeFactors, f q ≤ 1 := by
    refine Finset.prod_le_one ?_ ?_
    · intro q hq
      exact hfactor_nonneg q (Finset.mem_sdiff.mp hq).1
    · intro q hq
      exact hfactor_le_one q (Finset.mem_sdiff.mp hq).1
  have hprod_le : ∏ q ∈ t, f q ≤ ∏ q ∈ n.primeFactors, f q := by
    calc
      ∏ q ∈ t, f q = (∏ q ∈ t \ n.primeFactors, f q) * ∏ q ∈ n.primeFactors, f q := by
        symm
        exact Finset.prod_sdiff hsubset
      _ ≤ 1 * ∏ q ∈ n.primeFactors, f q := by
        exact mul_le_mul_of_nonneg_right hextra_le_one hs_nonneg
      _ = ∏ q ∈ n.primeFactors, f q := by simp
  have hmertens : 1 / (3 * Real.log n) ≤ ∏ q ∈ t, f q := by
    simpa [t, f] using mertens_third_theorem n hn3
  exact le_trans hmertens hprod_le

/-- Main counting lemma.

For fixed `a`, if `p` is an odd prime of the stated size, `p ∤ a*n`, and
`a*x^2 ≡ n [MOD p]` is solvable, then for all sufficiently large `n`
there are more than one candidates.

This is exactly where the Möbius-inversion count and `mertens_third_theorem` enter.
In this formalization, it is enough to count one chosen root class modulo `p`; the
factor `2` from the paper is not needed. -/
private lemma many_candidates_of_small_prime_size
    (a : ℕ)
    (ha : 1 ≤ a) :
    ∃ N0 : ℕ, ∀ {n p : ℕ},
      N0 ≤ n →
      p.Prime →
      p ≠ 2 →
      ¬ p ∣ a * n →
      SolvableAX2EqNMod a n p →
      (p : ℝ) ≤ smallPrimeSizeBound a n →
      1 < (candidateKs a n p).card := by
  classical
  obtain ⟨Nω, hω⟩ := two_pow_primeFactors_card_le_rpow_eventually
  obtain ⟨Nmain, hNmain_ge3, hmain⟩ := nat_rpow_div_log_eventually_large (96 * a)
  refine ⟨max Nω Nmain, ?_⟩
  intro n p hn hp hp2 hpndvd hsol hpbound
  have hnω : Nω ≤ n := le_trans (le_max_left _ _) hn
  have hnmain : Nmain ≤ n := le_trans (le_max_right _ _) hn
  have hn3 : 3 ≤ n := le_trans hNmain_ge3 hnmain
  have hn0 : n ≠ 0 := by omega
  let x : ℕ := Classical.choose hsol
  have hx : Nat.ModEq p (a * x ^ 2) n := Classical.choose_spec hsol
  let r : ℕ := x % p
  have hr_root : Nat.ModEq p (a * r ^ 2) n := by
    have hxr : Nat.ModEq p r x := Nat.mod_modEq x p
    exact ((Nat.ModEq.pow 2 hxr).mul_left a).trans hx
  have hr_lt_p : r < p := by
    dsimp [r]
    exact Nat.mod_lt _ hp.pos
  have hr_ne_zero : r ≠ 0 := by
    intro hr0
    have hmod : Nat.ModEq p n 0 := by
      simpa [r, hr0] using hr_root.symm
    have hpdvdn : p ∣ n := (Nat.modEq_zero_iff_dvd.mp hmod)
    exact hpndvd (dvd_mul_of_dvd_right hpdvdn a)
  let K : ℕ := Nat.sqrt ((n - 1) / a) + 1
  let U : Finset ℕ := ((Finset.range K).filter fun k ↦ Nat.ModEq p k r)
  let α := {k : ℕ // k ∈ U}
  let emb : α ↪ ℕ :=
    ⟨Subtype.val, by
      intro x y h
      exact Subtype.ext h⟩
  let S : ℕ → Finset α := fun q ↦ (Finset.univ : Finset α).filter fun k ↦ q ∣ (k : ℕ)
  let good : Finset α := n.primeFactors.inf fun q ↦ (S q)ᶜ
  have hgood_sub : good.map emb ⊆ candidateKs a n p := by
    intro k hk
    rcases Finset.mem_map.mp hk with ⟨y, hy, rfl⟩
    have hyU : (y : ℕ) ∈ U := y.property
    have hy_ltK : (y : ℕ) < K := by
      simpa [U] using (Finset.mem_filter.mp hyU).1
    have hy_mod : Nat.ModEq p (y : ℕ) r := by
      simpa [U] using (Finset.mem_filter.mp hyU).2
    have hy_notdvd : ∀ q ∈ n.primeFactors, ¬ q ∣ (y : ℕ) := by
      intro q hq
      have hyq : y ∈ (S q)ᶜ :=
        (mem_finset_inf_iff (s := n.primeFactors) (f := fun q ↦ (S q)ᶜ) (a := y)).1 hy q hq
      simpa [S] using hyq
    have hy_ne_zero : (y : ℕ) ≠ 0 := by
      intro hy0
      have hzr : Nat.ModEq p 0 r := by simpa [hy0] using hy_mod
      have hpdvdr : p ∣ r := Nat.modEq_zero_iff_dvd.mp hzr.symm
      exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hr_ne_zero) hr_lt_p) hpdvdr
    have hy_pos : 1 ≤ (y : ℕ) := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hy_ne_zero)
    have hy_disj : Disjoint (y : ℕ).primeFactors n.primeFactors := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      exact hy_notdvd q hq2 (Nat.dvd_of_mem_primeFactors hq1)
    have hy_coprime : Nat.Coprime (y : ℕ) n := by
      exact (Nat.disjoint_primeFactors hy_ne_zero hn0).mp hy_disj
    have hy_le_sqrt : (y : ℕ) ≤ Nat.sqrt ((n - 1) / a) := by
      simpa [K] using Nat.lt_succ_iff.mp hy_ltK
    have hy_sq_le : (y : ℕ) ^ 2 ≤ (n - 1) / a := (Nat.le_sqrt'.mp hy_le_sqrt)
    have hy_quad_le : a * (y : ℕ) ^ 2 ≤ n - 1 := by
      exact le_trans (Nat.mul_le_mul_left a hy_sq_le) (Nat.mul_div_le (n - 1) a)
    have hy_pred_lt : n - 1 < n := by
      have hnpos : 0 < n := by omega
      rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)]
      exact Nat.lt_succ_self _
    have hy_quad : a * (y : ℕ) ^ 2 < n := lt_of_le_of_lt hy_quad_le hy_pred_lt
    have hy_sq_lt_n : (y : ℕ) ^ 2 < n := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ ha) hy_quad
    have hy_lt_n : (y : ℕ) < n := by
      have hy_le_sq : (y : ℕ) ≤ (y : ℕ) ^ 2 := by
        simpa [pow_two] using Nat.le_mul_of_pos_right (y : ℕ) (Nat.pos_of_ne_zero hy_ne_zero)
      exact lt_of_le_of_lt hy_le_sq hy_sq_lt_n
    have hy_root : Nat.ModEq p (a * (y : ℕ) ^ 2) n := by
      exact (((Nat.ModEq.pow 2 hy_mod).mul_left a).trans hr_root)
    rw [candidateKs, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hy_lt_n, hy_pos, hy_quad, hy_coprime, hy_root⟩
  have hlower : ((good.map emb).card : ℝ)
      ≥ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card := by
    simpa [U, α, emb, S, good, K] using
      (Sieve.root_class_good_count_lower_bound (n := n) (p := p) (r := r) (K := K)
        hn0 hp.ne_zero (hp.coprime_iff_not_dvd.mpr
          (fun hpn ↦ hpndvd (dvd_mul_of_dvd_right hpn a))))
  have hmertens : 1 / (3 * Real.log n)
      ≤ ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) :=
    mertens_primeFactors_lower_bound hn3
  have hmain' : (96 * a : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 128) / (3 * Real.log n) := hmain n hnmain
  have hω' : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) ^ ((1 : ℝ) / 128) := hω hnω
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp_le : p ≤ (8 * a * n : ℝ) ^ ((31 : ℝ) / 64) := by
    simpa [smallPrimeSizeBound] using hpbound
  have hK_over_p : (2 : ℝ) + (2 : ℝ) ^ n.primeFactors.card
      ≤ (K : ℝ) / p * (1 / (3 * Real.log n)) := by
    have ha_pos_nat : 0 < a := by omega
    have hn_pos_nat : 0 < n := by omega
    have ha_pos : (0 : ℝ) < a := by exact_mod_cast ha_pos_nat
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
    have hnpow128_pos : 0 < (n : ℝ) ^ ((1 : ℝ) / 128) := by positivity
    have h8a_ne : (8 * a : ℝ) ≠ 0 := by positivity
    have hpow128_ne : (n : ℝ) ^ ((1 : ℝ) / 128) ≠ 0 := hnpow128_pos.ne'
    have hKp_lower : (n : ℝ) ^ ((1 : ℝ) / 64) / (8 * a) ≤ (K : ℝ) / p := by
      have hKsq_nat : ((n - 1) / a + 1) ≤ K ^ 2 := by
        dsimp [K]
        simpa [pow_two] using Nat.succ_le_succ_sqrt' ((n - 1) / a)
      have hn_le_div_nat : n ≤ a * (((n - 1) / a) + 1) := by
        have hlt : n - 1 < a * (((n - 1) / a) + 1) := by
          calc
            n - 1 = a * ((n - 1) / a) + ((n - 1) % a) := by
              simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                (Nat.div_add_mod' (n - 1) a).symm
            _ < a * ((n - 1) / a) + a := by
              exact Nat.add_lt_add_left (Nat.mod_lt _ ha_pos_nat) _
            _ = a * (((n - 1) / a) + 1) := by ring
        rw [← Nat.succ_pred_eq_of_pos hn_pos_nat]
        exact Nat.succ_le_of_lt hlt
      have hn_le_aKsq_nat : n ≤ a * K ^ 2 := by
        calc
          n ≤ a * (((n - 1) / a) + 1) := hn_le_div_nat
          _ ≤ a * K ^ 2 := Nat.mul_le_mul_left _ hKsq_nat
      have hn_le_aKsq : (n : ℝ) ≤ a * (K : ℝ) ^ 2 := by
        exact_mod_cast hn_le_aKsq_nat
      have hna_div : (n : ℝ) / a ≤ (K : ℝ) ^ 2 := by
        exact (div_le_iff₀ ha_pos).2 <| by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hn_le_aKsq
      have hsqrt_leK : ((n : ℝ) / a) ^ ((1 : ℝ) / 2) ≤ K := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
        exact ⟨by positivity, hna_div⟩
      have hmid :
          ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / (8 * a * n : ℝ) ^ ((31 : ℝ) / 64)
            ≤ (K : ℝ) / p := by
        have h1 :
            ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / (8 * a * n : ℝ) ^ ((31 : ℝ) / 64)
              ≤ ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / p := by
          exact div_le_div_of_nonneg_left (by positivity) hp_pos hp_le
        have h2 :
            ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / p ≤ (K : ℝ) / p := by
          exact div_le_div_of_nonneg_right hsqrt_leK hp_pos.le
        exact le_trans h1 h2
      have hbase :
          (n : ℝ) ^ ((1 : ℝ) / 64) / (8 * a)
            ≤ ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / (8 * a * n : ℝ) ^ ((31 : ℝ) / 64) := by
        have h8a_pos : 0 < (8 * a : ℝ) := by positivity
        have h8an_pos : 0 < (8 * a * n : ℝ) ^ ((31 : ℝ) / 64) := by positivity
        rw [div_le_div_iff₀ h8a_pos h8an_pos]
        have hrewrite :
            (8 * a * n : ℝ) ^ ((31 : ℝ) / 64)
              = ((8 : ℝ) * a) ^ ((31 : ℝ) / 64) * (n : ℝ) ^ ((31 : ℝ) / 64) := by
          have hmul : (8 * a * n : ℝ) = ((8 : ℝ) * a) * n := by ring
          rw [hmul, Real.mul_rpow (by positivity) (by positivity)]
        have hdivrpow :
            ((n : ℝ) / a) ^ ((1 : ℝ) / 2)
              = (n : ℝ) ^ ((1 : ℝ) / 2) / (a : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [Real.div_rpow (by positivity) (by positivity)]
        have hncombine :
            (n : ℝ) ^ ((1 : ℝ) / 64) * (n : ℝ) ^ ((31 : ℝ) / 64)
              = (n : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add hn_pos]
          norm_num
        have hahalf :
            (a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2) = (a : ℝ) ^ ((1 : ℝ) / 2) := by
          have hsub :
              (a : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 2)
                = (a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [Real.rpow_sub ha_pos, Real.rpow_one]
          calc
            (a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2)
                = (a : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 2) := by simpa using hsub.symm
            _ = (a : ℝ) ^ ((1 : ℝ) / 2) := by norm_num
        have hconst :
            ((8 : ℝ) * a) ^ ((31 : ℝ) / 64) ≤ (8 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2) := by
          calc
            ((8 : ℝ) * a) ^ ((31 : ℝ) / 64)
                = (8 : ℝ) ^ ((31 : ℝ) / 64) * (a : ℝ) ^ ((31 : ℝ) / 64) := by
                    rw [Real.mul_rpow (by positivity) (by positivity)]
            _ ≤ (8 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2) := by
              have h8 : (8 : ℝ) ^ ((31 : ℝ) / 64) ≤ 8 := by
                have htmp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8)
                  (by norm_num : (31 : ℝ) / 64 ≤ 1)
                simpa [Real.rpow_one] using htmp
              have haexp : (a : ℝ) ^ ((31 : ℝ) / 64) ≤ (a : ℝ) ^ ((1 : ℝ) / 2) := by
                have ha_one : (1 : ℝ) ≤ a := by exact_mod_cast ha
                exact Real.rpow_le_rpow_of_exponent_le ha_one
                  (by norm_num : (31 : ℝ) / 64 ≤ (1 : ℝ) / 2)
              exact mul_le_mul h8 haexp (by positivity) (by positivity)
        rw [hrewrite, hdivrpow]
        calc
          (n : ℝ) ^ ((1 : ℝ) / 64) *
              (((8 : ℝ) * a) ^ ((31 : ℝ) / 64) * (n : ℝ) ^ ((31 : ℝ) / 64))
              = ((8 : ℝ) * a) ^ ((31 : ℝ) / 64) *
                  ((n : ℝ) ^ ((1 : ℝ) / 64) * (n : ℝ) ^ ((31 : ℝ) / 64)) := by ring
          _ = ((8 : ℝ) * a) ^ ((31 : ℝ) / 64) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [hncombine]
          _ = (n : ℝ) ^ ((1 : ℝ) / 2) * (((8 : ℝ) * a) ^ ((31 : ℝ) / 64)) := by ring
          _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * ((8 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2)) := by
            exact mul_le_mul_of_nonneg_left hconst (by positivity)
          _ = ((n : ℝ) ^ ((1 : ℝ) / 2) / (a : ℝ) ^ ((1 : ℝ) / 2)) * ((8 : ℝ) * a) := by
            calc
              (n : ℝ) ^ ((1 : ℝ) / 2) * ((8 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2))
                  = (8 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) * (a : ℝ) ^ ((1 : ℝ) / 2) := by ring
              _ = (8 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) *
                    ((a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2)) := by rw [hahalf]
              _ = ((n : ℝ) ^ ((1 : ℝ) / 2) / (a : ℝ) ^ ((1 : ℝ) / 2)) * ((8 : ℝ) * a) := by
                ring
      exact le_trans hbase hmid
    have hlog_lower : (96 * a : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 128) ≤ 1 / (3 * Real.log n) := by
      have hmain'' : (96 * a : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 128) * (1 / (3 * Real.log n)) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmain'
      have hmain''' : (96 * a : ℝ) ≤ (1 / (3 * Real.log n)) * (n : ℝ) ^ ((1 : ℝ) / 128) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmain''
      exact (div_le_iff₀ hnpow128_pos).2 hmain'''
    have hpow64_eq :
        (n : ℝ) ^ ((1 : ℝ) / 64)
          = (n : ℝ) ^ ((1 : ℝ) / 128) * (n : ℝ) ^ ((1 : ℝ) / 128) := by
      rw [show ((1 : ℝ) / 64) = (1 : ℝ) / 128 + (1 : ℝ) / 128 by norm_num]
      rw [Real.rpow_add hn_pos]
    have hprod_eq :
        ((n : ℝ) ^ ((1 : ℝ) / 64) / (8 * a)) *
            ((96 * a : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 128))
          = 12 * (n : ℝ) ^ ((1 : ℝ) / 128) := by
      rw [hpow64_eq]
      field_simp [h8a_ne, hpow128_ne]
      ring
    have h12 :
        12 * (n : ℝ) ^ ((1 : ℝ) / 128)
          ≤ (K : ℝ) / p * (1 / (3 * Real.log n)) := by
      have hmul := mul_le_mul hKp_lower hlog_lower (by positivity) (by positivity)
      rw [hprod_eq] at hmul
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hn128_ge_one : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 128) := by
      have hn_one : (1 : ℝ) ≤ n := by
        exact_mod_cast (show 1 ≤ n by omega)
      simpa using Real.rpow_le_rpow_of_exponent_le hn_one
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 128)
    have hlhs : (2 : ℝ) + (2 : ℝ) ^ n.primeFactors.card
        ≤ 3 * (n : ℝ) ^ ((1 : ℝ) / 128) := by
      have h2le : (2 : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 128) := by
        nlinarith
      linarith
    have h3 : 3 * (n : ℝ) ^ ((1 : ℝ) / 128)
        ≤ (K : ℝ) / p * (1 / (3 * Real.log n)) := by
      nlinarith [h12, hnpow128_pos]
    exact le_trans hlhs h3
  have hcard_ge : (2 : ℝ) ≤ (good.map emb).card := by
    have htmp : (2 : ℝ) + (2 : ℝ) ^ n.primeFactors.card
        ≤ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
      exact le_trans hK_over_p (mul_le_mul_of_nonneg_left hmertens (by positivity))
    linarith [hlower, htmp]
  have hmap_le : (good.map emb).card ≤ (candidateKs a n p).card := Finset.card_le_card hgood_sub
  have hge_nat : 2 ≤ (candidateKs a n p).card := by
    exact le_trans (by exact_mod_cast hcard_ge) hmap_le
  exact lt_of_lt_of_le (by decide : 1 < 2) hge_nat

/-- Contradiction engine for the nonsquare case.

Once we have one odd prime `p` of the stated size such that `p ∤ a*n` and
`a*x^2 ≡ n [MOD p]` is solvable, the counting argument rules out `Pa a n`. -/
private lemma not_Pa_of_good_prime
    (a : ℕ) (ha : 1 ≤ a) :
    ∃ N0 : ℕ, ∀ {n p : ℕ},
      N0 ≤ n →
      p.Prime →
      p ≠ 2 →
      ¬ p ∣ a * n →
      SolvableAX2EqNMod a n p →
      (p : ℝ) ≤ smallPrimeSizeBound a n →
      ¬ Pa a n := by
  obtain ⟨N0, hcount⟩ := many_candidates_of_small_prime_size a ha
  refine ⟨N0, ?_⟩
  intro n p hn hp hp2 hpndvd hsol hpbound hPa
  have hgt : 1 < (candidateKs a n p).card :=
    hcount hn hp hp2 hpndvd hsol hpbound
  have hle : (candidateKs a n p).card ≤ 1 :=
    candidateKs_card_le_one ha hPa hp
  exact not_lt_of_ge hle hgt


/-! ## An elementary square-case argument -/

/-- The square case needs only the test at `k = 1`. -/
theorem not_Pa_of_square_large {a n u : ℕ} (ha : 1 ≤ a)
    (hn : 4 * a < n) (hsq : u ^ 2 = a * n) : ¬ Pa a n := by
  intro hPa
  have han : a < n := by omega
  have hprime : (n - a).Prime := by
    simpa using hPa 1 (by decide) (by simp) (by simpa using han)
  have hau : 2 * a < u := by
    by_contra! h
    have hmul := Nat.mul_self_le_mul_self h
    nlinarith
  have hau' : a ≤ u := by omega
  have hprod : (u + a) * (u - a) = a * (n - a) := by
    rw [← Nat.sq_sub_sq, hsq, Nat.mul_sub, pow_two]
  have hdiv : n - a ∣ (u + a) * (u - a) := by
    rw [hprod]
    exact dvd_mul_left _ _
  have hp_le : n - a ≤ u + a := by
    rcases hprime.dvd_mul.mp hdiv with h | h
    · exact Nat.le_of_dvd (by omega) h
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
  have hsub := Nat.sub_add_cancel han.le
  have hmul₁ := Nat.mul_lt_mul_of_pos_left hau (by omega : 0 < u)
  have hmul₂ := Nat.mul_lt_mul_of_pos_left hau (by omega : 0 < a)
  nlinarith

/-- The nonsquare-coefficient specialization of the elementary square case. -/
lemma square_case_nonsquare_coeff_impossible_of_coeff
    (a v d : ℕ) (ha : 1 ≤ a) (_hdSq : Squarefree d) (_hdGt : 1 < d)
    (_hadecomp : v ^ 2 * d = a) :
    ∃ N0 : ℕ, ∀ {n u : ℕ}, N0 ≤ n → u ^ 2 = a * n → ¬ Pa a n := by
  exact ⟨4 * a + 1, fun hn hsq ↦ not_Pa_of_square_large ha (by omega) hsq⟩

/-- The square-coefficient specialization of the elementary square case. -/
lemma square_case_square_coeff_impossible_of_coeff
    (a v : ℕ) (ha : 1 ≤ a) (_haSq : a = v ^ 2) :
    ∃ N0 : ℕ, ∀ {n u : ℕ}, N0 ≤ n → u ^ 2 = a * n → ¬ Pa a n := by
  exact ⟨4 * a + 1, fun hn hsq ↦ not_Pa_of_square_large ha (by omega) hsq⟩

/-! ## The two contradiction arguments -/

/-- Case 1: the squarefree part `d` of `a*n` is `> 1`.

The only nontrivial input is the existence of one small residue prime; once that is in hand,
the rest is again delegated to `not_Pa_of_good_prime`. -/
lemma case1_non_square_impossible
    (a : ℕ)
    (ha : 1 ≤ a) :
    ∃ N1 : ℕ, ∀ {n u d : ℕ},
      N1 ≤ n →
      Squarefree d →
      1 < d →
      u ^ 2 * d = a * n →
      ¬ Pa a n := by
  obtain ⟨M0, hPrime⟩ := exists_small_residue_prime
  obtain ⟨Nbad, hbad⟩ := not_Pa_of_good_prime a ha
  refine ⟨max M0 Nbad, ?_⟩
  intro n u d hn hdSq hdGt hdecomp
  have hm : M0 ≤ 8 * a * n := by
    exact le_trans (le_trans (le_max_left _ _) hn) (le_residue_modulus ha)
  have hdvd : 8 * d ∣ 8 * a * n :=
    squarefree_factor_dvd_residue_modulus hdecomp
  obtain ⟨p, hp, hp2, hpndvdMod, hpbound, hres⟩ := hPrime hm hdSq hdGt hdvd
  have hpndvd : ¬ p ∣ a * n := not_dvd_an_of_not_dvd_residue_modulus hpndvdMod
  have hsol : SolvableAX2EqNMod a n p :=
    solvable_of_squarefree_part hdecomp hp hpndvd hres
  exact hbad (le_trans (le_max_right _ _) hn) hp hp2 hpndvd hsol (by
    simpa [smallPrimeSizeBound] using hpbound)

/-- Case 2: `a*n` is a square. The explicit cutoff needs no analytic input. -/
lemma case2_square_impossible
    (a : ℕ) (ha : 1 ≤ a) :
    ∃ N2 : ℕ, ∀ {n u : ℕ}, N2 ≤ n → u ^ 2 = a * n → ¬ Pa a n := by
  exact ⟨4 * a + 1, fun hn hsq ↦ not_Pa_of_square_large ha (by omega) hsq⟩

/-! ## Main theorem -/

/-- Eventual failure of `Pa a n` for every fixed `a ≥ 1`. -/
theorem eventually_not_Pa (a : ℕ) (ha : 1 ≤ a) :
    ∃ N : ℕ, ∀ {n : ℕ}, N ≤ n → ¬ Pa a n := by
  obtain ⟨N1, h1⟩ := case1_non_square_impossible a ha
  obtain ⟨N2, h2⟩ := case2_square_impossible a ha
  refine ⟨max N1 N2, ?_⟩
  intro n hn hPa
  obtain ⟨u, d, hdecomp, hdSq⟩ := exists_squarefree_factorization (a * n)
  by_cases hd1 : d = 1
  · have hsq : u ^ 2 = a * n := by
      simpa [hd1] using hdecomp
    exact h2 (le_trans (le_max_right _ _) hn) hsq hPa
  · have hdGt : 1 < d := one_lt_of_squarefree_ne_one hdSq hd1
    exact h1 (le_trans (le_max_left _ _) hn) hdSq hdGt hdecomp hPa

/-- General finite-set formulation of the theorem. -/
theorem erdos_1141_variant_general (a : ℕ) (ha : 1 ≤ a) :
    Set.Finite {n : ℕ | Pa a n} := by
  obtain ⟨N, hN⟩ := eventually_not_Pa a ha
  refine (Set.finite_lt_nat N).subset ?_
  intro n hn
  by_contra hlt
  exact hN (n := n) (Nat.le_of_not_lt hlt) hn

/-- Paper-style `Pa` statement for `a = 1`, stronger than the Formal Conjectures
statement `not_erdos_1141` below. -/
theorem erdos_1141_variant : Set.Finite {n : ℕ | Pa 1 n} := by
  simpa using erdos_1141_variant_general 1 (by decide : 1 ≤ 1)

/-- info: 'Erdos1141b.erdos_1141_variant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erdos_1141_variant

/-! ## Block Copied from Formal Conjectures -/

/-
The following block is copied as literally as possible from
https://github.com/google-deepmind/formal-conjectures/blob/main/
FormalConjectures/ErdosProblems/1141.lean
with only the proof of `not_erdos_1141` filled in via the stronger theorem
`erdos_1141_variant` above.
-/

open Nat Set

/--
The property that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$.
-/
def Erdos1141Prop (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime

instance (n : ℕ) : Decidable (Erdos1141Prop n) :=
  decidable_of_iff (∀ k ≤ .sqrt (n - 1), Coprime n k → (n - k ^ 2).Prime) <| by
    cases n with
    | zero => simp [Erdos1141Prop]
    | succ n' =>
      simp [Erdos1141Prop, Nat.le_sqrt, pow_two]

theorem erdos1141Prop_iff_pa_one_ne_one (n : ℕ) :
    Erdos1141Prop n ↔ Pa 1 n ∧ n ≠ 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro k hk hcop hlt
      simpa [one_mul] using h k (by simpa [one_mul] using hlt) hcop.symm
    · intro hn
      have h0 := h 0 (by simp [hn]) (by simp [hn])
      have h1 : Nat.Prime 1 := by simpa [hn] using h0
      exact Nat.not_prime_one h1
  · rintro ⟨hPa, hn1⟩ k hk hcop
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exfalso
      have : ¬ Coprime n 0 := by simpa [Nat.coprime_zero_right] using hn1
      exact this hcop
    · simpa [one_mul] using hPa k hkpos hcop.symm (by simpa [one_mul] using hk)

/--
Are there infinitely many $n$ such that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$?

In [Va99] it is asked whether $968$ is the largest integer with this property, but this is an
error, since for example $968-9=7\cdot 137$.

The list of $n$ satisfying the given property is [A214583] in the OEIS. The largest known such $n$
is $1722$.
-/
theorem not_erdos_1141 :
    ¬ Infinite { n | Erdos1141Prop n } := by
  have hsubset : { n | Erdos1141Prop n } ⊆ { n | Pa 1 n } := by
    intro n hn
    exact (erdos1141Prop_iff_pa_one_ne_one n).1 hn |>.1
  exact Finite.not_infinite (erdos_1141_variant.subset hsubset).to_subtype

/-- info: 'Erdos1141b.not_erdos_1141' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_erdos_1141

end Erdos1141b

alias _root_.Erdos1141b.erdos_1141b := _root_.Erdos1141b.not_erdos_1141
