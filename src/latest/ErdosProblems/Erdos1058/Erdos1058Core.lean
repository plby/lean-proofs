/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Prime
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 1058

Let `2 = p₁ < p₂ < ⋯` be the primes.  This file formalizes Florian Luca's
classification of the positive integers `n` for which, when
`pₖ₋₁ ≤ n < pₖ`, every prime divisor of `n! + 1` is one of `pₖ, pₖ₊₁`.
The only such integers are `1, 2, 3, 4, 5`.

The prime enumeration below is zero-indexed: `primeAt 0 = 2`.  Consequently,
`lowerEndpoint 0 = 1` supplies the conventional left endpoint needed for
the solution `n = 1`.
-/

namespace Erdos1058

open Nat

noncomputable section

/-- The zero-indexed increasing sequence `2, 3, 5, 7, 11, ...` of primes. -/
noncomputable abbrev primeAt (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- The left endpoint preceding `primeAt k`, with the conventional value `1`
for the first prime interval. -/
def lowerEndpoint : ℕ → ℕ
  | 0 => 1
  | k + 1 => primeAt k

/-- The literal prime-divisor formulation of Erdős Problem 1058. -/
def IsSolution (n : ℕ) : Prop :=
  0 < n ∧ ∃ k,
    lowerEndpoint k ≤ n ∧ n < primeAt k ∧
      ∀ r, r.Prime → r ∣ n.factorial + 1 →
        r = primeAt k ∨ r = primeAt (k + 1)

/-- `p` is the least prime strictly larger than `n`. -/
def IsFirstPrimeAfter (n p : ℕ) : Prop :=
  n < p ∧ p.Prime ∧ ∀ r, r.Prime → n < r → p ≤ r

lemma primeAt_prime (k : ℕ) : (primeAt k).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k

lemma primeAt_strictMono : StrictMono primeAt :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

lemma primeAt_ne_succ (k : ℕ) : primeAt k ≠ primeAt (k + 1) :=
  _root_.ne_of_lt (primeAt_strictMono (Nat.lt_succ_self k))

lemma IsFirstPrimeAfter.unique {n p q : ℕ}
    (hp : IsFirstPrimeAfter n p) (hq : IsFirstPrimeAfter n q) : p = q :=
  Nat.le_antisymm (hp.2.2 q hq.2.1 hq.1) (hq.2.2 p hp.2.1 hp.1)

/-- The interval convention really makes `primeAt k` the first prime after
`n`; this is the bridge from the indexed statement to executable finite
prime searches. -/
lemma primeAt_isFirstPrimeAfter {n k : ℕ}
    (hlo : lowerEndpoint k ≤ n) (hhi : n < primeAt k) :
    IsFirstPrimeAfter n (primeAt k) := by
  refine ⟨hhi, primeAt_prime k, ?_⟩
  intro r hr hnr
  cases k with
  | zero =>
      simpa [primeAt] using hr.two_le
  | succ k =>
      have hpkn : primeAt k ≤ n := by simpa [lowerEndpoint] using hlo
      have hpkr : primeAt k < r := lt_of_le_of_lt hpkn hnr
      apply (Nat.isLeast_nth_of_infinite Nat.infinite_setOfPred_prime (k + 1)).2
      refine ⟨hr, ?_⟩
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hi)
      exact lt_of_le_of_lt (primeAt_strictMono.monotone hik) hpkr

lemma next_primeAt_isFirstPrimeAfter (k : ℕ) :
    IsFirstPrimeAfter (primeAt k) (primeAt (k + 1)) := by
  apply primeAt_isFirstPrimeAfter (n := primeAt k)
  · simp [lowerEndpoint]
  · exact primeAt_strictMono (Nat.lt_succ_self k)

/-- Executable bounded search used for the finite part of Luca's argument. -/
def boundedFirstPrimeAfter (bound n : ℕ) : ℕ :=
  ((List.range (bound + 1)).find? fun m => decide (n < m ∧ m.Prime)).getD 0

/-- The search bound `400` is sufficient whenever its input is below `211`.
The proof is generic: `211` is a prime candidate, and the order of
`List.range` makes the returned candidate minimal. -/
lemma boundedFirstPrimeAfter_spec (n : ℕ) (hn : n < 211) :
    IsFirstPrimeAfter n (boundedFirstPrimeAfter 400 n) := by
  let pred : ℕ → Bool := fun m => decide (n < m ∧ m.Prime)
  have h211mem : 211 ∈ List.range 401 := by simp
  have h211pred : pred 211 = true := by
    simp [pred, hn]
    norm_num
  generalize hopt : (List.range 401).find? pred = opt
  cases opt with
  | none =>
      have hfalse := (List.find?_eq_none.mp hopt) 211 h211mem h211pred
      contradiction
  | some p =>
      have hresult : boundedFirstPrimeAfter 400 n = p := by
        simpa [boundedFirstPrimeAfter, pred] using
          congrArg (fun o : Option ℕ => o.getD 0) hopt
      rw [hresult]
      have hpbool : pred p = true := List.find?_some hopt
      have hp : n < p ∧ p.Prime := by simpa [pred] using hpbool
      refine ⟨hp.1, hp.2, ?_⟩
      intro r hr hnr
      by_contra hpr
      have hrp : r < p := by omega
      rcases (List.find?_eq_some_iff_getElem.mp hopt).2 with ⟨i, hi, hip, hminimal⟩
      have hip' : i = p := by simpa only [List.getElem_range hi] using hip
      subst i
      have hnot := hminimal r hrp
      have hrbool : pred r = true := by simp [pred, hr, hnr]
      simp [hrbool] at hnot

lemma IsFirstPrimeAfter.le_two_mul {n p : ℕ}
    (hp : IsFirstPrimeAfter n p) (hn : n ≠ 0) : p ≤ 2 * n := by
  obtain ⟨r, hrprime, hnr, hrle⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  exact (hp.2.2 r hrprime hnr).trans hrle

/-- Bertrand's postulate, applied twice, bounds the first two primes after
`n` by `2n` and `4n`. -/
lemma first_two_primes_le_four_mul {n p q : ℕ}
    (hp : IsFirstPrimeAfter n p) (hq : IsFirstPrimeAfter p q) (hn : n ≠ 0) :
    p ≤ 2 * n ∧ q ≤ 4 * n := by
  have hp2 := hp.le_two_mul hn
  have hp0 : p ≠ 0 := hp.2.1.ne_zero
  have hq2 := hq.le_two_mul hp0
  constructor
  · exact hp2
  · omega

/-! ## Cubic residues

The finite part of Luca's proof works in the multiplicative groups modulo
small primes.  These definitions and lemmas isolate that algebra from the
eventual concrete certificate. -/

/-- An element of a monoid is a cube. -/
def IsCube {R : Type*} [Monoid R] (z : R) : Prop :=
  ∃ x : R, x ^ 3 = z

/-- `z` is a cubic residue modulo `m`. -/
def IsCubeMod (m z : ℕ) : Prop :=
  IsCube (z : ZMod m)

lemma isCubeMod_cube (m x : ℕ) : IsCubeMod m (x ^ 3) := by
  refine ⟨x, ?_⟩
  norm_cast

lemma isCubeMod_mul {m x y : ℕ}
    (hx : IsCubeMod m x) (hy : IsCubeMod m y) : IsCubeMod m (x * y) := by
  rcases hx with ⟨u, hu⟩
  rcases hy with ⟨v, hv⟩
  refine ⟨u * v, ?_⟩
  simp [mul_pow, hu, hv]

/-- In a commutative monoid, if a unit times a cube has product one, its
other factor is itself a cube. -/
lemma isCube_of_mul_cube_eq_one {R : Type*} [CommMonoid R] {c x : R}
    (hx : IsUnit x) (h : c * x ^ 3 = 1) : IsCube c := by
  rcases hx with ⟨u, rfl⟩
  refine ⟨↑(u⁻¹), ?_⟩
  calc
    (↑(u⁻¹) : R) ^ 3 = ↑((u⁻¹) ^ 3) := rfl
    _ = ↑((u ^ 3)⁻¹) := by rw [inv_pow]
    _ = c := Units.inv_eq_of_mul_eq_one_left h

/-- Squaring induces an automorphism of the quotient of a commutative group
by its subgroup of cubes. -/
lemma isCube_of_sq {R : Type*} [CommMonoid R] {z : R}
    (hz : IsUnit z) (h : IsCube (z ^ 2)) : IsCube z := by
  rcases hz with ⟨u, rfl⟩
  rcases h with ⟨w, hw⟩
  refine ⟨w ^ 2 * ↑(u⁻¹), ?_⟩
  rw [mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hw]
  rw [← pow_mul]
  norm_num
  norm_cast
  group

lemma pow_eq_cube_mul_pow_mod_three {R : Type*} [Monoid R] (x : R) (a : ℕ) :
    x ^ a = (x ^ (a / 3)) ^ 3 * x ^ (a % 3) := by
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

/-- If `n!+1=p^a q^b`, reduction modulo any prime at most `n` shows that
the factors left by reducing both exponents modulo three form a cube. -/
lemma residual_isCubeMod_of_factorial_add_one_eq
    {n p q a b r : ℕ} (hr : r.Prime) (hrn : r ≤ n)
    (hp : p.Prime) (hrp : r < p) (hq : q.Prime) (hrq : r < q)
    (heq : n.factorial + 1 = p ^ a * q ^ b) :
    IsCubeMod r (p ^ (a % 3) * q ^ (b % 3)) := by
  have hr0 : r ≠ 0 := hr.ne_zero
  let _ : NeZero r := ⟨hr0⟩
  have hrfac : r ∣ n.factorial := Nat.dvd_factorial hr.pos hrn
  have hfac0 : (n.factorial : ZMod r) = 0 := by
    exact (ZMod.natCast_eq_zero_iff _ _).2 hrfac
  have hcast := congrArg (fun z : ℕ ↦ (z : ZMod r)) heq
  have hprod : (p : ZMod r) ^ a * (q : ZMod r) ^ b = 1 := by
    simpa [hfac0] using hcast.symm
  have hpunit : IsUnit (p : ZMod r) :=
    ZMod.isUnit_prime_of_not_dvd hp (Nat.not_dvd_of_pos_of_lt hr.pos hrp)
  have hqunit : IsUnit (q : ZMod r) :=
    ZMod.isUnit_prime_of_not_dvd hq (Nat.not_dvd_of_pos_of_lt hr.pos hrq)
  have hxunit : IsUnit ((p : ZMod r) ^ (a / 3) * (q : ZMod r) ^ (b / 3)) :=
    (hpunit.pow _).mul (hqunit.pow _)
  apply isCube_of_mul_cube_eq_one hxunit
  calc
    ((p ^ (a % 3) * q ^ (b % 3) : ℕ) : ZMod r) *
        ((p : ZMod r) ^ (a / 3) * (q : ZMod r) ^ (b / 3)) ^ 3 =
      (p : ZMod r) ^ a * (q : ZMod r) ^ b := by
        push_cast
        rw [pow_eq_cube_mul_pow_mod_three (p : ZMod r) a,
          pow_eq_cube_mul_pow_mod_three (q : ZMod r) b, mul_pow]
        ring
    _ = 1 := hprod

/-- The one direction of the standard cubic-residue criterion needed by the
certificate: a nonzero cube modulo `r`, when `3 ∣ r-1`, has the indicated
power equal to one. -/
lemma pow_div_three_eq_one_of_isCubeMod
    {r z : ℕ} (hr : r.Prime) (h3 : 3 ∣ r - 1)
    (hz : IsUnit (z : ZMod r)) (hcube : IsCubeMod r z) :
    (z : ZMod r) ^ ((r - 1) / 3) = 1 := by
  rcases hcube with ⟨x, hx⟩
  have hxpow : IsUnit (x ^ 3) := by simpa [hx] using hz
  have hxunit : IsUnit x := (isUnit_pow_iff (by norm_num : 3 ≠ 0)).mp hxpow
  have heulerUnits := ZMod.pow_totient hxunit.unit
  have heuler := congrArg (fun u : (ZMod r)ˣ ↦ (u : ZMod r)) heulerUnits
  have hxEuler : x ^ (r - 1) = 1 := by
    simpa [Nat.totient_prime hr, hxunit.unit_spec] using heuler
  calc
    (z : ZMod r) ^ ((r - 1) / 3) = (x ^ 3) ^ ((r - 1) / 3) := by rw [hx]
    _ = x ^ (3 * ((r - 1) / 3)) := by rw [pow_mul]
    _ = x ^ (r - 1) := by rw [Nat.mul_div_cancel' h3]
    _ = 1 := hxEuler

/-- The prime moduli congruent to one modulo three through `433`.  The first
thirteen are Luca's original consecutive-prime sieve; the expanded list is
used for the formal bounded certificate below `36,000,000`. -/
def cubicModuli : Finset ℕ :=
  {7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
    157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
    331, 337, 349, 367, 373, 379, 397, 409, 421, 433}

lemma prime_of_mem_cubicModuli {r : ℕ} (hr : r ∈ cubicModuli) : r.Prime := by
  simp only [cubicModuli, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num

lemma le_433_of_mem_cubicModuli {r : ℕ} (hr : r ∈ cubicModuli) : r ≤ 433 := by
  simp only [cubicModuli, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num

lemma three_dvd_sub_one_of_mem_cubicModuli {r : ℕ} (hr : r ∈ cubicModuli) :
    3 ∣ r - 1 := by
  simp only [cubicModuli, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num

/-- Ordered form of `cubicModuli`, used by the executable verifier. -/
def cubicModuliList : List ℕ :=
  [7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151,
    157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313,
    331, 337, 349, 367, 373, 379, 397, 409, 421, 433]

lemma mem_cubicModuli_of_mem_list {r : ℕ} (hr : r ∈ cubicModuliList) :
    r ∈ cubicModuli := by
  simpa [cubicModuliList, cubicModuli] using hr

/-- Boolean witness that one exponent pair is rejected by one modulus. -/
def cubicRejects (r p q i j : ℕ) : Bool :=
  decide (((p ^ i * q ^ j : ℕ) : ZMod r) ^ ((r - 1) / 3) ≠ 1)

/-- Executable version of the forty-modulus cubic sieve. -/
def cubicSieveBool (p q : ℕ) : Bool :=
  (List.range 3).all fun i =>
    (List.range 3).all fun j =>
      if i = 0 ∧ j = 0 then true
      else cubicModuliList.any fun r => cubicRejects r p q i j

/-- A finite pair passes Luca's sieve precisely when every nonzero exponent
pair modulo three is rejected at one of the stored small moduli.  Testing all
eight pairs keeps the later algebraic argument independent of symmetry
optimizations in the certificate generator. -/
def CubicSieveHolds (p q : ℕ) : Prop :=
  ∀ i, i < 3 → ∀ j, j < 3 → (i ≠ 0 ∨ j ≠ 0) →
    ∃ r ∈ cubicModuli, ¬IsCubeMod r (p ^ i * q ^ j)

/-- The exact bounded computation still to be discharged: the forty cubic
characters separate consecutive prime pairs in the range needed after the
coarse Bertrand bound.  Recording consecutiveness here avoids asking the
certificate to prove the stronger, unused assertion for arbitrary prime
pairs. -/
def LargeCubicCertificate : Prop :=
  ∀ p q : ℕ, 433 < p → p.Prime → IsFirstPrimeAfter p q → q < 36000000 →
    CubicSieveHolds p q

lemma not_isCubeMod_of_cubicRejects
    {r p q i j : ℕ} (hr : r.Prime) (h3 : 3 ∣ r - 1)
    (hp : p.Prime) (hrp : r < p) (hq : q.Prime) (hrq : r < q)
    (hreject : cubicRejects r p q i j = true) :
    ¬IsCubeMod r (p ^ i * q ^ j) := by
  have hpunit : IsUnit (p : ZMod r) :=
    ZMod.isUnit_prime_of_not_dvd hp (Nat.not_dvd_of_pos_of_lt hr.pos hrp)
  have hqunit : IsUnit (q : ZMod r) :=
    ZMod.isUnit_prime_of_not_dvd hq (Nat.not_dvd_of_pos_of_lt hr.pos hrq)
  have hzunit : IsUnit (((p ^ i * q ^ j : ℕ) : ZMod r)) := by
    push_cast
    exact (hpunit.pow i).mul (hqunit.pow j)
  have hne : (((p ^ i * q ^ j : ℕ) : ZMod r) ^ ((r - 1) / 3)) ≠ 1 := by
    simpa [cubicRejects] using of_decide_eq_true hreject
  intro hcube
  exact hne (pow_div_three_eq_one_of_isCubeMod hr h3 hzunit hcube)

/-- Soundness of the executable cubic-sieve checker. -/
lemma cubicSieveHolds_of_cubicSieveBool
    {p q : ℕ} (hp433 : 433 < p) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcheck : cubicSieveBool p q = true) :
    CubicSieveHolds p q := by
  intro i hi j hj hpair
  have himem : i ∈ List.range 3 := by simp [hi]
  have hjmem : j ∈ List.range 3 := by simp [hj]
  have hirow := (List.all_eq_true.mp hcheck) i himem
  have hij := (List.all_eq_true.mp hirow) j hjmem
  have hnot : ¬(i = 0 ∧ j = 0) := by tauto
  simp only [hnot, ↓reduceIte] at hij
  obtain ⟨r, hrlist, hrreject⟩ := List.any_eq_true.mp hij
  have hrmem := mem_cubicModuli_of_mem_list hrlist
  refine ⟨r, hrmem, ?_⟩
  exact not_isCubeMod_of_cubicRejects (prime_of_mem_cubicModuli hrmem)
    (three_dvd_sub_one_of_mem_cubicModuli hrmem) hp
    (by have := le_433_of_mem_cubicModuli hrmem; omega) hq
    (by have := le_433_of_mem_cubicModuli hrmem; omega) hrreject

/-! The bounded certificate uses a shallow trial-division checker.  Its two
list dimensions have lengths `47` and `64`, so evaluation stays below Lean's
fixed recursion-depth limit even near `36,000,000`.  The checker is proved
equivalent to `Nat.Prime` on a slightly enlarged range; the enlargement
allows the 512-entry next-prime search to run past the certificate endpoint. -/

def cubicNoOddDivChunk (p k : ℕ) : Bool :=
  let start := 3 + 128 * k
  if p < start * start then true
  else
    (List.range 64).all fun t =>
      let d := start + 2 * t
      if d * d ≤ p then decide (¬d ∣ p) else true

def cubicPrimeFast (p : ℕ) : Bool :=
  decide (2 ≤ p) &&
    if p = 2 then true
    else decide (¬2 ∣ p) &&
      (List.range 47).all fun k => cubicNoOddDivChunk p k

/-- The same shallow grid, filtered by the proved checker.  Its equality to
the literal table below is a one-time kernel computation. -/
def cubicTrialDivisorChunksComputed : List (List ℕ) :=
  (List.range 47).map fun k =>
    ((List.range 64).map fun t => 3 + 128 * k + 2 * t).filter
      fun p => cubicPrimeFast p

/-- All 784 odd primes below 6018, retained in shallow chunks. -/
def cubicTrialDivisorChunks : List (List ℕ) :=
  [
    [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127],
    [131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257],
    [263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383],
    [389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509],
    [521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641],
    [643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769],
    [773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887],
    [907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021],
    [1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153],
    [1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279],
    [1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409],
    [1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531],
    [1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663],
    [1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789],
    [1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913],
    [1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039],
    [2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161],
    [2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297],
    [2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423],
    [2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557],
    [2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689],
    [2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803],
    [2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939],
    [2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067],
    [3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191],
    [3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329],
    [3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457],
    [3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583],
    [3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709],
    [3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833],
    [3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967],
    [3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093],
    [4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219],
    [4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349],
    [4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481],
    [4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603],
    [4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733],
    [4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861],
    [4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993],
    [4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119],
    [5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237],
    [5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351],
    [5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503],
    [5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623],
    [5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749],
    [5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881],
    [5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011]
  ]

lemma cubicTrialDivisorChunks_eq_computed :
    cubicTrialDivisorChunks = cubicTrialDivisorChunksComputed := by decide

/-- Faster finite-range primality checker using only the certified prime
divisors in the literal chunk table. -/
def cubicPrimeTableFast (p : ℕ) : Bool :=
  decide (2 ≤ p) &&
    if p = 2 then true
    else decide (¬2 ∣ p) && cubicTrialDivisorChunks.all fun chunk =>
      chunk.all fun d => if d * d ≤ p then decide (¬d ∣ p) else true

def cubicNextPrimeFast (p : ℕ) : ℕ :=
  ((List.range' (p + 1) 512).find? fun q => cubicPrimeTableFast q).getD 0

lemma cubicPrimeFast_of_prime_gt_two {p : ℕ} (hpgt2 : 2 < p) (hp : p.Prime) :
    cubicPrimeFast p = true := by
  have hp2 : p ≠ 2 := by omega
  have htwo : ¬2 ∣ p := by
    intro hdvd
    have h := (Nat.prime_def_lt.mp hp).2 2 (by omega) hdvd
    omega
  have hp2le : 2 ≤ p := by omega
  simp only [cubicPrimeFast, decide_eq_true_eq, hp2le, hp2, if_false,
    Bool.and_eq_true, true_and]
  refine ⟨htwo, ?_⟩
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  simp only [cubicNoOddDivChunk]
  split_ifs with hstart
  · rfl
  rw [List.all_eq_true]
  intro t ht
  rw [List.mem_range] at ht
  split_ifs with hd
  · apply decide_eq_true_eq.mpr
    intro hdiv
    have hdp : 3 + 128 * k + 2 * t < p := by
      nlinarith
    have hone := (Nat.prime_def_lt.mp hp).2 _ hdp hdiv
    omega
  · rfl

lemma cubicPrimeFast_of_prime {p : ℕ} (hp433 : 433 < p) (hp : p.Prime) :
    cubicPrimeFast p = true :=
  cubicPrimeFast_of_prime_gt_two (by omega) hp

lemma prime_of_cubicPrimeFast {p : ℕ} (hp433 : 433 < p)
    (hp36 : p < 36012001) (hfast : cubicPrimeFast p = true) : p.Prime := by
  have hp2 : p ≠ 2 := by omega
  have hdecoded := hfast
  simp only [cubicPrimeFast, decide_eq_true_eq, hp2, if_false,
    Bool.and_eq_true] at hdecoded
  rcases hdecoded with ⟨hp2le, heven, hall⟩
  rw [Nat.prime_def_le_sqrt]
  refine ⟨hp2le, ?_⟩
  intro m hm2 hmsqrt hmp
  have hsqrt : p.sqrt < 6018 := by
    rw [Nat.sqrt_lt]
    norm_num
    omega
  have hm6018 : m < 6018 := hmsqrt.trans_lt hsqrt
  have hmodm : m % 2 = 1 := by
    have hmodlt := Nat.mod_lt m (by norm_num : 0 < 2)
    have hdecomp := Nat.mod_add_div m 2
    by_contra hne
    have hm0 : m % 2 = 0 := by omega
    exact heven ((Nat.dvd_iff_mod_eq_zero.mpr hm0).trans hmp)
  have hm3 : 3 ≤ m := by omega
  let k := (m - 3) / 128
  let u := (m - 3) % 128
  let t := u / 2
  have hu128 : u < 128 := by
    dsimp [u]
    exact Nat.mod_lt _ (by norm_num)
  have hsplit := Nat.mod_add_div (m - 3) 128
  have humodlt : u % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have husplit := Nat.mod_add_div u 2
  have hmsplit := Nat.mod_add_div m 2
  have hsplit' : u + 128 * k = m - 3 := by
    simpa [u, k, mul_comm] using hsplit
  have huEven : u % 2 = 0 := by omega
  have hk : k < 47 := by
    dsimp [k]
    omega
  have ht : t < 64 := by
    dsimp [t]
    omega
  have hmrepr : m = 3 + 128 * k + 2 * t := by
    dsimp [k, u, t] at hsplit husplit huEven ⊢
    omega
  have hkMem : k ∈ List.range 47 := by simp [hk]
  have hchunk := (List.all_eq_true.mp hall) k hkMem
  have hstartle : (3 + 128 * k) * (3 + 128 * k) ≤ p := by
    have hmsq : m * m ≤ p := Nat.le_sqrt.mp hmsqrt
    nlinarith
  simp only [cubicNoOddDivChunk, if_neg (not_lt.mpr hstartle),
    List.all_eq_true] at hchunk
  have htMem : t ∈ List.range 64 := by simp [ht]
  have htest := hchunk t htMem
  have hmsq : m * m ≤ p := Nat.le_sqrt.mp hmsqrt
  rw [← hmrepr] at htest
  simp only [if_pos hmsq, decide_eq_true_eq] at htest
  exact htest hmp

lemma mem_cubicTrialDivisorChunks_of_prime {r : ℕ}
    (hr2 : 2 < r) (hr6018 : r < 6018) (hr : r.Prime) :
    ∃ chunk ∈ cubicTrialDivisorChunks, r ∈ chunk := by
  rw [cubicTrialDivisorChunks_eq_computed]
  have hrfast := cubicPrimeFast_of_prime_gt_two hr2 hr
  have hmodr : r % 2 = 1 := by
    have hmodlt := Nat.mod_lt r (by norm_num : 0 < 2)
    by_contra hne
    have hrmod0 : r % 2 = 0 := by omega
    have hdvd : 2 ∣ r := Nat.dvd_iff_mod_eq_zero.mpr hrmod0
    have heq := (Nat.prime_def_lt.mp hr).2 2 hr2 hdvd
    omega
  let k := (r - 3) / 128
  let u := (r - 3) % 128
  let t := u / 2
  have hu128 : u < 128 := by
    dsimp [u]
    exact Nat.mod_lt _ (by norm_num)
  have hsplit := Nat.mod_add_div (r - 3) 128
  have humodlt : u % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have husplit := Nat.mod_add_div u 2
  have hrsplit := Nat.mod_add_div r 2
  have hsplit' : u + 128 * k = r - 3 := by
    simpa [u, k, mul_comm] using hsplit
  have huEven : u % 2 = 0 := by omega
  have hk : k < 47 := by
    dsimp [k]
    omega
  have ht : t < 64 := by
    dsimp [t]
    omega
  have hrrepr : r = 3 + 128 * k + 2 * t := by
    dsimp [k, u, t] at hsplit husplit huEven ⊢
    omega
  let chunk := ((List.range 64).map fun t => 3 + 128 * k + 2 * t).filter
    fun p => cubicPrimeFast p
  refine ⟨chunk, ?_, ?_⟩
  · rw [show cubicTrialDivisorChunksComputed =
        (List.range 47).map fun k =>
          ((List.range 64).map fun t => 3 + 128 * k + 2 * t).filter
            fun p => cubicPrimeFast p by rfl]
    exact List.mem_map.mpr ⟨k, by simp [hk], rfl⟩
  · apply List.mem_filter.mpr
    refine ⟨?_, hrfast⟩
    exact List.mem_map.mpr ⟨t, by simp [ht], hrrepr.symm⟩

lemma three_le_of_mem_cubicTrialDivisorChunks
    {chunk : List ℕ} (hchunk : chunk ∈ cubicTrialDivisorChunks)
    {d : ℕ} (hd : d ∈ chunk) : 3 ≤ d := by
  rw [cubicTrialDivisorChunks_eq_computed] at hchunk
  rcases List.mem_map.mp hchunk with ⟨k, hk, rfl⟩
  have hdmap := (List.mem_filter.mp hd).1
  rcases List.mem_map.mp hdmap with ⟨t, ht, rfl⟩
  omega

lemma cubicPrimeTableFast_of_prime {p : ℕ} (hp433 : 433 < p) (hp : p.Prime) :
    cubicPrimeTableFast p = true := by
  have hp2 : p ≠ 2 := by omega
  have htwo : ¬2 ∣ p := by
    intro hdvd
    have h := (Nat.prime_def_lt.mp hp).2 2 (by omega) hdvd
    omega
  have hp2le : 2 ≤ p := by omega
  simp only [cubicPrimeTableFast, decide_eq_true_eq, hp2le, hp2, if_false,
    Bool.and_eq_true, true_and]
  refine ⟨htwo, ?_⟩
  rw [List.all_eq_true]
  intro chunk hchunk
  rw [List.all_eq_true]
  intro d hd
  split_ifs with hsq
  · apply decide_eq_true_eq.mpr
    intro hdiv
    have hd3 := three_le_of_mem_cubicTrialDivisorChunks hchunk hd
    have hdp : d < p := by nlinarith
    have hone := (Nat.prime_def_lt.mp hp).2 d hdp hdiv
    omega
  · rfl

lemma prime_of_cubicPrimeTableFast {p : ℕ} (hp433 : 433 < p)
    (hp36 : p < 36012001) (hfast : cubicPrimeTableFast p = true) : p.Prime := by
  have hp2 : p ≠ 2 := by omega
  have hdecoded := hfast
  simp only [cubicPrimeTableFast, decide_eq_true_eq, hp2, if_false,
    Bool.and_eq_true] at hdecoded
  rcases hdecoded with ⟨hp2le, heven, hall⟩
  rw [Nat.prime_def_le_sqrt]
  refine ⟨hp2le, ?_⟩
  intro m hm2 hmsqrt hmp
  have hsqrt : p.sqrt < 6018 := by
    rw [Nat.sqrt_lt]
    norm_num
    omega
  have hm6018 : m < 6018 := hmsqrt.trans_lt hsqrt
  let r := m.minFac
  have hm1 : m ≠ 1 := by omega
  have hrprime : r.Prime := Nat.minFac_prime hm1
  have hrdvdm : r ∣ m := Nat.minFac_dvd m
  have hrle : r ≤ m := Nat.minFac_le (by omega)
  by_cases hr2eq : r = 2
  · exact heven (by simpa [hr2eq] using hrdvdm.trans hmp)
  have hr2 : 2 < r := by have := hrprime.two_le; omega
  have hr6018 : r < 6018 := hrle.trans_lt hm6018
  obtain ⟨chunk, hchunk, hrmem⟩ :=
    mem_cubicTrialDivisorChunks_of_prime hr2 hr6018 hrprime
  have hchunkcheck := (List.all_eq_true.mp hall) chunk hchunk
  have hrcheck := (List.all_eq_true.mp hchunkcheck) r hrmem
  have hrsq : r * r ≤ p := by
    have hmsq : m * m ≤ p := Nat.le_sqrt.mp hmsqrt
    nlinarith
  simp only [if_pos hrsq, decide_eq_true_eq] at hrcheck
  exact hrcheck (hrdvdm.trans hmp)

lemma cubicNextPrimeFast_eq_of_first {p q : ℕ} (hp433 : 433 < p)
    (hq36 : q < 36000000) (hq : IsFirstPrimeAfter p q)
    (hnonzero : cubicNextPrimeFast p ≠ 0) : cubicNextPrimeFast p = q := by
  unfold cubicNextPrimeFast at hnonzero ⊢
  generalize hopt :
    (List.range' (p + 1) 512).find? (fun q => cubicPrimeTableFast q) = opt
  cases opt with
  | none =>
      rw [hopt] at hnonzero
      simp at hnonzero
  | some r =>
      simp only [Option.getD_some]
      have hfind := hopt
      rw [List.find?_eq_some_iff_getElem] at hfind
      rcases hfind with ⟨hrfast, i, hi, hir, hbefore⟩
      have hi512 : i < 512 := by simpa using hi
      have hri : r = p + 1 + i := by simpa using hir.symm
      have hrp : p < r := by omega
      have hp36 : p < 36000000 := hq.1.trans hq36
      have hrbound : r < 36012001 := by omega
      have hrprime : r.Prime :=
        prime_of_cubicPrimeTableFast (by omega) hrbound hrfast
      have hrfirst : IsFirstPrimeAfter p r := by
        refine ⟨hrp, hrprime, ?_⟩
        intro s hsprime hps
        by_contra hrs
        have hsr : s < r := by omega
        let j := s - (p + 1)
        have hsj : s = p + 1 + j := by
          dsimp [j]
          omega
        have hj : j < i := by omega
        have hget : (List.range' (p + 1) 512)[j] = s := by
          simpa [hsj]
        have hnot := hbefore j hj
        rw [hget] at hnot
        have hsfast := cubicPrimeTableFast_of_prime (by omega) hsprime
        simp [hsfast] at hnot
      exact IsFirstPrimeAfter.unique hrfirst hq

/-- A structurally recursive, balanced checker for a block of `2^depth`
integers.  Structural recursion on `depth` keeps reduction depth logarithmic
in the block length. -/
def cubicAllPowBlock (start : ℕ) : ℕ → (ℕ → Bool) → Bool
  | 0, f => f start
  | depth + 1, f =>
      cubicAllPowBlock start depth f &&
        cubicAllPowBlock (start + 2 ^ depth) depth f

def cubicFastPairCheck (p : ℕ) : Bool :=
  if cubicPrimeTableFast p then
    cubicNextPrimeFast p ≠ 0 && cubicSieveBool p (cubicNextPrimeFast p)
  else true

def cubicFastPowBlock (start depth : ℕ) : Bool :=
  cubicAllPowBlock start depth cubicFastPairCheck

lemma cubicAllPowBlock_spec {start depth : ℕ} {f : ℕ → Bool}
    (hcheck : cubicAllPowBlock start depth f = true)
    {i : ℕ} (hi : i < 2 ^ depth) : f (start + i) = true := by
  induction depth generalizing start i with
  | zero =>
      have hi0 : i = 0 := by simpa using hi
      simpa [cubicAllPowBlock, hi0] using hcheck
  | succ depth ih =>
      simp only [cubicAllPowBlock, Bool.and_eq_true] at hcheck
      rw [Nat.pow_succ] at hi
      by_cases hleft : i < 2 ^ depth
      · exact ih hcheck.1 hleft
      · have hj : i - 2 ^ depth < 2 ^ depth := by omega
        have hright := ih hcheck.2 hj
        have hieq : 2 ^ depth + (i - 2 ^ depth) = i :=
          Nat.add_sub_of_le (Nat.le_of_not_gt hleft)
        simpa [Nat.add_assoc, hieq] using hright

/-- Soundness theorem for each checked power-of-two block.  Concrete block
equalities can therefore be generated independently while this single proof
handles primality, adjacency, and the modular-sieve reflection. -/
lemma cubicFastPowBlock_spec
    {start depth p q : ℕ} (hcheck : cubicFastPowBlock start depth = true)
    (hstart : start ≤ p) (hend : p < start + 2 ^ depth)
    (hp433 : 433 < p) (hp : p.Prime) (hq : IsFirstPrimeAfter p q)
    (hq36 : q < 36000000) : CubicSieveHolds p q := by
  have hi : p - start < 2 ^ depth := by omega
  have hrow := cubicAllPowBlock_spec hcheck hi
  rw [show start + (p - start) = p by omega] at hrow
  have hpfast := cubicPrimeTableFast_of_prime hp433 hp
  simp only [cubicFastPairCheck, hpfast, if_true, Bool.and_eq_true] at hrow
  have hnext := cubicNextPrimeFast_eq_of_first hp433 hq36 hq
    (of_decide_eq_true hrow.1)
  apply cubicSieveHolds_of_cubicSieveBool hp433 hp hq.2.1 hq.1
  simpa [hnext] using hrow.2

/-! The second certificate format is a mixed-radix search.  Unlike the
integer-by-integer block checker above, it imposes the small cubic-character
conditions before enumerating actual integers.  Binary branching keeps the
kernel reduction depth logarithmic. -/

def cubicFastPowMod (a : ℕ) : ℕ → ℕ → ℕ
  | 0, m => 1 % m
  | e + 1, m =>
      let z := cubicFastPowMod (a * a % m) ((e + 1) / 2) m
      if (e + 1) % 2 = 0 then z else a * z % m
termination_by e _ => e
decreasing_by omega

/-- A structurally recursive modular-power evaluator used only in concrete
certificates.  Its recursion depth is at most the (small) character exponent,
while reduction never constructs the enormous unreduced natural power. -/
def cubicPowModCert (a m : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | e + 1 => cubicPowModCert a m e * a % m

lemma cubicPowModCert_eq_pow_mod (a m e : ℕ) :
    cubicPowModCert a m e = a ^ e % m := by
  induction e with
  | zero => simp [cubicPowModCert]
  | succ e ih =>
      simp only [cubicPowModCert, ih, pow_succ]
      exact Nat.mod_mul_mod _ _ _

/-- Binary modular exponentiation with an explicit structural fuel.  Eight
steps suffice for every exponent occurring in the forty-modulus certificate. -/
def cubicPowModFuel : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, e, m => if e = 0 then 1 % m else 0
  | fuel + 1, a, e, m =>
      if e = 0 then 1 % m
      else
        let z := cubicPowModFuel fuel (a * a % m) (e / 2) m
        if e % 2 = 0 then z else a * z % m

lemma cubicPowModFuel_eq_pow_mod {fuel a e m : ℕ} (he : e < 2 ^ fuel) :
    cubicPowModFuel fuel a e m = a ^ e % m := by
  induction fuel generalizing a e with
  | zero =>
      have he0 : e = 0 := by simpa using he
      simp [cubicPowModFuel, he0]
  | succ fuel ih =>
      by_cases he0 : e = 0
      · simp [cubicPowModFuel, he0]
      have hhalf : e / 2 < 2 ^ fuel := by
        rw [pow_succ] at he
        omega
      simp only [cubicPowModFuel, he0, if_false]
      rw [ih hhalf, ← Nat.pow_mod]
      by_cases heven : e % 2 = 0
      · simp only [heven, if_true, ← pow_two]
        have hsplit := Nat.mod_add_div e 2
        have hexp : 2 * (e / 2) = e := by omega
        rw [← pow_mul, hexp]
      · simp only [heven, if_false, Nat.mul_mod_mod, ← pow_two]
        have hmodlt := Nat.mod_lt e (by omega : 0 < 2)
        have hsplit := Nat.mod_add_div e 2
        have hexp : 1 + 2 * (e / 2) = e := by omega
        rw [← pow_mul]
        calc
          a * a ^ (2 * (e / 2)) % m = a ^ (1 + 2 * (e / 2)) % m := by
            simp [pow_add]
          _ = a ^ e % m := by rw [hexp]

lemma cubicPowModFuel_self_eq_one_iff_zmod {a e r : ℕ} (hr : 1 < r) :
    cubicPowModFuel e a e r = 1 ↔ (a : ZMod r) ^ e = 1 := by
  rw [cubicPowModFuel_eq_pow_mod e.lt_two_pow_self]
  constructor
  · intro h
    have hmod : a ^ e % r = 1 % r := by simpa [Nat.mod_eq_of_lt hr] using h
    have hcast : ((a ^ e : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) :=
      (ZMod.natCast_eq_natCast_iff' (a ^ e) 1 r).mpr hmod
    simpa only [Nat.cast_pow, Nat.cast_one] using hcast
  · intro h
    have hcast : ((a ^ e : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
      simpa only [Nat.cast_pow, Nat.cast_one] using h
    have hmod := (ZMod.natCast_eq_natCast_iff' (a ^ e) 1 r).mp hcast
    simpa [Nat.mod_eq_of_lt hr] using hmod

lemma cubicFastPowMod_eq_pow_mod (a e m : ℕ) :
    cubicFastPowMod a e m = a ^ e % m := by
  fun_induction cubicFastPowMod a e m with
  | case1 a m => simp
  | case2 a e m z heven ih =>
      have hsplit := Nat.mod_add_div (e + 1) 2
      have hexp : 2 * ((e + 1) / 2) = e + 1 := by omega
      simp only [z]
      rw [ih, ← Nat.pow_mod]
      simp only [← pow_two]
      rw [← pow_mul, hexp]
  | case3 a e m z hodd ih =>
      have hmodlt := Nat.mod_lt (e + 1) (by omega : 0 < 2)
      have hsplit := Nat.mod_add_div (e + 1) 2
      have hexp : 1 + 2 * ((e + 1) / 2) = e + 1 := by omega
      simp only [z]
      rw [ih, ← Nat.pow_mod, Nat.mul_mod_mod]
      simp only [← pow_two]
      rw [← pow_mul]
      calc
        a * a ^ (2 * ((e + 1) / 2)) % m =
            a ^ (1 + 2 * ((e + 1) / 2)) % m := by simp [pow_add]
        _ = a ^ (e + 1) % m := by rw [hexp]

def cubicCRTLocalBase (d kind r p : ℕ) : ℕ :=
  let q := p + d
  if kind = 0 then (p % r) * (q % r) % r
  else if kind = 1 then (p % r) * ((q % r) * (q % r) % r) % r
  else p % r

def cubicCRTLocalForm (d kind r p : ℕ) : Bool :=
  let q := p + d
  decide (p % r ≠ 0) && decide (q % r ≠ 0) &&
    decide (cubicPowModFuel ((r - 1) / 3)
      (cubicCRTLocalBase d kind r p) ((r - 1) / 3) r = 1)

lemma cubicFastPowMod_eq_one_iff_zmod {a e r : ℕ} (hr : 1 < r) :
    cubicFastPowMod a e r = 1 ↔ (a : ZMod r) ^ e = 1 := by
  rw [cubicFastPowMod_eq_pow_mod]
  constructor
  · intro h
    have hmod : a ^ e % r = 1 % r := by simpa [Nat.mod_eq_of_lt hr] using h
    have hcast : ((a ^ e : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) :=
      (ZMod.natCast_eq_natCast_iff' (a ^ e) 1 r).mpr hmod
    simpa only [Nat.cast_pow, Nat.cast_one] using hcast
  · intro h
    have hcast : ((a ^ e : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
      simpa only [Nat.cast_pow, Nat.cast_one] using h
    have hmod := (ZMod.natCast_eq_natCast_iff' (a ^ e) 1 r).mp hcast
    simpa [Nat.mod_eq_of_lt hr] using hmod

lemma cubicPowModCert_eq_one_iff_zmod {a e r : ℕ} (hr : 1 < r) :
    cubicPowModCert a r e = 1 ↔ (a : ZMod r) ^ e = 1 := by
  rw [cubicPowModCert_eq_pow_mod]
  constructor
  · intro h
    have hmod : a ^ e % r = 1 % r := by simpa [Nat.mod_eq_of_lt hr] using h
    have hcast : ((a ^ e : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) :=
      (ZMod.natCast_eq_natCast_iff' (a ^ e) 1 r).mpr hmod
    simpa only [Nat.cast_pow, Nat.cast_one] using hcast
  · intro h
    have hcast : ((a ^ e : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
      simpa only [Nat.cast_pow, Nat.cast_one] using h
    have hmod := (ZMod.natCast_eq_natCast_iff' (a ^ e) 1 r).mp hcast
    simpa [Nat.mod_eq_of_lt hr] using hmod

lemma cubicCRTLocalForm_eq_true_iff {d kind r p : ℕ} (hr : 1 < r) :
    cubicCRTLocalForm d kind r p = true ↔
      p % r ≠ 0 ∧ (p + d) % r ≠ 0 ∧
        ((cubicCRTLocalBase d kind r p : ℕ) : ZMod r) ^ ((r - 1) / 3) = 1 := by
  simp only [cubicCRTLocalForm, Bool.and_eq_true, decide_eq_true_eq]
  rw [cubicPowModFuel_self_eq_one_iff_zmod hr]
  tauto

lemma cubicCRTLocalForm_eq_false_of_character_ne {d kind r p : ℕ}
    (hr : 1 < r)
    (hne : ((cubicCRTLocalBase d kind r p : ℕ) : ZMod r) ^
      ((r - 1) / 3) ≠ 1) :
    cubicCRTLocalForm d kind r p = false := by
  cases hlocal : cubicCRTLocalForm d kind r p with
  | false => rfl
  | true =>
      exfalso
      exact hne ((cubicCRTLocalForm_eq_true_iff hr).mp hlocal).2.2

lemma cubicCRTLocalForm_eq_true_of_cert {d kind r p : ℕ}
    (hr : 1 < r) (hp : p % r ≠ 0) (hq : (p + d) % r ≠ 0)
    (hcert : cubicPowModCert (cubicCRTLocalBase d kind r p) r
      ((r - 1) / 3) = 1) :
    cubicCRTLocalForm d kind r p = true := by
  rw [cubicCRTLocalForm_eq_true_iff hr]
  exact ⟨hp, hq, (cubicPowModCert_eq_one_iff_zmod hr).mp hcert⟩

lemma cubicCRTLocalForm_eq_false_of_cert {d kind r p : ℕ}
    (hr : 1 < r)
    (hcert : cubicPowModCert (cubicCRTLocalBase d kind r p) r
      ((r - 1) / 3) ≠ 1) :
    cubicCRTLocalForm d kind r p = false := by
  apply cubicCRTLocalForm_eq_false_of_character_ne hr
  exact fun hpow ↦ hcert ((cubicPowModCert_eq_one_iff_zmod hr).mpr hpow)

lemma cast_cubicCRTLocalBase_zero (d r p : ℕ) :
    ((cubicCRTLocalBase d 0 r p : ℕ) : ZMod r) =
      (p : ZMod r) * ((p + d : ℕ) : ZMod r) := by
  simp [cubicCRTLocalBase]

lemma cast_cubicCRTLocalBase_one (d r p : ℕ) :
    ((cubicCRTLocalBase d 1 r p : ℕ) : ZMod r) =
      (p : ZMod r) * ((p + d : ℕ) : ZMod r) ^ 2 := by
  simp [cubicCRTLocalBase, pow_two]

lemma cast_cubicCRTLocalBase_two (d r p : ℕ) :
    ((cubicCRTLocalBase d 2 r p : ℕ) : ZMod r) = (p : ZMod r) := by
  simp [cubicCRTLocalBase]

lemma pow_cast_product_eq_character_product
    (r p q i j e : ℕ) :
    (((p ^ i * q ^ j : ℕ) : ZMod r) ^ e) =
      ((p : ZMod r) ^ e) ^ i * ((q : ZMod r) ^ e) ^ j := by
  push_cast
  simp only [mul_pow]
  rw [← pow_mul, ← pow_mul, mul_comm i e, mul_comm j e, pow_mul, pow_mul]

def cubicCRTRepresentative (bound M p : ℕ) : ℕ :=
  if bound ≤ M then p else p % M

lemma cubicCRTLocalForm_of_modEq {d kind r p z : ℕ}
    (hz : z % r = p % r) (h : cubicCRTLocalForm d kind r p = true) :
    cubicCRTLocalForm d kind r z = true := by
  have hqmod : (z + d) % r = (p + d) % r := by
    calc
      (z + d) % r = (z % r + d % r) % r := Nat.add_mod z d r
      _ = (p % r + d % r) % r := by rw [hz]
      _ = (p + d) % r := (Nat.add_mod p d r).symm
  have hbase : cubicCRTLocalBase d kind r z = cubicCRTLocalBase d kind r p := by
    simp only [cubicCRTLocalBase, hz, hqmod]
  unfold cubicCRTLocalForm at h ⊢
  dsimp only at h ⊢
  rw [hz, hqmod, hbase]
  exact h

/-- Search constraints: the two smallest wheel primes are inserted before
the sixth cubic-character modulus.  This prunes five sixths of the residue
classes before the mixed-radix product crosses the numerical bound. -/
def cubicCRTConstraint (d kind r p : ℕ) : Bool :=
  if r = 2 then decide (p % r ≠ 0) && decide ((p + d) % r ≠ 0)
  else if r = 3 then decide (p % r ≠ 0) && decide ((p + d) % r ≠ 0)
  else cubicCRTLocalForm d kind r p

def cubicCRTConstraintList : List ℕ :=
  [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139,
    151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307,
    313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433]

lemma cubicCRTConstraint_of_modEq {d kind r p z : ℕ}
    (hz : z % r = p % r) (h : cubicCRTConstraint d kind r p = true) :
    cubicCRTConstraint d kind r z = true := by
  have hqmod : (z + d) % r = (p + d) % r := by
    calc
      (z + d) % r = (z % r + d % r) % r := Nat.add_mod z d r
      _ = (p % r + d % r) % r := by rw [hz]
      _ = (p + d) % r := (Nat.add_mod p d r).symm
  unfold cubicCRTConstraint at h ⊢
  split_ifs <;> simp_all [cubicCRTLocalForm_of_modEq hz]

lemma seven_le_of_mem_cubicModuliList {r : ℕ} (hr : r ∈ cubicModuliList) :
    7 ≤ r := by
  norm_num [cubicModuliList] at hr ⊢
  omega

def cubicCRTPrimeGate (d p : ℕ) : Bool :=
  cubicPrimeTableFast p && cubicPrimeTableFast (p + d)

/-- Trial divisors are interleaved between the two entries of a candidate
pair.  A genuine prime pair passes this gate, while a composite candidate is
discarded as soon as a divisor of either entry is found. -/
def cubicCRTTrialPairGate (d p : ℕ) : Bool :=
  cubicTrialDivisorChunks.all fun chunk ↦
    chunk.all fun s ↦
      (if s * s ≤ p then decide (¬s ∣ p) else true) &&
        (if s * s ≤ p + d then decide (¬s ∣ p + d) else true)

lemma cubicCRTTrialPairGate_of_prime_pair {d p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hqp : q = p + d) :
    cubicCRTTrialPairGate d p = true := by
  rw [cubicCRTTrialPairGate, List.all_eq_true]
  intro chunk hchunk
  rw [List.all_eq_true]
  intro s hs
  rw [Bool.and_eq_true]
  constructor
  · split_ifs with hsq
    · apply decide_eq_true_eq.mpr
      intro hdiv
      have hs3 := three_le_of_mem_cubicTrialDivisorChunks hchunk hs
      have hsp : s < p := by nlinarith
      have hone := (Nat.prime_def_lt.mp hp).2 s hsp hdiv
      omega
    · rfl
  · split_ifs with hsq
    · apply decide_eq_true_eq.mpr
      intro hdiv
      have hs3 := three_le_of_mem_cubicTrialDivisorChunks hchunk hs
      have hsq' : s * s ≤ q := by simpa [hqp] using hsq
      have hdiv' : s ∣ q := by simpa [hqp] using hdiv
      have hsqLt : s < q := by nlinarith
      have hone := (Nat.prime_def_lt.mp hq).2 s hsqLt hdiv'
      omega
    · rfl

lemma cubicCRTTrialPairGate_eq_false_of_left_divisor {d p s : ℕ}
    (hsmem : ∃ chunk ∈ cubicTrialDivisorChunks, s ∈ chunk)
    (hsq : s * s ≤ p) (hdiv : s ∣ p) :
    cubicCRTTrialPairGate d p = false := by
  rw [cubicCRTTrialPairGate, List.all_eq_false]
  obtain ⟨chunk, hchunk, hs⟩ := hsmem
  refine ⟨chunk, hchunk, ?_⟩
  intro hall
  have hsval := (List.all_eq_true.mp hall) s hs
  simp [hsq, hdiv] at hsval

lemma cubicCRTTrialPairGate_eq_false_of_right_divisor {d p s : ℕ}
    (hsmem : ∃ chunk ∈ cubicTrialDivisorChunks, s ∈ chunk)
    (hsq : s * s ≤ p + d) (hdiv : s ∣ p + d) :
    cubicCRTTrialPairGate d p = false := by
  rw [cubicCRTTrialPairGate, List.all_eq_false]
  obtain ⟨chunk, hchunk, hs⟩ := hsmem
  refine ⟨chunk, hchunk, ?_⟩
  intro hall
  have hsval := (List.all_eq_true.mp hall) s hs
  simp [hsq, hdiv] at hsval

/-- Every representative below `36,000,000` which survives all forty
cubic-character tests in the finite searches used below.  The second component
is a proper divisor when the representative is larger than `433`; small
representatives are rejected by the lower-bound test. -/
def cubicCRTTerminalCompositeData0 : List (ℕ × ℕ) := [
  (1, 1), (6967871, 191), (12977875, 5), (2985984, 2), (24389, 29),
  (148877, 53), (4492125, 3), (25672375, 5), (10648, 2), (8489664, 2),
  (17779581, 3), (4096, 2), (18191447, 263), (22425768, 2), (778688, 2),
  (1000000, 2), (531441, 3), (729, 3), (16777216, 2), (1728000, 2),
  (24137569, 17), (4913000, 2), (20570824, 2), (7762392, 2), (1225043, 107)
]

def cubicCRTTerminalCompositeData1 : List (ℕ × ℕ) := [
  (1442897, 113), (8, 1), (15438249, 3), (23887872, 2), (357911, 71),
  (2460375, 3), (11543176, 2), (3307949, 149), (9800344, 2), (20796875, 5),
  (16194277, 11), (85184, 2), (1860867, 3), (5832, 2), (13824000, 2),
  (1191016, 2), (35937000, 2), (195112, 2), (7645373, 197), (13651919, 239),
  (3375, 3), (6229504, 2), (8000000, 2), (31855013, 317), (4251528, 2)
]

def cubicCRTTerminalCompositeData2 : List (ℕ × ℕ) := [
  (32768, 2), (5451776, 2), (970299, 3), (614125, 5), (5545233, 3),
  (2571353, 137), (12487168, 2), (512, 2), (2803221, 3), (125000, 2),
  (22906304, 2), (97336, 2), (1331, 11), (19034163, 3), (1061208, 2),
  (32461759, 11), (373248, 2), (22188041, 281), (216000, 2), (2097152, 2),
  (14172488, 2), (64, 1), (12167, 23), (19683000, 2), (15625, 5)
]

def cubicCRTTerminalCompositeData3 : List (ℕ × ℕ) := [
  (2863288, 2), (27818127, 3), (5735339, 179), (681472, 2), (14886936, 2),
  (1771561, 11), (27000, 2), (34012224, 2), (262144, 2), (132651, 3),
  (8615125, 5), (26463592, 2), (1560896, 2), (9528128, 2), (8869743, 3),
  (11390625, 3), (46656, 2), (12649337, 233), (27, 1), (12167000, 2),
  (19465109, 269), (64000, 2), (15625000, 2), (166375, 5), (33076161, 3)
]

def cubicCRTTerminalCompositeData4 : List (ℕ × ℕ) := [
  (35287552, 2), (2248091, 131), (287496, 2), (1643032, 2), (19683, 3),
  (830584, 2), (5639752, 2), (658503, 3), (314432, 2), (4019679, 3),
  (110592, 2), (21024576, 2), (14348907, 3), (27000000, 2), (125, 1),
  (6539203, 11), (157464, 2), (6644672, 2), (216, 1), (9663597, 3),
  (512000, 2), (18609625, 5), (13144256, 2), (11697083, 227), (3048625, 5)
]

def cubicCRTTerminalCompositeData5 : List (ℕ × ℕ) := [
  (2299968, 2), (884736, 2), (571787, 83), (91125, 3), (17984728, 2),
  (1331000, 2), (68921, 41), (5268024, 2), (2515456, 2), (32157432, 2),
  (5832000, 2), (103823, 47), (4410944, 2), (25153757, 293), (16581375, 3),
  (8242408, 2), (26198073, 3), (10077696, 2), (8000, 2), (1520875, 5),
  (1953125, 5), (704969, 89), (39304, 2), (4657463, 167), (28652616, 2)
]

def cubicCRTTerminalCompositeData6 : List (ℕ × ℕ) := [
  (35937, 3), (205379, 59), (2628072, 2), (13824, 2), (32768000, 2),
  (3375000, 2), (30080231, 311), (10648000, 2), (3581577, 3), (1000, 2),
  (1259712, 2), (16974593, 257), (7077888, 2), (4574296, 2), (729000, 2),
  (5177717, 173), (24389000, 2), (4913, 17), (18399744, 2), (15813251, 251),
  (1030301, 101), (551368, 2), (20123648, 2), (1728, 2), (328509, 3)
]

def cubicCRTTerminalCompositeData7 : List (ℕ × ℕ) := [
  (4096000, 2), (421875, 3), (2, 1), (3, 1), (12, 1),
  (250, 1), (36, 1), (4, 1), (16, 1), (108, 1),
  (80, 1), (5, 1), (32, 1), (450, 2), (45, 1),
  (150, 1), (6, 1), (20, 1), (2400, 2), (544, 2),
  (24, 1), (96, 1), (2000, 2), (625, 5), (54, 1)
]

def cubicCRTTerminalCompositeData8 : List (ℕ × ℕ) := [
  (783, 3), (432, 1), (1280, 2), (10, 1), (9, 1),
  (576, 2), (18, 1), (47916, 2), (810, 2), (529, 23),
  (288, 1), (5618, 2), (1100, 2), (484, 2), (50, 1),
  (11, 1), (25, 1), (5940, 2), (242, 1), (48668, 2),
  (48, 1), (72, 1), (200, 1), (128, 1), (78608, 2)
]

def cubicCRTTerminalCompositeData9 : List (ℕ × ℕ) := [
  (162, 1), (4374, 2), (4224, 2), (1452, 2), (243, 1),
  (400, 1), (22, 1), (640, 2), (864, 2), (40, 1),
  (6750, 2), (324, 1), (81, 1), (100, 1), (289, 1),
  (121, 1), (256, 1), (225, 1), (144, 1), (44, 1),
  (891, 3), (15, 1), (7776, 2), (90, 1), (30, 1)
]

def cubicCRTTerminalCompositeData : List (ℕ × ℕ) :=
  cubicCRTTerminalCompositeData0 ++ cubicCRTTerminalCompositeData1 ++
    cubicCRTTerminalCompositeData2 ++ cubicCRTTerminalCompositeData3 ++
    cubicCRTTerminalCompositeData4 ++ cubicCRTTerminalCompositeData5 ++
    cubicCRTTerminalCompositeData6 ++ cubicCRTTerminalCompositeData7 ++
    cubicCRTTerminalCompositeData8 ++ cubicCRTTerminalCompositeData9

def cubicCRTTerminalCompositeGate (p : ℕ) : Bool :=
  !(cubicCRTTerminalCompositeData.map Prod.fst).contains p

def cubicCRTTerminalCompositeWitness (z : ℕ × ℕ) : Prop :=
  z.1 ≤ 433 ∨ (1 < z.2 ∧ z.2 < z.1 ∧ z.2 ∣ z.1)

private lemma cubicCRTTerminalCompositeData_forall0 :
    cubicCRTTerminalCompositeData0.Forall cubicCRTTerminalCompositeWitness := by
  norm_num [cubicCRTTerminalCompositeData0, cubicCRTTerminalCompositeWitness]

private lemma cubicCRTTerminalCompositeData_forall1 :
    cubicCRTTerminalCompositeData1.Forall cubicCRTTerminalCompositeWitness := by
  norm_num [cubicCRTTerminalCompositeData1, cubicCRTTerminalCompositeWitness]

private lemma cubicCRTTerminalCompositeData_forall2 :
    cubicCRTTerminalCompositeData2.Forall cubicCRTTerminalCompositeWitness := by
  norm_num [cubicCRTTerminalCompositeData2, cubicCRTTerminalCompositeWitness]

private lemma cubicCRTTerminalCompositeData_forall3 :
    cubicCRTTerminalCompositeData3.Forall cubicCRTTerminalCompositeWitness := by
  norm_num [cubicCRTTerminalCompositeData3, cubicCRTTerminalCompositeWitness]

private lemma cubicCRTTerminalCompositeData_forall4 :
    cubicCRTTerminalCompositeData4.Forall cubicCRTTerminalCompositeWitness := by
  norm_num [cubicCRTTerminalCompositeData4, cubicCRTTerminalCompositeWitness]

private lemma cubicCRTTerminalCompositeData_forall5 :
    cubicCRTTerminalCompositeData5.Forall cubicCRTTerminalCompositeWitness := by
  norm_num [cubicCRTTerminalCompositeData5, cubicCRTTerminalCompositeWitness]

private lemma cubicCRTTerminalCompositeData_forall6 :
    cubicCRTTerminalCompositeData6.Forall cubicCRTTerminalCompositeWitness := by
  norm_num [cubicCRTTerminalCompositeData6, cubicCRTTerminalCompositeWitness]

private lemma cubicCRTTerminalCompositeData_forall7 :
    cubicCRTTerminalCompositeData7.Forall cubicCRTTerminalCompositeWitness := by
  norm_num [cubicCRTTerminalCompositeData7, cubicCRTTerminalCompositeWitness]

private lemma cubicCRTTerminalCompositeData_forall8 :
    cubicCRTTerminalCompositeData8.Forall cubicCRTTerminalCompositeWitness := by
  norm_num [cubicCRTTerminalCompositeData8, cubicCRTTerminalCompositeWitness]

private lemma cubicCRTTerminalCompositeData_forall9 :
    cubicCRTTerminalCompositeData9.Forall cubicCRTTerminalCompositeWitness := by
  norm_num [cubicCRTTerminalCompositeData9, cubicCRTTerminalCompositeWitness]

lemma cubicCRTTerminalCompositeData_forall :
    cubicCRTTerminalCompositeData.Forall cubicCRTTerminalCompositeWitness := by
  simp only [cubicCRTTerminalCompositeData, List.forall_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨cubicCRTTerminalCompositeData_forall0, cubicCRTTerminalCompositeData_forall1⟩, cubicCRTTerminalCompositeData_forall2⟩, cubicCRTTerminalCompositeData_forall3⟩, cubicCRTTerminalCompositeData_forall4⟩, cubicCRTTerminalCompositeData_forall5⟩, cubicCRTTerminalCompositeData_forall6⟩, cubicCRTTerminalCompositeData_forall7⟩, cubicCRTTerminalCompositeData_forall8⟩, cubicCRTTerminalCompositeData_forall9⟩

lemma cubicCRTTerminalCompositeData_spec {z : ℕ × ℕ}
    (hz : z ∈ cubicCRTTerminalCompositeData) :
    z.1 ≤ 433 ∨ (1 < z.2 ∧ z.2 < z.1 ∧ z.2 ∣ z.1) := by
  have hz' :=
    List.forall_iff_forall_mem.mp cubicCRTTerminalCompositeData_forall z hz
  simpa [cubicCRTTerminalCompositeWitness] using hz'

lemma cubicCRTTerminalCompositeGate_of_prime {p : ℕ}
    (hp433 : 433 < p) (hp : p.Prime) :
    cubicCRTTerminalCompositeGate p = true := by
  rw [cubicCRTTerminalCompositeGate, Bool.not_eq_true']
  apply Bool.eq_false_iff.mpr
  intro hcontains
  have hmem : p ∈ cubicCRTTerminalCompositeData.map Prod.fst := by
    simpa using (List.contains_iff_mem.mp hcontains)
  obtain ⟨z, hz, hzp⟩ := List.mem_map.mp hmem
  have hspec := cubicCRTTerminalCompositeData_spec hz
  have hfirst : z.1 = p := by simpa using hzp
  subst p
  rcases hspec with hsmall | ⟨hs1, hsz, hdiv⟩
  · omega
  · rcases (Nat.dvd_prime hp).mp hdiv with h | h <;> omega


def cubicCRTWheelPrimes : List ℕ :=
  [2, 3, 5, 11, 17, 23, 29, 41]

def cubicCRTWheelGate (d p : ℕ) : Bool :=
  cubicCRTWheelPrimes.all fun s ↦
    decide (p % s ≠ 0) && decide ((p + d) % s ≠ 0)

lemma cubicCRTWheelGate_of_prime_pair {d p q : ℕ}
    (hp433 : 433 < p) (hp : p.Prime) (hq : q.Prime) (hqp : q = p + d) :
    cubicCRTWheelGate d p = true := by
  rw [cubicCRTWheelGate, List.all_eq_true]
  intro s hs
  have hsBounds : 2 ≤ s ∧ s ≤ 433 := by
    norm_num [cubicCRTWheelPrimes] at hs ⊢
    omega
  rw [Bool.and_eq_true]
  constructor <;> apply decide_eq_true_eq.mpr
  · intro hzero
    have hdiv : s ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hzero
    rcases (Nat.dvd_prime hp).mp hdiv with h | h <;> omega
  · intro hzero
    have hdiv : s ∣ p + d := Nat.dvd_iff_mod_eq_zero.mpr hzero
    have hdivq : s ∣ q := by simpa [hqp] using hdiv
    rcases (Nat.dvd_prime hq).mp hdivq with h | h <;> omega

def cubicBalancedAny (start : ℕ) : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | 1, f => f start
  | count + 2, f =>
      let left := (count + 2) / 2
      cubicBalancedAny start left f ||
        cubicBalancedAny (start + left) (count + 2 - left) f
termination_by count _ => count
decreasing_by all_goals omega

lemma cubicBalancedAny_eq_true_of {start count i : ℕ} {f : ℕ → Bool}
    (hlo : start ≤ i) (hi : i < start + count) (hfi : f i = true) :
    cubicBalancedAny start count f = true := by
  induction count using Nat.strong_induction_on generalizing start with
  | h count ih =>
      rcases count with _ | count
      · omega
      rcases count with _ | count
      · have hiEq : i = start := by omega
        simpa [cubicBalancedAny, hiEq] using hfi
      · let left := (count + 2) / 2
        have hleftPos : 0 < left := by
          dsimp [left]
          omega
        have hleftLt : left < count + 2 := by
          dsimp [left]
          omega
        have hrightLt : count + 2 - left < count + 2 := by omega
        simp only [cubicBalancedAny, Bool.or_eq_true]
        by_cases hil : i < start + left
        · left
          exact ih left hleftLt (start := start) hlo hil
        · right
          exact ih (count + 2 - left) hrightLt (start := start + left)
            (by omega) (by omega)

lemma cubicBalancedAny_eq_false_of {start count : ℕ} {f : ℕ → Bool}
    (h : ∀ i, start ≤ i → i < start + count → f i = false) :
    cubicBalancedAny start count f = false := by
  induction count using Nat.strong_induction_on generalizing start with
  | h count ih =>
      rcases count with _ | count
      · simp only [cubicBalancedAny]
      rcases count with _ | count
      · change cubicBalancedAny start 1 f = false
        simpa only [cubicBalancedAny] using h start (by omega) (by omega)
      · let left := (count + 2) / 2
        have hleftPos : 0 < left := by
          dsimp [left]
          omega
        have hleftLt : left < count + 2 := by
          dsimp [left]
          omega
        have hrightLt : count + 2 - left < count + 2 := by omega
        simp only [cubicBalancedAny]
        rw [ih left hleftLt (start := start),
          ih (count + 2 - left) hrightLt (start := start + left)]
        · rfl
        · intro i hlo hi
          exact h i (by omega) (by omega)
        · intro i hlo hi
          exact h i hlo (by omega)

/-- A structurally recursive range disjunction.  The largest concrete range
in this certificate has length `433`, so its linear call stack remains below
Lean's ordinary recursion limit while definitional evaluation stays lazy. -/
def cubicAnyRange (start : ℕ) : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | count + 1, f => f start || cubicAnyRange (start + 1) count f

lemma cubicAnyRange_eq_true_of {start count i : ℕ} {f : ℕ → Bool}
    (hlo : start ≤ i) (hi : i < start + count) (hfi : f i = true) :
    cubicAnyRange start count f = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
      simp only [cubicAnyRange, Bool.or_eq_true]
      by_cases his : i = start
      · left
        simpa [his] using hfi
      · right
        apply ih (start := start + 1) (by omega) (by omega)

def cubicCRTSearchAux (d kind : ℕ) : List ℕ → ℕ → ℕ → Bool
  | [], _, x =>
      decide (433 < x) && cubicCRTTerminalCompositeGate x &&
        cubicCRTTrialPairGate d x
  | r :: rs, M, x =>
      if 36000000 ≤ M then
        cubicCRTConstraint d kind r x && cubicCRTSearchAux d kind rs (M * r) x
      else
        cubicAnyRange 0 r fun t ↦
          let z := x + M * t
          decide (z < 36000000) && cubicCRTConstraint d kind r z &&
            (if 36000000 ≤ M * r then cubicCRTWheelGate d z else true) &&
              cubicCRTSearchAux d kind rs (M * r) z

def cubicCRTSearch (d kind : ℕ) : Bool :=
  cubicCRTSearchAux d kind cubicCRTConstraintList 1 0

def cubicCRTSearchGapCheck (d : ℕ) : Bool :=
  !cubicCRTSearch d 0 && !cubicCRTSearch d 1

def cubicCRTSearchSingleCheck : Bool :=
  !cubicCRTSearch 0 2

end

end Erdos1058
