/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes the density-theoretic deduction resolving Erdős Problem 378
from Granville and Ramaré's distribution theorem for squarefree entries in rows
of Pascal's triangle.

Mathematical source:
A. Granville and O. Ramaré, "Explicit bounds on exponential sums and the
scarcity of squarefree binomial coefficients", Mathematika 43 (1996), 73--107.

The detailed reconstruction and Leanization plan is `tex/378.tex`.
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Periodic
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Analysis.PSeries
import ErdosProblems.Erdos387.LocalDensity
import ErdosProblems.Erdos378.ReciprocalPrimeSelection
import ErdosProblems.Erdos378.ThreeBlockSieve
import ErdosProblems.Erdos378.CentralAsymptotic
import ErdosProblems.Erdos378.HighIndexCutoffBridge
import Util.Density

open Filter
open scoped Topology symmDiff

namespace Erdos378

/-- The interior indices `1 ≤ k < n` for which `n.choose k` is squarefree. -/
def squarefreeBinomialIndices (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter fun k ↦ Squarefree (Nat.choose n k)

/-- The number of squarefree interior entries in row `n` of Pascal's triangle. -/
def squarefreeBinomialCount (n : ℕ) : ℕ :=
  (squarefreeBinomialIndices n).card

/-- Rows having exactly `j` squarefree entries in the range `1 ≤ k < n`. -/
def exactCountSet (j : ℕ) : Set ℕ :=
  {n | squarefreeBinomialCount n = j}

/-- Rows having at least `r` squarefree entries in the range `1 ≤ k < n`. -/
def atLeastCountSet (r : ℕ) : Set ℕ :=
  {n | r ≤ squarefreeBinomialCount n}

/-- Rows having fewer than `r` squarefree interior entries. -/
def belowCountSet (r : ℕ) : Set ℕ :=
  {n | squarefreeBinomialCount n < r}

/-! ## Finite edge cutoffs and the middle-index tail -/

/-- The squarefree coefficients whose index lies within `M` places of one
of the two endpoints.  Unlike a one-sided cutoff, this definition partitions
the full interior range without needing a separate small-row exception. -/
def edgeSquarefreeBinomialIndices (M n : ℕ) : Finset ℕ :=
  (squarefreeBinomialIndices n).filter fun k ↦ k ≤ M ∨ n - k ≤ M

/-- The complementary squarefree coefficients, farther than `M` from both
endpoints. -/
def middleSquarefreeBinomialIndices (M n : ℕ) : Finset ℕ :=
  (squarefreeBinomialIndices n).filter fun k ↦ M < k ∧ M < n - k

/-- Rows containing a squarefree coefficient farther than `M` from both
endpoints.  Granville--Ramaré's uniform scarcity theorem says that the upper
density of these sets tends to zero as `M → ∞`. -/
def middleExceptionalSet (M : ℕ) : Set ℕ :=
  {n | (middleSquarefreeBinomialIndices M n).Nonempty}

/-- Exact-count fibers for the finite two-sided edge cutoff. -/
def cutoffExactCountSet (M j : ℕ) : Set ℕ :=
  {n | (edgeSquarefreeBinomialIndices M n).card = j}

/-- The squarefree coefficients at the fixed left indices `1, ..., M`.
For rows beyond `2 * M`, symmetry gives two edge coefficients for each
member of this finset. -/
def leftSquarefreeBinomialIndices (M n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter fun k ↦ Squarefree (Nat.choose n k)

/-- The fiber of one complete squarefree/non-squarefree pattern at the fixed
left indices. -/
def leftPatternSet (M : ℕ) (K : Finset ℕ) : Set ℕ :=
  {n | leftSquarefreeBinomialIndices M n = K}

/-- Rows with exactly `q` squarefree coefficients among the fixed left
indices `1, ..., M`. -/
def leftExactCountSet (M q : ℕ) : Set ℕ :=
  {n | (leftSquarefreeBinomialIndices M n).card = q}

/-- The eventual two-sided edge count expressed through the fixed left
indices and binomial symmetry. -/
def doubledLeftExactCountSet (M j : ℕ) : Set ℕ :=
  {n | 2 * (leftSquarefreeBinomialIndices M n).card = j}

/-- The finite-pattern density input.  This is the elementary fixed-index
sieve portion of Granville--Ramaré, separated from their uniform tail. -/
def FiniteLeftPatternsHaveDensity : Prop :=
  ∀ M : ℕ, ∀ K ∈ (Finset.Icc 1 M).powerset,
    ∃ d : ℝ, (leftPatternSet M K).HasDensity d

/-- The source-faithful uniform tail statement needed to pass from every
finite edge cutoff to the whole row. -/
def MiddleTailVanishes : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ᶠ N : ℕ in atTop,
    (middleExceptionalSet M).partialDensity (b := N) < ε

/-- The total number of squarefree middle entries in rows below `N`.
Counting pairs is stronger than merely counting rows containing such an
entry, and is the form in which the analytic sieve naturally supplies the
tail estimate. -/
def middlePairCount (M N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, (middleSquarefreeBinomialIndices M n).card

/-- Pair-counting form of the uniform scarcity estimate. -/
def MiddlePairScarcity : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ᶠ N : ℕ in atTop,
    (middlePairCount M N : ℝ) / N < ε

/-! ## The local two-carry obstruction

The residue rectangles in Granville--Ramaré's sieve force a borrow modulo
`p` and another modulo `p ^ 2`.  The next three declarations isolate that
source-faithful Kummer step. -/

/-- The full two-borrow rectangle modulo `p ^ 2` for the index `k`. -/
def kummerBadResidues (p k : ℕ) : Finset ℕ :=
  (Finset.range (p ^ 2)).filter fun m ↦ m % p < k % p ∧ m < k

/-- Subtraction modulo `q` after a borrow. -/
lemma sub_mod_of_mod_lt {n k q : ℕ} (hq : 0 < q) (hkn : k ≤ n)
    (hmod : n % q < k % q) :
    (n - k) % q = q + n % q - k % q := by
  have hle : k % q ≤ q + n % q := by
    have hklt := Nat.mod_lt k hq
    omega
  have hcong : q + n % q - k % q ≡ n - k [MOD q] := by
    apply Nat.ModEq.sub hle hkn
    · change (q + n % q) % q = n % q
      simp
    · exact Nat.mod_modEq k q
  have hcandlt : q + n % q - k % q < q := by omega
  change (q + n % q - k % q) % q = (n - k) % q at hcong
  rw [Nat.mod_eq_of_lt hcandlt] at hcong
  exact hcong.symm

/-- A borrow modulo `q` is exactly a carry in Kummer's sum. -/
lemma carry_of_mod_lt {n k q : ℕ} (hq : 0 < q) (hkn : k ≤ n)
    (hmod : n % q < k % q) :
    q ≤ k % q + (n - k) % q := by
  rw [sub_mod_of_mod_lt hq hkn hmod]
  omega

/-- Two prescribed modular borrows force a square prime divisor of the
binomial coefficient. -/
lemma prime_sq_dvd_choose_of_two_mod_borrows {p n k : ℕ}
    (hp : p.Prime) (hkn : k ≤ n) (hp2n : p ^ 2 ≤ n)
    (h₁ : n % p < k % p) (h₂ : n % (p ^ 2) < k % (p ^ 2)) :
    p ^ 2 ∣ n.choose k := by
  rw [hp.pow_dvd_iff_le_factorization (Nat.choose_pos hkn).ne']
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)]
  have hlog : 2 ≤ Nat.log p n :=
    Nat.le_log_of_pow_le hp.one_lt hp2n
  have hsub : ({1, 2} : Finset ℕ) ⊆
      (Finset.Ico 1 (Nat.log p n + 1)).filter
        (fun i ↦ p ^ i ≤ k % p ^ i + (n - k) % p ^ i) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simp only [Finset.mem_filter, Finset.mem_Ico, pow_one]
      exact ⟨⟨by omega, by omega⟩, carry_of_mod_lt hp.pos hkn h₁⟩
    · simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨by omega, by omega⟩,
        carry_of_mod_lt (pow_pos hp.pos 2) hkn h₂⟩
  have hcard := Finset.card_le_card hsub
  norm_num at hcard ⊢
  exact hcard

/-- Membership in the full bad rectangle is the concrete local obstruction
used in the sieve. -/
theorem prime_sq_dvd_choose_of_mod_mem_kummerBadResidues {p n k : ℕ}
    (hp : p.Prime) (hkn : k ≤ n) (hkp : k < p ^ 2) (hp2n : p ^ 2 ≤ n)
    (hbad : n % (p ^ 2) ∈ kummerBadResidues p k) :
    p ^ 2 ∣ n.choose k := by
  rw [kummerBadResidues, Finset.mem_filter] at hbad
  have hmodp : n % p = (n % (p ^ 2)) % p := by
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self p two_ne_zero)]
  apply prime_sq_dvd_choose_of_two_mod_borrows hp hkn hp2n
  · rw [hmodp]
    exact hbad.2.1
  · rw [Nat.mod_eq_of_lt hkp]
    exact hbad.2.2

/-- Quotient/remainder coordinates for the full two-borrow rectangle. -/
def kummerRectanglePairs (p k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k / p + 1)).product (Finset.range (k % p))

/-- Recombine quotient/remainder coordinates in base `p`. -/
def kummerRectangleEncode (p : ℕ) (x : ℕ × ℕ) : ℕ :=
  x.1 * p + x.2

lemma kummerRectangleEncode_injectiveOn {p k : ℕ} (hp : 0 < p) :
    Set.InjOn (kummerRectangleEncode p) (kummerRectanglePairs p k : Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  have hxc : x.2 < p := by
    have hxmem := Finset.mem_product.mp hx
    exact (Finset.mem_range.mp hxmem.2).trans (Nat.mod_lt k hp)
  have hyc : y.2 < p := by
    have hymem := Finset.mem_product.mp hy
    exact (Finset.mem_range.mp hymem.2).trans (Nat.mod_lt k hp)
  have hxd : (kummerRectangleEncode p x) / p = x.1 := by
    simp only [kummerRectangleEncode]
    calc
      (x.1 * p + x.2) / p = (p * x.1 + x.2) / p := by rw [Nat.mul_comm]
      _ = x.1 + x.2 / p := Nat.mul_add_div hp x.1 x.2
      _ = x.1 := by rw [Nat.div_eq_of_lt hxc, Nat.add_zero]
  have hyd : (kummerRectangleEncode p y) / p = y.1 := by
    simp only [kummerRectangleEncode]
    calc
      (y.1 * p + y.2) / p = (p * y.1 + y.2) / p := by rw [Nat.mul_comm]
      _ = y.1 + y.2 / p := Nat.mul_add_div hp y.1 y.2
      _ = y.1 := by rw [Nat.div_eq_of_lt hyc, Nat.add_zero]
  apply Prod.ext
  · have hd : x.1 = y.1 := by rw [← hxd, ← hyd, hxy]
    exact hd
  · have hd : x.1 = y.1 := by rw [← hxd, ← hyd, hxy]
    simp only [kummerRectangleEncode, hd] at hxy
    omega

lemma kummerBadResidues_eq_image {p k : ℕ} (hp : 0 < p) (hkp : k < p ^ 2) :
    kummerBadResidues p k =
      (kummerRectanglePairs p k).image (kummerRectangleEncode p) := by
  ext m
  constructor
  · intro hm
    rw [kummerBadResidues, Finset.mem_filter, Finset.mem_range] at hm
    apply Finset.mem_image.mpr
    refine ⟨(m / p, m % p), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hm.2.2.le)
      · exact Finset.mem_range.mpr hm.2.1
    · simp only [kummerRectangleEncode]
      calc
        m / p * p + m % p = m % p + p * (m / p) := by ac_rfl
        _ = m := Nat.mod_add_div m p
  · intro hm
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
    have hx' : x ∈ (Finset.range (k / p + 1)).product
        (Finset.range (k % p)) := by
      simpa only [kummerRectanglePairs] using hx
    have hxpair := Finset.mem_product.mp hx'
    have hxd : x.1 ≤ k / p := by
      have := Finset.mem_range.mp hxpair.1
      omega
    have hxc : x.2 < k % p := Finset.mem_range.mp hxpair.2
    have hcp : x.2 < p := hxc.trans (Nat.mod_lt k hp)
    have hkdecomp : k = k / p * p + k % p := by
      calc
        k = k % p + p * (k / p) := (Nat.mod_add_div k p).symm
        _ = k / p * p + k % p := by ac_rfl
    have hlt : kummerRectangleEncode p x < k := by
      change x.1 * p + x.2 < k
      calc
        x.1 * p + x.2 ≤ (k / p) * p + x.2 := by gcongr
        _ < (k / p) * p + k % p := Nat.add_lt_add_left hxc _
        _ = k := hkdecomp.symm
    rw [kummerBadResidues, Finset.mem_filter, Finset.mem_range]
    refine ⟨hlt.trans hkp, ?_, hlt⟩
    have hmod : (kummerRectangleEncode p x) % p = x.2 := by
      simp only [kummerRectangleEncode]
      calc
        (x.1 * p + x.2) % p = (x.2 + p * x.1) % p := by
          congr 1
          ac_rfl
        _ = x.2 % p := Nat.add_mul_mod_self_left x.2 p x.1
        _ = x.2 := Nat.mod_eq_of_lt hcp
    rw [hmod]
    exact hxc

/-- The local two-borrow rectangle has the exact size predicted by its
base-`p` quotient/remainder coordinates. -/
theorem card_kummerBadResidues {p k : ℕ} (hp : 0 < p) (hkp : k < p ^ 2) :
    (kummerBadResidues p k).card = (k / p + 1) * (k % p) := by
  rw [kummerBadResidues_eq_image hp hkp,
    Finset.card_image_of_injOn (kummerRectangleEncode_injectiveOn hp)]
  simp [kummerRectanglePairs]

/-- In the prime window used by Granville--Ramaré, the exact bad rectangle
occupies a fixed positive proportion of all classes modulo `p²`.  The
inequalities below are deliberately weaker integral consequences of their
fractional-part conditions. -/
theorem half_sq_le_card_kummerBadResidues {p k : ℕ} (hp : 0 < p)
    (hkp : k < p ^ 2) (hlarge : p ^ 2 ≤ 2 * k)
    (hrem : p ≤ 2 * (k % p)) :
    (p / 2) ^ 2 ≤ (kummerBadResidues p k).card := by
  rw [card_kummerBadResidues hp hkp, pow_two]
  have hquot : p / 2 ≤ k / p + 1 := by
    have hmod := Nat.mod_lt k hp
    have hkdecomp : k = k / p * p + k % p := by
      calc
        k = k % p + p * (k / p) := (Nat.mod_add_div k p).symm
        _ = k / p * p + k % p := by ac_rfl
    by_contra h
    have hsmall : 2 * (k / p + 1) ≤ p := by omega
    have hklt : k < (k / p + 1) * p := by
      rw [hkdecomp]
      nlinarith
    nlinarith
  have hhalf : p / 2 ≤ k % p := by omega
  exact Nat.mul_le_mul hquot hhalf

/-! The same rectangle can be used without the temporary hypothesis
`k < p ^ 2`: only the lowest two base-`p` digits of `k` enter the two
prescribed borrows. -/

/-- The two-borrow rectangle for an arbitrary index, obtained by reducing
the index modulo `p ^ 2`. -/
def generalKummerBadResidues (p k : ℕ) : Finset ℕ :=
  kummerBadResidues p (k % (p ^ 2))

/-- Reduction modulo `p ^ 2` and then modulo `p` is reduction modulo `p`. -/
lemma mod_sq_mod_eq_mod {p k : ℕ} :
    (k % (p ^ 2)) % p = k % p := by
  rw [Nat.mod_mod_of_dvd k (dvd_pow_self p two_ne_zero)]

/-- Membership in the general rectangle forces two Kummer borrows and hence
a square prime divisor. -/
theorem prime_sq_dvd_choose_of_mod_mem_generalKummerBadResidues
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hp2n : p ^ 2 ≤ n)
    (hbad : n % (p ^ 2) ∈ generalKummerBadResidues p k) :
    p ^ 2 ∣ n.choose k := by
  rw [generalKummerBadResidues, kummerBadResidues, Finset.mem_filter] at hbad
  have hmodp : n % p = (n % (p ^ 2)) % p := by
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self p two_ne_zero)]
  apply prime_sq_dvd_choose_of_two_mod_borrows hp hkn hp2n
  · rw [hmodp]
    simpa only [mod_sq_mod_eq_mod] using hbad.2.1
  · exact hbad.2.2

/-! The source's second Kummer interface concerns primes whose squares lie
between `n - k` and `n`.  In that range the addition `k + (n - k) = n`
already has a carry in the `p¹` column.  Squarefreeness therefore forbids a
second carry in the units column.  The fractional-part identity in
Granville--Ramaré Proposition 3.1 is exactly the following integral
statement. -/

/-- If `n.choose k` is squarefree and `n - k < p² ≤ n` (with
`k ≤ n / 2`), then the base-`p` units digits of `k` and `n-k` add without
a carry. -/
theorem no_low_carry_of_prime_sq_near_n {p n k : ℕ}
    (hp : p.Prime) (hhalf : k ≤ n / 2)
    (hlower : n - k < p ^ 2) (hupper : p ^ 2 ≤ n)
    (hsq : Squarefree (n.choose k)) :
    k % p + (n - k) % p < p := by
  have hkn : k ≤ n := hhalf.trans (Nat.div_le_self n 2)
  have hother : k ≤ n - k := by omega
  have hklt : k < p ^ 2 := hother.trans_lt hlower
  by_contra hcarry
  have hlow : n % p < k % p := by
    by_contra hnborrow
    have hsumMod := Nat.add_mod_add_of_le_add_mod (Nat.le_of_not_gt hcarry)
        (a := k) (b := n - k) (c := p)
    rw [show k + (n - k) = n by omega] at hsumMod
    have hnkp : (n - k) % p < p := Nat.mod_lt (n - k) hp.pos
    omega
  have hnlt : n < 2 * p ^ 2 := by omega
  have hnmod : n % (p ^ 2) = n - p ^ 2 := by
    rw [Nat.mod_eq_sub_mod hupper,
      Nat.mod_eq_of_lt (by omega : n - p ^ 2 < p ^ 2)]
  have hhigh : n % (p ^ 2) < k % (p ^ 2) := by
    rw [hnmod, Nat.mod_eq_of_lt hklt]
    omega
  have hdiv := prime_sq_dvd_choose_of_two_mod_borrows
    hp hkn hupper hlow hhigh
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) (by
    simpa only [pow_two] using hdiv)

/-- The general two-borrow rectangle has the same quotient/remainder count,
now applied to the two-digit residue of `k`. -/
theorem card_generalKummerBadResidues {p k : ℕ} (hp : 0 < p) :
    (generalKummerBadResidues p k).card =
      ((k % (p ^ 2)) / p + 1) * (k % p) := by
  rw [generalKummerBadResidues,
    card_kummerBadResidues hp (Nat.mod_lt _ (pow_pos hp 2)),
    mod_sq_mod_eq_mod]

/-- The integral form of the two fractional-part hypotheses used in
Granville--Ramaré's section 5c.  In the window `sqrt k < p ≤ 10/9 sqrt k`,
the second inequality follows from the endpoints, while the first is the
prime-selection condition supplied by their Lemma 5.1. -/
def SourceSievePrimeConditions (p k : ℕ) : Prop :=
  k < p ^ 2 ∧ 2 * p ≤ 3 * (k % p) ∧ 81 * p ^ 2 ≤ 100 * k

/-- Under the source's `2/3` and `81/100` fractional-part conditions, the
exact Kummer rectangle occupies at least `27/50` of all classes modulo
`p²`.  Keeping the assertion over naturals avoids all rounding issues. -/
theorem fifty_mul_card_generalKummerBadResidues_ge
    {p k : ℕ} (hp : 0 < p) (hsource : SourceSievePrimeConditions p k) :
    27 * p ^ 2 ≤ 50 * (generalKummerBadResidues p k).card := by
  rcases hsource with ⟨hkp2, hrem, hsize⟩
  rw [card_generalKummerBadResidues hp, Nat.mod_eq_of_lt hkp2]
  let a := k / p
  let b := k % p
  have hk : k = a * p + b := by
    dsimp only [a, b]
    simpa only [Nat.mul_comm] using (Nat.div_add_mod k p).symm
  have hb : b < p := by
    dsimp only [b]
    exact Nat.mod_lt k hp
  have ha : 81 * p ≤ 100 * (a + 1) := by
    have hklt : k < (a + 1) * p := by
      rw [hk]
      calc
        a * p + b < a * p + p := Nat.add_lt_add_left hb _
        _ = (a + 1) * p := by rw [Nat.add_mul]; simp
    have hscaled : 81 * p ^ 2 < 100 * ((a + 1) * p) :=
      hsize.trans_lt ((Nat.mul_lt_mul_left (by norm_num : 0 < 100)).mpr hklt)
    have hcancel : (81 * p) * p < (100 * (a + 1)) * p := by
      calc
        (81 * p) * p = 81 * p ^ 2 := by ring
        _ < 100 * ((a + 1) * p) := hscaled
        _ = (100 * (a + 1)) * p := by ring
    exact ((Nat.mul_lt_mul_right hp).mp hcancel).le
  have hab : (81 * p) * (2 * p) ≤
      (100 * (a + 1)) * (3 * b) :=
    Nat.mul_le_mul ha (by simpa only [b] using hrem)
  have hab' : 6 * (27 * p ^ 2) ≤
      6 * (50 * ((a + 1) * b)) := by
    calc
      6 * (27 * p ^ 2) = (81 * p) * (2 * p) := by ring
      _ ≤ (100 * (a + 1)) * (3 * b) := hab
      _ = 6 * (50 * ((a + 1) * b)) := by ring
  exact (Nat.mul_le_mul_left_iff (by norm_num : 0 < 6)).mp hab'

/-- In particular the bad rectangle is at least as large as its complement.
This is the precise local inequality used to discard the Euler weights in
the lower bound for Granville--Ramaré's large-sieve denominator. -/
theorem complement_card_le_generalKummerBadResidues
    {p k : ℕ} (hp : 0 < p) (hsource : SourceSievePrimeConditions p k) :
    p ^ 2 - (generalKummerBadResidues p k).card ≤
      (generalKummerBadResidues p k).card := by
  have hbad := fifty_mul_card_generalKummerBadResidues_ge hp hsource
  have hsub : generalKummerBadResidues p k ⊆ Finset.range (p ^ 2) := by
    intro m hm
    exact (Finset.mem_filter.mp hm).1
  have hcard : (generalKummerBadResidues p k).card ≤ p ^ 2 := by
    simpa using Finset.card_le_card hsub
  omega

/-- The section-5c local sieve implication in its final form: for an index
in the left half of a row, every source sieve prime rules out its complete
Kummer rectangle whenever the binomial coefficient is squarefree. -/
theorem squarefree_avoids_generalKummerBadResidues
    {p n k : ℕ} (hp : p.Prime) (hhalf : k ≤ n / 2)
    (hsource : SourceSievePrimeConditions p k)
    (hsq : Squarefree (n.choose k)) :
    n % (p ^ 2) ∉ generalKummerBadResidues p k := by
  intro hbad
  have hkn : k ≤ n := hhalf.trans (Nat.div_le_self n 2)
  have hp2n : p ^ 2 ≤ n := by
    have hsize := hsource.2.2
    have hkn2 : 2 * k ≤ n := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hhalf
    nlinarith
  have hdiv := prime_sq_dvd_choose_of_mod_mem_generalKummerBadResidues
    hp hkn hp2n hbad
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) (by
    simpa only [pow_two] using hdiv)

/-- The analytic prime-selection theorem supplies exactly the three integral
conditions used by the Kummer rectangle. -/
lemma sourceGoodPrimeSet_mem_conditions {k p : ℕ}
    (hp : p ∈ ReciprocalPrimeSelection.sourceGoodPrimeSet k) :
    p.Prime ∧ SourceSievePrimeConditions p k := by
  rcases ReciprocalPrimeSelection.sourceGoodPrimeSet_conditions hp with
    ⟨hprime, _hsqrt, _hupper, hkp, hrem, hsize⟩
  exact ⟨hprime, hkp, hrem, hsize⟩

/-! ## A fixed-degree CRT sieve for one index -/

open ThreeBlockSieve
open FiniteResiduePolynomial

lemma generalKummerBadResidues_subset_range (p k : ℕ) :
    generalKummerBadResidues p k ⊆ Finset.range (p ^ 2) := by
  intro a ha
  exact (Finset.mem_filter.mp ha).1

lemma card_generalKummerBadResidues_le (p k : ℕ) :
    (generalKummerBadResidues p k).card ≤ p ^ 2 := by
  simpa using Finset.card_le_card (generalKummerBadResidues_subset_range p k)

lemma half_le_source_bad_density {p k : ℕ}
    (hp : p ∈ ReciprocalPrimeSelection.sourceGoodPrimeSet k) :
    (1 / 2 : ℝ) ≤
      ((generalKummerBadResidues p k).card : ℝ) / p ^ 2 := by
  obtain ⟨hprime, hsource⟩ := sourceGoodPrimeSet_mem_conditions hp
  have hnat := fifty_mul_card_generalKummerBadResidues_ge
    hprime.pos hsource
  have hp2pos : (0 : ℝ) < (p : ℝ) ^ 2 := by
    exact pow_pos (by exact_mod_cast hprime.pos) 2
  rw [le_div_iff₀ hp2pos]
  have hreal : (27 : ℝ) * (p : ℝ) ^ 2 ≤
      50 * (generalKummerBadResidues p k).card := by
    exact_mod_cast hnat
  nlinarith

lemma source_block_mass_ge_half_card {k : ℕ} (G : Finset ℕ)
    (hG : G ⊆ ReciprocalPrimeSelection.sourceGoodPrimeSet k) :
    (G.card : ℝ) / 2 ≤
      blockMass (fun p : ℕ ↦ p ^ 2)
        (fun p : ℕ ↦ generalKummerBadResidues p k) G := by
  unfold blockMass
  calc
    (G.card : ℝ) / 2 = ∑ _p ∈ G, (1 / 2 : ℝ) := by simp; ring
    _ ≤ ∑ p ∈ G,
        ((generalKummerBadResidues p k).card : ℝ) / p ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact half_le_source_bad_density (hG hp)
    _ = _ := by simp only [Nat.cast_pow]

lemma source_block_mass_pos {k : ℕ} {G : Finset ℕ}
    (hG : G ⊆ ReciprocalPrimeSelection.sourceGoodPrimeSet k)
    (hG0 : G.Nonempty) :
    0 < blockMass (fun p : ℕ ↦ p ^ 2)
      (fun p : ℕ ↦ generalKummerBadResidues p k) G := by
  have hcard : (0 : ℝ) < G.card := by
    exact_mod_cast Finset.card_pos.mpr hG0
  exact (by positivity : (0 : ℝ) < (G.card : ℝ) / 2).trans_le
    (source_block_mass_ge_half_card G hG)

lemma source_card_le_twice_block_mass {k : ℕ} {G : Finset ℕ}
    (hG : G ⊆ ReciprocalPrimeSelection.sourceGoodPrimeSet k) :
    (G.card : ℝ) ≤ 2 *
      blockMass (fun p : ℕ ↦ p ^ 2)
        (fun p : ℕ ↦ generalKummerBadResidues p k) G := by
  linarith [source_block_mass_ge_half_card G hG]

lemma source_block_hitCount_eq_zero {k n : ℕ} {G : Finset ℕ}
    (hG : G ⊆ ReciprocalPrimeSelection.sourceGoodPrimeSet k)
    (hhalf : k ≤ n / 2) (hsq : Squarefree (n.choose k)) :
    blockHitCount (fun p : ℕ ↦ p ^ 2)
      (fun p : ℕ ↦ generalKummerBadResidues p k) G n = 0 := by
  unfold blockHitCount
  apply Finset.sum_eq_zero
  intro p hp
  unfold localIndicator
  rw [if_neg]
  exact squarefree_avoids_generalKummerBadResidues
    (sourceGoodPrimeSet_mem_conditions (hG hp)).1 hhalf
      (sourceGoodPrimeSet_mem_conditions (hG hp)).2 hsq

/-- A three-block, fixed-degree Selberg weight gives a uniform finite count
for rows in which one prescribed coefficient is squarefree.  The endpoint
error has degree six, independently of the number of available primes. -/
theorem card_squarefree_choose_fixed_index_le_three_block
    {k N : ℕ} (hk : 1 ≤ k)
    (G₀ G₁ G₂ : Finset ℕ) (T : ℝ)
    (hG₀ : G₀ ⊆ ReciprocalPrimeSelection.sourceGoodPrimeSet k)
    (hG₁ : G₁ ⊆ ReciprocalPrimeSelection.sourceGoodPrimeSet k)
    (hG₂ : G₂ ⊆ ReciprocalPrimeSelection.sourceGoodPrimeSet k)
    (h₀₁ : Disjoint G₀ G₁) (h₀₂ : Disjoint G₀ G₂)
    (h₁₂ : Disjoint G₁ G₂)
    (hT : 0 < T)
    (hTG₀ : T ≤ (G₀.card : ℝ)) (hTG₁ : T ≤ (G₁.card : ℝ))
    (hTG₂ : T ≤ (G₂.card : ℝ)) :
    (((Finset.range N).filter fun n ↦
      k ≤ n / 2 ∧ Squarefree (n.choose k)).card : ℝ) ≤
      (N : ℝ) * (64 / T ^ 3) + 729 * (4 * (k : ℝ)) ^ 6 := by
  let q : ℕ → ℕ := fun p ↦ p ^ 2
  let A : ℕ → Finset ℕ := fun p ↦ generalKummerBadResidues p k
  let B₀ : ℝ := blockMass q A G₀
  let B₁ : ℝ := blockMass q A G₁
  let B₂ : ℝ := blockMass q A G₂
  let P : ℕ → Prop := fun n ↦ k ≤ n / 2 ∧ Squarefree (n.choose k)
  have hG₀ne : G₀.Nonempty := Finset.card_pos.mp (by
    have : (0 : ℝ) < G₀.card := hT.trans_le hTG₀
    exact_mod_cast this)
  have hG₁ne : G₁.Nonempty := Finset.card_pos.mp (by
    have : (0 : ℝ) < G₁.card := hT.trans_le hTG₁
    exact_mod_cast this)
  have hG₂ne : G₂.Nonempty := Finset.card_pos.mp (by
    have : (0 : ℝ) < G₂.card := hT.trans_le hTG₂
    exact_mod_cast this)
  have hB₀ : 0 < B₀ := source_block_mass_pos hG₀ hG₀ne
  have hB₁ : 0 < B₁ := source_block_mass_pos hG₁ hG₁ne
  have hB₂ : 0 < B₂ := source_block_mass_pos hG₂ hG₂ne
  have hcard₀ : (G₀.card : ℝ) ≤ 2 * B₀ :=
    source_card_le_twice_block_mass hG₀
  have hcard₁ : (G₁.card : ℝ) ≤ 2 * B₁ :=
    source_card_le_twice_block_mass hG₁
  have hcard₂ : (G₂.card : ℝ) ≤ 2 * B₂ :=
    source_card_le_twice_block_mass hG₂
  have hsupp {t : TripleTerm G₀ G₁ G₂} :
      tripleTermSupport t ⊆ G₀ ∪ G₁ ∪ G₂ := by
    intro p hp
    change p ∈ (blockTermSupport t.1 ∪ blockTermSupport t.2.1) ∪
      blockTermSupport t.2.2 at hp
    rcases Finset.mem_union.mp hp with hp₀₁ | hp₂
    · rcases Finset.mem_union.mp hp₀₁ with hp₀ | hp₁
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inl (blockTermSupport_subset t.1 hp₀))))
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inr (blockTermSupport_subset t.2.1 hp₁))))
    · exact Finset.mem_union.mpr
        (Or.inr (blockTermSupport_subset t.2.2 hp₂))
  have hall : G₀ ∪ G₁ ∪ G₂ ⊆
      ReciprocalPrimeSelection.sourceGoodPrimeSet k := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp₀₁ | hp₂
    · rcases Finset.mem_union.mp hp₀₁ with hp₀ | hp₁
      · exact hG₀ hp₀
      · exact hG₁ hp₁
    · exact hG₂ hp₂
  have hq : ∀ t : TripleTerm G₀ G₁ G₂,
      ∀ p ∈ tripleTermSupport t, q p ≠ 0 := by
    intro t p hp
    have hprime := (sourceGoodPrimeSet_mem_conditions (hall (hsupp hp))).1
    dsimp only [q]
    exact pow_ne_zero 2 hprime.ne_zero
  have hcop : ∀ t : TripleTerm G₀ G₁ G₂,
      ∀ p ∈ tripleTermSupport t, ∀ r ∈ tripleTermSupport t,
        p ≠ r → Nat.Coprime (q p) (q r) := by
    intro t p hp r hr hpr
    have hpprime := (sourceGoodPrimeSet_mem_conditions (hall (hsupp hp))).1
    have hrprime := (sourceGoodPrimeSet_mem_conditions (hall (hsupp hr))).1
    dsimp only [q]
    exact ((Nat.coprime_primes hpprime hrprime).mpr hpr).pow 2 2
  have hA : ∀ t : TripleTerm G₀ G₁ G₂,
      ∀ p ∈ tripleTermSupport t, ∀ a ∈ A p, a < q p := by
    intro t p hp a ha
    exact Finset.mem_range.mp (generalKummerBadResidues_subset_range p k ha)
  have hlocalCard : ∀ p ∈ G₀ ∪ G₁ ∪ G₂,
      ((A p).card : ℝ) ≤ 4 * (k : ℝ) := by
    intro p hp
    have hpdata := sourceGoodPrimeSet_mem_conditions (hall hp)
    have hcard := card_generalKummerBadResidues_le p k
    have hsize := hpdata.2.2
    dsimp only [A]
    have hcardR : ((generalKummerBadResidues p k).card : ℝ) ≤
        (p : ℝ) ^ 2 := by exact_mod_cast hcard
    have hsizeR : (81 : ℝ) * (p : ℝ) ^ 2 ≤ 100 * k := by
      exact_mod_cast hsize.2
    nlinarith
  have hprod : ∀ t : TripleTerm G₀ G₁ G₂,
      (∏ p ∈ tripleTermSupport t, ((A p).card : ℝ)) ≤
        (4 * (k : ℝ)) ^ 6 := by
    intro t
    apply product_local_cards_le_pow_six A G₀ G₁ G₂
    · exact_mod_cast (show 1 ≤ 4 * k by omega)
    · exact hlocalCard
  have hmajor : ∀ n ∈ Finset.range N,
      (if P n then (1 : ℝ) else 0) ≤
        ∑ t : TripleTerm G₀ G₁ G₂,
          tripleTermCoeff B₀ B₁ B₂ t *
            indicatorMonomial q A (tripleTermSupport t) n := by
    intro n hn
    rw [sum_tripleTerm_indicator q A G₀ G₁ G₂ B₀ B₁ B₂
      h₀₁ h₀₂ h₁₂]
    by_cases hPn : P n
    · simp only [hPn, if_true]
      have hz₀ : blockHitCount q A G₀ n = 0 := by
        simpa only [q, A] using source_block_hitCount_eq_zero hG₀ hPn.1 hPn.2
      have hz₁ : blockHitCount q A G₁ n = 0 := by
        simpa only [q, A] using source_block_hitCount_eq_zero hG₁ hPn.1 hPn.2
      have hz₂ : blockHitCount q A G₂ n = 0 := by
        simpa only [q, A] using source_block_hitCount_eq_zero hG₂ hPn.1 hPn.2
      rw [hz₀, hz₁, hz₂]
      norm_num
    · simp only [hPn, if_false]
      positivity
  have hcount := card_filter_le_triple_model q A G₀ G₁ G₂
    B₀ B₁ B₂ ((4 * (k : ℝ)) ^ 6) P
    hB₀ hB₁ hB₂ hcard₀ hcard₁ hcard₂ (by positivity)
    hq hcop hA hprod N hmajor
  have hmodel :
      (∑ t : TripleTerm G₀ G₁ G₂,
        tripleTermCoeff B₀ B₁ B₂ t *
          densityMonomial q A (tripleTermSupport t)) =
        (blockVariance q A G₀ / B₀ ^ 2) *
          (blockVariance q A G₁ / B₁ ^ 2) *
            (blockVariance q A G₂ / B₂ ^ 2) := by
    exact sum_tripleTerm_density q A G₀ G₁ G₂ B₀ B₁ B₂
      h₀₁ h₀₂ h₁₂ rfl rfl rfl hB₀.ne' hB₁.ne' hB₂.ne'
  have hAq₀ : ∀ p ∈ G₀, (A p).card ≤ q p := by
    intro p hp
    exact card_generalKummerBadResidues_le p k
  have hAq₁ : ∀ p ∈ G₁, (A p).card ≤ q p := by
    intro p hp
    exact card_generalKummerBadResidues_le p k
  have hAq₂ : ∀ p ∈ G₂, (A p).card ≤ q p := by
    intro p hp
    exact card_generalKummerBadResidues_le p k
  have hmodelLe := triple_model_le_sixtyfour_div_cube q A G₀ G₁ G₂
    B₀ B₁ B₂ T hAq₀ hAq₁ hAq₂ hB₀ hB₁ hB₂ hT
    hTG₀ hTG₁ hTG₂ hcard₀ hcard₁ hcard₂
  rw [hmodel] at hcount
  exact hcount.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmodelLe (by positivity : (0 : ℝ) ≤ N)) le_rfl)

theorem card_squarefree_choose_fixed_index_le_selected
    {k N t : ℕ} (hk : 1 ≤ k)
    (hcard : 3 * t ≤
      (ReciprocalPrimeSelection.sourceGoodPrimeSet k).card)
    (ht : 0 < t) :
    (((Finset.range N).filter fun n ↦
      k ≤ n / 2 ∧ Squarefree (n.choose k)).card : ℝ) ≤
      (N : ℝ) * (64 / (t : ℝ) ^ 3) +
        729 * (4 * (k : ℝ)) ^ 6 := by
  obtain ⟨G₀, G₁, G₂, hG₀, hG₁, hG₂, h₀₁, h₀₂, h₁₂,
      hc₀, hc₁, hc₂⟩ :=
    exists_three_pairwise_disjoint_subsets_card_eq
      (ReciprocalPrimeSelection.sourceGoodPrimeSet k) hcard
  apply card_squarefree_choose_fixed_index_le_three_block hk G₀ G₁ G₂
    (t : ℝ) hG₀ hG₁ hG₂ h₀₁ h₀₂ h₁₂
  · exact_mod_cast ht
  · exact_mod_cast hc₀.ge
  · exact_mod_cast hc₁.ge
  · exact_mod_cast hc₂.ge

def lowSieveBlockSize (k : ℕ) : ℕ := AdaptiveShifts.baseShift k ^ 7

lemma baseShift_pow_eight_le_sqrt (k : ℕ) :
    AdaptiveShifts.baseShift k ^ 8 ≤ Nat.sqrt k := by
  let a := Nat.sqrt k
  let b := Nat.sqrt a
  let c := Nat.sqrt b
  let q := Nat.sqrt c
  have hq : q ^ 2 ≤ c := by
    simpa only [q, pow_two] using Nat.sqrt_le c
  have hc : c ^ 2 ≤ b := by
    simpa only [c, pow_two] using Nat.sqrt_le b
  have hb : b ^ 2 ≤ a := by
    simpa only [b, pow_two] using Nat.sqrt_le a
  calc
    AdaptiveShifts.baseShift k ^ 8 = q ^ 8 := rfl
    _ = ((q ^ 2) ^ 2) ^ 2 := by ring
    _ ≤ (c ^ 2) ^ 2 := by gcongr
    _ ≤ b ^ 2 := by gcongr
    _ ≤ a := hb
    _ = Nat.sqrt k := rfl

lemma eventually_log_sourcePrimeUpper_le_baseShift_div :
    ∀ᶠ k : ℕ in atTop,
      Real.log (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ) ≤
        (AdaptiveShifts.baseShift k : ℝ) / 600 := by
  have hqTop := CentralAsymptotic.tendsto_baseShift_atTop
  have hsize := hqTop.eventually
    CentralAsymptotic.eventually_centralCorrelationSizeCondition
  have hqge : ∀ᶠ k : ℕ in atTop, 2 ≤ AdaptiveShifts.baseShift k :=
    hqTop.eventually (eventually_ge_atTop 2)
  filter_upwards [hsize, hqge] with k hsize hqge
  let q := AdaptiveShifts.baseShift k
  let s := Nat.sqrt k
  let u := ReciprocalPrimeSelection.sourcePrimeUpper k
  have hq8 : q ^ 8 ≤ s := by
    simpa only [q, s] using baseShift_pow_eight_le_sqrt k
  have hs2 : s ^ 2 ≤ k := by
    simpa only [s, pow_two] using Nat.sqrt_le k
  have hsge : 2 ≤ s := by
    have : 2 ^ 8 ≤ q ^ 8 := by gcongr
    omega
  have hkpos : 0 < k := by nlinarith
  have hupos : 0 < u := by
    dsimp only [u, ReciprocalPrimeSelection.sourcePrimeUpper]
    omega
  have huk : u ≤ k := by
    have hu2s : u ≤ 2 * s := by
      dsimp only [u, ReciprocalPrimeSelection.sourcePrimeUpper]
      omega
    nlinarith
  have hloguk : Real.log (u : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by exact_mod_cast hupos) (by exact_mod_cast huk)
  have hkq := CentralAsymptotic.lt_baseShift_succ_pow_sixteen k
  have hkqR : (k : ℝ) ≤ ((q + 1 : ℕ) : ℝ) ^ 16 := by
    exact_mod_cast hkq.le
  have hlogk : Real.log (k : ℝ) ≤ 16 * Real.log ((q + 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by exact_mod_cast hkpos) hkqR
    norm_num only [Nat.cast_add, Nat.cast_one, Real.log_pow, Nat.cast_ofNat] at h ⊢
    exact h
  have hqq : q + 1 ≤ q ^ 2 := by
    calc
      q + 1 ≤ 2 * q := by omega
      _ ≤ q * q := Nat.mul_le_mul_right q hqge
      _ = q ^ 2 := by ring
  have hlogq1 : Real.log ((q + 1 : ℕ) : ℝ) ≤
      2 * Real.log (q : ℝ) := by
    have hqqR : (((q + 1 : ℕ) : ℝ)) ≤ (q : ℝ) ^ 2 := by
      exact_mod_cast hqq
    norm_num only [Nat.cast_add, Nat.cast_one] at hqqR
    have h := Real.log_le_log (by positivity : (0 : ℝ) < q + 1)
      hqqR
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Real.log_pow,
      Nat.cast_ofNat] at h ⊢
    exact h
  have hlogq0 : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hbase : 1 ≤ Real.log (q : ℝ) + 2 := by linarith
  have hpow : Real.log (q : ℝ) + 2 ≤
      (Real.log (q : ℝ) + 2) ^ 2000 :=
    le_self_pow₀ hbase (by norm_num)
  have hconst : (19200 : ℝ) ≤
      2 * CentralCorrelation.centralFrequencyConstant * ((21).factorial : ℝ) := by
    have hf : (19200 : ℝ) ≤ ((21).factorial : ℝ) := by norm_num
    have hc : (1 : ℝ) ≤ 2 * CentralCorrelation.centralFrequencyConstant := by
      norm_num [CentralCorrelation.centralFrequencyConstant]
    calc
      (19200 : ℝ) = 1 * 19200 := by ring
      _ ≤ (2 * CentralCorrelation.centralFrequencyConstant) *
          ((21).factorial : ℝ) :=
        mul_le_mul hc hf (by norm_num) (by positivity)
      _ = _ := by ring
  have hlarge : 19200 * (Real.log (q : ℝ) + 2) ≤ (q : ℝ) := by
    calc
      _ ≤ (2 * CentralCorrelation.centralFrequencyConstant *
            ((21).factorial : ℝ)) *
          (Real.log (q : ℝ) + 2) ^ 2000 := by gcongr
      _ = 2 * CentralCorrelation.centralFrequencyConstant *
          ((21).factorial : ℝ) *
            AdaptiveShifts.logarithmicSafety q ^ 20 := by
        unfold AdaptiveShifts.logarithmicSafety
        rw [← pow_mul]
      _ ≤ 2 * CentralCorrelation.centralFrequencyConstant *
          ((33).factorial : ℝ) *
            AdaptiveShifts.logarithmicSafety q ^ 32 := by
        have hsafety : 1 ≤ AdaptiveShifts.logarithmicSafety q := by
          unfold AdaptiveShifts.logarithmicSafety
          exact one_le_pow₀ hbase
        have hfac : (((21).factorial : ℕ) : ℝ) ≤
            (((33).factorial : ℕ) : ℝ) := by
          exact_mod_cast (Nat.factorial_le (by omega : 21 ≤ 33))
        have hpowers : AdaptiveShifts.logarithmicSafety q ^ 20 ≤
            AdaptiveShifts.logarithmicSafety q ^ 32 :=
          pow_le_pow_right₀ hsafety (by omega : 20 ≤ 32)
        have hconstant : 0 ≤
            2 * CentralCorrelation.centralFrequencyConstant := by
          norm_num [CentralCorrelation.centralFrequencyConstant]
        have hsafety0 : 0 ≤ AdaptiveShifts.logarithmicSafety q :=
          le_trans (by norm_num) hsafety
        calc
          2 * CentralCorrelation.centralFrequencyConstant *
                (((21).factorial : ℕ) : ℝ) *
              AdaptiveShifts.logarithmicSafety q ^ 20 ≤
              2 * CentralCorrelation.centralFrequencyConstant *
                (((33).factorial : ℕ) : ℝ) *
              AdaptiveShifts.logarithmicSafety q ^ 20 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfac hconstant)
              (pow_nonneg hsafety0 20)
          _ ≤ _ := mul_le_mul_of_nonneg_left hpowers
            (mul_nonneg hconstant (by exact_mod_cast Nat.zero_le ((33).factorial)))
      _ ≤ (q : ℝ) := by
        simpa only [q, CentralCorrelation.centralCorrelationSizeCondition]
          using hsize
  have hlogkq : Real.log (k : ℝ) ≤ (q : ℝ) / 600 := by
    calc
      Real.log (k : ℝ) ≤ 16 * Real.log ((q + 1 : ℕ) : ℝ) := hlogk
      _ ≤ 16 * (2 * Real.log (q : ℝ)) := by gcongr
      _ = 32 * Real.log (q : ℝ) := by ring
      _ ≤ 32 * (Real.log (q : ℝ) + 2) := by linarith
      _ = (19200 * (Real.log (q : ℝ) + 2)) / 600 := by ring
      _ ≤ (q : ℝ) / 600 := div_le_div_of_nonneg_right hlarge (by norm_num)
  exact hloguk.trans hlogkq

theorem eventually_three_mul_lowSieveBlockSize_le_goodPrimeCard :
    ∀ᶠ k : ℕ in atTop,
      3 * lowSieveBlockSize k ≤
        (ReciprocalPrimeSelection.sourceGoodPrimeSet k).card := by
  filter_upwards [ReciprocalPrimeSelection.eventually_good_prime_card_mul_log_lower,
    eventually_log_sourcePrimeUpper_le_baseShift_div,
    CentralAsymptotic.tendsto_baseShift_atTop.eventually
      (eventually_ge_atTop 1)] with k hlower hlog hq
  let q := AdaptiveShifts.baseShift k
  let s := Nat.sqrt k
  let c := (ReciprocalPrimeSelection.sourceGoodPrimeSet k).card
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq8 : (q : ℝ) ^ 8 ≤ (s : ℝ) := by
    exact_mod_cast baseShift_pow_eight_le_sqrt k
  have hmain : 3 * (s : ℝ) ≤ (c : ℝ) * q := by
    have hlog' : Real.log (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ) ≤
        (q : ℝ) / 600 := by simpa only [q] using hlog
    have h := hlower.trans (mul_le_mul_of_nonneg_left hlog'
      (by positivity : (0 : ℝ) ≤ c))
    nlinarith
  have hq7 : 3 * (q : ℝ) ^ 7 ≤ (c : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hqR).mp
    calc
      (3 * (q : ℝ) ^ 7) * q = 3 * (q : ℝ) ^ 8 := by ring
      _ ≤ 3 * (s : ℝ) := by gcongr
      _ ≤ (c : ℝ) * q := hmain
  exact_mod_cast hq7

lemma lowSieveMain_nonneg (k : ℕ) :
    0 ≤ 64 / (lowSieveBlockSize k : ℝ) ^ 3 := by positivity

theorem summable_lowSieveMain :
    Summable (fun k : ℕ ↦ 64 / (lowSieveBlockSize k : ℝ) ^ 3) := by
  let p : ℝ := 5 / 4
  let C : ℝ := 64 * 2 ^ 20
  have hg : Summable (fun k : ℕ ↦ C * (1 / (k : ℝ) ^ p)) := by
    apply Summable.mul_left
    exact Real.summable_one_div_nat_rpow.mpr (by norm_num [p])
  have hle : ∀ k : ℕ,
      64 / (lowSieveBlockSize k : ℝ) ^ 3 ≤
        C * (1 / (k : ℝ) ^ p) := by
    intro k
    let q := AdaptiveShifts.baseShift k
    by_cases hq0 : q = 0
    · simp [lowSieveBlockSize, q, hq0]
      positivity
    have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
    have hq8 := baseShift_pow_eight_le_sqrt k
    have hkpos : 0 < k := by
      have : 0 < Nat.sqrt k := lt_of_lt_of_le (by positivity : 0 < q ^ 8) hq8
      by_contra hk
      simp_all
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hkq := CentralAsymptotic.lt_baseShift_succ_pow_sixteen k
    have hqdouble : q + 1 ≤ 2 * q := by omega
    have hkqR : (k : ℝ) ≤ (2 * (q : ℝ)) ^ 16 := by
      calc
        (k : ℝ) ≤ (((q + 1) ^ 16 : ℕ) : ℝ) := by exact_mod_cast hkq.le
        _ = (((q + 1 : ℕ) : ℝ)) ^ 16 := by push_cast; ring
        _ ≤ (2 * (q : ℝ)) ^ 16 := by
          gcongr
          exact_mod_cast hqdouble
    have hp0 : 0 ≤ p := by norm_num [p]
    have hkpow : (k : ℝ) ^ p ≤ (2 * (q : ℝ)) ^ 20 := by
      calc
        (k : ℝ) ^ p ≤ ((2 * (q : ℝ)) ^ 16) ^ p :=
          Real.rpow_le_rpow (by positivity) hkqR hp0
        _ = (2 * (q : ℝ)) ^ 20 := by
          dsimp only [p]
          calc
            (((2 * (q : ℝ)) ^ 16) : ℝ) ^ ((5 : ℝ) / 4) =
                (2 * (q : ℝ)) ^ ((16 : ℝ) * ((5 : ℝ) / 4)) := by
              rw [Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * q)]
              norm_num [Real.rpow_natCast]
            _ = (2 * (q : ℝ)) ^ 20 := by
              norm_num [Real.rpow_natCast]
    have hkpow' : (k : ℝ) ^ p ≤ 2 ^ 20 * (q : ℝ) ^ 20 := by
      simpa only [mul_pow] using hkpow
    have hcore : 1 / (q : ℝ) ^ 21 ≤ 2 ^ 20 / (k : ℝ) ^ p := by
      rw [div_le_div_iff₀ (pow_pos hqR 21) (Real.rpow_pos_of_pos hkR p)]
      calc
        1 * (k : ℝ) ^ p ≤ 2 ^ 20 * (q : ℝ) ^ 20 := by simpa using hkpow'
        _ ≤ (2 ^ 20) * (q : ℝ) ^ 21 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            (q : ℝ) ^ 20 = (q : ℝ) ^ 20 * 1 := by ring
            _ ≤ (q : ℝ) ^ 20 * q := by
              gcongr
              exact_mod_cast hq
            _ = (q : ℝ) ^ 21 := by ring
    change 64 / (((q ^ 7 : ℕ) : ℝ)) ^ 3 ≤ C * (1 / (k : ℝ) ^ p)
    have hcast : (((q ^ 7 : ℕ) : ℝ)) ^ 3 = (q : ℝ) ^ 21 := by
      push_cast
      ring
    rw [hcast]
    dsimp only [C]
    calc
      64 / (q : ℝ) ^ 21 = 64 * (1 / (q : ℝ) ^ 21) := by ring
      _ ≤ 64 * (2 ^ 20 / (k : ℝ) ^ p) := by gcongr
      _ = (64 * 2 ^ 20) * (1 / (k : ℝ) ^ p) := by ring
  exact Summable.of_nonneg_of_le lowSieveMain_nonneg hle hg

/-- The middle indices in the left half of a row. -/
def leftMiddleSquarefreeBinomialIndices (M n : ℕ) : Finset ℕ :=
  (middleSquarefreeBinomialIndices M n).filter fun k ↦ k ≤ n / 2

lemma mem_leftMiddleSquarefreeBinomialIndices_iff {M n k : ℕ} :
    k ∈ leftMiddleSquarefreeBinomialIndices M n ↔
      M < k ∧ k ≤ n / 2 ∧ Squarefree (n.choose k) := by
  simp only [leftMiddleSquarefreeBinomialIndices,
    middleSquarefreeBinomialIndices, squarefreeBinomialIndices,
    Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨⟨⟨hk1, hkn⟩, hsq⟩, hMk, hMnk⟩, hhalf⟩
    exact ⟨hMk, hhalf, hsq⟩
  · rintro ⟨hMk, hhalf, hsq⟩
    have hk1 : 1 ≤ k := by omega
    have h2k : 2 * k ≤ n :=
      by simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hhalf
    have hkn : k < n := by
      omega
    have hMnk : M < n - k := by
      have hkle : k ≤ n - k := by
        omega
      omega
    exact ⟨⟨⟨⟨hk1, hkn⟩, hsq⟩, hMk, hMnk⟩, hhalf⟩

lemma middleSquarefreeBinomialIndices_card_le_twice_left (M n : ℕ) :
    (middleSquarefreeBinomialIndices M n).card ≤
      2 * (leftMiddleSquarefreeBinomialIndices M n).card := by
  let L := leftMiddleSquarefreeBinomialIndices M n
  have hsubset : middleSquarefreeBinomialIndices M n ⊆
      L ∪ L.image (fun k ↦ n - k) := by
    intro k hk
    have hkdata := (Finset.mem_filter.mp hk)
    have hkfull := Finset.mem_filter.mp hkdata.1
    have hkrange := Finset.mem_Ico.mp hkfull.1
    by_cases hhalf : k ≤ n / 2
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hk, hhalf⟩))
    · apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_image.mpr
      refine ⟨n - k, ?_, by omega⟩
      rw [mem_leftMiddleSquarefreeBinomialIndices_iff]
      refine ⟨hkdata.2.2, ?_, ?_⟩
      · omega
      · rw [Nat.choose_symm hkrange.2.le]
        exact hkfull.2
  calc
    (middleSquarefreeBinomialIndices M n).card ≤ (L ∪ L.image (fun k ↦ n - k)).card :=
      Finset.card_le_card hsubset
    _ ≤ L.card + (L.image (fun k ↦ n - k)).card :=
      Finset.card_union_le _ _
    _ ≤ L.card + L.card := Nat.add_le_add_left (Finset.card_image_le) _
    _ = 2 * L.card := by ring

lemma leftMiddleSquarefreeBinomialIndices_eq_bounded
    {M Q n : ℕ}
    (hQ : ∀ k ∈ leftMiddleSquarefreeBinomialIndices M n, k ≤ Q) :
    leftMiddleSquarefreeBinomialIndices M n =
      (Finset.Ioc M Q).filter fun k ↦
        k ≤ n / 2 ∧ Squarefree (n.choose k) := by
  ext k
  rw [mem_leftMiddleSquarefreeBinomialIndices_iff]
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · intro hk
    exact ⟨⟨hk.1, hQ k (mem_leftMiddleSquarefreeBinomialIndices_iff.mpr hk)⟩,
      hk.2.1, hk.2.2⟩
  · rintro ⟨⟨hMk, hkQ⟩, hhalf, hsq⟩
    exact ⟨hMk, hhalf, hsq⟩

lemma sum_leftMiddle_card_eq_sum_fixed_index
    {M Q N : ℕ}
    (hQ : ∀ n ∈ Finset.range N,
      ∀ k ∈ leftMiddleSquarefreeBinomialIndices M n, k ≤ Q) :
    (∑ n ∈ Finset.range N,
        (leftMiddleSquarefreeBinomialIndices M n).card) =
      ∑ k ∈ Finset.Ioc M Q,
        ((Finset.range N).filter fun n ↦
          k ≤ n / 2 ∧ Squarefree (n.choose k)).card := by
  calc
    _ = ∑ n ∈ Finset.range N,
        ((Finset.Ioc M Q).filter fun k ↦
          k ≤ n / 2 ∧ Squarefree (n.choose k)).card := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [leftMiddleSquarefreeBinomialIndices_eq_bounded (hQ n hn)]
    _ = ∑ n ∈ Finset.range N, ∑ k ∈ Finset.Ioc M Q,
        if k ≤ n / 2 ∧ Squarefree (n.choose k) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ k ∈ Finset.Ioc M Q, ∑ n ∈ Finset.range N,
        if k ≤ n / 2 ∧ Squarefree (n.choose k) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

def middleIndexBase (N : ℕ) : ℕ :=
  Nat.sqrt (Nat.sqrt (Nat.sqrt N))

/-- A very slowly growing factor used to leave room for arbitrary fixed
Fourier modes in the high-index argument.  It has order `N^(1/64)`. -/
def middleIndexAmplifier (N : ℕ) : ℕ :=
  Nat.sqrt (Nat.sqrt (Nat.sqrt (middleIndexBase N)))

/-- The middle-index cutoff has order `N^(9/64)`.  Thus its seventh power is
`o(N)`, while its eighth power dominates `N` by an unbounded factor. -/
def middleIndexCutoff (N : ℕ) : ℕ :=
  middleIndexBase N * middleIndexAmplifier N

def lowIndexSquarefreePairCount (M N : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ioc M (middleIndexCutoff N),
    ((Finset.range N).filter fun n ↦
      k ≤ n / 2 ∧ Squarefree (n.choose k)).card

lemma lowIndexSquarefreePairCount_le
    {M N : ℕ}
    (hselected : ∀ k, M < k →
      3 * lowSieveBlockSize k ≤
        (ReciprocalPrimeSelection.sourceGoodPrimeSet k).card)
    (hblock : ∀ k, M < k → 0 < lowSieveBlockSize k) :
    (lowIndexSquarefreePairCount M N : ℝ) ≤
      (N : ℝ) *
        (∑ k ∈ Finset.Ioc M (middleIndexCutoff N),
          64 / (lowSieveBlockSize k : ℝ) ^ 3) +
        (729 * 4 ^ 6 : ℝ) * (middleIndexCutoff N : ℝ) ^ 7 := by
  let Q := middleIndexCutoff N
  have hterm (k : ℕ) (hk : k ∈ Finset.Ioc M Q) :
      (((Finset.range N).filter fun n ↦
        k ≤ n / 2 ∧ Squarefree (n.choose k)).card : ℝ) ≤
        (N : ℝ) * (64 / (lowSieveBlockSize k : ℝ) ^ 3) +
          729 * (4 * (k : ℝ)) ^ 6 := by
    have hkM := (Finset.mem_Ioc.mp hk).1
    exact card_squarefree_choose_fixed_index_le_selected
      (by omega) (hselected k hkM) (hblock k hkM)
  have herror :
      (∑ k ∈ Finset.Ioc M Q, 729 * (4 * (k : ℝ)) ^ 6) ≤
        (729 * 4 ^ 6 : ℝ) * (Q : ℝ) ^ 7 := by
    calc
      _ ≤ ∑ _k ∈ Finset.Ioc M Q,
          (729 * 4 ^ 6 : ℝ) * (Q : ℝ) ^ 6 := by
        apply Finset.sum_le_sum
        intro k hk
        have hkQ : (k : ℝ) ≤ Q := by
          exact_mod_cast (Finset.mem_Ioc.mp hk).2
        have hkpow : (k : ℝ) ^ 6 ≤ (Q : ℝ) ^ 6 := by gcongr
        calc
          729 * (4 * (k : ℝ)) ^ 6 =
              (729 * 4 ^ 6 : ℝ) * (k : ℝ) ^ 6 := by ring
          _ ≤ (729 * 4 ^ 6 : ℝ) * (Q : ℝ) ^ 6 := by gcongr
      _ = ((Finset.Ioc M Q).card : ℝ) *
          ((729 * 4 ^ 6 : ℝ) * (Q : ℝ) ^ 6) := by simp
      _ ≤ (Q : ℝ) * ((729 * 4 ^ 6 : ℝ) * (Q : ℝ) ^ 6) := by
        gcongr
        exact_mod_cast (show (Finset.Ioc M Q).card ≤ Q by simp)
      _ = (729 * 4 ^ 6 : ℝ) * (Q : ℝ) ^ 7 := by ring
  unfold lowIndexSquarefreePairCount
  push_cast
  calc
    (∑ k ∈ Finset.Ioc M Q,
        (((Finset.range N).filter fun n ↦
          k ≤ n / 2 ∧ Squarefree (n.choose k)).card : ℝ)) ≤
        ∑ k ∈ Finset.Ioc M Q,
          ((N : ℝ) * (64 / (lowSieveBlockSize k : ℝ) ^ 3) +
            729 * (4 * (k : ℝ)) ^ 6) := by
      exact Finset.sum_le_sum fun k hk ↦ hterm k hk
    _ = (N : ℝ) *
          (∑ k ∈ Finset.Ioc M Q,
            64 / (lowSieveBlockSize k : ℝ) ^ 3) +
        ∑ k ∈ Finset.Ioc M Q, 729 * (4 * (k : ℝ)) ^ 6 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (N : ℝ) *
        (∑ k ∈ Finset.Ioc M Q,
            64 / (lowSieveBlockSize k : ℝ) ^ 3) +
        (729 * 4 ^ 6 : ℝ) * (Q : ℝ) ^ 7 := add_le_add le_rfl herror
    _ = _ := by rfl

lemma middleIndexBase_pow_eight_le (N : ℕ) :
    middleIndexBase N ^ 8 ≤ N := by
  let a := Nat.sqrt N
  let b := Nat.sqrt a
  let q := Nat.sqrt b
  have hq : q ^ 2 ≤ b := by
    simpa only [q, pow_two] using Nat.sqrt_le b
  have hb : b ^ 2 ≤ a := by
    simpa only [b, pow_two] using Nat.sqrt_le a
  have ha : a ^ 2 ≤ N := by
    simpa only [a, pow_two] using Nat.sqrt_le N
  calc
    middleIndexBase N ^ 8 = q ^ 8 := rfl
    _ = ((q ^ 2) ^ 2) ^ 2 := by ring
    _ ≤ (b ^ 2) ^ 2 := by gcongr
    _ ≤ a ^ 2 := by gcongr
    _ ≤ N := ha

lemma middleIndexAmplifier_pow_eight_le_base (N : ℕ) :
    middleIndexAmplifier N ^ 8 ≤ middleIndexBase N := by
  exact middleIndexBase_pow_eight_le (middleIndexBase N)

lemma middleIndexCutoff_pow_seven_mul_amplifier_le (N : ℕ) :
    middleIndexCutoff N ^ 7 * middleIndexAmplifier N ≤ N := by
  let a := middleIndexBase N
  let b := middleIndexAmplifier N
  have hb : b ^ 8 ≤ a := middleIndexAmplifier_pow_eight_le_base N
  have ha : a ^ 8 ≤ N := middleIndexBase_pow_eight_le N
  calc
    middleIndexCutoff N ^ 7 * middleIndexAmplifier N =
        a ^ 7 * b ^ 8 := by simp only [middleIndexCutoff, a, b]; ring
    _ ≤ a ^ 8 := by
      calc
        a ^ 7 * b ^ 8 ≤ a ^ 7 * a := Nat.mul_le_mul_left _ hb
        _ = a ^ 8 := by ring
    _ ≤ N := ha

lemma tendsto_middleIndexBase_atTop : Tendsto middleIndexBase atTop atTop := by
  unfold middleIndexBase
  have h : Tendsto (fun n : ℕ ↦ Nat.sqrt n) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b * b, fun _ ha ↦ Nat.le_sqrt.mpr ha⟩
  exact h.comp (h.comp h)

lemma tendsto_middleIndexAmplifier_atTop :
    Tendsto middleIndexAmplifier atTop atTop := by
  unfold middleIndexAmplifier
  have h : Tendsto (fun n : ℕ ↦ Nat.sqrt n) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b * b, fun _ ha ↦ Nat.le_sqrt.mpr ha⟩
  exact h.comp (h.comp (h.comp tendsto_middleIndexBase_atTop))

lemma tendsto_middleIndexCutoff_atTop : Tendsto middleIndexCutoff atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  have hevent : ∀ᶠ N : ℕ in atTop, B ≤ middleIndexCutoff N := by
    filter_upwards [tendsto_middleIndexAmplifier_atTop.eventually
        (eventually_ge_atTop B),
      tendsto_middleIndexBase_atTop.eventually (eventually_ge_atTop 1)] with
        N hb ha
    calc
      B ≤ middleIndexAmplifier N := hb
      _ ≤ middleIndexBase N * middleIndexAmplifier N := by
        simpa using Nat.mul_le_mul_right (middleIndexAmplifier N) ha
      _ = middleIndexCutoff N := rfl
  exact hevent.exists_forall_of_atTop

lemma tendsto_middleIndexCutoff_pow_seven_div :
    Tendsto (fun N : ℕ ↦
      (middleIndexCutoff N : ℝ) ^ 7 / (N : ℝ))
      atTop (nhds 0) := by
  let q : ℕ → ℕ := middleIndexCutoff
  let b : ℕ → ℕ := middleIndexAmplifier
  have hbTop : Tendsto b atTop atTop :=
    tendsto_middleIndexAmplifier_atTop
  have hbRTop : Tendsto (fun N : ℕ ↦ (b N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hbTop
  have hinv : Tendsto (fun N : ℕ ↦ ((b N : ℝ))⁻¹) atTop (nhds 0) :=
    hbRTop.inv_tendsto_atTop
  have hinv1 : Tendsto (fun N : ℕ ↦ ((b N : ℝ))⁻¹)
      atTop (nhds 0) := by
    exact hinv
  have hnonneg : ∀ N : ℕ,
      0 ≤ (q N : ℝ) ^ 7 / (N : ℝ) := fun N ↦ by positivity
  have hbound : ∀ᶠ N : ℕ in atTop,
      (q N : ℝ) ^ 7 / (N : ℝ) ≤ ((b N : ℝ))⁻¹ := by
    filter_upwards [hbTop.eventually (eventually_ge_atTop 1),
      eventually_gt_atTop 0] with N hq hN
    have hqR : (0 : ℝ) < b N := by exact_mod_cast (Nat.zero_lt_of_lt hq)
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [inv_eq_one_div]
    rw [div_le_div_iff₀ hNR hqR]
    calc
      (q N : ℝ) ^ 7 * (b N : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast middleIndexCutoff_pow_seven_mul_amplifier_le N
      _ = 1 * (N : ℝ) := by ring
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hbound hinv1

noncomputable def lowSieveTail (M : ℕ) : ℝ :=
  (∑' k : ℕ, 64 / (lowSieveBlockSize k : ℝ) ^ 3) -
    ∑ k ∈ Finset.range (M + 1), 64 / (lowSieveBlockSize k : ℝ) ^ 3

lemma tendsto_finset_range_atTop : Tendsto Finset.range atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro s
  refine ⟨s.sup id + 1, ?_⟩
  intro N hN k hk
  rw [Finset.mem_range]
  have hksup : k ≤ s.sup id := Finset.le_sup (f := id) hk
  omega

lemma tendsto_lowSieveTail_zero :
    Tendsto lowSieveTail atTop (nhds 0) := by
  have hsum : Tendsto
      (fun M : ℕ ↦ ∑ k ∈ Finset.range M,
        64 / (lowSieveBlockSize k : ℝ) ^ 3)
      atTop (nhds (∑' k : ℕ, 64 / (lowSieveBlockSize k : ℝ) ^ 3)) := by
    exact (summable_lowSieveMain.hasSum_iff_tendsto_nat).mp
      summable_lowSieveMain.hasSum
  unfold lowSieveTail
  have hsum' := hsum.comp (tendsto_add_atTop_nat 1)
  have hconst : Tendsto
      (fun _ : ℕ ↦ ∑' k : ℕ, 64 / (lowSieveBlockSize k : ℝ) ^ 3)
      atTop (nhds (∑' k : ℕ, 64 / (lowSieveBlockSize k : ℝ) ^ 3)) :=
    tendsto_const_nhds
  simpa only [Function.comp_apply, sub_self] using hconst.sub hsum'

lemma lowSieveTail_nonneg (M : ℕ) : 0 ≤ lowSieveTail M := by
  unfold lowSieveTail
  exact sub_nonneg.mpr (summable_lowSieveMain.sum_le_tsum _
    (fun k hk ↦ lowSieveMain_nonneg k))

lemma sum_Ioc_lowSieveMain_le_tail (M Q : ℕ) :
    (∑ k ∈ Finset.Ioc M Q,
      64 / (lowSieveBlockSize k : ℝ) ^ 3) ≤ lowSieveTail M := by
  let f : ℕ → ℝ := fun k ↦ 64 / (lowSieveBlockSize k : ℝ) ^ 3
  have hdisj : Disjoint (Finset.range (M + 1)) (Finset.Ioc M Q) := by
    rw [Finset.disjoint_left]
    intro k hkRange hkIoc
    have hk₁ := Finset.mem_range.mp hkRange
    have hk₂ := (Finset.mem_Ioc.mp hkIoc).1
    omega
  have hunion :
      (∑ k ∈ Finset.range (M + 1), f k) +
          ∑ k ∈ Finset.Ioc M Q, f k =
        ∑ k ∈ Finset.range (M + 1) ∪ Finset.Ioc M Q, f k := by
    rw [Finset.sum_union hdisj]
  have hle := summable_lowSieveMain.sum_le_tsum
    (Finset.range (M + 1) ∪ Finset.Ioc M Q)
    (fun k hk ↦ lowSieveMain_nonneg k)
  dsimp only [f] at hunion hle
  unfold lowSieveTail
  linarith

/-- Pointwise high-index exclusion in the only uniform form needed by the
pair-counting deduction. -/
def HighIndexExcluded : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ n ∈ Finset.range N, ∀ k : ℕ,
    middleIndexCutoff N < k → k ≤ n / 2 →
      ¬ Squarefree (n.choose k)

/-- Granville--Ramaré's two-window argument excludes every squarefree
coefficient whose index lies beyond the growing cutoff. -/
theorem highIndexExcluded : HighIndexExcluded := by
  rcases eventually_high_index_squarefree_impossible.exists_forall_of_atTop with
    ⟨K, hK⟩
  have hcutLarge : ∀ᶠ N : ℕ in atTop, K ≤ middleIndexCutoff N :=
    tendsto_middleIndexCutoff_atTop.eventually (eventually_ge_atTop K)
  have hbridge :=
    HighIndexCutoffBridge.eventually_N_le_sourceUpper_cutoff_pow_fifteen
  filter_upwards [hcutLarge, hbridge] with N hcut hN
  intro n hn k hkCut hhalf
  have hkLarge : K ≤ k := hcut.trans hkCut.le
  apply hK k hkLarge n hhalf
  have hNmain : N ≤
      ReciprocalPrimeSelection.sourcePrimeUpper (middleIndexCutoff N) ^ 15 := by
    simpa only [middleIndexCutoff, middleIndexBase, middleIndexAmplifier,
      HighIndexCutoffBridge.middleIndexCutoff,
      HighIndexCutoffBridge.middleIndexBase,
      HighIndexCutoffBridge.middleIndexAmplifier] using hN
  have hsourceMono :
      ReciprocalPrimeSelection.sourcePrimeUpper (middleIndexCutoff N) ≤
        ReciprocalPrimeSelection.sourcePrimeUpper k := by
    unfold ReciprocalPrimeSelection.sourcePrimeUpper
    gcongr
  exact (Finset.mem_range.mp hn).le.trans
    (hNmain.trans (by gcongr))

theorem middlePairScarcity_of_highIndexExcluded
    (hHigh : HighIndexExcluded) : MiddlePairScarcity := by
  intro ε hε
  have hselEvent := eventually_three_mul_lowSieveBlockSize_le_goodPrimeCard
  have hblockEvent : ∀ᶠ k : ℕ in atTop, 0 < lowSieveBlockSize k := by
    filter_upwards [CentralAsymptotic.tendsto_baseShift_atTop.eventually
      (eventually_ge_atTop 1)] with k hk
    unfold lowSieveBlockSize
    positivity
  have htailSmall : ∀ᶠ M : ℕ in atTop, lowSieveTail M < ε / 8 :=
    tendsto_lowSieveTail_zero.eventually (Iio_mem_nhds (by linarith))
  rcases hselEvent.exists_forall_of_atTop with ⟨Msel, hsel⟩
  rcases hblockEvent.exists_forall_of_atTop with ⟨Mblock, hblock⟩
  rcases htailSmall.exists_forall_of_atTop with ⟨Mtail, htail⟩
  let M := max Msel (max Mblock Mtail)
  have hMsel : Msel ≤ M := le_max_left _ _
  have hMblock : Mblock ≤ M :=
    (le_max_left Mblock Mtail).trans (le_max_right Msel _)
  have hMtail : Mtail ≤ M :=
    (le_max_right Mblock Mtail).trans (le_max_right Msel _)
  have hselM : ∀ k, M < k →
      3 * lowSieveBlockSize k ≤
        (ReciprocalPrimeSelection.sourceGoodPrimeSet k).card := by
    intro k hk
    exact hsel k (hMsel.trans hk.le)
  have hblockM : ∀ k, M < k → 0 < lowSieveBlockSize k := by
    intro k hk
    exact hblock k (hMblock.trans hk.le)
  have htailM : lowSieveTail M < ε / 8 :=
    htail M hMtail
  refine ⟨M, ?_⟩
  have hendpoint : ∀ᶠ N : ℕ in atTop,
      2 * (729 * 4 ^ 6 : ℝ) *
        ((middleIndexCutoff N : ℝ) ^ 7 / (N : ℝ)) < ε / 2 := by
    have ht := tendsto_middleIndexCutoff_pow_seven_div.const_mul
      (2 * (729 * 4 ^ 6 : ℝ))
    exact ht.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hHigh, hendpoint, eventually_gt_atTop 0] with
      N hHighN hendpointN hN
  have hcut : ∀ n ∈ Finset.range N,
      ∀ k ∈ leftMiddleSquarefreeBinomialIndices M n,
        k ≤ middleIndexCutoff N := by
    intro n hn k hk
    by_contra hkQ
    have hkQ' : middleIndexCutoff N < k := Nat.lt_of_not_ge hkQ
    have hkdata := mem_leftMiddleSquarefreeBinomialIndices_iff.mp hk
    exact (hHighN n hn k hkQ' hkdata.2.1) hkdata.2.2
  have hpairsNat : middlePairCount M N ≤
      2 * lowIndexSquarefreePairCount M N := by
    unfold middlePairCount
    calc
      (∑ n ∈ Finset.range N,
          (middleSquarefreeBinomialIndices M n).card) ≤
          ∑ n ∈ Finset.range N,
            2 * (leftMiddleSquarefreeBinomialIndices M n).card := by
        exact Finset.sum_le_sum fun n hn ↦
          middleSquarefreeBinomialIndices_card_le_twice_left M n
      _ = 2 * (∑ n ∈ Finset.range N,
          (leftMiddleSquarefreeBinomialIndices M n).card) := by
        rw [Finset.mul_sum]
      _ = 2 * lowIndexSquarefreePairCount M N := by
        rw [sum_leftMiddle_card_eq_sum_fixed_index hcut]
        rfl
  have hlow := lowIndexSquarefreePairCount_le
    (M := M) (N := N)
    (fun k hk ↦ hselM k (by simpa using hk))
    (fun k hk ↦ hblockM k (by simpa using hk))
  have hsumTail := sum_Ioc_lowSieveMain_le_tail M (middleIndexCutoff N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpairsR : (middlePairCount M N : ℝ) ≤
      2 * (lowIndexSquarefreePairCount M N : ℝ) := by exact_mod_cast hpairsNat
  have hlowDiv : (lowIndexSquarefreePairCount M N : ℝ) / N ≤
      lowSieveTail M + (729 * 4 ^ 6 : ℝ) *
        ((middleIndexCutoff N : ℝ) ^ 7 / N) := by
    rw [div_le_iff₀ hNR]
    calc
      (lowIndexSquarefreePairCount M N : ℝ) ≤
          (N : ℝ) *
            (∑ k ∈ Finset.Ioc M (middleIndexCutoff N),
              64 / (lowSieveBlockSize k : ℝ) ^ 3) +
            (729 * 4 ^ 6 : ℝ) * (middleIndexCutoff N : ℝ) ^ 7 := hlow
      _ ≤ (N : ℝ) * lowSieveTail M +
            (729 * 4 ^ 6 : ℝ) * (middleIndexCutoff N : ℝ) ^ 7 := by
        gcongr
      _ = (lowSieveTail M + (729 * 4 ^ 6 : ℝ) *
          ((middleIndexCutoff N : ℝ) ^ 7 / N)) * N := by
        field_simp
  calc
    (middlePairCount M N : ℝ) / N ≤
        2 * ((lowIndexSquarefreePairCount M N : ℝ) / N) := by
      rw [div_le_iff₀ hNR]
      calc
        (middlePairCount M N : ℝ) ≤
            2 * (lowIndexSquarefreePairCount M N : ℝ) := hpairsR
        _ = (2 * ((lowIndexSquarefreePairCount M N : ℝ) / N)) * N := by
          field_simp
    _ ≤ 2 * (lowSieveTail M + (729 * 4 ^ 6 : ℝ) *
        ((middleIndexCutoff N : ℝ) ^ 7 / N)) := by gcongr
    _ < ε := by linarith

/-! A useful elementary replacement for one part of the source's
fractional-part estimate: above `sqrt k`, distinct primes have distinct
remainders of `k`.  Indeed, two such primes attached to the same remainder
would have a product larger than `k` dividing a positive integer at most
`k`. -/

lemma prime_remainder_injective_above_sqrt {k p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpk : p ≤ k)
    (hsp : Nat.sqrt k < p) (hsq : Nat.sqrt k < q)
    (hrem : k % p = k % q) : p = q := by
  by_contra hpq
  let c := k % p
  have hcp : c < p := Nat.mod_lt k hp.pos
  have hck : c < k := hcp.trans_le hpk
  have hpdiv : p ∣ k - c := by
    apply (Nat.modEq_iff_dvd' hck.le).mp
    simpa [c] using Nat.mod_modEq k p
  have hqc : c < q := by
    change k % p < q
    rw [hrem]
    exact Nat.mod_lt k hq.pos
  have hqdiv : q ∣ k - c := by
    apply (Nat.modEq_iff_dvd' hck.le).mp
    have hmod : c ≡ k [MOD q] := by
      simpa [c, hrem] using Nat.mod_modEq k q
    exact hmod
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hpqdiv : p * q ∣ k - c :=
    hcop.mul_dvd_of_dvd_of_dvd hpdiv hqdiv
  have hpqle : p * q ≤ k - c :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt hck) hpqdiv
  have hklt : k < p * q := by
    calc
      k < (Nat.sqrt k + 1) * (Nat.sqrt k + 1) := Nat.lt_succ_sqrt k
      _ ≤ p * q := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- Consequently at most `Y` primes above `sqrt k` can have remainder below
`Y`.  No exponential-sum estimate is used in this finite lemma. -/
lemma card_primes_with_small_remainder_le {k Y : ℕ} (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsqrt : ∀ p ∈ P, Nat.sqrt k < p)
    (hle : ∀ p ∈ P, p ≤ k) :
    (P.filter fun p ↦ k % p < Y).card ≤ Y := by
  let small := P.filter fun p ↦ k % p < Y
  have hinj : Set.InjOn (fun p : ℕ ↦ k % p) (small : Set ℕ) := by
    intro p hpMem q hqMem hpqRem
    have hpP := (Finset.mem_filter.mp hpMem).1
    have hqP := (Finset.mem_filter.mp hqMem).1
    exact prime_remainder_injective_above_sqrt
      (hprime p hpP) (hprime q hqP) (hle p hpP)
      (hsqrt p hpP) (hsqrt q hqP) hpqRem
  have himage : small.image (fun p ↦ k % p) ⊆ Finset.range Y := by
    intro c hc
    obtain ⟨p, hpSmall, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hpSmall).2
  calc
    (P.filter fun p ↦ k % p < Y).card = small.card := rfl
    _ = (small.image fun p ↦ k % p).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range Y).card := Finset.card_le_card himage
    _ = Y := Finset.card_range Y

/-- At least `P.card - Y` of the primes in such a window have remainder at
least `Y`. -/
lemma card_primes_with_large_remainder_ge {k Y : ℕ} (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsqrt : ∀ p ∈ P, Nat.sqrt k < p)
    (hle : ∀ p ∈ P, p ≤ k) :
    P.card - Y ≤ (P.filter fun p ↦ Y ≤ k % p).card := by
  have hsmall := card_primes_with_small_remainder_le (Y := Y) P hprime hsqrt hle
  have hlarge : (P.filter fun p ↦ Y ≤ k % p) =
      P \ (P.filter fun p ↦ k % p < Y) := by
    ext p
    by_cases hpP : p ∈ P <;> simp [hpP]
  rw [hlarge, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  omega

lemma squarefreeBinomialIndices_eq_edge_of_not_middle {M n : ℕ}
    (hn : n ∉ middleExceptionalSet M) :
    squarefreeBinomialIndices n = edgeSquarefreeBinomialIndices M n := by
  apply Finset.Subset.antisymm
  · intro k hk
    rw [edgeSquarefreeBinomialIndices, Finset.mem_filter]
    refine ⟨hk, ?_⟩
    by_contra hedge
    have hmiddle : k ∈ middleSquarefreeBinomialIndices M n := by
      rw [middleSquarefreeBinomialIndices, Finset.mem_filter]
      exact ⟨hk, by omega⟩
    exact hn ⟨k, hmiddle⟩
  · exact Finset.filter_subset _ _

lemma edgeSquarefreeBinomialIndices_eq_left_union_image {M n : ℕ}
    (hMn : 2 * M < n) :
    edgeSquarefreeBinomialIndices M n =
      leftSquarefreeBinomialIndices M n ∪
        (leftSquarefreeBinomialIndices M n).image (fun k ↦ n - k) := by
  ext k
  constructor
  · intro hk
    rw [edgeSquarefreeBinomialIndices, Finset.mem_filter] at hk
    rcases hk with ⟨hkfull, hkedge⟩
    rw [squarefreeBinomialIndices, Finset.mem_filter, Finset.mem_Ico] at hkfull
    rw [Finset.mem_union]
    rcases hkedge with hkleft | hkright
    · exact Or.inl (by
        rw [leftSquarefreeBinomialIndices, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hkfull.1.1, hkleft⟩, hkfull.2⟩)
    · apply Or.inr
      apply Finset.mem_image.mpr
      refine ⟨n - k, ?_, by omega⟩
      rw [leftSquarefreeBinomialIndices, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, hkright⟩, ?_⟩
      rw [Nat.choose_symm (by omega : k ≤ n)]
      exact hkfull.2
  · intro hk
    rw [Finset.mem_union] at hk
    rw [edgeSquarefreeBinomialIndices, Finset.mem_filter]
    rcases hk with hk | hk
    · rw [leftSquarefreeBinomialIndices, Finset.mem_filter, Finset.mem_Icc] at hk
      refine ⟨?_, Or.inl hk.1.2⟩
      rw [squarefreeBinomialIndices, Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨hk.1.1, by omega⟩, hk.2⟩
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
      rw [leftSquarefreeBinomialIndices, Finset.mem_filter, Finset.mem_Icc] at hl
      refine ⟨?_, Or.inr (by omega)⟩
      rw [squarefreeBinomialIndices, Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simpa [Nat.choose_symm (by omega : l ≤ n)] using hl.2

lemma disjoint_leftSquarefreeBinomialIndices_image {M n : ℕ}
    (hMn : 2 * M < n) :
    Disjoint (leftSquarefreeBinomialIndices M n)
      ((leftSquarefreeBinomialIndices M n).image (fun k ↦ n - k)) := by
  rw [Finset.disjoint_left]
  intro k hkleft hkright
  obtain ⟨l, hl, hEq⟩ := Finset.mem_image.mp hkright
  rw [leftSquarefreeBinomialIndices, Finset.mem_filter, Finset.mem_Icc] at hkleft hl
  omega

lemma edgeSquarefreeBinomialIndices_card {M n : ℕ} (hMn : 2 * M < n) :
    (edgeSquarefreeBinomialIndices M n).card =
      2 * (leftSquarefreeBinomialIndices M n).card := by
  rw [edgeSquarefreeBinomialIndices_eq_left_union_image hMn,
    Finset.card_union_of_disjoint (disjoint_leftSquarefreeBinomialIndices_image hMn)]
  have hinj : Set.InjOn (fun k : ℕ ↦ n - k)
      (leftSquarefreeBinomialIndices M n : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∈ leftSquarefreeBinomialIndices M n := ha
    have hb' : b ∈ leftSquarefreeBinomialIndices M n := hb
    rw [leftSquarefreeBinomialIndices, Finset.mem_filter, Finset.mem_Icc] at ha' hb'
    change n - a = n - b at hab
    omega
  rw [Finset.card_image_of_injOn hinj]
  omega

lemma cutoffExactCountSet_symmDiff_doubledLeft_subset (M j : ℕ) :
    cutoffExactCountSet M j ∆ doubledLeftExactCountSet M j ⊆ Set.Iic (2 * M) := by
  intro n hn
  by_contra hnsmall
  have hMn : 2 * M < n := by simpa using hnsmall
  have hcard := edgeSquarefreeBinomialIndices_card hMn
  rcases Set.mem_symmDiff.mp hn with hn | hn
  · exact hn.2 (by
      change 2 * (leftSquarefreeBinomialIndices M n).card = j
      have hncut : (edgeSquarefreeBinomialIndices M n).card = j := hn.1
      omega)
  · exact hn.2 (by
      change (edgeSquarefreeBinomialIndices M n).card = j
      have hnleft : 2 * (leftSquarefreeBinomialIndices M n).card = j := hn.1
      omega)

lemma exactCountSet_symmDiff_cutoff_subset_middle (M j : ℕ) :
    exactCountSet j ∆ cutoffExactCountSet M j ⊆ middleExceptionalSet M := by
  intro n hn
  by_contra hmiddle
  have hcount : squarefreeBinomialCount n =
      (edgeSquarefreeBinomialIndices M n).card := by
    rw [squarefreeBinomialCount,
      squarefreeBinomialIndices_eq_edge_of_not_middle hmiddle]
  rcases Set.mem_symmDiff.mp hn with hn | hn
  · exact hn.2 (by simpa [exactCountSet, cutoffExactCountSet, hcount] using hn.1)
  · exact hn.2 (by simpa [exactCountSet, cutoffExactCountSet, hcount] using hn.1)

/-- The exact distributional consequence of Granville--Ramaré Theorem 5 used
in the resolution.  Its indexing is for the *interior* count: their whole-row
count `2 * m + 2` includes the two endpoint entries equal to one. -/
def GranvilleRamareDistribution : Prop :=
  (∀ j : ℕ, ∃ d : ℝ, (exactCountSet j).HasDensity d) ∧
    ∀ m : ℕ, 0 < m → ∃ d : ℝ, 0 < d ∧ (exactCountSet (2 * m)).HasDensity d

/-! ## Elementary density algebra -/

/-- On naturals, the repository's partial density is the usual count below
`n`, divided by `n`. -/
lemma partialDensity_eq_ncard (S : Set ℕ) (n : ℕ) :
    S.partialDensity (b := n) =
      ((S ∩ Set.Iio n).ncard : ℝ) / (n : ℝ) := by
  simp [Set.partialDensity]

/-- A row containing a middle entry contributes at least one to the total
middle-pair count. -/
lemma ncard_middleExceptional_le_middlePairCount (M N : ℕ) :
    (middleExceptionalSet M ∩ Set.Iio N).ncard ≤ middlePairCount M N := by
  classical
  let rows := (Finset.range N).filter fun n ↦
    (middleSquarefreeBinomialIndices M n).Nonempty
  have hset : middleExceptionalSet M ∩ Set.Iio N = (rows : Set ℕ) := by
    ext n
    simp only [middleExceptionalSet, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_Iio, Finset.mem_coe, rows, Finset.mem_filter,
      Finset.mem_range]
    tauto
  rw [hset, Set.ncard_coe_finset]
  have hfirst : rows.card ≤
      ∑ n ∈ rows, (middleSquarefreeBinomialIndices M n).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro n hn
    exact Finset.one_le_card.mpr (Finset.mem_filter.mp hn).2
  exact hfirst.trans <| by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact (Finset.mem_filter.mp hn).1
    · intro n _ _
      exact Nat.zero_le _

/-- The pair-counting scarcity estimate implies the row-counting tail needed
for the density argument. -/
theorem middleTailVanishes_of_pairScarcity
    (hPairs : MiddlePairScarcity) : MiddleTailVanishes := by
  intro ε hε
  obtain ⟨M, hM⟩ := hPairs ε hε
  refine ⟨M, ?_⟩
  filter_upwards [hM] with N hN
  rw [partialDensity_eq_ncard]
  exact (div_le_div_of_nonneg_right
      (by exact_mod_cast ncard_middleExceptional_le_middlePairCount M N)
      (Nat.cast_nonneg N)).trans_lt hN

/-- The set of natural numbers lying in one of finitely many residue classes
modulo `g`. -/
def residueSet (g : ℕ) (A : Finset ℕ) : Set ℕ :=
  {n | n % g ∈ A}

/-- A finite union of residue classes has its expected natural density. -/
lemma residueSet_hasDensity {g : ℕ} (hg : 0 < g) (A : Finset ℕ)
    (hA : ∀ a ∈ A, a < g) :
    (residueSet g A).HasDensity ((A.card : ℝ) / g) := by
  rw [Set.HasDensity]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hzero : Tendsto (fun N : ℕ ↦ (A.card : ℝ) / N) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (A.card : ℝ)
  have hsmall : ∀ᶠ N : ℕ in atTop, (A.card : ℝ) / N < ε :=
    hzero (Iio_mem_nhds hε)
  filter_upwards [hsmall, eventually_gt_atTop 0] with N hNsmall hN
  rw [Real.dist_eq, partialDensity_eq_ncard]
  have hset : residueSet g A ∩ Set.Iio N =
      ↑(Erdos387.modularPreimage N g A) := by
    ext n
    simp only [residueSet, Erdos387.modularPreimage, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_Iio, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range]
    tauto
  rw [hset, Set.ncard_coe_finset]
  have hdisc := Erdos387.abs_card_modularPreimage_sub_density
    (X := N) hg A hA
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hrearrange :
      (((Erdos387.modularPreimage N g A).card : ℝ) -
          (A.card : ℝ) * (N : ℝ) / g) / N =
        ((Erdos387.modularPreimage N g A).card : ℝ) / N -
          (A.card : ℝ) / g := by
    field_simp
  rw [← hrearrange, abs_div, abs_of_pos hNreal]
  exact (div_le_div_of_nonneg_right hdisc (le_of_lt hNreal)).trans_lt hNsmall

/-- Any decidable periodic predicate on the naturals has a natural density,
obtained by counting the successful residues in one period. -/
lemma periodic_set_hasDensity (p : ℕ → Prop) [DecidablePred p] {g : ℕ}
    (hg : 0 < g) (hp : Function.Periodic p g) :
    {n | p n}.HasDensity
      ((((Finset.range g).filter p).card : ℝ) / g) := by
  let A := (Finset.range g).filter p
  have hA : ∀ a ∈ A, a < g := by
    intro a ha
    exact Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hd := residueSet_hasDensity hg A hA
  convert hd using 1
  ext n
  simp only [Set.mem_ofPred_eq, residueSet, Finset.mem_filter,
    Finset.mem_range, A]
  rw [hp.map_mod_nat n]
  exact (and_iff_right (Nat.mod_lt n hg)).symm

/-- A common period, modulo `q`, for the binomial polynomials
`n ↦ n.choose k` with `k ≤ M`. -/
def binomialPeriod (q M : ℕ) : ℕ := q * M.factorial

lemma dvd_choose_binomialPeriod {q M i : ℕ} (hi : 0 < i) (hiM : i ≤ M) :
    q ∣ (binomialPeriod q M).choose i := by
  obtain ⟨t, ht⟩ := Nat.dvd_factorial hi hiM
  have hperiod : binomialPeriod q M = (q * t) * i := by
    simp only [binomialPeriod, ht]
    ac_rfl
  rw [hperiod, Nat.choose_mul_right hi.ne']
  exact dvd_mul_of_dvd_left (Nat.dvd_mul_right q t) _

/-- Adding the common period does not change any of the first `M` binomial
coefficients modulo `q`. -/
lemma choose_add_binomialPeriod_modEq (q M n k : ℕ) (hk : k ≤ M) :
    (n + binomialPeriod q M).choose k ≡ n.choose k [MOD q] := by
  rw [Nat.add_comm n, Nat.add_choose_eq]
  have hsingle :
      (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) k,
          (binomialPeriod q M).choose ij.1 * n.choose ij.2) ≡
        (binomialPeriod q M).choose 0 * n.choose k [MOD q] := by
    apply Nat.sum_modEq_single (a := (0, k))
    · intro hnot
      exact False.elim (hnot (by simp))
    · intro ij hij hne
      have hijsum : ij.1 + ij.2 = k :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hi0 : 0 < ij.1 := by
        by_contra hi
        have hi' : ij.1 = 0 := Nat.eq_zero_of_not_pos hi
        have hj' : ij.2 = k := by omega
        exact hne (Prod.ext hi' hj')
      have hiM : ij.1 ≤ M := by omega
      rw [Nat.modEq_zero_iff_dvd]
      exact dvd_mul_of_dvd_left
        (dvd_choose_binomialPeriod hi0 hiM) _
  simpa using hsingle

/-- Hence each fixed binomial coefficient, reduced modulo `q`, is periodic
with the common period `q * M!`. -/
lemma choose_mod_periodic (q M k : ℕ) (hk : k ≤ M) :
    Function.Periodic (fun n : ℕ ↦ n.choose k % q)
      (binomialPeriod q M) := by
  intro n
  exact choose_add_binomialPeriod_modEq q M n k hk

/-- Squarefreeness tested only at primes at most `P`. -/
def SquarefreeUpTo (P a : ℕ) : Prop :=
  ∀ p ∈ Finset.range (P + 1), p.Prime → ¬ p * p ∣ a

instance (P a : ℕ) : Decidable (SquarefreeUpTo P a) := by
  unfold SquarefreeUpTo
  infer_instance

/-- A modulus simultaneously containing the square of every prime at most
`P`. -/
def squarefreeCutoffModulus (P : ℕ) : ℕ := P.factorial ^ 2

lemma prime_sq_dvd_squarefreeCutoffModulus {P p : ℕ} (hp : p.Prime)
    (hpP : p ≤ P) : p * p ∣ squarefreeCutoffModulus P := by
  have hpf : p ∣ P.factorial := Nat.dvd_factorial hp.pos hpP
  simpa [squarefreeCutoffModulus, pow_two] using Nat.mul_dvd_mul hpf hpf

lemma squarefreeUpTo_iff_of_modEq {P a b : ℕ}
    (h : a ≡ b [MOD squarefreeCutoffModulus P]) :
    SquarefreeUpTo P a ↔ SquarefreeUpTo P b := by
  constructor
  · intro ha p hpP hp hpb
    have hple : p ≤ P := by
      have := Finset.mem_range.mp hpP
      omega
    have hab : a ≡ b [MOD p * p] :=
      h.of_dvd (prime_sq_dvd_squarefreeCutoffModulus hp hple)
    exact ha p hpP hp
      (Nat.modEq_zero_iff_dvd.mp
        (hab.trans hpb.modEq_zero_nat))
  · intro hb p hpP hp hpa
    have hple : p ≤ P := by
      have := Finset.mem_range.mp hpP
      omega
    have hab : a ≡ b [MOD p * p] :=
      h.of_dvd (prime_sq_dvd_squarefreeCutoffModulus hp hple)
    exact hb p hpP hp
      (Nat.modEq_zero_iff_dvd.mp
        (hab.symm.trans hpa.modEq_zero_nat))

/-- The fixed left indices which pass all square-divisor tests at primes up
to `P`. -/
def truncatedLeftSquarefreeBinomialIndices (P M n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter fun k ↦ SquarefreeUpTo P (Nat.choose n k)

lemma truncatedLeftSquarefreeBinomialIndices_periodic (P M : ℕ) :
    Function.Periodic (truncatedLeftSquarefreeBinomialIndices P M)
      (binomialPeriod (squarefreeCutoffModulus P) M) := by
  intro n
  ext k
  simp only [truncatedLeftSquarefreeBinomialIndices, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨hk, hsf⟩
    refine ⟨hk, ?_⟩
    exact (squarefreeUpTo_iff_of_modEq
      (choose_add_binomialPeriod_modEq
        (squarefreeCutoffModulus P) M n k hk.2)).mp hsf
  · rintro ⟨hk, hsf⟩
    refine ⟨hk, ?_⟩
    exact (squarefreeUpTo_iff_of_modEq
      (choose_add_binomialPeriod_modEq
        (squarefreeCutoffModulus P) M n k hk.2)).mpr hsf

/-- One complete left pattern with squarefreeness truncated at `P`. -/
def truncatedLeftPatternSet (P M : ℕ) (K : Finset ℕ) : Set ℕ :=
  {n | truncatedLeftSquarefreeBinomialIndices P M n = K}

lemma truncatedLeftPatternSet_hasDensity (P M : ℕ) (K : Finset ℕ) :
    ∃ d : ℝ, (truncatedLeftPatternSet P M K).HasDensity d := by
  let g := binomialPeriod (squarefreeCutoffModulus P) M
  have hg : 0 < g := by
    simp only [g, binomialPeriod, squarefreeCutoffModulus]
    positivity
  let p : ℕ → Prop := fun n ↦
    truncatedLeftSquarefreeBinomialIndices P M n = K
  let _ : DecidablePred p := fun n ↦ inferInstanceAs
    (Decidable (truncatedLeftSquarefreeBinomialIndices P M n = K))
  have hp : Function.Periodic p g := by
    intro n
    dsimp only [p]
    rw [truncatedLeftSquarefreeBinomialIndices_periodic P M n]
  refine ⟨(((Finset.range g).filter p).card : ℝ) / g, ?_⟩
  simpa [truncatedLeftPatternSet, p] using periodic_set_hasDensity p hg hp

lemma squarefree_imp_squarefreeUpTo {P a : ℕ} (ha : Squarefree a) :
    SquarefreeUpTo P a := by
  intro p hpP hp hsq
  exact (Nat.squarefree_iff_prime_squarefree.mp ha p hp) hsq

/-- If a prime square divides a finite product and at most one factor is
divisible by that prime, then its square already divides one factor. -/
lemma prime_sq_dvd_finset_prod_imp {p : ℕ} (hp : p.Prime)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hunique : ∀ i ∈ s, ∀ j ∈ s, p ∣ f i → p ∣ f j → i = j)
    (hdiv : p * p ∣ ∏ i ∈ s, f i) :
    ∃ i ∈ s, p * p ∣ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty] at hdiv
      have hlt : 1 < p * p := by nlinarith [hp.two_le]
      exact False.elim (Nat.not_dvd_of_pos_of_lt Nat.zero_lt_one hlt hdiv)
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha] at hdiv
      by_cases hpa : p ∣ f a
      · have hpProd : ¬ p ∣ ∏ i ∈ s, f i := by
          intro hprod
          obtain ⟨j, hjs, hpj⟩ :=
            (Erdos387.prime_dvd_finset_prod_iff hp s f).mp hprod
          have haj := hunique a (Finset.mem_insert_self a s) j
            (Finset.mem_insert_of_mem hjs) hpa hpj
          exact ha (haj ▸ hjs)
        have hcop : Nat.Coprime (p * p) (∏ i ∈ s, f i) := by
          rw [← pow_two]
          exact (hp.coprime_iff_not_dvd.mpr hpProd).pow_left 2
        refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        exact hcop.dvd_mul_right.mp hdiv
      · have hcop : Nat.Coprime (p * p) (f a) := by
          rw [← pow_two]
          exact (hp.coprime_iff_not_dvd.mpr hpa).pow_left 2
        have hrest : p * p ∣ ∏ i ∈ s, f i :=
          hcop.dvd_mul_left.mp hdiv
        obtain ⟨i, his, hi⟩ := ih
          (fun i hi j hj hpi hpj ↦ hunique i
            (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hpi hpj)
          hrest
        exact ⟨i, Finset.mem_insert_of_mem his, hi⟩

/-- For a prime larger than `k`, square divisibility of `n.choose k` forces
`n` into one of the `k` residue classes `0, ..., k - 1` modulo `p²`. -/
lemma prime_sq_dvd_choose_imp_exists_mod_eq {n k p : ℕ}
    (hp : p.Prime) (hkp : k < p) (hkn : k ≤ n)
    (hdiv : p * p ∣ n.choose k) :
    ∃ i < k, n % (p * p) = i := by
  have hdesc : p * p ∣ n.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact dvd_mul_of_dvd_right hdiv _
  rw [Nat.descFactorial_eq_prod_range] at hdesc
  obtain ⟨i, hi, hsqi⟩ := prime_sq_dvd_finset_prod_imp hp
    (Finset.range k) (fun i ↦ n - i) (by
      intro i hi j hj hpi hpj
      have hik : i < k := Finset.mem_range.mp hi
      have hjk : j < k := Finset.mem_range.mp hj
      have hin : i ≤ n := (Nat.le_of_lt hik).trans hkn
      have hjn : j ≤ n := (Nat.le_of_lt hjk).trans hkn
      have himod : i ≡ n [MOD p] := (Nat.modEq_iff_dvd' hin).mpr hpi
      have hjmod : j ≡ n [MOD p] := (Nat.modEq_iff_dvd' hjn).mpr hpj
      exact (himod.trans hjmod.symm).eq_of_lt_of_lt
        (hik.trans hkp) (hjk.trans hkp)) hdesc
  have hik : i < k := Finset.mem_range.mp hi
  have hin : i ≤ n := (Nat.le_of_lt hik).trans hkn
  have himod : i ≡ n [MOD p * p] :=
    (Nat.modEq_iff_dvd' hin).mpr hsqi
  refine ⟨i, hik, Nat.mod_eq_of_modEq himod.symm ?_⟩
  have hp2 := hp.two_le
  nlinarith

lemma squarefreeUpTo_not_squarefree_exists_large_prime {P a : ℕ}
    (hsmall : SquarefreeUpTo P a) (hnot : ¬ Squarefree a) :
    ∃ p : ℕ, p.Prime ∧ P < p ∧ p * p ∣ a := by
  have hex : ∃ p : ℕ, p.Prime ∧ p * p ∣ a := by
    by_contra h
    push Not at h
    exact hnot (Nat.squarefree_iff_prime_squarefree.mpr h)
  obtain ⟨p, hp, hsq⟩ := hex
  refine ⟨p, hp, ?_, hsq⟩
  by_contra hpP
  have hple : p ≤ P := by omega
  exact hsmall p (Finset.mem_range.mpr (by omega)) hp hsq

/-- The large-prime square obstruction for the first `M` binomial
coefficients. -/
def largeSquareExceptionalSet (P M : ℕ) : Set ℕ :=
  {n | M ≤ n ∧ ∃ k ∈ Finset.Icc 1 M, ∃ p : ℕ,
    p.Prime ∧ P < p ∧ p * p ∣ n.choose k}

/-! ## A positive-density progression for the first finitely many entries -/

/-- The progression on which every prime-square test up to `P` is forced to
pass for all indices at most `M`. -/
def positivityProgression (P M : ℕ) : Set ℕ :=
  residueSet (binomialPeriod (squarefreeCutoffModulus P) M)
    {binomialPeriod (squarefreeCutoffModulus P) M - 1}

lemma binomialPeriod_pos (q M : ℕ) (hq : 0 < q) :
    0 < binomialPeriod q M := by
  simp only [binomialPeriod]
  positivity

/-- If the common binomial period modulo `q` divides `n + 1`, then none of
the first `M` binomial coefficients in row `n` is divisible by `q`.  Pascal's
recurrence propagates nondivisibility from `n.choose 0 = 1`. -/
lemma not_dvd_choose_of_binomialPeriod_dvd_succ {q M n k : ℕ}
    (hq : 1 < q) (hperiod : binomialPeriod q M ∣ n + 1) (hk : k ≤ M) :
    ¬ q ∣ n.choose k := by
  induction k with
  | zero =>
      simpa using Nat.not_dvd_of_pos_of_lt Nat.zero_lt_one hq
  | succ k ih =>
      intro hcur
      have hkM : k + 1 ≤ M := hk
      have hnextmod : (n + 1).choose (k + 1) % q = 0 := by
        have hperiodic := choose_mod_periodic q M (k + 1) hkM
        have hmap := hperiodic.map_mod_nat (n + 1)
        rw [Nat.mod_eq_zero_of_dvd hperiod] at hmap
        simpa using hmap.symm
      have hnext : q ∣ (n + 1).choose (k + 1) :=
        Nat.dvd_iff_mod_eq_zero.mpr hnextmod
      rw [Nat.choose_succ_succ'] at hnext
      exact ih (by omega) ((Nat.dvd_add_iff_left hcur).mpr hnext)

lemma binomialPeriod_prime_sq_dvd_cutoff {P M p : ℕ}
    (hp : p.Prime) (hpP : p ≤ P) :
    binomialPeriod (p * p) M ∣
      binomialPeriod (squarefreeCutoffModulus P) M := by
  exact Nat.mul_dvd_mul_right
    (prime_sq_dvd_squarefreeCutoffModulus hp hpP) M.factorial

lemma binomialPeriod_dvd_succ_of_mem_positivityProgression
    {P M n : ℕ} (hn : n ∈ positivityProgression P M) :
    binomialPeriod (squarefreeCutoffModulus P) M ∣ n + 1 := by
  let g := binomialPeriod (squarefreeCutoffModulus P) M
  have hq : 0 < squarefreeCutoffModulus P := by
    exact pow_pos (Nat.factorial_pos P) 2
  have hg : 0 < g := binomialPeriod_pos _ _ hq
  have hnmod : n % g = g - 1 := by
    simpa [positivityProgression, residueSet, g] using hn
  refine ⟨n / g + 1, ?_⟩
  calc
    n + 1 = (n % g + g * (n / g)) + 1 := by
      rw [Nat.mod_add_div]
    _ = (g - 1 + g * (n / g)) + 1 := by rw [hnmod]
    _ = g * (n / g + 1) := by
      rw [Nat.mul_add]
      omega

lemma positivityProgression_squarefreeUpTo {P M n k : ℕ}
    (hn : n ∈ positivityProgression P M) (hk : k ≤ M) :
    SquarefreeUpTo P (n.choose k) := by
  intro p hpRange hp hpSq
  have hpP : p ≤ P := by
    have := Finset.mem_range.mp hpRange
    omega
  have hsmallPeriod : binomialPeriod (p * p) M ∣ n + 1 :=
    (binomialPeriod_prime_sq_dvd_cutoff hp hpP).trans
      (binomialPeriod_dvd_succ_of_mem_positivityProgression hn)
  have hp2 : 1 < p * p := by nlinarith [hp.two_le]
  exact not_dvd_choose_of_binomialPeriod_dvd_succ hp2 hsmallPeriod hk hpSq

lemma positivityProgression_hasDensity (P M : ℕ) :
    (positivityProgression P M).HasDensity
      (1 / (binomialPeriod (squarefreeCutoffModulus P) M : ℕ) : ℝ) := by
  let g := binomialPeriod (squarefreeCutoffModulus P) M
  have hq : 0 < squarefreeCutoffModulus P := by
    exact pow_pos (Nat.factorial_pos P) 2
  have hg : 0 < g := binomialPeriod_pos _ _ hq
  have hres := residueSet_hasDensity hg ({g - 1} : Finset ℕ) (by
    intro a ha
    rw [Finset.mem_singleton] at ha
    subst a
    omega)
  simpa [positivityProgression, g] using hres

lemma leftSquarefreeBinomialIndices_subset_truncated (P M n : ℕ) :
    leftSquarefreeBinomialIndices M n ⊆
      truncatedLeftSquarefreeBinomialIndices P M n := by
  intro k hk
  rw [leftSquarefreeBinomialIndices, Finset.mem_filter] at hk
  rw [truncatedLeftSquarefreeBinomialIndices, Finset.mem_filter]
  exact ⟨hk.1, squarefree_imp_squarefreeUpTo hk.2⟩

lemma leftPatternSet_symmDiff_truncated_subset (P M : ℕ) (K : Finset ℕ) :
    leftPatternSet M K ∆ truncatedLeftPatternSet P M K ⊆
      Set.Iio M ∪ largeSquareExceptionalSet P M := by
  intro n hn
  by_cases hnM : n < M
  · exact Or.inl hnM
  · apply Or.inr
    refine ⟨by omega, ?_⟩
    have hne : leftSquarefreeBinomialIndices M n ≠
        truncatedLeftSquarefreeBinomialIndices P M n := by
      intro heq
      rcases Set.mem_symmDiff.mp hn with hn | hn
      · exact hn.2 (by simpa [leftPatternSet, truncatedLeftPatternSet, heq] using hn.1)
      · exact hn.2 (by simpa [leftPatternSet, truncatedLeftPatternSet, heq] using hn.1)
    have hnsubset : ¬ truncatedLeftSquarefreeBinomialIndices P M n ⊆
        leftSquarefreeBinomialIndices M n := by
      intro hsub
      exact hne (Finset.Subset.antisymm
        (leftSquarefreeBinomialIndices_subset_truncated P M n) hsub)
    obtain ⟨k, hktrunc, hkfull⟩ := Finset.not_subset.mp hnsubset
    rw [truncatedLeftSquarefreeBinomialIndices, Finset.mem_filter] at hktrunc
    rw [leftSquarefreeBinomialIndices, Finset.mem_filter] at hkfull
    have hnotsf : ¬ Squarefree (n.choose k) := by
      intro hsf
      exact hkfull ⟨hktrunc.1, hsf⟩
    obtain ⟨p, hp, hpP, hpsq⟩ :=
      squarefreeUpTo_not_squarefree_exists_large_prime hktrunc.2 hnotsf
    exact ⟨k, hktrunc.1, p, hp, hpP, hpsq⟩

/-- A finite residue-class cover for the large-square exceptional rows below
`N`.  We enlarge from primes to all possible square moduli; this only makes
the upper bound simpler. -/
def largeSquareCover (N P M : ℕ) : Finset ℕ :=
  (Finset.Ioo P (Nat.sqrt N + 1)).biUnion fun p ↦
    (Finset.range M).biUnion fun i ↦
      Erdos387.modularPreimage N (p * p) {i}

lemma largeSquareExceptionalSet_below_subset_cover {N P M : ℕ}
    (hMP : M ≤ P) :
    largeSquareExceptionalSet P M ∩ Set.Iio N ⊆
      ↑(largeSquareCover N P M) := by
  intro n hn
  rcases hn with ⟨hnE, hnN⟩
  change M ≤ n ∧ ∃ k : ℕ, k ∈ Finset.Icc 1 M ∧ ∃ p : ℕ,
    p.Prime ∧ P < p ∧ p * p ∣ n.choose k at hnE
  rcases hnE with ⟨hnM, k, hk, p, hp, hpP, hsq⟩
  have hkIcc : 1 ≤ k ∧ k ≤ M := Finset.mem_Icc.mp hk
  have hkp : k < p := lt_of_le_of_lt hkIcc.2 (hMP.trans_lt hpP)
  have hkn : k ≤ n := hkIcc.2.trans hnM
  obtain ⟨i, hik, hmod⟩ :=
    prime_sq_dvd_choose_imp_exists_mod_eq hp hkp hkn hsq
  have hin : i < n := hik.trans_le hkn
  have hsqn : p * p ≤ n := by
    by_contra h
    have hnlt : n < p * p := by omega
    have := Nat.mod_eq_of_lt hnlt
    rw [this] at hmod
    omega
  have hpsqrt : p ≤ Nat.sqrt N := by
    apply Nat.le_sqrt.mpr
    exact hsqn.trans (Nat.le_of_lt hnN)
  change n ∈ largeSquareCover N P M
  rw [largeSquareCover]
  apply Finset.mem_biUnion.mpr
  refine ⟨p, Finset.mem_Ioo.mpr ⟨hpP, by omega⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_range.mpr (hik.trans_le hkIcc.2), ?_⟩
  simp only [Erdos387.modularPreimage, Finset.mem_filter, Finset.mem_range,
    Finset.mem_singleton]
  exact ⟨hnN, hmod⟩

/-- A prime larger than `P` is coprime to the modulus of the positivity
progression, provided `P` also dominates the fixed indices. -/
lemma positivityProgressionModulus_coprime_prime_sq {P M p : ℕ}
    (hMP : M ≤ P) (hp : p.Prime) (hpP : P < p) :
    Nat.Coprime (binomialPeriod (squarefreeCutoffModulus P) M) (p * p) := by
  have hpFacP : ¬ p ∣ P.factorial := by
    rw [hp.dvd_factorial]
    omega
  have hpCutoff : ¬ p ∣ squarefreeCutoffModulus P := by
    simpa [squarefreeCutoffModulus, pow_two, hp.dvd_mul] using hpFacP
  have hpFacM : ¬ p ∣ M.factorial := by
    rw [hp.dvd_factorial]
    omega
  have hpPeriod : ¬ p ∣ binomialPeriod (squarefreeCutoffModulus P) M := by
    rw [binomialPeriod, hp.dvd_mul]
    exact not_or_intro hpCutoff hpFacM
  have hcop : p.Coprime (binomialPeriod (squarefreeCutoffModulus P) M) :=
    hp.coprime_iff_not_dvd.mpr hpPeriod
  simpa [pow_two] using hcop.symm.pow_right 2

/-- Canonical residue simultaneously congruent to the final residue of the
positivity progression and to `i` modulo `p²`.  The fallback branch is never
used for the primes in the cover below. -/
noncomputable def progressionCombinedResidue (P M p i : ℕ) : ℕ :=
  if h : Nat.Coprime (binomialPeriod (squarefreeCutoffModulus P) M) (p * p)
  then Nat.chineseRemainder h
    (binomialPeriod (squarefreeCutoffModulus P) M - 1) i
  else 0

lemma progressionCombinedResidue_spec {P M p i : ℕ}
    (hcop : Nat.Coprime
      (binomialPeriod (squarefreeCutoffModulus P) M) (p * p)) :
    progressionCombinedResidue P M p i ≡
        binomialPeriod (squarefreeCutoffModulus P) M - 1
          [MOD binomialPeriod (squarefreeCutoffModulus P) M] ∧
      progressionCombinedResidue P M p i ≡ i [MOD p * p] := by
  simp only [progressionCombinedResidue, dif_pos hcop]
  exact (Nat.chineseRemainder hcop
    (binomialPeriod (squarefreeCutoffModulus P) M - 1) i).prop

lemma progressionCombinedResidue_lt {P M p i : ℕ}
    (hcop : Nat.Coprime
      (binomialPeriod (squarefreeCutoffModulus P) M) (p * p))
    (hp : 0 < p) :
    progressionCombinedResidue P M p i <
      binomialPeriod (squarefreeCutoffModulus P) M * (p * p) := by
  have hq : 0 < squarefreeCutoffModulus P :=
    pow_pos (Nat.factorial_pos P) 2
  rw [progressionCombinedResidue, dif_pos hcop]
  exact Nat.chineseRemainder_lt_mul hcop
    (binomialPeriod (squarefreeCutoffModulus P) M - 1) i
    (binomialPeriod_pos _ _ hq).ne' (Nat.mul_pos hp hp).ne'

/-- The CRT-refined cover of large-prime obstructions which also lie in the
positivity progression.  Each class now has modulus `g * p²`, rather than
only `p²`. -/
noncomputable def progressionLargeSquareCover (N P M : ℕ) : Finset ℕ :=
  ((Finset.Ioo P (Nat.sqrt N + 1)).filter Nat.Prime).biUnion fun p ↦
    (Finset.range M).biUnion fun i ↦
      Erdos387.modularPreimage N
        (binomialPeriod (squarefreeCutoffModulus P) M * (p * p))
        {progressionCombinedResidue P M p i}

lemma progression_largeSquareExceptionalSet_below_subset_cover {N P M : ℕ}
    (hMP : M ≤ P) :
    (positivityProgression P M ∩ largeSquareExceptionalSet P M) ∩ Set.Iio N ⊆
      ↑(progressionLargeSquareCover N P M) := by
  intro n hn
  rcases hn with ⟨⟨hnProg, hnE⟩, hnN⟩
  change M ≤ n ∧ ∃ k : ℕ, k ∈ Finset.Icc 1 M ∧ ∃ p : ℕ,
    p.Prime ∧ P < p ∧ p * p ∣ n.choose k at hnE
  rcases hnE with ⟨hnM, k, hk, p, hp, hpP, hsq⟩
  have hkIcc : 1 ≤ k ∧ k ≤ M := Finset.mem_Icc.mp hk
  have hkp : k < p := lt_of_le_of_lt hkIcc.2 (hMP.trans_lt hpP)
  have hkn : k ≤ n := hkIcc.2.trans hnM
  obtain ⟨i, hik, hmod⟩ :=
    prime_sq_dvd_choose_imp_exists_mod_eq hp hkp hkn hsq
  have hsqn : p * p ≤ n := by
    by_contra h
    have hnlt : n < p * p := by omega
    have := Nat.mod_eq_of_lt hnlt
    rw [this] at hmod
    omega
  have hpsqrt : p ≤ Nat.sqrt N := by
    apply Nat.le_sqrt.mpr
    exact hsqn.trans (Nat.le_of_lt hnN)
  let g := binomialPeriod (squarefreeCutoffModulus P) M
  have hq : 0 < squarefreeCutoffModulus P :=
    pow_pos (Nat.factorial_pos P) 2
  have hg : 0 < g := binomialPeriod_pos _ _ hq
  have hnmodG : n % g = g - 1 := by
    simpa [positivityProgression, residueSet, g] using hnProg
  have hnG : n ≡ g - 1 [MOD g] := by
    change n % g = (g - 1) % g
    rw [Nat.mod_eq_of_lt (show g - 1 < g by omega)]
    exact hnmodG
  have hiSq : i < p * p := by nlinarith [hik, hkp, hp.two_le]
  have hnP : n ≡ i [MOD p * p] := by
    change n % (p * p) = i % (p * p)
    rw [Nat.mod_eq_of_lt hiSq]
    exact hmod
  have hcop := positivityProgressionModulus_coprime_prime_sq hMP hp hpP
  have hnCombined : n ≡ progressionCombinedResidue P M p i
      [MOD g * (p * p)] := by
    have hcrt := Nat.chineseRemainder_modEq_unique hcop hnG hnP
    rw [progressionCombinedResidue, dif_pos hcop]
    simpa [g] using hcrt
  have hresLt : progressionCombinedResidue P M p i < g * (p * p) := by
    simpa [g] using progressionCombinedResidue_lt hcop hp.pos
  change n ∈ progressionLargeSquareCover N P M
  rw [progressionLargeSquareCover]
  apply Finset.mem_biUnion.mpr
  refine ⟨p, ?_, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_Ioo]
    exact ⟨⟨hpP, by omega⟩, hp⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_range.mpr (hik.trans_le hkIcc.2), ?_⟩
    simp only [Erdos387.modularPreimage, Finset.mem_filter, Finset.mem_range,
      Finset.mem_singleton]
    exact ⟨hnN, Nat.mod_eq_of_modEq hnCombined hresLt⟩

lemma card_progressionCombinedPreimage_le {N P M p i : ℕ}
    (hMP : M ≤ P) (hp : p.Prime) (hpP : P < p) :
    ((Erdos387.modularPreimage N
      (binomialPeriod (squarefreeCutoffModulus P) M * (p * p))
      {progressionCombinedResidue P M p i}).card : ℝ) ≤
        (N : ℝ) *
          ((binomialPeriod (squarefreeCutoffModulus P) M : ℝ)⁻¹ *
            ((p : ℝ) ^ 2)⁻¹) + 1 := by
  let g := binomialPeriod (squarefreeCutoffModulus P) M
  have hq : 0 < squarefreeCutoffModulus P :=
    pow_pos (Nat.factorial_pos P) 2
  have hg : 0 < g := binomialPeriod_pos _ _ hq
  have hcop := positivityProgressionModulus_coprime_prime_sq hMP hp hpP
  have hr : progressionCombinedResidue P M p i < g * (p * p) := by
    simpa [g] using progressionCombinedResidue_lt hcop hp.pos
  have hdisc := Erdos387.abs_card_modularPreimage_sub_density
    (X := N) (Nat.mul_pos hg (Nat.mul_pos hp.pos hp.pos))
    ({progressionCombinedResidue P M p i} : Finset ℕ) (by simpa [g] using hr)
  have hupp := (abs_le.mp hdisc).2
  norm_num at hupp
  calc
    ((Erdos387.modularPreimage N (g * (p * p))
      {progressionCombinedResidue P M p i}).card : ℝ) ≤
        (N : ℝ) / ((g : ℝ) * ((p : ℝ) * p)) + 1 := by
          simpa [add_comm] using hupp
    _ = (N : ℝ) * ((g : ℝ)⁻¹ * ((p : ℝ) ^ 2)⁻¹) + 1 := by
      rw [div_eq_mul_inv, pow_two, mul_inv]

lemma card_progressionLargeSquareCover_le (N P M : ℕ) (hMP : M ≤ P) :
    ((progressionLargeSquareCover N P M).card : ℝ) ≤
      (M : ℝ) *
        ((N : ℝ) *
            ((binomialPeriod (squarefreeCutoffModulus P) M : ℝ)⁻¹ *
              (2 / (P + 1 : ℕ) : ℝ)) +
          (Nat.sqrt N + 1 : ℕ)) := by
  let primes := (Finset.Ioo P (Nat.sqrt N + 1)).filter Nat.Prime
  let residues (p : ℕ) := (Finset.range M).biUnion fun i ↦
    Erdos387.modularPreimage N
      (binomialPeriod (squarefreeCutoffModulus P) M * (p * p))
      {progressionCombinedResidue P M p i}
  have houterNat : (progressionLargeSquareCover N P M).card ≤
      ∑ p ∈ primes, (residues p).card := by
    simpa [progressionLargeSquareCover, primes, residues] using
      (Finset.card_biUnion_le (s := primes) (t := residues))
  have houter : ((progressionLargeSquareCover N P M).card : ℝ) ≤
      ∑ p ∈ primes, ((residues p).card : ℝ) := by
    exact_mod_cast houterNat
  calc
    ((progressionLargeSquareCover N P M).card : ℝ) ≤
        ∑ p ∈ primes, ((residues p).card : ℝ) := houter
    _ ≤ ∑ p ∈ primes, ∑ i ∈ Finset.range M,
          ((Erdos387.modularPreimage N
            (binomialPeriod (squarefreeCutoffModulus P) M * (p * p))
            {progressionCombinedResidue P M p i}).card : ℝ) := by
        apply Finset.sum_le_sum
        intro p hpMem
        have hinner := Finset.card_biUnion_le
          (s := Finset.range M)
          (t := fun i ↦ Erdos387.modularPreimage N
            (binomialPeriod (squarefreeCutoffModulus P) M * (p * p))
            {progressionCombinedResidue P M p i})
        exact_mod_cast hinner
    _ ≤ ∑ p ∈ primes, ∑ _i ∈ Finset.range M,
          ((N : ℝ) *
            ((binomialPeriod (squarefreeCutoffModulus P) M : ℝ)⁻¹ *
              ((p : ℝ) ^ 2)⁻¹) + 1) := by
        apply Finset.sum_le_sum
        intro p hpMem
        have hpData := Finset.mem_filter.mp hpMem
        have hpIoo := Finset.mem_Ioo.mp hpData.1
        apply Finset.sum_le_sum
        intro i hi
        exact card_progressionCombinedPreimage_le hMP hpData.2 hpIoo.1
    _ = (M : ℝ) *
          ((N : ℝ) *
              ((binomialPeriod (squarefreeCutoffModulus P) M : ℝ)⁻¹ *
                (∑ p ∈ primes, ((p : ℝ) ^ 2)⁻¹)) + primes.card) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        rw [← Finset.mul_sum]
        rw [← Finset.mul_sum]
        ring
    _ ≤ (M : ℝ) *
          ((N : ℝ) *
              ((binomialPeriod (squarefreeCutoffModulus P) M : ℝ)⁻¹ *
                (2 / (P + 1 : ℕ) : ℝ)) + primes.card) := by
        gcongr
        calc
          ∑ p ∈ primes, ((p : ℝ) ^ 2)⁻¹ ≤
              ∑ p ∈ Finset.Ioo P (Nat.sqrt N + 1), ((p : ℝ) ^ 2)⁻¹ := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · exact Finset.filter_subset _ _
                · intro p hpNot hpMem
                  positivity
          _ ≤ 2 / (P + 1 : ℕ) := by
            simpa using
              (sum_Ioo_inv_sq_le (k := P) (n := Nat.sqrt N + 1) (α := ℝ))
    _ ≤ (M : ℝ) *
          ((N : ℝ) *
              ((binomialPeriod (squarefreeCutoffModulus P) M : ℝ)⁻¹ *
                (2 / (P + 1 : ℕ) : ℝ)) + (Nat.sqrt N + 1 : ℕ)) := by
        gcongr
        have hsub : primes ⊆ Finset.range (Nat.sqrt N + 1) := by
          intro p hpMem
          have hpIoo := Finset.mem_Ioo.mp (Finset.mem_filter.mp hpMem).1
          exact Finset.mem_range.mpr (by omega)
        exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)

lemma progressionLargeSquareExceptionalSet_partialDensity_le {N P M : ℕ}
    (hMP : M ≤ P) (hN : 0 < N) :
    (positivityProgression P M ∩ largeSquareExceptionalSet P M).partialDensity
        (b := N) ≤
      (M : ℝ) *
        ((binomialPeriod (squarefreeCutoffModulus P) M : ℝ)⁻¹ *
            (2 / (P + 1 : ℕ) : ℝ) +
          ((Nat.sqrt N + 1 : ℕ) : ℝ) / N) := by
  rw [partialDensity_eq_ncard]
  have hsubset := progression_largeSquareExceptionalSet_below_subset_cover
    (N := N) hMP
  have hncard :
      ((positivityProgression P M ∩ largeSquareExceptionalSet P M) ∩
        Set.Iio N).ncard ≤ (progressionLargeSquareCover N P M).card := by
    simpa using Set.ncard_le_ncard hsubset
  have hncardR :
      ((((positivityProgression P M ∩ largeSquareExceptionalSet P M) ∩
        Set.Iio N).ncard : ℕ) : ℝ) ≤
          (progressionLargeSquareCover N P M).card := by
    exact_mod_cast hncard
  have hcover := card_progressionLargeSquareCover_le N P M hMP
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    ((((positivityProgression P M ∩ largeSquareExceptionalSet P M) ∩
        Set.Iio N).ncard : ℕ) : ℝ) / N ≤
        ((progressionLargeSquareCover N P M).card : ℝ) / N := by
          exact div_le_div_of_nonneg_right hncardR hNreal.le
    _ ≤ ((M : ℝ) *
        ((N : ℝ) *
            ((binomialPeriod (squarefreeCutoffModulus P) M : ℝ)⁻¹ *
              (2 / (P + 1 : ℕ) : ℝ)) +
          (Nat.sqrt N + 1 : ℕ))) / N := by
          exact div_le_div_of_nonneg_right hcover hNreal.le
    _ = (M : ℝ) *
        ((binomialPeriod (squarefreeCutoffModulus P) M : ℝ)⁻¹ *
            (2 / (P + 1 : ℕ) : ℝ) +
          ((Nat.sqrt N + 1 : ℕ) : ℝ) / N) := by
          field_simp

lemma card_modularPreimage_singleton_le {N p i : ℕ} (hp : 0 < p)
    (hi : i < p * p) :
    ((Erdos387.modularPreimage N (p * p) {i}).card : ℝ) ≤
      (N : ℝ) * ((p : ℝ) ^ 2)⁻¹ + 1 := by
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have hdisc := Erdos387.abs_card_modularPreimage_sub_density
    (X := N) hpp ({i} : Finset ℕ) (by simpa using hi)
  have hupp := (abs_le.mp hdisc).2
  norm_num at hupp
  calc
    ((Erdos387.modularPreimage N (p * p) {i}).card : ℝ) ≤
        (N : ℝ) / ((p : ℝ) * p) + 1 := by linarith
    _ = (N : ℝ) * ((p : ℝ) ^ 2)⁻¹ + 1 := by
      rw [pow_two, div_eq_mul_inv]

lemma card_largeSquareCover_le (N P M : ℕ) (hMP : M ≤ P) :
    ((largeSquareCover N P M).card : ℝ) ≤
      (M : ℝ) *
        ((N : ℝ) * (2 / (P + 1 : ℕ) : ℝ) + (Nat.sqrt N + 1 : ℕ)) := by
  let primes := Finset.Ioo P (Nat.sqrt N + 1)
  let residues (p : ℕ) := (Finset.range M).biUnion fun i ↦
    Erdos387.modularPreimage N (p * p) {i}
  have houterNat : (largeSquareCover N P M).card ≤
      ∑ p ∈ primes, (residues p).card := by
    simpa [largeSquareCover, primes, residues] using
      (Finset.card_biUnion_le (s := primes) (t := residues))
  have houter : ((largeSquareCover N P M).card : ℝ) ≤
      ∑ p ∈ primes, ((residues p).card : ℝ) := by
    exact_mod_cast houterNat
  calc
    ((largeSquareCover N P M).card : ℝ) ≤
        ∑ p ∈ primes, ((residues p).card : ℝ) := houter
    _ ≤ ∑ p ∈ primes, ∑ i ∈ Finset.range M,
          ((Erdos387.modularPreimage N (p * p) {i}).card : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hinner := Finset.card_biUnion_le
          (s := Finset.range M)
          (t := fun i ↦ Erdos387.modularPreimage N (p * p) {i})
        exact_mod_cast hinner
    _ ≤ ∑ p ∈ primes, ∑ _i ∈ Finset.range M,
          ((N : ℝ) * ((p : ℝ) ^ 2)⁻¹ + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro i hi
        have hpIoo := Finset.mem_Ioo.mp hp
        have hp0 : 0 < p := by omega
        have hiM : i < M := Finset.mem_range.mp hi
        have hip : i < p * p := by
          have hp2 : 2 ≤ p := by omega
          nlinarith
        exact card_modularPreimage_singleton_le hp0 hip
    _ = (M : ℝ) *
          ((N : ℝ) * (∑ p ∈ primes, ((p : ℝ) ^ 2)⁻¹) + primes.card) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        rw [← Finset.mul_sum]
        ring
    _ ≤ (M : ℝ) *
          ((N : ℝ) * (2 / (P + 1 : ℕ) : ℝ) + primes.card) := by
        gcongr
        simpa [primes] using
          (sum_Ioo_inv_sq_le (k := P) (n := Nat.sqrt N + 1) (α := ℝ))
    _ ≤ (M : ℝ) *
          ((N : ℝ) * (2 / (P + 1 : ℕ) : ℝ) + (Nat.sqrt N + 1 : ℕ)) := by
        gcongr
        have hsub : primes ⊆ Finset.range (Nat.sqrt N + 1) := by
          intro p hp
          have hp' : P < p ∧ p ≤ Nat.sqrt N := by simpa [primes] using hp
          exact Finset.mem_range.mpr (by omega)
        exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    _ = _ := by rfl

lemma largeSquareExceptionalSet_partialDensity_le {N P M : ℕ}
    (hMP : M ≤ P) (hN : 0 < N) :
    (largeSquareExceptionalSet P M).partialDensity (b := N) ≤
      (M : ℝ) *
        (2 / (P + 1 : ℕ) + ((Nat.sqrt N + 1 : ℕ) : ℝ) / N) := by
  rw [partialDensity_eq_ncard]
  have hsubset := largeSquareExceptionalSet_below_subset_cover
    (N := N) hMP
  have hncard : (largeSquareExceptionalSet P M ∩ Set.Iio N).ncard ≤
      (largeSquareCover N P M).card := by
    simpa using Set.ncard_le_ncard hsubset
  have hncardR : ((largeSquareExceptionalSet P M ∩ Set.Iio N).ncard : ℝ) ≤
      (largeSquareCover N P M).card := by
    exact_mod_cast hncard
  have hcover := card_largeSquareCover_le N P M hMP
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    ((largeSquareExceptionalSet P M ∩ Set.Iio N).ncard : ℝ) / N ≤
        ((largeSquareCover N P M).card : ℝ) / N := by
          exact div_le_div_of_nonneg_right hncardR hNreal.le
    _ ≤ ((M : ℝ) *
        ((N : ℝ) * (2 / (P + 1 : ℕ) : ℝ) +
          (Nat.sqrt N + 1 : ℕ))) / N := by
          exact div_le_div_of_nonneg_right hcover hNreal.le
    _ = (M : ℝ) *
        (2 / (P + 1 : ℕ) + ((Nat.sqrt N + 1 : ℕ) : ℝ) / N) := by
          field_simp

lemma eventually_natSqrt_add_one_div_lt {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ((Nat.sqrt N + 1 : ℕ) : ℝ) / N < δ := by
  obtain ⟨L, hL⟩ := exists_nat_gt (2 / δ)
  have hLpos : 0 < L := by
    have htwo : (0 : ℝ) < 2 / δ := by positivity
    exact_mod_cast htwo.trans hL
  filter_upwards [eventually_ge_atTop (L * L)] with N hN
  have hLs : L ≤ Nat.sqrt N := Nat.le_sqrt.mpr hN
  have hsN : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have hNpos : 0 < N := by
    have : 0 < L * L := Nat.mul_pos hLpos hLpos
    omega
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hfrac : ((Nat.sqrt N + 1 : ℕ) : ℝ) / N ≤ 2 / L := by
    rw [div_le_div_iff₀ hNreal hLreal]
    push_cast
    have hLsR : (L : ℝ) ≤ Nat.sqrt N := by exact_mod_cast hLs
    have hsNR : ((Nat.sqrt N : ℕ) : ℝ) * Nat.sqrt N ≤ N := by
      exact_mod_cast hsN
    have hspos : (1 : ℝ) ≤ Nat.sqrt N := by
      exact_mod_cast (hLpos.trans_le hLs)
    nlinarith
  have htwoL : (2 : ℝ) / L < δ := by
    rw [div_lt_iff₀ hLreal]
    have hscaled : (2 : ℝ) < δ * L := by
      have := (div_lt_iff₀ hδ).mp hL
      nlinarith
    exact hscaled
  exact hfrac.trans_lt htwoL

/-- For every fixed collection of left indices, the rows with a square
prime factor above the cutoff have uniformly vanishing upper density. -/
lemma exists_largeSquareExceptionalSet_eventually_small (M : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ, M ≤ P ∧ ∀ᶠ N : ℕ in atTop,
      (largeSquareExceptionalSet P M).partialDensity (b := N) < ε := by
  by_cases hM : M = 0
  · subst M
    refine ⟨0, le_rfl, ?_⟩
    filter_upwards with N
    have hempty : largeSquareExceptionalSet 0 0 = ∅ := by
      ext n
      simp [largeSquareExceptionalSet]
    rw [hempty]
    simpa [Set.partialDensity] using hε
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    obtain ⟨L, hL⟩ := exists_nat_gt ((4 * (M : ℝ)) / ε)
    let P := M + L
    have hMP : M ≤ P := by simp [P]
    have hconst : (M : ℝ) * (2 / (P + 1 : ℕ) : ℝ) < ε / 2 := by
      have hPL : (L : ℝ) ≤ ((P + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show L ≤ P + 1 by simp only [P]; omega)
      have hmain : (4 : ℝ) * M < ε * (P + 1 : ℕ) := by
        have hscaled := (div_lt_iff₀ hε).mp hL
        calc
          (4 : ℝ) * M < (L : ℝ) * ε := hscaled
          _ = ε * L := by ring
          _ ≤ ε * (P + 1 : ℕ) := mul_le_mul_of_nonneg_left hPL hε.le
      have hPpos : (0 : ℝ) < (P + 1 : ℕ) := by positivity
      calc
        (M : ℝ) * (2 / (P + 1 : ℕ) : ℝ) =
            (2 * M) / (P + 1 : ℕ) := by ring
        _ < ε / 2 := by
          rw [div_lt_div_iff₀ hPpos (by norm_num : (0 : ℝ) < 2)]
          nlinarith
    have hδ : 0 < ε / (2 * (M : ℝ)) := by positivity
    have hend := eventually_natSqrt_add_one_div_lt hδ
    refine ⟨P, hMP, ?_⟩
    filter_upwards [hend, eventually_gt_atTop 0] with N hNend hN
    have hbound := largeSquareExceptionalSet_partialDensity_le hMP hN
    have hMnonneg : (0 : ℝ) ≤ M := by positivity
    calc
      (largeSquareExceptionalSet P M).partialDensity (b := N) ≤
          (M : ℝ) * (2 / (P + 1 : ℕ) +
            ((Nat.sqrt N + 1 : ℕ) : ℝ) / N) := hbound
      _ < ε := by
        have htail : (M : ℝ) *
            (((Nat.sqrt N + 1 : ℕ) : ℝ) / N) < ε / 2 := by
          calc
            (M : ℝ) * (((Nat.sqrt N + 1 : ℕ) : ℝ) / N) <
                (M : ℝ) * (ε / (2 * (M : ℝ))) := by
                  gcongr
            _ = ε / 2 := by field_simp
        nlinarith

/-- If the symmetric difference of two sets is contained in an exceptional
set, their partial densities differ by at most the exceptional partial
density. -/
lemma abs_partialDensity_sub_le_of_symmDiff_subset {S T E : Set ℕ}
    (hSTE : S ∆ T ⊆ E) (N : ℕ) :
    |S.partialDensity (b := N) - T.partialDensity (b := N)| ≤
      E.partialDensity (b := N) := by
  by_cases hN : N = 0
  · subst N
    simp [Set.partialDensity]
  have hST : S ∩ Set.Iio N ⊆
      (T ∩ Set.Iio N) ∪ (E ∩ Set.Iio N) := by
    intro n hn
    by_cases hnT : n ∈ T
    · exact Or.inl ⟨hnT, hn.2⟩
    · exact Or.inr ⟨hSTE (Set.mem_symmDiff.mpr (Or.inl ⟨hn.1, hnT⟩)), hn.2⟩
  have hTS : T ∩ Set.Iio N ⊆
      (S ∩ Set.Iio N) ∪ (E ∩ Set.Iio N) := by
    intro n hn
    by_cases hnS : n ∈ S
    · exact Or.inl ⟨hnS, hn.2⟩
    · exact Or.inr ⟨hSTE (Set.mem_symmDiff.mpr (Or.inr ⟨hn.1, hnS⟩)), hn.2⟩
  have hcardST : (S ∩ Set.Iio N).ncard ≤
      (T ∩ Set.Iio N).ncard + (E ∩ Set.Iio N).ncard :=
    (Set.ncard_le_ncard hST).trans (Set.ncard_union_le _ _)
  have hcardTS : (T ∩ Set.Iio N).ncard ≤
      (S ∩ Set.Iio N).ncard + (E ∩ Set.Iio N).ncard :=
    (Set.ncard_le_ncard hTS).trans (Set.ncard_union_le _ _)
  rw [partialDensity_eq_ncard, partialDensity_eq_ncard,
    partialDensity_eq_ncard, ← sub_div, abs_div]
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [abs_of_nonneg hNnonneg]
  rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < N)]
  have hcardSTR : ((S ∩ Set.Iio N).ncard : ℝ) ≤
      (T ∩ Set.Iio N).ncard + (E ∩ Set.Iio N).ncard := by
    exact_mod_cast hcardST
  have hcardTSR : ((T ∩ Set.Iio N).ncard : ℝ) ≤
      (S ∩ Set.Iio N).ncard + (E ∩ Set.Iio N).ncard := by
    exact_mod_cast hcardTS
  rw [abs_le]
  constructor <;> linarith

lemma partialDensity_union_le (S T : Set ℕ) (N : ℕ) :
    (S ∪ T).partialDensity (b := N) ≤
      S.partialDensity (b := N) + T.partialDensity (b := N) := by
  by_cases hN : N = 0
  · subst N
    simp [Set.partialDensity]
  rw [partialDensity_eq_ncard, partialDensity_eq_ncard,
    partialDensity_eq_ncard]
  have hset : (S ∪ T) ∩ Set.Iio N =
      (S ∩ Set.Iio N) ∪ (T ∩ Set.Iio N) := by
    ext n
    aesop
  rw [hset, ← add_div]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Set.ncard_union_le
      (S ∩ Set.Iio N) (T ∩ Set.Iio N)
  · positivity

/-- A real sequence converges if, at every accuracy, it is eventually close
to some convergent real sequence.  The comparison sequence and its limit may
depend on the requested accuracy. -/
lemma exists_tendsto_of_eventually_approximable (f : ℕ → ℝ)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ g : ℕ → ℝ, ∃ a : ℝ, Tendsto g atTop (𝓝 a) ∧
        ∀ᶠ N : ℕ in atTop, dist (f N) (g N) < ε) :
    ∃ a : ℝ, Tendsto f atTop (𝓝 a) := by
  rw [← cauchy_map_iff_exists_tendsto]
  change CauchySeq f
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨g, a, hg, hfg⟩ := happrox (ε / 3) (by positivity)
  obtain ⟨N₁, hN₁⟩ := (eventually_atTop.1 hfg)
  obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.mp hg.cauchySeq
    (ε / 3) (by positivity)
  refine ⟨max N₁ N₂, fun m hm n hn ↦ ?_⟩
  have hfm : dist (f m) (g m) < ε / 3 := hN₁ m (le_trans (le_max_left _ _) hm)
  have hfn : dist (f n) (g n) < ε / 3 := hN₁ n (le_trans (le_max_left _ _) hn)
  have hgm : N₂ ≤ m := le_trans (le_max_right _ _) hm
  have hgn : N₂ ≤ n := le_trans (le_max_right _ _) hn
  calc
    dist (f m) (f n) ≤
        dist (f m) (g m) + dist (g m) (g n) + dist (g n) (f n) :=
      dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · exact hN₂ m hgm n hgn
      · simpa [dist_comm] using hfn
    _ = ε := by ring

/-- Every bounded initial interval of naturals has density zero. -/
lemma Iic_hasDensity_zero (B : ℕ) : (Set.Iic B).HasDensity 0 := by
  rw [Set.HasDensity]
  apply (tendsto_const_div_atTop_nhds_zero_nat (B + 1 : ℝ)).congr'
  filter_upwards [eventually_gt_atTop B] with N hN
  rw [partialDensity_eq_ncard]
  have hinter : Set.Iic B ∩ Set.Iio N = Set.Iic B := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Iio]
    omega
  rw [hinter, Set.ncard_Iic_nat]
  norm_num

/-- The elementary fixed-index sieve: every complete squarefree pattern
among `n.choose 1, ..., n.choose M` has a natural density. -/
theorem finiteLeftPatternsHaveDensity : FiniteLeftPatternsHaveDensity := by
  intro M K hK
  change ∃ d : ℝ, Tendsto
    (fun N : ℕ ↦ (leftPatternSet M K).partialDensity (b := N))
      atTop (nhds d)
  apply exists_tendsto_of_eventually_approximable
  intro ε hε
  obtain ⟨P, hMP, hlarge⟩ :=
    exists_largeSquareExceptionalSet_eventually_small M (show 0 < ε / 2 by positivity)
  obtain ⟨d, hd⟩ := truncatedLeftPatternSet_hasDensity P M K
  refine ⟨fun N ↦ (truncatedLeftPatternSet P M K).partialDensity (b := N),
    d, hd, ?_⟩
  have hIic : ∀ᶠ N : ℕ in atTop,
      (Set.Iic M).partialDensity (b := N) < ε / 2 :=
    (Iic_hasDensity_zero M) (Iio_mem_nhds (show 0 < ε / 2 by positivity))
  filter_upwards [hlarge, hIic] with N hNlarge hNIic
  rw [Real.dist_eq]
  have hsymm : leftPatternSet M K ∆ truncatedLeftPatternSet P M K ⊆
      Set.Iic M ∪ largeSquareExceptionalSet P M := by
    intro n hn
    rcases leftPatternSet_symmDiff_truncated_subset P M K hn with hn | hn
    · exact Or.inl (Nat.le_of_lt hn)
    · exact Or.inr hn
  calc
    |(leftPatternSet M K).partialDensity (b := N) -
        (truncatedLeftPatternSet P M K).partialDensity (b := N)| ≤
      (Set.Iic M ∪ largeSquareExceptionalSet P M).partialDensity (b := N) :=
        abs_partialDensity_sub_le_of_symmDiff_subset hsymm N
    _ ≤ (Set.Iic M).partialDensity (b := N) +
        (largeSquareExceptionalSet P M).partialDensity (b := N) :=
          partialDensity_union_le _ _ N
    _ < ε := by linarith

/-- A row in the positivity progression, outside the large-prime exceptional
set and the finite initial interval, has every one of its first `M`
coefficients squarefree. -/
lemma positivityProgression_subset_fullLeftPattern_union (P M : ℕ) :
    positivityProgression P M ⊆
      leftPatternSet M (Finset.Icc 1 M) ∪
        ((positivityProgression P M ∩ largeSquareExceptionalSet P M) ∪
          Set.Iic M) := by
  intro n hnProg
  by_cases hnM : M ≤ n
  · by_cases hnE : n ∈ largeSquareExceptionalSet P M
    · exact Or.inr (Or.inl ⟨hnProg, hnE⟩)
    · apply Or.inl
      change leftSquarefreeBinomialIndices M n = Finset.Icc 1 M
      apply Finset.Subset.antisymm
      · exact Finset.filter_subset _ _
      · intro k hk
        rw [leftSquarefreeBinomialIndices, Finset.mem_filter]
        refine ⟨hk, ?_⟩
        have hsmall := positivityProgression_squarefreeUpTo hnProg
          (Finset.mem_Icc.mp hk).2
        by_contra hnot
        obtain ⟨p, hp, hpP, hsq⟩ :=
          squarefreeUpTo_not_squarefree_exists_large_prime hsmall hnot
        exact hnE ⟨hnM, k, hk, p, hp, hpP, hsq⟩
  · exact Or.inr (Or.inr (show n ≤ M by omega))

/-- Simultaneously requiring any fixed initial block of binomial
coefficients to be squarefree has positive natural density. -/
theorem fullLeftPattern_hasPositiveDensity (M : ℕ) :
    ∃ d : ℝ, 0 < d ∧
      (leftPatternSet M (Finset.Icc 1 M)).HasDensity d := by
  by_cases hM0 : M = 0
  · subst M
    refine ⟨1, by norm_num, ?_⟩
    have hset : leftPatternSet 0 (Finset.Icc 1 0) = Set.univ := by
      ext n
      simp [leftPatternSet, leftSquarefreeBinomialIndices]
    rw [hset]
    rw [Set.HasDensity]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp [Set.partialDensity, hn.ne']
  · have hM : 0 < M := Nat.pos_of_ne_zero hM0
    let P := 8 * M
    let g := binomialPeriod (squarefreeCutoffModulus P) M
    have hMP : M ≤ P := by dsimp [P]; omega
    have hq : 0 < squarefreeCutoffModulus P :=
      pow_pos (Nat.factorial_pos P) 2
    have hg : 0 < g := binomialPeriod_pos _ _ hq
    obtain ⟨d, hd⟩ := finiteLeftPatternsHaveDensity M
      (Finset.Icc 1 M) (Finset.mem_powerset.mpr fun _ h ↦ h)
    have hratio : (2 / (P + 1 : ℕ) : ℝ) ≤ 1 / (4 * (M : ℝ)) := by
      dsimp [P]
      have hmR : (0 : ℝ) < M := by exact_mod_cast hM
      field_simp
      norm_num [Nat.cast_add, Nat.cast_mul] at *
    have hExceptional : ∀ᶠ N : ℕ in atTop,
        (positivityProgression P M ∩ largeSquareExceptionalSet P M).partialDensity
            (b := N) < 1 / (2 * (g : ℝ)) := by
      have hδ : 0 < 1 / (4 * (M : ℝ) * (g : ℝ)) := by positivity
      have hsqrt := eventually_natSqrt_add_one_div_lt hδ
      filter_upwards [hsqrt, eventually_gt_atTop 0] with N hNsqrt hN
      have hbound := progressionLargeSquareExceptionalSet_partialDensity_le
        (N := N) hMP hN
      have hconst :
          (M : ℝ) * ((g : ℝ)⁻¹ * (2 / (P + 1 : ℕ) : ℝ)) ≤
            1 / (4 * (g : ℝ)) := by
        calc
          (M : ℝ) * ((g : ℝ)⁻¹ * (2 / (P + 1 : ℕ) : ℝ)) ≤
              (M : ℝ) * ((g : ℝ)⁻¹ * (1 / (4 * (M : ℝ)))) := by
                gcongr
          _ = 1 / (4 * (g : ℝ)) := by
            field_simp
      have herr :
          (M : ℝ) * (((Nat.sqrt N + 1 : ℕ) : ℝ) / N) <
            1 / (4 * (g : ℝ)) := by
        calc
          (M : ℝ) * (((Nat.sqrt N + 1 : ℕ) : ℝ) / N) <
              (M : ℝ) * (1 / (4 * (M : ℝ) * (g : ℝ))) := by
                exact mul_lt_mul_of_pos_left hNsqrt (by exact_mod_cast hM)
          _ = 1 / (4 * (g : ℝ)) := by
            field_simp
      calc
        (positivityProgression P M ∩ largeSquareExceptionalSet P M).partialDensity
            (b := N) ≤
            (M : ℝ) *
              ((g : ℝ)⁻¹ * (2 / (P + 1 : ℕ) : ℝ) +
                ((Nat.sqrt N + 1 : ℕ) : ℝ) / N) := by
                  simpa [g] using hbound
        _ = (M : ℝ) * ((g : ℝ)⁻¹ * (2 / (P + 1 : ℕ) : ℝ)) +
              (M : ℝ) * (((Nat.sqrt N + 1 : ℕ) : ℝ) / N) := by ring
        _ < 1 / (2 * (g : ℝ)) := by
          have hgR : (0 : ℝ) < g := by exact_mod_cast hg
          calc
            (M : ℝ) * ((g : ℝ)⁻¹ * (2 / (P + 1 : ℕ) : ℝ)) +
                (M : ℝ) * (((Nat.sqrt N + 1 : ℕ) : ℝ) / N) <
                1 / (4 * (g : ℝ)) + 1 / (4 * (g : ℝ)) :=
                  add_lt_add_of_le_of_lt hconst herr
            _ = 1 / (2 * (g : ℝ)) := by
              field_simp
              ring
    have hProgressionLow : ∀ᶠ N : ℕ in atTop,
        7 / (8 * (g : ℝ)) <
          (positivityProgression P M).partialDensity (b := N) := by
      have hden : (positivityProgression P M).HasDensity (1 / (g : ℝ)) := by
        simpa [g] using positivityProgression_hasDensity P M
      apply hden
      apply Ioi_mem_nhds
      have hgR : (0 : ℝ) < g := by exact_mod_cast hg
      field_simp
      norm_num
    have hInitialSmall : ∀ᶠ N : ℕ in atTop,
        (Set.Iic M).partialDensity (b := N) < 1 / (8 * (g : ℝ)) := by
      exact (Iic_hasDensity_zero M)
        (Iio_mem_nhds (show 0 < 1 / (8 * (g : ℝ)) by positivity))
    have hGoodLow : ∀ᶠ N : ℕ in atTop,
        1 / (4 * (g : ℝ)) <
          (leftPatternSet M (Finset.Icc 1 M)).partialDensity (b := N) := by
      filter_upwards [hExceptional, hProgressionLow, hInitialSmall] with
        N hE hProg hInit
      have hcontain := positivityProgression_subset_fullLeftPattern_union P M
      have hmono : (positivityProgression P M).partialDensity (b := N) ≤
          (leftPatternSet M (Finset.Icc 1 M) ∪
            ((positivityProgression P M ∩ largeSquareExceptionalSet P M) ∪
              Set.Iic M)).partialDensity (b := N) := by
        rw [partialDensity_eq_ncard, partialDensity_eq_ncard]
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Set.ncard_le_ncard
            (Set.inter_subset_inter_left (Set.Iio N) hcontain)
        · positivity
      have hunion₁ := partialDensity_union_le
        (leftPatternSet M (Finset.Icc 1 M))
        ((positivityProgression P M ∩ largeSquareExceptionalSet P M) ∪ Set.Iic M) N
      have hunion₂ := partialDensity_union_le
        (positivityProgression P M ∩ largeSquareExceptionalSet P M) (Set.Iic M) N
      have hgR : (0 : ℝ) < g := by exact_mod_cast hg
      have htotal : (positivityProgression P M).partialDensity (b := N) ≤
          (leftPatternSet M (Finset.Icc 1 M)).partialDensity (b := N) +
            (positivityProgression P M ∩ largeSquareExceptionalSet P M).partialDensity
              (b := N) + (Set.Iic M).partialDensity (b := N) := by
        calc
          (positivityProgression P M).partialDensity (b := N) ≤
              (leftPatternSet M (Finset.Icc 1 M) ∪
                ((positivityProgression P M ∩ largeSquareExceptionalSet P M) ∪
                  Set.Iic M)).partialDensity (b := N) := hmono
          _ ≤ (leftPatternSet M (Finset.Icc 1 M)).partialDensity (b := N) +
                ((positivityProgression P M ∩ largeSquareExceptionalSet P M) ∪
                  Set.Iic M).partialDensity (b := N) := hunion₁
          _ ≤ (leftPatternSet M (Finset.Icc 1 M)).partialDensity (b := N) +
                ((positivityProgression P M ∩ largeSquareExceptionalSet P M).partialDensity
                  (b := N) + (Set.Iic M).partialDensity (b := N)) := by gcongr
          _ = _ := by ring
      have harith : 7 / (8 * (g : ℝ)) - 1 / (2 * (g : ℝ)) -
          1 / (8 * (g : ℝ)) = 1 / (4 * (g : ℝ)) := by
        field_simp
        ring
      linarith
    have hdLower : 1 / (4 * (g : ℝ)) ≤ d :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hd
        (hGoodLow.mono fun _ h ↦ h.le)
    refine ⟨d, ?_, hd⟩
    exact (show 0 < 1 / (4 * (g : ℝ)) by positivity).trans_le hdLower

/-- Changing a set inside a density-zero exceptional set preserves existence
of natural density. -/
lemma exists_hasDensity_of_symmDiff_subset_density_zero {S T E : Set ℕ}
    (hSTE : S ∆ T ⊆ E) (hT : ∃ d : ℝ, T.HasDensity d)
    (hE : E.HasDensity 0) : ∃ d : ℝ, S.HasDensity d := by
  obtain ⟨d, hd⟩ := hT
  change ∃ a : ℝ, Tendsto (fun N : ℕ ↦ S.partialDensity (b := N)) atTop (𝓝 a)
  apply exists_tendsto_of_eventually_approximable
  intro ε hε
  refine ⟨fun N ↦ T.partialDensity (b := N), d, hd, ?_⟩
  have hEsmall : ∀ᶠ N : ℕ in atTop, E.partialDensity (b := N) < ε :=
    hE (gt_mem_nhds hε)
  filter_upwards [hEsmall] with N hN
  rw [Real.dist_eq]
  exact (abs_partialDensity_sub_le_of_symmDiff_subset hSTE N).trans_lt hN

/-- Finite-cutoff exact-fiber densities plus the vanishing middle tail imply
the existence of every full exact-count density.  This is the abstract
two-parameter limit in the proof of Granville--Ramaré Theorem 5. -/
theorem exactCountSet_hasDensity_of_cutoff_and_tail
    (hCutoff : ∀ M j : ℕ, ∃ d : ℝ, (cutoffExactCountSet M j).HasDensity d)
    (hTail : MiddleTailVanishes) (j : ℕ) :
    ∃ d : ℝ, (exactCountSet j).HasDensity d := by
  change ∃ d : ℝ, Tendsto
    (fun N : ℕ ↦ (exactCountSet j).partialDensity (b := N)) atTop (𝓝 d)
  apply exists_tendsto_of_eventually_approximable
  intro ε hε
  obtain ⟨M, hM⟩ := hTail ε hε
  obtain ⟨d, hd⟩ := hCutoff M j
  refine ⟨fun N ↦ (cutoffExactCountSet M j).partialDensity (b := N), d, hd, ?_⟩
  filter_upwards [hM] with N hN
  rw [Real.dist_eq]
  exact (abs_partialDensity_sub_le_of_symmDiff_subset
    (exactCountSet_symmDiff_cutoff_subset_middle M j) N).trans_lt hN

/-- Source-faithful construction of the distributional input used below.
Only the finite-cutoff theorem, the uniform middle-tail theorem, and the
positive even-fiber theorem remain as number-theoretic inputs. -/
theorem granvilleRamareDistribution_of_cutoff_tail_positivity
    (hCutoff : ∀ M j : ℕ, ∃ d : ℝ, (cutoffExactCountSet M j).HasDensity d)
    (hTail : MiddleTailVanishes)
    (hPos : ∀ m : ℕ, 0 < m → ∃ d : ℝ,
      0 < d ∧ (exactCountSet (2 * m)).HasDensity d) :
    GranvilleRamareDistribution := by
  refine ⟨?_, hPos⟩
  exact exactCountSet_hasDensity_of_cutoff_and_tail hCutoff hTail

/-- Densities add on a disjoint union. -/
lemma hasDensity_union_of_disjoint {S T : Set ℕ} {s t : ℝ}
    (hS : S.HasDensity s) (hT : T.HasDensity t) (hdisj : Disjoint S T) :
    (S ∪ T).HasDensity (s + t) := by
  rw [Set.HasDensity] at hS hT ⊢
  apply (hS.add hT).congr'
  filter_upwards with n
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  have hST : Disjoint (S ∩ Set.Iio n) (T ∩ Set.Iio n) :=
    hdisj.mono Set.inter_subset_left Set.inter_subset_left
  rw [show (S ∪ T) ∩ Set.Iio n =
      (S ∩ Set.Iio n) ∪ (T ∩ Set.Iio n) by ext; aesop]
  rw [Set.ncard_union_eq hST]
  push_cast
  ring

/-- Densities add over a finite pairwise-disjoint indexed union. -/
lemma hasDensity_iUnion_finset_of_pairwise_disjoint {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (S : ι → Set ℕ) (d : ι → ℝ)
    (hd : ∀ i ∈ s, (S i).HasDensity (d i))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) :
    (⋃ i ∈ s, S i).HasDensity (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [Set.HasDensity, Set.partialDensity]
  | @insert a s ha ih =>
      have hda : (S a).HasDensity (d a) := hd a (Finset.mem_insert_self _ _)
      have hds : (⋃ i ∈ s, S i).HasDensity (∑ i ∈ s, d i) := by
        apply ih
        · exact fun i hi ↦ hd i (Finset.mem_insert_of_mem hi)
        · exact fun i hi j hj hij ↦
            hpair i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hdisj : Disjoint (S a) (⋃ i ∈ s, S i) := by
        rw [Set.disjoint_left]
        intro n hna hn
        simp only [Set.mem_iUnion] at hn
        obtain ⟨i, hi, hni⟩ := hn
        exact (Set.disjoint_left.mp
          (hpair a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
            (fun hai ↦ ha (hai ▸ hi)))) hna hni
      simpa [ha, Finset.sum_insert] using
        hasDensity_union_of_disjoint hda hds hdisj

lemma leftExactCountSet_eq_iUnion_patterns (M q : ℕ) :
    leftExactCountSet M q =
      ⋃ K ∈ (Finset.Icc 1 M).powersetCard q, leftPatternSet M K := by
  ext n
  simp only [leftExactCountSet, leftPatternSet, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hn
    exact ⟨leftSquarefreeBinomialIndices M n,
      Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hn⟩, rfl⟩
  · rintro ⟨K, hK, hEq⟩
    rw [hEq]
    exact (Finset.mem_powersetCard.mp hK).2

/-- Complete finite-pattern densities imply densities for every fixed
left-count fiber, by a literal finite disjoint union over patterns. -/
theorem leftExactCountSet_hasDensity_of_finite_patterns
    (hPatterns : FiniteLeftPatternsHaveDensity) (M q : ℕ) :
    ∃ d : ℝ, (leftExactCountSet M q).HasDensity d := by
  classical
  let patterns := (Finset.Icc 1 M).powersetCard q
  have hexists : ∀ K ∈ patterns, ∃ d : ℝ, (leftPatternSet M K).HasDensity d := by
    intro K hK
    exact hPatterns M K (Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hK).1)
  let density (K : Finset ℕ) : ℝ :=
    if hK : K ∈ patterns then Classical.choose (hexists K hK) else 0
  have hdensity : ∀ K ∈ patterns, (leftPatternSet M K).HasDensity (density K) := by
    intro K hK
    simp only [density, dif_pos hK]
    exact Classical.choose_spec (hexists K hK)
  refine ⟨∑ K ∈ patterns, density K, ?_⟩
  rw [leftExactCountSet_eq_iUnion_patterns]
  apply hasDensity_iUnion_finset_of_pairwise_disjoint patterns
  · exact hdensity
  · intro K hK L hL hKL
    rw [Set.disjoint_left]
    intro n hnK hnL
    exact hKL (hnK.symm.trans hnL)

/-- Finite left-pattern densities give a density for every doubled left
count, including the empty odd fibers. -/
theorem doubledLeftExactCountSet_hasDensity_of_finite_patterns
    (hPatterns : FiniteLeftPatternsHaveDensity) (M j : ℕ) :
    ∃ d : ℝ, (doubledLeftExactCountSet M j).HasDensity d := by
  obtain ⟨q, hj | hj⟩ := Nat.even_or_odd' j
  · subst j
    obtain ⟨d, hd⟩ := leftExactCountSet_hasDensity_of_finite_patterns hPatterns M q
    refine ⟨d, ?_⟩
    convert hd using 1
    ext n
    simp only [doubledLeftExactCountSet, leftExactCountSet, Set.mem_ofPred_eq]
    omega
  · subst j
    refine ⟨0, ?_⟩
    have hempty : doubledLeftExactCountSet M (2 * q + 1) = ∅ := by
      ext n
      simp only [doubledLeftExactCountSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      constructor
      · intro h
        have hmod := congrArg (fun x : ℕ ↦ x % 2) h
        norm_num at hmod
      · exact False.elim
    rw [hempty]
    simp [Set.HasDensity, Set.partialDensity]

/-- The elementary finite-pattern theorem supplies every finite two-sided
edge-cutoff density.  The only discrepancy occurs in the finite initial
interval `n ≤ 2 * M`. -/
theorem cutoffExactCountSet_hasDensity_of_finite_patterns
    (hPatterns : FiniteLeftPatternsHaveDensity) (M j : ℕ) :
    ∃ d : ℝ, (cutoffExactCountSet M j).HasDensity d := by
  apply exists_hasDensity_of_symmDiff_subset_density_zero
    (cutoffExactCountSet_symmDiff_doubledLeft_subset M j)
  · exact doubledLeftExactCountSet_hasDensity_of_finite_patterns hPatterns M j
  · exact Iic_hasDensity_zero (2 * M)

/-- After the elementary fixed-index sieve proved above, the only remaining
input for existence of all exact row-count densities is the uniform middle
tail. -/
theorem exactCountSet_hasDensity_of_middleTail
    (hTail : MiddleTailVanishes) (j : ℕ) :
    ∃ d : ℝ, (exactCountSet j).HasDensity d := by
  apply exactCountSet_hasDensity_of_cutoff_and_tail
  · exact cutoffExactCountSet_hasDensity_of_finite_patterns
      finiteLeftPatternsHaveDensity
  · exact hTail

/-- Passing to a complement subtracts a density from one. -/
lemma hasDensity_compl {S : Set ℕ} {d : ℝ} (hS : S.HasDensity d) :
    Sᶜ.HasDensity (1 - d) := by
  classical
  rw [Set.HasDensity] at hS ⊢
  apply (tendsto_const_nhds.sub hS).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  have hdisj : Disjoint (Sᶜ ∩ Set.Iio n) (S ∩ Set.Iio n) := by
    rw [Set.disjoint_left]
    aesop
  have hunion : (Sᶜ ∩ Set.Iio n) ∪ (S ∩ Set.Iio n) = Set.Iio n := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_Iio]
    tauto
  have hcard :
      (Sᶜ ∩ Set.Iio n).ncard + (S ∩ Set.Iio n).ncard = n := by
    rw [← Set.ncard_union_eq hdisj, hunion]
    simp
  rw [Set.ncard_Iio_nat]
  have hcardR :
      ((Sᶜ ∩ Set.Iio n).ncard : ℝ) + ((S ∩ Set.Iio n).ncard : ℝ) = n := by
    exact_mod_cast hcard
  have hnR : (n : ℝ) ≠ 0 := by positivity
  field_simp
  linarith

/-- Natural density is monotone whenever the two densities exist. -/
lemma hasDensity_mono {S T : Set ℕ} {s t : ℝ} (hST : S ⊆ T)
    (hS : S.HasDensity s) (hT : T.HasDensity t) : s ≤ t := by
  rw [Set.HasDensity] at hS hT
  apply le_of_tendsto_of_tendsto hS hT
  exact Filter.Eventually.of_forall fun n ↦ by
    change S.partialDensity (b := n) ≤ T.partialDensity (b := n)
    rw [partialDensity_eq_ncard, partialDensity_eq_ncard]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Set.ncard_le_ncard
        (Set.inter_subset_inter_left (Set.Iio n) hST)
    · positivity

/-! ## Partition by the exact count -/

@[simp] lemma belowCountSet_zero : belowCountSet 0 = ∅ := by
  ext n
  simp [belowCountSet]

lemma belowCountSet_succ (r : ℕ) :
    belowCountSet (r + 1) = belowCountSet r ∪ exactCountSet r := by
  ext n
  simp only [belowCountSet, exactCountSet, Set.mem_ofPred_eq, Set.mem_union]
  omega

lemma belowCountSet_disjoint_exactCountSet (r : ℕ) :
    Disjoint (belowCountSet r) (exactCountSet r) := by
  rw [Set.disjoint_left]
  intro n hn hne
  exact (Nat.ne_of_lt hn) hne

lemma atLeastCountSet_eq_compl (r : ℕ) :
    atLeastCountSet r = (belowCountSet r)ᶜ := by
  ext n
  simp [atLeastCountSet, belowCountSet]

/-- If every exact-count fiber has a density, then every lower tail has a
density. -/
lemma belowCountSet_hasDensity
    (hExact : ∀ j : ℕ, ∃ d : ℝ, (exactCountSet j).HasDensity d) :
    ∀ r : ℕ, ∃ d : ℝ, (belowCountSet r).HasDensity d := by
  intro r
  induction r with
  | zero =>
      refine ⟨0, ?_⟩
      simp [Set.HasDensity, Set.partialDensity]
  | succ r ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := hExact r
      refine ⟨a + b, ?_⟩
      rw [show r + 1 = Nat.succ r by omega, belowCountSet_succ]
      exact hasDensity_union_of_disjoint ha hb
        (belowCountSet_disjoint_exactCountSet r)

/-- Beyond the finite initial interval, making the first `r` coefficients
squarefree supplies at least `r` squarefree interior coefficients, using
binomial symmetry. -/
lemma fullLeftPattern_subset_atLeast_union_initial (r : ℕ) :
    leftPatternSet r (Finset.Icc 1 r) ⊆
      atLeastCountSet r ∪ Set.Iic (2 * r) := by
  intro n hn
  by_cases hnr : 2 * r < n
  · apply Or.inl
    have hleft : leftSquarefreeBinomialIndices r n = Finset.Icc 1 r := hn
    have hleftCard : (leftSquarefreeBinomialIndices r n).card = r := by
      rw [hleft]
      simp
    have hedgeCard := edgeSquarefreeBinomialIndices_card hnr
    have hedgeSubset : edgeSquarefreeBinomialIndices r n ⊆
        squarefreeBinomialIndices n := Finset.filter_subset _ _
    have hcard := Finset.card_le_card hedgeSubset
    change r ≤ squarefreeBinomialCount n
    rw [squarefreeBinomialCount]
    omega
  · apply Or.inr
    change n ≤ 2 * r
    omega

/-- The established uniform middle-tail theorem is enough by itself for the
full resolution: fixed-pattern density gives existence of exact fibers, and
the positive progression above gives strict positivity of every upper tail. -/
theorem erdos378_of_middleTail (hTail : MiddleTailVanishes) :
    ∀ r : ℕ, ∃ d : ℝ, 0 < d ∧ (atLeastCountSet r).HasDensity d := by
  intro r
  have hExact : ∀ j : ℕ, ∃ d : ℝ, (exactCountSet j).HasDensity d :=
    exactCountSet_hasDensity_of_middleTail hTail
  obtain ⟨belowDensity, hBelow⟩ := belowCountSet_hasDensity hExact r
  have hAtLeast : (atLeastCountSet r).HasDensity (1 - belowDensity) := by
    rw [atLeastCountSet_eq_compl]
    exact hasDensity_compl hBelow
  obtain ⟨patternDensity, hPatternPos, hPattern⟩ :=
    fullLeftPattern_hasPositiveDensity r
  have hInitial := Iic_hasDensity_zero (2 * r)
  have hle : patternDensity ≤ 1 - belowDensity := by
    rw [Set.HasDensity] at hPattern hAtLeast hInitial
    have hEventually : ∀ᶠ N : ℕ in atTop,
        (leftPatternSet r (Finset.Icc 1 r)).partialDensity (b := N) ≤
          (atLeastCountSet r).partialDensity (b := N) +
            (Set.Iic (2 * r)).partialDensity (b := N) := by
      filter_upwards with N
      have hmono :
          (leftPatternSet r (Finset.Icc 1 r)).partialDensity (b := N) ≤
            (atLeastCountSet r ∪ Set.Iic (2 * r)).partialDensity (b := N) := by
        rw [partialDensity_eq_ncard, partialDensity_eq_ncard]
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Set.ncard_le_ncard
            (Set.inter_subset_inter_left (Set.Iio N)
              (fullLeftPattern_subset_atLeast_union_initial r))
        · positivity
      exact hmono.trans (partialDensity_union_le _ _ N)
    simpa using
      (le_of_tendsto_of_tendsto hPattern (hAtLeast.add hInitial) hEventually)
  exact ⟨1 - belowDensity, hPatternPos.trans_le hle, hAtLeast⟩

/-! ## Resolution from Granville--Ramaré's distribution theorem -/

/-- The exact density-theoretic deduction resolving Erdős Problem 378 from
Granville and Ramaré's Theorem 5. -/
theorem erdos378_of_granville_ramare
    (hGR : GranvilleRamareDistribution) :
    ∀ r : ℕ, ∃ d : ℝ, 0 < d ∧ (atLeastCountSet r).HasDensity d := by
  intro r
  obtain ⟨belowDensity, hBelow⟩ := belowCountSet_hasDensity hGR.1 r
  have hAtLeast :
      (atLeastCountSet r).HasDensity (1 - belowDensity) := by
    rw [atLeastCountSet_eq_compl]
    exact hasDensity_compl hBelow
  obtain ⟨fiberDensity, hFiberPos, hFiber⟩ :=
    hGR.2 (r + 1) (by omega)
  have hsubset : exactCountSet (2 * (r + 1)) ⊆ atLeastCountSet r := by
    intro n hn
    change squarefreeBinomialCount n = 2 * (r + 1) at hn
    change r ≤ squarefreeBinomialCount n
    omega
  have hle : fiberDensity ≤ 1 - belowDensity :=
    hasDensity_mono hsubset hFiber hAtLeast
  exact ⟨1 - belowDensity, hFiberPos.trans_le hle, hAtLeast⟩

#print axioms erdos378_of_granville_ramare

/-- Complete resolution of Erdős Problem 378: for every `r ≥ 0`, the rows
with at least `r` squarefree interior binomial coefficients have an existing,
strictly positive natural density. -/
theorem erdos378 :
    ∀ r : ℕ, ∃ d : ℝ, 0 < d ∧ (atLeastCountSet r).HasDensity d := by
  apply erdos378_of_middleTail
  apply middleTailVanishes_of_pairScarcity
  apply middlePairScarcity_of_highIndexExcluded
  exact highIndexExcluded

#print axioms erdos378

end Erdos378
