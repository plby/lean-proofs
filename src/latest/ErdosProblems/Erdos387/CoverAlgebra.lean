/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Algebraic interface for the BNPZ covering construction

The analytic part of Bui--Naprienko--Pratt--Zaharescu constructs integers
`g i` dividing the consecutive factors `n - i`, with product `k!`.  This
file records, without any analytic assumptions, the exact consequence needed
for the binomial coefficient: after dividing the `i`-th factor by `g i`, the
remaining factors multiply to `n.choose k`.
-/

namespace Erdos387

open scoped Function

/-- The purely finite input supplied by a weighted covering: the assigned
moduli are positive and pairwise coprime, and their product is `k!`.  In the
BNPZ construction the moduli are products of disjoint sets of prime powers. -/
structure PairwiseCover (k : ℕ) where
  g : ℕ → ℕ
  positive : ∀ i < k, 0 < g i
  pairwise : Set.Pairwise (↑(Finset.range k) : Set ℕ) (Nat.Coprime on g)
  product_eq_factorial : ∏ i ∈ Finset.range k, g i = k.factorial

/-- Data extracted from the weighted covering congruences: every `g i`
divides the corresponding falling-factorial term, and all the `g i` together
account for the denominator `k!`. -/
structure CoverFactorization (n k : ℕ) where
  g : ℕ → ℕ
  divides_term : ∀ i < k, g i ∣ n - i
  product_eq_factorial : ∏ i ∈ Finset.range k, g i = k.factorial

/-- A pairwise-coprime cover can be realized by congruences, and the solution
can be lifted beyond any prescribed lower bound by adding a multiple of
`k!`.  This is the exact CRT step in the BNPZ construction. -/
theorem PairwiseCover.exists_factorization_ge (C : PairwiseCover k) (L : ℕ) :
    ∃ n : ℕ, L ≤ n ∧ Nonempty (CoverFactorization n k) := by
  let r := Nat.chineseRemainderOfFinset id C.g (Finset.range k)
    (fun i hi => (C.positive i (Finset.mem_range.mp hi)).ne') C.pairwise
  let M := max L k
  let n := (r : ℕ) + M * k.factorial
  have hMprod : M ≤ M * k.factorial :=
    Nat.le_mul_of_pos_right M (Nat.factorial_pos k)
  have hLn : L ≤ n := by
    have hLM : L ≤ M := le_max_left L k
    dsimp [n]
    omega
  have hkn : k ≤ n := by
    have hkM : k ≤ M := le_max_right L k
    dsimp [n]
    omega
  have hdiv : ∀ i < k, C.g i ∣ n - i := by
    intro i hi
    have hri : (r : ℕ) ≡ i [MOD C.g i] := r.prop i (Finset.mem_range.mpr hi)
    have hgid : C.g i ∣ k.factorial := by
      rw [← C.product_eq_factorial]
      exact Finset.dvd_prod_of_mem C.g (Finset.mem_range.mpr hi)
    have hzero : M * k.factorial ≡ 0 [MOD C.g i] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hgid M)
    have hnmod : n ≡ i [MOD C.g i] := by
      dsimp [n]
      simpa using hri.add hzero
    have hin : i ≤ n := le_trans (Nat.le_of_lt hi) hkn
    exact (Nat.modEq_iff_dvd' hin).mp hnmod.symm
  exact ⟨n, hLn, ⟨CoverFactorization.mk C.g hdiv C.product_eq_factorial⟩⟩

/-- The elementary identity at the interface between the covering theorem
and the divisor analysis in BNPZ. -/
theorem choose_eq_prod_coverQuotients (D : CoverFactorization n k) :
    n.choose k = ∏ i ∈ Finset.range k, (n - i) / D.g i := by
  have hprod :
      (∏ i ∈ Finset.range k, (n - i) / D.g i) *
          (∏ i ∈ Finset.range k, D.g i) = n.descFactorial k := by
    rw [← Finset.prod_mul_distrib]
    calc
      ∏ i ∈ Finset.range k, (n - i) / D.g i * D.g i =
          ∏ i ∈ Finset.range k, (n - i) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact Nat.div_mul_cancel (D.divides_term i (Finset.mem_range.mp hi))
      _ = n.descFactorial k := (Nat.descFactorial_eq_prod_range n k).symm
  rw [D.product_eq_factorial, Nat.descFactorial_eq_factorial_mul_choose,
    mul_comm k.factorial] at hprod
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k) hprod.symm

/-- A quotient left after removing a covering factor still divides the
corresponding falling-factorial term. -/
theorem coverQuotient_dvd_term (D : CoverFactorization n k) {i : ℕ} (hi : i < k) :
    (n - i) / D.g i ∣ n - i := by
  exact Nat.div_dvd_of_dvd (D.divides_term i hi)

/-- If the covering factor at every index is at least `B`, every residual
factor is at most `n / B`.  This is the elementary size estimate used before
the much subtler analysis of products of residual factors. -/
theorem coverQuotient_le_div (D : CoverFactorization n k) {B i : ℕ}
    (hBpos : 0 < B) (hB : B ≤ D.g i) (_hi : i < k) :
    (n - i) / D.g i ≤ n / B := by
  exact Nat.div_le_div (Nat.sub_le n i) hB hBpos.ne'

/-- The factorization identity in divisibility form. -/
theorem coverQuotient_dvd_choose (D : CoverFactorization n k) {i : ℕ} (hi : i < k) :
    (n - i) / D.g i ∣ n.choose k := by
  rw [choose_eq_prod_coverQuotients D]
  exact Finset.dvd_prod_of_mem (fun j => (n - j) / D.g j) (Finset.mem_range.mpr hi)

/-- Every divisor of a finite product can be split into a product of divisors
of the individual factors.  No coprimality is needed for existence (without
coprimality the splitting need not be unique). -/
theorem exists_dvd_factors_of_dvd_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) {d : ℕ} (hd : d ∣ ∏ i ∈ s, f i) :
    ∃ e : ι → ℕ, (∀ i ∈ s, e i ∣ f i) ∧ d = ∏ i ∈ s, e i := by
  induction s using Finset.induction_on generalizing d with
  | empty =>
      refine ⟨fun _ => 1, by simp, ?_⟩
      simpa using Nat.dvd_one.mp hd
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha] at hd
      obtain ⟨da, ds, hda, hds, hsplit⟩ := exists_dvd_and_dvd_of_dvd_mul hd
      obtain ⟨es, hes, hdseq⟩ := ih hds
      let e : ι → ℕ := fun i => if i = a then da else es i
      refine ⟨e, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | his
        · simpa [e] using hda
        · have hia : i ≠ a := by
            intro hia
            exact ha (hia ▸ his)
          simpa [e, hia] using hes i his
      · rw [Finset.prod_insert ha]
        have hea : e a = da := by simp [e]
        have heprod : ∏ i ∈ s, e i = ds := by
          calc
            ∏ i ∈ s, e i = ∏ i ∈ s, es i := by
              apply Finset.prod_congr rfl
              intro i hi
              have hia : i ≠ a := by
                intro hia
                exact ha (hia ▸ hi)
              simp [e, hia]
            _ = ds := hdseq.symm
        rw [hea, heprod]
        exact hsplit

/-- If the ambient factors are pairwise coprime, a divisor of each factor is
uniquely determined by the product of all the chosen divisors.  This is the
finite unique-factorization statement used to count divisors of a covered
binomial coefficient by counting tuples. -/
theorem divisorFactors_unique_of_pairwise_coprime
    {ι : Type*} [DecidableEq ι] (s : Finset ι) {q e e' : ι → ℕ}
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (q i) (q j))
    (he : ∀ i ∈ s, e i ∣ q i) (he' : ∀ i ∈ s, e' i ∣ q i)
    (hprod : ∏ i ∈ s, e i = ∏ i ∈ s, e' i) :
    ∀ i ∈ s, e i = e' i := by
  intro i hi
  have hdvd : e i ∣ e' i := by
    have hdvdprod : e i ∣ ∏ j ∈ s, e' j := by
      rw [← hprod]
      exact Finset.dvd_prod_of_mem e hi
    rw [← Finset.mul_prod_erase s e' hi] at hdvdprod
    have hcop : Nat.Coprime (e i) (∏ j ∈ s.erase i, e' j) := by
      apply Nat.Coprime.prod_right
      intro j hj
      have hjs : j ∈ s := Finset.mem_of_mem_erase hj
      have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      exact Nat.Coprime.of_dvd_right (he' j hjs)
        (Nat.Coprime.of_dvd_left (he i hi) (hpair i hi j hjs hij))
    exact hcop.dvd_of_dvd_mul_right hdvdprod
  have hdvd' : e' i ∣ e i := by
    have hdvdprod : e' i ∣ ∏ j ∈ s, e j := by
      rw [hprod]
      exact Finset.dvd_prod_of_mem e' hi
    rw [← Finset.mul_prod_erase s e hi] at hdvdprod
    have hcop : Nat.Coprime (e' i) (∏ j ∈ s.erase i, e j) := by
      apply Nat.Coprime.prod_right
      intro j hj
      have hjs : j ∈ s := Finset.mem_of_mem_erase hj
      have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      exact Nat.Coprime.of_dvd_right (he j hjs)
        (Nat.Coprime.of_dvd_left (he' i hi) (hpair i hi j hjs hij))
    exact hcop.dvd_of_dvd_mul_right hdvdprod
  exact Nat.dvd_antisymm hdvd hdvd'

/-- Consequently, every divisor of `n.choose k` is a product of one divisor
from each residual factor created by the cover.  The analytic heart of BNPZ
is precisely the proof that no such product can lie in the forbidden interval. -/
theorem exists_coverDivisorFactors (D : CoverFactorization n k) {d : ℕ}
    (hd : d ∣ n.choose k) :
    ∃ e : ℕ → ℕ,
      (∀ i < k, e i ∣ (n - i) / D.g i) ∧
      d = ∏ i ∈ Finset.range k, e i := by
  rw [choose_eq_prod_coverQuotients D] at hd
  obtain ⟨e, he, hde⟩ :=
    exists_dvd_factors_of_dvd_prod (Finset.range k) (fun i => (n - i) / D.g i) hd
  exact ⟨e, fun i hi => he i (Finset.mem_range.mpr hi), hde⟩

/-- Residual factors supported on distinct shifts are coprime as soon as all
their prime factors are at least `k`.  Indeed, a common prime would divide the
difference of two distinct shifts, a positive integer strictly smaller than
`k`.  BNPZ arrange the stronger lower bound `p > 2k`. -/
theorem coverQuotients_pairwise_coprime (D : CoverFactorization n k) (hkn : k ≤ n)
    (hrough : ∀ i < k, ∀ p : ℕ, p.Prime → p ∣ (n - i) / D.g i → k ≤ p) :
    ∀ i < k, ∀ j < k, i ≠ j →
      Nat.Coprime ((n - i) / D.g i) ((n - j) / D.g j) := by
  have ordered : ∀ i < k, ∀ j < k, i < j →
      Nat.Coprime ((n - i) / D.g i) ((n - j) / D.g j) := by
    intro i hi j hj hij
    apply Nat.coprime_of_dvd
    intro p hp hpqi hpqj
    have hpti : p ∣ n - i := hpqi.trans (coverQuotient_dvd_term D hi)
    have hptj : p ∣ n - j := hpqj.trans (coverQuotient_dvd_term D hj)
    have hpdiff : p ∣ j - i := by
      have h := Nat.dvd_sub hpti hptj
      convert h using 1
      omega
    have hple : p ≤ j - i := Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hpdiff
    have hpge : k ≤ p := hrough i hi p hp hpqi
    omega
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij' | hji
  · exact ordered i hi j hj hij'
  · exact (ordered j hj i hi hji).symm

/-- A finite tuple choosing one divisor of every residual factor.  Its value
is the product of the choices. -/
structure CoverDivisorTuple (D : CoverFactorization n k) where
  factor : Fin k → ℕ
  divides : ∀ i, factor i ∣ (n - (i : ℕ)) / D.g i

namespace CoverDivisorTuple

/-- The divisor represented by a residual-divisor tuple. -/
def value {D : CoverFactorization n k} (E : CoverDivisorTuple D) : ℕ :=
  ∏ i, E.factor i

/-- Every divisor of the covered binomial coefficient has a residual-divisor
tuple representation. -/
theorem exists_value_eq {D : CoverFactorization n k} {d : ℕ}
    (hd : d ∣ n.choose k) :
    ∃ E : CoverDivisorTuple D, E.value = d := by
  obtain ⟨e, he, hde⟩ := exists_coverDivisorFactors D hd
  let E : CoverDivisorTuple D :=
    { factor := fun i => e i
      divides := fun i => he i i.isLt }
  refine ⟨E, ?_⟩
  rw [value, Fin.prod_univ_eq_prod_range]
  exact hde.symm

/-- Pairwise coprimality of the residual factors makes the tuple
representation injective. -/
theorem value_injective {D : CoverFactorization n k}
    (hpair : ∀ i < k, ∀ j < k, i ≠ j →
      Nat.Coprime ((n - i) / D.g i) ((n - j) / D.g j)) :
    Function.Injective (value : CoverDivisorTuple D → ℕ) := by
  intro E E' hvalue
  have hfactor : E.factor = E'.factor := by
    funext i
    apply divisorFactors_unique_of_pairwise_coprime
      (s := Finset.univ)
      (q := fun j : Fin k => (n - (j : ℕ)) / D.g j)
      (e := E.factor) (e' := E'.factor)
    · intro a _ b _ hab
      apply hpair a a.isLt b b.isLt
      intro habNat
      exact hab (Fin.ext habNat)
    · intro a _
      exact E.divides a
    · intro a _
      exact E'.divides a
    · exact hvalue
    · exact Finset.mem_univ i
  cases E with
  | mk factor divides =>
      cases E' with
      | mk factor' divides' =>
          dsimp at hfactor
          subst factor'
          rfl

end CoverDivisorTuple

end Erdos387
