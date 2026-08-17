/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# The common-nearby-multiple argument for Erdős Problem 297

This file isolates the elementary finite argument at the end of the
minor-arc analysis of Liu--Sawhney.  For each relevant prime power `q`, the
analytic and sieve parts of the proof construct an integer `x q` in one
fixed half-open interval and a set `aux q` containing at least ninety percent
of a common set `primes` of auxiliary primes.  The product of `aux q` divides
`x q`.  Two such auxiliary sets have an intersection containing at least
eighty percent of `primes`; once the product of every such large subset is
greater than `N`, divisibility and the interval-width bound force all the
integers `x q` to be equal.

The theorem `common_nearby_multiple` records exactly this gluing step.  It is
stated for arbitrary finite index and auxiliary sets: primality is used by
the preceding sieve argument to establish the hypotheses, but is not needed
again here.
-/

open Finset

namespace Erdos297.NearbyMultiple

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Membership in the half-open integer interval `(lower, upper]`.  This is
the integer version of the interval `I_h = (h-K/2,h+K/2]` in the Fourier
argument. -/
def InHalfOpenInterval (lower upper x : ℤ) : Prop :=
  lower < x ∧ x ≤ upper

/-- Two integers in an interval of width at most `N` are equal if a natural
number strictly larger than `N` divides their difference. -/
lemma eq_of_large_dvd_sub_of_mem_halfOpen
    {lower upper x y : ℤ} {N d : ℕ}
    (hx : InHalfOpenInterval lower upper x)
    (hy : InHalfOpenInterval lower upper y)
    (hwidth : upper - lower ≤ (N : ℤ))
    (hlarge : N < d)
    (hdvd : (d : ℤ) ∣ x - y) :
    x = y := by
  by_contra hxy
  have hdiff_pos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hdiff_large : (d : ℤ) ≤ |x - y| :=
    Int.le_of_dvd hdiff_pos ((dvd_abs (d : ℤ) (x - y)).mpr hdvd)
  unfold InHalfOpenInterval at hx hy
  rcases hx with ⟨hlx, hxu⟩
  rcases hy with ⟨hly, hyu⟩
  rcases abs_cases (x - y) with hnonneg | hnonpos <;> omega

/-- Inclusion--exclusion turns two ninety-percent subsets of one finite set
into an eighty-percent intersection.  The integral inequalities avoid any
rounding convention for the percentages. -/
lemma four_mul_card_le_five_mul_card_inter
    {primes left right : Finset ℕ}
    (hleft : left ⊆ primes)
    (hright : right ⊆ primes)
    (hleft_dense : 9 * primes.card ≤ 10 * left.card)
    (hright_dense : 9 * primes.card ≤ 10 * right.card) :
    4 * primes.card ≤ 5 * (left ∩ right).card := by
  have hunion : (left ∪ right).card ≤ primes.card :=
    card_le_card (union_subset hleft hright)
  have hinclusion_exclusion := card_union_add_card_inter left right
  omega

/-- If each modulus in a finite family divides an integer, then the natural
LCM of the family (viewed in `ℤ`) divides that integer. -/
lemma int_coe_lcm_dvd_of_forall
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (modulus : ι → ℕ) (z : ℤ)
    (hdiv : ∀ i ∈ indices, (modulus i : ℤ) ∣ z) :
    ((indices.lcm modulus : ℕ) : ℤ) ∣ z := by
  induction indices using Finset.induction with
  | empty => simp
  | @insert i indices hi ih =>
      rw [Finset.lcm_insert, lcm_eq_nat_lcm]
      have hiDiv : (modulus i : ℤ) ∣ z :=
        hdiv i (mem_insert_self i indices)
      have hrestDiv : ((indices.lcm modulus : ℕ) : ℤ) ∣ z := by
        apply ih
        intro j hj
        exact hdiv j (mem_insert_of_mem hj)
      simpa [Int.lcm_def] using Int.coe_lcm_dvd hiDiv hrestDiv

/-- The common-nearby-multiple lemma.

`chosen q` is the integer `x_q` selected for the index `q`.  `aux q` is its
set of auxiliary primes.  The two density hypotheses are written without
fractions: `9 * |primes| ≤ 10 * |aux q|` means that `aux q` contains at
least ninety percent of `primes`.  `hlargeProduct` is precisely the PNT input
used in the paper: every subset containing at least eighty percent of the
auxiliary primes has product greater than `N`.

The conclusion includes both formulations used in the source: every
individual modulus divides the common integer, and therefore their LCM does.
The explicit interval witness handles the vacuous case `indices = ∅`.
-/
theorem common_nearby_multiple
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (modulus : ι → ℕ)
    (lower upper : ℤ) (N : ℕ)
    (chosen : ι → ℤ)
    (primes : Finset ℕ) (aux : ι → Finset ℕ)
    (hintervalExists : ∃ z : ℤ, InHalfOpenInterval lower upper z)
    (hwidth : upper - lower ≤ (N : ℤ))
    (hchosen : ∀ q ∈ indices, InHalfOpenInterval lower upper (chosen q))
    (hmodulus : ∀ q ∈ indices, (modulus q : ℤ) ∣ chosen q)
    (hauxSubset : ∀ q ∈ indices, aux q ⊆ primes)
    (hauxDense : ∀ q ∈ indices,
      9 * primes.card ≤ 10 * (aux q).card)
    (hauxProductDvd : ∀ q ∈ indices,
      (((aux q).prod id : ℕ) : ℤ) ∣ chosen q)
    (hlargeProduct : ∀ block ⊆ primes,
      4 * primes.card ≤ 5 * block.card → N < block.prod id) :
    ∃ z : ℤ,
      InHalfOpenInterval lower upper z ∧
      (∀ q ∈ indices, (modulus q : ℤ) ∣ z) ∧
      ((indices.lcm modulus : ℕ) : ℤ) ∣ z := by
  by_cases hempty : indices = ∅
  · obtain ⟨z, hz⟩ := hintervalExists
    refine ⟨z, hz, ?_, ?_⟩
    · simp [hempty]
    · simp [hempty]
  · obtain ⟨q₀, hq₀⟩ := nonempty_iff_ne_empty.mpr hempty
    have hchosen_eq : ∀ q ∈ indices, chosen q = chosen q₀ := by
      intro q hq
      let common : Finset ℕ := aux q ∩ aux q₀
      have hcommonSubset : common ⊆ primes := by
        intro p hp
        exact hauxSubset q hq (inter_subset_left hp)
      have hcommonDense : 4 * primes.card ≤ 5 * common.card := by
        exact four_mul_card_le_five_mul_card_inter
          (hauxSubset q hq) (hauxSubset q₀ hq₀)
          (hauxDense q hq) (hauxDense q₀ hq₀)
      have hcommonLarge : N < common.prod id :=
        hlargeProduct common hcommonSubset hcommonDense
      have hcommonDvdQ : ((common.prod id : ℕ) : ℤ) ∣ chosen q := by
        have hnat : common.prod id ∣ (aux q).prod id :=
          Finset.prod_dvd_prod_of_subset common (aux q) id inter_subset_left
        exact (Int.natCast_dvd_natCast.mpr hnat).trans (hauxProductDvd q hq)
      have hcommonDvdQ₀ : ((common.prod id : ℕ) : ℤ) ∣ chosen q₀ := by
        have hnat : common.prod id ∣ (aux q₀).prod id :=
          Finset.prod_dvd_prod_of_subset common (aux q₀) id inter_subset_right
        exact (Int.natCast_dvd_natCast.mpr hnat).trans
          (hauxProductDvd q₀ hq₀)
      exact eq_of_large_dvd_sub_of_mem_halfOpen
        (hchosen q hq) (hchosen q₀ hq₀) hwidth hcommonLarge
        (dvd_sub hcommonDvdQ hcommonDvdQ₀)
    have hallDiv : ∀ q ∈ indices, (modulus q : ℤ) ∣ chosen q₀ := by
      intro q hq
      rw [← hchosen_eq q hq]
      exact hmodulus q hq
    refine ⟨chosen q₀, hchosen q₀ hq₀, hallDiv, ?_⟩
    exact int_coe_lcm_dvd_of_forall indices modulus (chosen q₀) hallDiv

end

end Erdos297.NearbyMultiple

#print axioms Erdos297.NearbyMultiple.common_nearby_multiple
