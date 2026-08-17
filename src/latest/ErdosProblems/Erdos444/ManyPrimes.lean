import ErdosProblems.Erdos285.RoughCounts
import ErdosProblems.Erdos851.BetaSieveFailureCombinatorics

/-!
# Counting integers with many prescribed prime divisors

This is the finite union-bound form of the large-deviation estimate needed
for Erdős Problem 444.  It deliberately uses only elementary symmetric sums:
an integer divisible by at least `r` primes from `P` is covered by the
multiples of the product of one `r`-element sublist of `P`.
-/

open scoped BigOperators

namespace Erdos444

open Erdos285.RoughCounts
open List

/-- The number of primes from a finite set which divide `n`. -/
def primeDivisorCount (P : Finset ℕ) (n : ℕ) : ℕ :=
  (P.filter fun p ↦ p ∣ n).card

/-- Positive integers at most `U` having at least `r` prime divisors from
`P`. -/
def manyPrimeDivisorsUpTo (P : Finset ℕ) (r U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun n ↦ r ≤ primeDivisorCount P n

@[simp] theorem mem_manyPrimeDivisorsUpTo {P : Finset ℕ} {r U n : ℕ} :
    n ∈ manyPrimeDivisorsUpTo P r U ↔
      1 ≤ n ∧ n ≤ U ∧ r ≤ primeDivisorCount P n := by
  simp [manyPrimeDivisorsUpTo, and_assoc]

private theorem chosenPrimeList_data
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {r n : ℕ} (hr : r ≤ primeDivisorCount P n) (hn : n ≠ 0) :
    let l := (P.toList.filter fun p ↦ p ∣ n).take r
    l ∈ P.toList.sublistsLen r ∧ l.prod ∣ n := by
  let l := (P.toList.filter fun p ↦ p ∣ n).take r
  have hlenFilter : (P.toList.filter fun p ↦ p ∣ n).length =
      primeDivisorCount P n := by
    rw [← List.toFinset_card_of_nodup
      (P.nodup_toList.filter (fun p ↦ p ∣ n))]
    simp [primeDivisorCount]
  have hlen : l.length = r := by
    simp [l, List.length_take, hlenFilter, Nat.min_eq_left hr]
  have hsub : l.Sublist P.toList :=
    (List.take_sublist r _).trans (List.filter_sublist)
  have hmem : l ∈ P.toList.sublistsLen r :=
    List.mem_sublistsLen.mpr ⟨hsub, hlen⟩
  have hnodup : l.Nodup := P.nodup_toList.sublist hsub
  have hsubset : l.toFinset ⊆ n.primeFactors := by
    intro p hp
    have hpl : p ∈ l := List.mem_toFinset.mp hp
    have hpfilter : p ∈ P.toList.filter (fun p ↦ p ∣ n) :=
      List.mem_of_mem_take hpl
    have hpP : p ∈ P := by
      exact Finset.mem_toList.mp (List.mem_filter.mp hpfilter).1
    have hpdvd : p ∣ n := of_decide_eq_true (List.mem_filter.mp hpfilter).2
    exact Nat.mem_primeFactors.mpr ⟨hP p hpP, hpdvd, hn⟩
  have hprodFin : l.toFinset.prod id ∣ n :=
    (Finset.prod_dvd_prod_of_subset l.toFinset n.primeFactors id hsubset).trans
      (Nat.prod_primeFactors_dvd n)
  have hprodList : l.prod = l.toFinset.prod id := by
    simpa using (List.prod_toFinset (fun x : ℕ ↦ x) hnodup).symm
  exact ⟨hmem, hprodList ▸ hprodFin⟩

private theorem manyPrimeDivisorsUpTo_subset_cover
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (r U : ℕ) :
    manyPrimeDivisorsUpTo P r U ⊆
      (P.toList.sublistsLen r).toFinset.biUnion
        (fun l ↦ multiplesUpTo U l.prod) := by
  intro n hn
  have hnData := mem_manyPrimeDivisorsUpTo.mp hn
  obtain ⟨hl, hldvd⟩ := chosenPrimeList_data hP hnData.2.2
    (Nat.ne_of_gt hnData.1)
  rw [Finset.mem_biUnion]
  refine ⟨_, List.mem_toFinset.mpr hl, ?_⟩
  exact mem_multiplesUpTo.mpr ⟨hnData.1, hnData.2.1, hldvd⟩

private theorem card_multiplesUpTo (U q : ℕ) :
    (multiplesUpTo U q).card = U / q := by
  unfold multiplesUpTo
  have heq : (Finset.Icc 1 U).filter (fun n ↦ q ∣ n) =
      (Finset.Ioc 0 U).filter (fun n ↦ q ∣ n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hn1, hnU⟩, hdiv⟩
      exact ⟨⟨by omega, hnU⟩, hdiv⟩
    · rintro ⟨⟨hn0, hnU⟩, hdiv⟩
      exact ⟨⟨by omega, hnU⟩, hdiv⟩
  rw [heq, Nat.Ioc_filter_dvd_card_eq_div]

private theorem list_prod_reciprocal {l : List ℕ}
    (hlpos : ∀ p ∈ l, 0 < p) :
    (l.map fun p : ℕ ↦ (1 : ℝ) / (p : ℝ)).prod = (l.prod : ℝ)⁻¹ := by
  induction l with
  | nil => simp
  | cons p l ih =>
      have hp : 0 < p := hlpos p (by simp)
      have htail : ∀ q ∈ l, 0 < q := by
        intro q hq
        exact hlpos q (by simp [hq])
      rw [List.map_cons, List.prod_cons, ih htail, List.prod_cons,
        Nat.cast_mul, mul_inv]
      simp [one_div]

private theorem cast_card_multiplesUpTo_le
    {U : ℕ} {l : List ℕ} (hlpos : ∀ p ∈ l, 0 < p) :
    ((multiplesUpTo U l.prod).card : ℝ) ≤
      (U : ℝ) * (l.map fun p : ℕ ↦ (1 : ℝ) / (p : ℝ)).prod := by
  have hprodpos : 0 < l.prod := List.prod_pos hlpos
  rw [card_multiplesUpTo]
  calc
    ((U / l.prod : ℕ) : ℝ) ≤ (U : ℝ) / l.prod := Nat.cast_div_le
    _ = (U : ℝ) *
        (l.map fun p : ℕ ↦ (1 : ℝ) / (p : ℝ)).prod := by
      rw [list_prod_reciprocal hlpos]
      rfl

/-- Elementary-symmetric large-deviation bound.

The right side is interpreted as zero when the family of `r`-subsets is
empty.  No asymptotic estimate enters this statement. -/
theorem card_manyPrimeDivisorsUpTo_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (r U : ℕ) :
    ((manyPrimeDivisorsUpTo P r U).card : ℝ) ≤
      (U : ℝ) *
        ((∑ p ∈ P, (1 : ℝ) / p) ^ r / (r.factorial : ℝ)) := by
  let C : Finset (List ℕ) := (P.toList.sublistsLen r).toFinset
  have hcover := manyPrimeDivisorsUpTo_subset_cover hP r U
  have hcardNat : (manyPrimeDivisorsUpTo P r U).card ≤
      ∑ l ∈ C, (multiplesUpTo U l.prod).card := by
    exact (Finset.card_le_card hcover).trans
      Finset.card_biUnion_le
  have hcard : ((manyPrimeDivisorsUpTo P r U).card : ℝ) ≤
      ∑ l ∈ C, ((multiplesUpTo U l.prod).card : ℝ) := by
    exact_mod_cast hcardNat
  have hterm : ∀ l ∈ C,
      ((multiplesUpTo U l.prod).card : ℝ) ≤
        (U : ℝ) * (l.map fun p : ℕ ↦ (1 : ℝ) / (p : ℝ)).prod := by
    intro l hl
    apply cast_card_multiplesUpTo_le
    intro p hp
    have hlsub : l.Sublist P.toList :=
      (List.mem_sublistsLen.mp (List.mem_toFinset.mp hl)).1
    have hpP : p ∈ P := Finset.mem_toList.mp (hlsub.mem hp)
    exact (hP p hpP).pos
  calc
    ((manyPrimeDivisorsUpTo P r U).card : ℝ)
        ≤ ∑ l ∈ C, ((multiplesUpTo U l.prod).card : ℝ) := hcard
    _ ≤ ∑ l ∈ C,
          (U : ℝ) * (l.map fun p : ℕ ↦ (1 : ℝ) / (p : ℝ)).prod :=
      Finset.sum_le_sum hterm
    _ = (U : ℝ) * Erdos851.BetaSieveFundamental.sublistsLenMass
          (fun p : ℕ ↦ (1 : ℝ) / (p : ℝ)) P.toList r := by
      rw [← Finset.mul_sum]
      unfold C Erdos851.BetaSieveFundamental.sublistsLenMass
      rw [← List.sum_toFinset]
      exact List.nodup_sublistsLen r P.nodup_toList
    _ ≤ (U : ℝ) *
          ((P.toList.map (fun p : ℕ ↦ (1 : ℝ) / (p : ℝ))).sum ^ r /
            (r.factorial : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg U)
      have hfac : (0 : ℝ) < (r.factorial : ℕ) := by
        exact_mod_cast Nat.factorial_pos r
      apply (le_div_iff₀ hfac).2
      simpa [mul_comm] using
        Erdos851.BetaSieveFundamental.factorial_mul_sublistsLenMass_le_sum_pow
          (fun p : ℕ ↦ (1 : ℝ) / (p : ℝ))
          (fun p ↦ by positivity) P.toList r
    _ = (U : ℝ) *
          ((∑ p ∈ P, (1 : ℝ) / p) ^ r /
            (r.factorial : ℝ)) := by
      congr 3
      induction P using Finset.induction_on with
      | empty => simp
      | @insert p P hp ih =>
          simp [hp]

end Erdos444
