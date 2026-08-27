import ErdosProblems.Erdos587.HooleyMaximal
import ErdosProblems.Erdos587.HooleySmoothNumbers
import ErdosProblems.Erdos587.HooleyMertens

/-!
# Prime subsets as weighted binary choices

Choosing a prime has weight `1/p`. The generic finite maximal inequality
therefore controls reciprocal mass once its choices are identified with
squarefree products of primes.
-/

open scoped BigOperators

namespace Erdos587

noncomputable abbrev deltaPrimeWeights (P : List ℕ) : List ℝ :=
  P.map (fun p : ℕ => (1 : ℝ) / (p : ℝ))

abbrev DeltaPrimeChoice (P : List ℕ) := DeltaChoice (deltaPrimeWeights P).length

def deltaPrimeChoiceSet : (P : List ℕ) → DeltaPrimeChoice P → Finset ℕ
  | [], _ => ∅
  | p :: P, s => if s.1 then insert p (deltaPrimeChoiceSet P s.2) else deltaPrimeChoiceSet P s.2

lemma deltaPrimeChoiceSet_subset (P : List ℕ) (s : DeltaPrimeChoice P) :
    deltaPrimeChoiceSet P s ⊆ P.toFinset := by
  induction P with
  | nil => exact Finset.empty_subset _
  | cons p P ih =>
    change (if s.1 then insert p (deltaPrimeChoiceSet P s.2) else deltaPrimeChoiceSet P s.2) ⊆ _
    have hsub := ih s.2
    rw [List.toFinset_cons]
    split_ifs
    · exact Finset.insert_subset_insert p hsub
    · exact hsub.trans (Finset.subset_insert _ _)

lemma exists_deltaPrimeChoiceSet (P : List ℕ) (S : Finset ℕ) (hS : S ⊆ P.toFinset) :
    ∃ s : DeltaPrimeChoice P, deltaPrimeChoiceSet P s = S := by
  induction P generalizing S with
  | nil =>
    have hS0 : S = ∅ := Finset.Subset.antisymm hS (Finset.empty_subset _)
    exact ⟨(), hS0.symm⟩
  | cons p P ih =>
    by_cases hp : p ∈ S
    · have htail : S.erase p ⊆ P.toFinset := by
        intro r hr
        obtain ⟨hrp, hrS⟩ := Finset.mem_erase.mp hr
        have hrP := hS hrS
        simpa only [List.toFinset_cons, Finset.mem_insert, hrp, false_or] using hrP
      obtain ⟨s, hs⟩ := ih (S.erase p) htail
      refine ⟨⟨true, s⟩, ?_⟩
      simpa only [deltaPrimeChoiceSet, if_true, hs] using Finset.insert_erase hp
    · have htail : S ⊆ P.toFinset := by
        intro r hr
        have hrp : r ≠ p := by rintro rfl; exact hp hr
        have hrP := hS hr
        simpa only [List.toFinset_cons, Finset.mem_insert, hrp, false_or] using hrP
      obtain ⟨s, hs⟩ := ih S htail
      refine ⟨⟨false, s⟩, ?_⟩
      simpa only [deltaPrimeChoiceSet, Bool.false_eq_true, if_false] using hs

lemma deltaPrimeChoiceSet_head_notMem {p : ℕ} {P : List ℕ} (hP : (p :: P).Nodup)
    (s : DeltaPrimeChoice P) : p ∉ deltaPrimeChoiceSet P s := by
  intro hp
  exact (List.nodup_cons.mp hP).1 (List.mem_toFinset.mp (deltaPrimeChoiceSet_subset P s hp))

lemma deltaPrimeChoiceWeight_eq {P : List ℕ} (hP : P.Nodup) (s : DeltaPrimeChoice P) :
    deltaChoiceWeight (deltaPrimeWeights P) s =
      (1 : ℝ) / (∏ p ∈ deltaPrimeChoiceSet P s, p : ℕ) := by
  induction P with
  | nil =>
    change (1 : ℝ) = 1 / (∏ p ∈ (∅ : Finset ℕ), p : ℕ)
    norm_num
  | cons p P ih =>
    have htail := (List.nodup_cons.mp hP).2
    have hnot := deltaPrimeChoiceSet_head_notMem hP s.2
    rcases s with ⟨b, s⟩
    change (if b then (1 : ℝ) / p else 1) * deltaChoiceWeight (deltaPrimeWeights P) s = _
    cases b <;>
      simp [deltaPrimeChoiceSet, ih htail s,
        Finset.prod_insert hnot, Nat.cast_mul, one_div, mul_comm]

noncomputable def deltaPrimePrefixNormalizer (P : List ℕ) (k : ℕ) : ℝ :=
  ((P.take k).map (fun p : ℕ => deltaChoiceNormalizer ((1 : ℝ) / (p : ℝ)))).prod

lemma one_le_deltaChoiceNormalizer {a : ℝ} (ha : 0 ≤ a) : 1 ≤ deltaChoiceNormalizer a := by
  unfold deltaChoiceNormalizer
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + a)]
  linarith

lemma deltaChoiceNormalizer_le_one_add {a : ℝ} (ha : 0 ≤ a) :
    deltaChoiceNormalizer a ≤ 1 + a := by
  unfold deltaChoiceNormalizer
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + a)]
  nlinarith only [sq_nonneg a]

lemma one_le_deltaPrimePrefixNormalizer (P : List ℕ) (k : ℕ) :
    1 ≤ deltaPrimePrefixNormalizer P k := by
  apply List.one_le_prod
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact one_le_deltaChoiceNormalizer (by positivity)

/-- The normalized prefix value is exactly the divisor count of the
chosen prefix, divided by its mean normalizer. -/
lemma deltaPrimeChoicePrefixValue_eq {P : List ℕ} (hP : P.Nodup)
    (s : DeltaPrimeChoice P) (k : ℕ) (z : ℝ) :
    deltaChoicePrefixValue (deltaPrimeWeights P) z s k =
      z * (2 : ℝ) ^ (deltaPrimeChoiceSet P s ∩ (P.take k).toFinset).card /
        deltaPrimePrefixNormalizer P k := by
  induction P generalizing k z with
  | nil =>
    change z = z * (2 : ℝ) ^ (∅ ∩ ([].take k : List ℕ).toFinset).card /
      deltaPrimePrefixNormalizer [] k
    simp [deltaPrimePrefixNormalizer]
  | cons p P ih =>
    cases k with
    | zero =>
      change z = z * (2 : ℝ) ^ (deltaPrimeChoiceSet (p :: P) s ∩ (∅ : Finset ℕ)).card / 1
      simp
    | succ k =>
      have htail := (List.nodup_cons.mp hP).2
      have hnot := deltaPrimeChoiceSet_head_notMem hP s.2
      have hnotInter : p ∉ deltaPrimeChoiceSet P s.2 ∩ (P.take k).toFinset :=
        fun hp => hnot (Finset.mem_inter.mp hp).1
      rcases s with ⟨b, s⟩
      cases b with
      | false =>
        change deltaChoicePrefixValue (deltaPrimeWeights P)
          (1 * z / deltaChoiceNormalizer ((1 : ℝ) / p)) s k = _
        rw [one_mul]
        rw [ih htail]
        simp only [deltaPrimeChoiceSet, Bool.false_eq_true, if_false, List.take_succ_cons,
          List.toFinset_cons, Finset.inter_insert_of_notMem hnot,
          deltaPrimePrefixNormalizer, List.map_cons, List.prod_cons]
        ring
      | true =>
        change deltaChoicePrefixValue (deltaPrimeWeights P)
          (2 * z / deltaChoiceNormalizer ((1 : ℝ) / p)) s k = _
        rw [ih htail]
        simp only [deltaPrimeChoiceSet, if_true, List.take_succ_cons, List.toFinset_cons,
          ← Finset.insert_inter_distrib, Finset.card_insert_of_notMem hnotInter,
          deltaPrimePrefixNormalizer, List.map_cons, List.prod_cons, pow_succ]
        ring

end Erdos587
