import ErdosProblems.Erdos248.MomentCombinatorics
import Util.TaoTeravainen.PrimePowerCounting
import Util.TaoTeravainen.PrimePowerEventMass

/-!
# Tao--Teräväinen: finite second moment of excess multiplicity

This file is the purely finite bridge from the exact factorization excess to
pairwise prime-power event masses. Analytic estimates for those pair masses
can be inserted through the final hypothesis without changing the
combinatorial expansion.
-/

noncomputable section

open scoped BigOperators

namespace TaoTeravainen

local instance primePowerMomentDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The finite sample interval carrying the Maynard weight. -/
def sieveInterval (K : ℕ) : Finset ℕ :=
  Finset.Ico (Erdos248.intervalStart K) (2 * Erdos248.intervalStart K)

/-- Second weighted moment of the multiplicity excess at one shift. -/
def excessSecondMoment (K k : ℕ) : ℝ :=
  Erdos248.weightedSecondMoment (sieveInterval K) (Erdos248.sieveWeight K)
    (fun n => (factorizationExcess (n + k) : ℝ))

/-- Weighted mass of the event that excess multiplicity exceeds T*k. -/
def weightedExcessBadMass (K T k : ℕ) : ℝ :=
  Erdos248.weightedMass (sieveInterval K) (Erdos248.sieveWeight K)
    (fun n => T * k < factorizationExcess (n + k))

/-- Square-moment Markov for the exact excess event. -/
theorem sq_mul_weightedExcessBadMass_le_secondMoment
    (K T k : ℕ) :
    ((T * k : ℕ) : ℝ) ^ 2 * weightedExcessBadMass K T k ≤
      excessSecondMoment K k := by
  let s := sieveInterval K
  let w := Erdos248.sieveWeight K
  let Z : ℕ → ℝ := fun n => (factorizationExcess (n + k) : ℝ)
  have hsubset : weightedExcessBadMass K T k ≤
      Erdos248.weightedMass s w
        (fun n => ((T * k : ℕ) : ℝ) ≤ |Z n|) := by
    unfold weightedExcessBadMass Erdos248.weightedMass
      Erdos248.weightedSum
    apply Finset.sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_left _ (Erdos248.sieveWeight_nonneg K n)
    change Erdos248.realIndicator (T * k < factorizationExcess (n + k)) ≤
      Erdos248.realIndicator (((T * k : ℕ) : ℝ) ≤ |Z n|)
    by_cases hbad : T * k < factorizationExcess (n + k)
    · rw [Erdos248.realIndicator_of_true hbad,
        Erdos248.realIndicator_of_true]
      dsimp [Z]
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hbad.le
    · rw [Erdos248.realIndicator_of_false hbad]
      exact Erdos248.realIndicator_nonneg _
  have hmarkov := Erdos248.sq_mul_weightedMass_threshold_abs_le_secondMoment
    (s := s) (w := w) (Z := Z) (t := ((T * k : ℕ) : ℝ))
    (by positivity) (by intro n hn; exact Erdos248.sieveWeight_nonneg K n)
  calc
    ((T * k : ℕ) : ℝ) ^ 2 * weightedExcessBadMass K T k ≤
        ((T * k : ℕ) : ℝ) ^ 2 *
          Erdos248.weightedMass s w
            (fun n => ((T * k : ℕ) : ℝ) ≤ |Z n|) :=
      mul_le_mul_of_nonneg_left hsubset (by positivity)
    _ ≤ Erdos248.weightedSecondMoment s w Z := hmarkov
    _ = excessSecondMoment K k := rfl

/-- The mass of the conjunction selected by a two-tuple of prime-power
indices is the explicit pair-event mass. -/
theorem weightedMass_tuplePrimePowerEvent_eq_pairEventMass
    (K k : ℕ) (t : Fin 2 → ℕ × ℕ) :
    Erdos248.weightedMass (sieveInterval K) (Erdos248.sieveWeight K)
      (Erdos248.tupleEvent
        (fun pa : ℕ × ℕ => fun n : ℕ => pa.1 ^ pa.2 ∣ n + k) t) =
      primePowerPairEventMass K k (t 0).1 (t 0).2 (t 1).1 (t 1).2 := by
  classical
  unfold Erdos248.weightedMass Erdos248.weightedSum sieveInterval
    primePowerPairEventMass BoundedGaps.Maynard.sieveWeightSum
  apply Finset.sum_congr rfl
  intro n hn
  unfold Erdos248.realIndicator Erdos248.tupleEvent
  by_cases h0 : (t 0).1 ^ (t 0).2 ∣ n + k <;>
    by_cases h1 : (t 1).1 ^ (t 1).2 ∣ n + k <;>
      simp [h0, h1, Fin.forall_fin_two]

/-- Pair-event bounds imply a bound for the exact weighted second moment of
the factorization excess. -/
theorem excessSecondMoment_le_of_pairBound
    {K k : ℕ} (hk : k ≤ Erdos248.intervalExponent K)
    (Q : (Fin 2 → ℕ × ℕ) → ℝ)
    (hpair : ∀ t ∈ Erdos248.indexTuples 2
        (properPrimePowerIndices (3 * Erdos248.intervalStart K)),
      primePowerPairEventMass K k (t 0).1 (t 0).2 (t 1).1 (t 1).2 ≤ Q t) :
    excessSecondMoment K k ≤
      ∑ t ∈ Erdos248.indexTuples 2
          (properPrimePowerIndices (3 * Erdos248.intervalStart K)),
        Q t := by
  let I := properPrimePowerIndices (3 * Erdos248.intervalStart K)
  have hrewrite :
      excessSecondMoment K k =
        Erdos248.weightedSecondMoment (sieveInterval K)
          (Erdos248.sieveWeight K)
          (fun n =>
            ∑ pa ∈ I,
              (1 : ℝ) *
                Erdos248.realIndicator (pa.1 ^ pa.2 ∣ n + k)) := by
    unfold excessSecondMoment Erdos248.weightedSecondMoment
      Erdos248.weightedMoment Erdos248.weightedSum
    apply Finset.sum_congr rfl
    intro n hn
    have hcount := factorizationExcess_shift_cast_eq_indicatorSum
      (K := K) (n := n) (k := k) (by simpa [sieveInterval] using hn) hk
    rw [properPrimePower_indicatorSum_eq_indexSum] at hcount
    change Erdos248.sieveWeight K n *
        (factorizationExcess (n + k) : ℝ) ^ 2 =
      Erdos248.sieveWeight K n *
        (∑ pa ∈ I, (1 : ℝ) *
          Erdos248.realIndicator (pa.1 ^ pa.2 ∣ n + k)) ^ 2
    rw [hcount]
    simp [I, Erdos248.realIndicator]
  rw [hrewrite]
  have hraw := Erdos248.weightedSecondMoment_indicatorSum_le_pairBound
    (sieveInterval K) I (Erdos248.sieveWeight K)
    (fun _ => (1 : ℝ))
    (fun pa : ℕ × ℕ => fun n : ℕ => pa.1 ^ pa.2 ∣ n + k)
    Q (by intro i hi; norm_num) (by
      intro t ht
      rw [weightedMass_tuplePrimePowerEvent_eq_pairEventMass]
      exact hpair t (by simpa [I] using ht))
  simpa [I] using hraw

end TaoTeravainen
