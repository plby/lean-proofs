/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos999.PairDeterminant

/-!
# Reduction of nearby reduced pairs to short determinant intervals

This file turns the circle-geometric pair condition into a finite sum that
can be estimated by a one-dimensional sieve.  Put `g = gcd q r` and
`t = (a*r - b*q) / g`.  When the sum of the two physical radii is at most
one, `t` belongs to one of three integer intervals.  Their common radius is
the ceiling of `(r*L + q*M) / g`, and their centres are the normalized lifts
of `-q*r`, `0`, and `q*r`.  Reducedness further forces
`t.natAbs` to be coprime to `(q/g)*(r/g)`.
-/

open Set
open scoped BigOperators

namespace Erdos999

noncomputable section

/-- The normalized determinant attached to a residue pair. -/
def normalizedPairDet (q r : ℕ) (z : Fin q × Fin r) : ℤ :=
  pairDet q r z / (q.gcd r : ℤ)

/-- The real radius of the normalized determinant intervals. -/
def normalizedPairDetRadius (q r : ℕ) (L M : ℝ) : ℝ :=
  (r * L + q * M) / (q.gcd r : ℕ)

/-- A natural integral cutoff containing the normalized determinant radius. -/
def normalizedPairDetCutoff (q r : ℕ) (L M : ℝ) : ℕ :=
  Nat.ceil (normalizedPairDetRadius q r L M)

/-- The positive normalized lift of one full turn. -/
def normalizedPairDetPositiveCenter (q r : ℕ) : ℤ :=
  (q * r : ℕ) / (q.gcd r : ℤ)

/-- The negative normalized lift of one full turn. -/
def normalizedPairDetNegativeCenter (q r : ℕ) : ℤ :=
  -(q * r : ℕ) / (q.gcd r : ℤ)

/-- The closed integer interval of natural radius `N` around `C`. -/
def centeredIntInterval (C : ℤ) (N : ℕ) : Finset ℤ :=
  Finset.Icc (C - N) (C + N)

/-- The union of the three short intervals that can contain a normalized
determinant of a nearby pair. -/
def normalizedPairDetIntervals (q r : ℕ) (L M : ℝ) : Finset ℤ :=
  centeredIntInterval (normalizedPairDetNegativeCenter q r)
      (normalizedPairDetCutoff q r L M) ∪
    centeredIntInterval 0 (normalizedPairDetCutoff q r L M) ∪
    centeredIntInterval (normalizedPairDetPositiveCenter q r)
      (normalizedPairDetCutoff q r L M)

/-- The three determinant intervals restricted by the coprimality condition
forced by reduced numerators. -/
def admissibleNormalizedPairDetIntervals
    (q r : ℕ) (L M : ℝ) : Finset ℤ :=
  (normalizedPairDetIntervals q r L M).filter fun t =>
    t.natAbs.Coprime ((q / q.gcd r) * (r / q.gcd r))

/-- The exact reduced-pair fiber above a normalized determinant. -/
def reducedNormalizedPairDetFiber (q r : ℕ) (t : ℤ) :
    Finset (Fin q × Fin r) :=
  (Finset.univ : Finset (Fin q × Fin r)).filter fun z =>
    q.Coprime (z.1 : ℕ) ∧ r.Coprime (z.2 : ℕ) ∧
      normalizedPairDet q r z = t

/-- Even before using reducedness, a normalized determinant fiber has at
most `gcd q r` pairs. -/
theorem card_reducedNormalizedPairDetFiber_le_gcd
    {q r : ℕ} (hq : 0 < q) (t : ℤ) :
    (reducedNormalizedPairDetFiber q r t).card ≤ q.gcd r := by
  classical
  let rawFiber := (Finset.univ : Finset (Fin q × Fin r)).filter fun z =>
    pairDet q r z = (q.gcd r : ℤ) * t
  have hsubset : reducedNormalizedPairDetFiber q r t ⊆ rawFiber := by
    intro z hz
    rw [reducedNormalizedPairDetFiber, Finset.mem_filter] at hz
    change z ∈ (Finset.univ : Finset (Fin q × Fin r)).filter
      (fun z => pairDet q r z = (q.gcd r : ℤ) * t)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ z, ?_⟩
    have hmul := Int.ediv_mul_cancel (gcd_dvd_pairDet q r z)
    calc
      pairDet q r z = normalizedPairDet q r z * (q.gcd r : ℤ) := by
        simpa [normalizedPairDet] using hmul.symm
      _ = t * (q.gcd r : ℤ) := by rw [hz.2.2.2]
      _ = (q.gcd r : ℤ) * t := mul_comm _ _
  calc
    (reducedNormalizedPairDetFiber q r t).card ≤ rawFiber.card :=
      Finset.card_le_card hsubset
    _ ≤ q.gcd r := by
      simpa [rawFiber] using
        card_pairDet_fiber_le_gcd hq ((q.gcd r : ℤ) * t)

lemma mem_centeredIntInterval_of_abs_sub_lt
    {t C : ℤ} {X : ℝ} (h : |(t : ℝ) - C| < X) :
    t ∈ centeredIntInterval C (Nat.ceil X) := by
  rw [centeredIntInterval, Finset.mem_Icc]
  have hceil : X ≤ (Nat.ceil X : ℕ) := Nat.le_ceil X
  have hp := abs_lt.mp h
  constructor
  · have hreal : ((C - (Nat.ceil X : ℕ) : ℤ) : ℝ) ≤ t := by
      push_cast
      linarith
    exact_mod_cast hreal
  · have hreal : (t : ℝ) ≤ (C + (Nat.ceil X : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast hreal

private lemma normalized_sub_lt_of_sub_lt
    {g : ℕ} (hg : 0 < g) {c s : ℤ} {D : ℝ}
    (hc : (g : ℤ) ∣ c) (hs : (g : ℤ) ∣ s)
    (h : |(c : ℝ) - s| < D) :
    |((c / (g : ℤ) : ℤ) : ℝ) - (s / (g : ℤ) : ℤ)| < D / g := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  rw [lt_div_iff₀ hgR]
  have heqZ : (c / (g : ℤ) - s / (g : ℤ)) * (g : ℤ) = c - s := by
    rw [sub_mul, Int.ediv_mul_cancel hc, Int.ediv_mul_cancel hs]
  calc
    |((c / (g : ℤ) : ℤ) : ℝ) - (s / (g : ℤ) : ℤ)| * (g : ℝ) =
        |((((c / (g : ℤ) - s / (g : ℤ)) * (g : ℤ)) : ℤ) : ℝ)| := by
      push_cast
      rw [abs_mul, abs_of_pos hgR]
    _ = |(c : ℝ) - s| := by rw [heqZ]; push_cast; rfl
    _ < D := h

/-- A nearby pair has normalized determinant in the union of the three short
integer intervals. -/
theorem normalizedPairDet_mem_intervals_of_nearby
    {q r : ℕ} {L M : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hsmall : L / q + M / r ≤ 1) {z : Fin q × Fin r}
    (hz : isNearbyReducedPair q r L M z) :
    normalizedPairDet q r z ∈ normalizedPairDetIntervals q r L M := by
  let g := q.gcd r
  let c := pairDet q r z
  let P : ℤ := q * r
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hq
  have hgc : (g : ℤ) ∣ c := by
    simpa [g, c] using gcd_dvd_pairDet q r z
  have hgP : (g : ℤ) ∣ P := by
    exact Int.natCast_dvd_natCast.mpr
      ((Nat.gcd_dvd_left q r).mul_right r)
  have hthree := nearby_pairDet_mem_three_intervals hq hr hsmall hz
  rcases hthree with hzero | hpos | hneg
  · have hn := normalized_sub_lt_of_sub_lt hg hgc (dvd_zero _) (s := 0)
      (by simpa [c] using hzero)
    have hm := mem_centeredIntInterval_of_abs_sub_lt hn
    simp only [normalizedPairDet, normalizedPairDetIntervals,
      normalizedPairDetCutoff, normalizedPairDetRadius, Finset.mem_union]
    exact Or.inl <| Or.inr <| by simpa [c, g] using hm
  · have hn := normalized_sub_lt_of_sub_lt hg hgc hgP (s := P)
      (by simpa [c, P] using hpos)
    have hm := mem_centeredIntInterval_of_abs_sub_lt hn
    simp only [normalizedPairDet, normalizedPairDetIntervals,
      normalizedPairDetCutoff, normalizedPairDetRadius, Finset.mem_union]
    exact Or.inr <| by
      simpa [c, g, P, normalizedPairDetPositiveCenter] using hm
  · have hgnegP : (g : ℤ) ∣ -P := dvd_neg.mpr hgP
    have hn := normalized_sub_lt_of_sub_lt hg hgc hgnegP (s := -P)
      (by convert hneg using 1 <;> simp [c, P] <;> ring)
    have hm := mem_centeredIntInterval_of_abs_sub_lt hn
    simp only [normalizedPairDet, normalizedPairDetIntervals,
      normalizedPairDetCutoff, normalizedPairDetRadius, Finset.mem_union]
    exact Or.inl <| Or.inl <| by
      simpa [c, g, P, normalizedPairDetNegativeCenter] using hm

/-- Public finite reduction for the arithmetic pair count.  The right side is
a sum of exact reduced determinant fibers over three short intervals, already
filtered by the necessary coprimality condition. -/
theorem nearbyReducedPairCount_le_sum_reducedNormalizedPairDetFiber
    {q r : ℕ} {L M : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hsmall : L / q + M / r ≤ 1) :
    nearbyReducedPairCount q r L M ≤
      ∑ t ∈ admissibleNormalizedPairDetIntervals q r L M,
        (reducedNormalizedPairDetFiber q r t).card := by
  classical
  let nearby := (Finset.univ : Finset (Fin q × Fin r)).filter
    (isNearbyReducedPair q r L M)
  let intervals := admissibleNormalizedPairDetIntervals q r L M
  let fiber := reducedNormalizedPairDetFiber q r
  have hsubset : nearby ⊆ intervals.biUnion fiber := by
    intro z hz
    have hz' : isNearbyReducedPair q r L M z := (Finset.mem_filter.mp hz).2
    let t := normalizedPairDet q r z
    have htIntervals : t ∈ normalizedPairDetIntervals q r L M :=
      normalizedPairDet_mem_intervals_of_nearby hq hr hsmall hz'
    have htCoprime : t.natAbs.Coprime
        ((q / q.gcd r) * (r / q.gcd r)) := by
      exact normalized_pairDet_coprime hq hz'.1 hz'.2.1
    have ht : t ∈ intervals := by
      simpa [intervals, admissibleNormalizedPairDetIntervals] using
        And.intro htIntervals htCoprime
    rw [Finset.mem_biUnion]
    refine ⟨t, ht, ?_⟩
    change z ∈ reducedNormalizedPairDetFiber q r t
    simp only [reducedNormalizedPairDetFiber, Finset.mem_filter]
    exact ⟨Finset.mem_univ z, hz'.1, hz'.2.1, rfl⟩
  calc
    nearbyReducedPairCount q r L M = nearby.card := by
      simp [nearby, nearbyReducedPairCount]
    _ ≤ (intervals.biUnion fiber).card := Finset.card_le_card hsubset
    _ ≤ ∑ t ∈ intervals, (fiber t).card := Finset.card_biUnion_le
    _ = ∑ t ∈ admissibleNormalizedPairDetIntervals q r L M,
        (reducedNormalizedPairDetFiber q r t).card := rfl

/-- Crude corollary exposing the exact one-dimensional sieve input: it is
enough to count admissible normalized determinants in the three intervals. -/
theorem nearbyReducedPairCount_le_gcd_mul_admissibleIntervalCard
    {q r : ℕ} {L M : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hsmall : L / q + M / r ≤ 1) :
    nearbyReducedPairCount q r L M ≤
      (admissibleNormalizedPairDetIntervals q r L M).card * q.gcd r := by
  calc
    nearbyReducedPairCount q r L M ≤
        ∑ t ∈ admissibleNormalizedPairDetIntervals q r L M,
          (reducedNormalizedPairDetFiber q r t).card :=
      nearbyReducedPairCount_le_sum_reducedNormalizedPairDetFiber hq hr hsmall
    _ ≤ ∑ _t ∈ admissibleNormalizedPairDetIntervals q r L M, q.gcd r := by
      exact Finset.sum_le_sum fun t _ ↦
        card_reducedNormalizedPairDetFiber_le_gcd hq t
    _ = (admissibleNormalizedPairDetIntervals q r L M).card * q.gcd r := by
      simp

end

end Erdos999
