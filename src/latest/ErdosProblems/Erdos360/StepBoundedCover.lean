import ErdosProblems.Erdos360.CyclicInverse
import ErdosProblems.Erdos360.LargeSubgroup
import ErdosProblems.Erdos360.SharpModular

open scoped BigOperators Pointwise

namespace Erdos360

/-!
# Normalizing cyclic progression covers to bounded steps

Every set of shifted representatives modulo `b` lies in the half-open
interval `[b, b + b)`.  A positive-step natural progression whose step is
larger than `b` meets such an interval in at most one point.  Consequently,
in any long-progression cover we may replace each overlarge-step piece that
meets the covered set by a same-length step-one progression based at that
unique point.  The number of pieces, every parameter length, and hence both
the mass and longness bounds are unchanged.

This gives a representation-independent bridge from all existing cyclic
inverse-theorem outputs (including the sharp large-subgroup output) to the
step-bounded interface used by the arbitrary-step sieve.
-/

/-- A progression of step greater than the width of a half-open interval
contains at most one point of that interval. -/
lemma eq_of_mem_natProgression_of_step_gt_interval
    {lower width x y : ℕ} (P : NatProgressionSpec)
    (hstep : width < P.step)
    (hxl : lower ≤ x) (hxu : x < lower + width)
    (hyl : lower ≤ y) (hyu : y < lower + width)
    (hxP : x ∈ P.carrier) (hyP : y ∈ P.carrier) :
    x = y := by
  obtain ⟨i, hi, hxi⟩ := mem_natProgression_iff.mp hxP
  obtain ⟨j, hj, hyj⟩ := mem_natProgression_iff.mp hyP
  rcases lt_trichotomy i j with hij | hij | hij
  · have hij' : i + 1 ≤ j := Nat.succ_le_iff.mpr hij
    have hsep : x + P.step ≤ y := by
      rw [hxi, hyj]
      calc
        P.start + P.step * i + P.step =
            P.start + P.step * (i + 1) := by ring
        _ ≤ P.start + P.step * j :=
          Nat.add_le_add_left (Nat.mul_le_mul_left P.step hij') P.start
    omega
  · subst j
    exact hxi.trans hyj.symm
  · have hji' : j + 1 ≤ i := Nat.succ_le_iff.mpr hij
    have hsep : y + P.step ≤ x := by
      rw [hxi, hyj]
      calc
        P.start + P.step * j + P.step =
            P.start + P.step * (j + 1) := by ring
        _ ≤ P.start + P.step * i :=
          Nat.add_le_add_left (Nat.mul_le_mul_left P.step hji') P.start
    omega

/-- A point selected from the intersection of the covered set and a
progression, when that intersection is nonempty. -/
noncomputable def boundedStepReplacementStart
    (X : Finset ℕ) (P : NatProgressionSpec) : ℕ :=
  if h : ∃ x, x ∈ X ∧ x ∈ P.carrier then h.choose else P.start

lemma boundedStepReplacementStart_spec
    {X : Finset ℕ} {P : NatProgressionSpec}
    (h : ∃ x, x ∈ X ∧ x ∈ P.carrier) :
    boundedStepReplacementStart X P ∈ X ∧
      boundedStepReplacementStart X P ∈ P.carrier := by
  simp only [boundedStepReplacementStart, dif_pos h]
  exact h.choose_spec

/-- Replace a step larger than `stepBound` by step one, without changing
the parameter length.  The start is chosen from the part of the old piece
which actually meets `X`. -/
noncomputable def NatProgressionSpec.boundStep
    (X : Finset ℕ) (stepBound : ℕ) (P : NatProgressionSpec) :
    NatProgressionSpec :=
  if h : P.step ≤ stepBound then P else
    { start := boundedStepReplacementStart X P
      step := 1
      length := P.length
      step_pos := by omega }

@[simp] lemma NatProgressionSpec.boundStep_length
    (X : Finset ℕ) (stepBound : ℕ) (P : NatProgressionSpec) :
    (P.boundStep X stepBound).length = P.length := by
  by_cases h : P.step ≤ stepBound <;> simp [NatProgressionSpec.boundStep, h]

lemma NatProgressionSpec.boundStep_step_le
    (X : Finset ℕ) {stepBound : ℕ} (hbound : 0 < stepBound)
    (P : NatProgressionSpec) :
    (P.boundStep X stepBound).step ≤ stepBound := by
  by_cases h : P.step ≤ stepBound
  · rw [NatProgressionSpec.boundStep, dif_pos h]
    exact h
  · simp only [NatProgressionSpec.boundStep, dif_neg h]
    exact hbound

/-- On a set contained in an interval of width `stepBound`, replacing an
overlarge step preserves every covered point. -/
lemma NatProgressionSpec.mem_boundStep_of_mem_interval
    {X : Finset ℕ} {lower stepBound x : ℕ}
    (P : NatProgressionSpec)
    (hlo : ∀ z ∈ X, lower ≤ z)
    (hhi : ∀ z ∈ X, z < lower + stepBound)
    (hxX : x ∈ X) (hxP : x ∈ P.carrier) :
    x ∈ (P.boundStep X stepBound).carrier := by
  by_cases hstep : P.step ≤ stepBound
  · simpa [NatProgressionSpec.boundStep, hstep] using hxP
  · have hmeet : ∃ z, z ∈ X ∧ z ∈ P.carrier := ⟨x, hxX, hxP⟩
    let y := boundedStepReplacementStart X P
    have hy := boundedStepReplacementStart_spec hmeet
    have hxy : x = y :=
      eq_of_mem_natProgression_of_step_gt_interval P
        (Nat.lt_of_not_ge hstep)
        (hlo x hxX) (hhi x hxX) (hlo y hy.1) (hhi y hy.1) hxP hy.2
    have hlen : 0 < P.length := by
      obtain ⟨i, hi, _⟩ := mem_natProgression_iff.mp hxP
      omega
    rw [hxy]
    rw [NatProgressionSpec.carrier, mem_natProgression_iff]
    refine ⟨0, ?_, ?_⟩
    · simpa [NatProgressionSpec.boundStep, hstep] using hlen
    · simp [NatProgressionSpec.boundStep, hstep, y]

/-- Any long-progression cover of a set lying in a half-open interval can
be normalized, with exactly the same mass and piece lengths, so that every
step is at most the interval width. -/
theorem HasLongProgressionCover.toStepBounded_of_subset_interval
    {X : Finset ℕ} {mass lower stepBound : ℕ}
    (hbound : 0 < stepBound)
    (hlo : ∀ x ∈ X, lower ≤ x)
    (hhi : ∀ x ∈ X, x < lower + stepBound)
    (h : HasLongProgressionCover X mass) :
    HasStepBoundedLongProgressionCover X mass stepBound := by
  obtain ⟨m, P, hcover, hmass, hlong⟩ := h
  let Q : Fin m → NatProgressionSpec := fun i ↦
    (P i).boundStep X stepBound
  refine ⟨m, Q, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hxi⟩ := hcover x hx
    exact ⟨i, (P i).mem_boundStep_of_mem_interval hlo hhi hx hxi⟩
  · simpa [Q] using hmass
  · intro i
    simpa [Q] using hlong i
  · intro i
    exact (P i).boundStep_step_le X hbound

lemma shiftedZmodValues_mem_modulus_interval
    {b : ℕ} [NeZero b] (R : Finset (ZMod b)) :
    (∀ x ∈ shiftedZmodValues R, b ≤ x) ∧
      ∀ x ∈ shiftedZmodValues R, x < b + b := by
  constructor
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_shiftedZmodValues_iff.mp hx
    omega
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_shiftedZmodValues_iff.mp hx
    have hrlt := ZMod.val_lt r
    omega

/-- Representation-independent cyclic bridge.  In particular this applies
to every cover produced by the cyclic-coset-progression, affine pullback,
and large-subgroup constructors, while preserving their sharp mass bound. -/
theorem HasLongProgressionCover.toStepBounded_shiftedZmodValues
    {b mass : ℕ} [NeZero b] {R : Finset (ZMod b)}
    (h : HasLongProgressionCover (shiftedZmodValues R) mass) :
    HasStepBoundedLongProgressionCover (shiftedZmodValues R) mass b := by
  obtain ⟨hlo, hhi⟩ := shiftedZmodValues_mem_modulus_interval R
  exact h.toStepBounded_of_subset_interval (NeZero.pos b) hlo hhi

/-- The general cyclic-coset-progression lift with the ambient-modulus step
bound made explicit. -/
theorem cyclicCosetProgression_shifted_stepBoundedLongProgressionCover_parametric
    {b q length : ℕ} [NeZero b]
    (hb : 0 < b) (hq : 0 < q) (hqb : q ∣ b) (hlength : 0 < length)
    (H : AddSubgroup (ZMod b))
    (hHdiv : ∀ x : ZMod b, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod b) ∈ H)
    (a d : ZMod b) :
    HasStepBoundedLongProgressionCover
      (shiftedZmodValues (cyclicCosetProgression H a d length))
      (6 * (length * Nat.card H)) b := by
  exact (cyclicCosetProgression_shifted_longProgressionCover_parametric
    hb hq hqb hlength H hHdiv hmult a d).toStepBounded_shiftedZmodValues

/-- The controlled affine product-core cover with the ambient modulus as a
step bound.  Both the factor-six cover and the sharp large-subgroup branch
retain exactly their original masses. -/
theorem affine_dense_productCore_stepBounded_cover
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (D : Finset (ZMod (m * d))) (hm : 0 < m)
    (hA : (firstCoordinateSet (zmodQuotRemImage m d D)).Nonempty)
    {base : ℕ} (hbase :
      base ∈ firstCoordinateSet (zmodQuotRemImage m d D))
    (H : AddSubgroup (ZMod d)) (u v : ZMod d)
    (hbaseCos : ContainedInAddCoset H
      (coordinateFiber (zmodQuotRemImage m d D) base))
    (hbaseDense : 2 * Nat.card H <
      3 * (coordinateFiber (zmodQuotRemImage m d D) base).card)
    (haffine : ∀ a ∈ firstCoordinateSet (zmodQuotRemImage m d D),
      ∀ y ∈ coordinateFiber (zmodQuotRemImage m d D) a,
        y - (a • u + v) ∈ H) :
    let L :=
      (firstCoordinateSet (zmodQuotRemImage m d D)).max' hA + 1
    let K := H.map (zmodQuotientEmbedding m d)
    D ⊆ cyclicCosetProgression K (zmodQuotientEmbedding m d v)
        ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d u) L ∧
      HasStepBoundedLongProgressionCover (shiftedZmodValues D)
        (6 * (L * Nat.card H)) (m * d) ∧
      (D.card ≤ (Nat.card H) ^ 3 →
        ∃ mass : ℕ, 2 * mass < 3 * (D + D).card ∧
          HasStepBoundedLongProgressionCover
            (shiftedZmodValues D) mass (m * d)) := by
  obtain ⟨hprog, hcover, hsharp⟩ := affine_dense_productCore_cover
    D hm hA hbase H u v hbaseCos hbaseDense haffine
  refine ⟨hprog, hcover.toStepBounded_shiftedZmodValues, ?_⟩
  intro hlarge
  obtain ⟨mass, hmass, hcoverMass⟩ := hsharp hlarge
  exact ⟨mass, hmass, hcoverMass.toStepBounded_shiftedZmodValues⟩

/-- Sharp large-subgroup output with its ambient-modulus step bound. -/
theorem zmodQuotRem_common_dense_large_subgroup_stepBounded_cover
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (D : Finset (ZMod (m * d))) (hm : 0 < m)
    (hA : (firstCoordinateSet (zmodQuotRemImage m d D)).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet (zmodQuotRemImage m d D))
    (hAcard : 6 ≤ (firstCoordinateSet (zmodQuotRemImage m d D)).card)
    (hgcd : (firstCoordinateSet (zmodQuotRemImage m d D)).gcd
      (fun n ↦ (n : ℤ)) = 1)
    (hsmall : 2 * (zmodQuotRemImage m d D +
        zmodQuotRemImage m d D).card <
      5 * (zmodQuotRemImage m d D).card) :
    ∃ base ∈ firstCoordinateSet (zmodQuotRemImage m d D),
      ∃ H : AddSubgroup (ZMod d),
        ContainedInAddCoset H
            (coordinateFiber (zmodQuotRemImage m d D) base) ∧
          2 * Nat.card H <
            3 * (coordinateFiber (zmodQuotRemImage m d D) base).card ∧
          (∀ a ∈ firstCoordinateSet (zmodQuotRemImage m d D),
            (coordinateFiber (zmodQuotRemImage m d D) a).card ≤
              (coordinateFiber (zmodQuotRemImage m d D) base).card) ∧
          (∀ a ∈ firstCoordinateSet (zmodQuotRemImage m d D),
            ContainedInAddCoset H
              (coordinateFiber (zmodQuotRemImage m d D) a)) ∧
          (D.card ≤ (Nat.card H) ^ 3 →
            ∃ mass : ℕ, 2 * mass < 3 * (D + D).card ∧
              HasStepBoundedLongProgressionCover
                (shiftedZmodValues D) mass (m * d)) := by
  obtain ⟨base, hbase, H, hcos, hdense, hmax, hall, hsharp⟩ :=
    zmodQuotRem_common_dense_large_subgroup_cover
      D hm hA hAzero hAcard hgcd hsmall
  refine ⟨base, hbase, H, hcos, hdense, hmax, hall, ?_⟩
  intro hlarge
  obtain ⟨mass, hmass, hcover⟩ := hsharp hlarge
  exact ⟨mass, hmass, hcover.toStepBounded_shiftedZmodValues⟩

end Erdos360
