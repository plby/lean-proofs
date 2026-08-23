/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Data.Finset.Preimage
import ErdosProblems.Erdos551.External.Erdos207.FiniteConditioning

/-!
# Conditioned selections inherited from an independent reservoir

The matching used in the KSSS outer-link stage is chosen after all link
reservoirs have been exposed.  There is no need to introduce a second random
matching oracle: on the global good event choose one admissible matching
deterministically and push the conditioned reservoir law forward along this
choice.  Every prescribed family in the chosen output must already occur in
the reservoir, so its joint-inclusion probability is inherited from the
independent bits, with exactly the reciprocal conditioning loss.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace FiniteLaw

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

/-- The law obtained by conditioning on `Good` and then applying a
deterministic finite-set selector. -/
def conditionedSelectionLaw [DecidableEq I]
    (L : FiniteLaw Ω) (Good : Ω → Prop) (hGood : 0 < L.probability Good)
    (selected : Ω → Finset I) : FiniteLaw (Finset I) :=
  (L.conditionOn Good hGood).map selected

/-- A property proved for the selected output on every good reservoir holds
throughout the support of the conditioned selection law. -/
theorem conditionedSelectionLaw_supported [DecidableEq I]
    (L : FiniteLaw Ω) (Good : Ω → Prop) (hGood : 0 < L.probability Good)
    (selected : Ω → Finset I) (Q : Finset I → Prop)
    (hQ : ∀ ω, Good ω → Q (selected ω)) :
    (L.conditionedSelectionLaw Good hGood selected).SupportedOn Q := by
  simpa only [conditionedSelectionLaw] using
    ((L.conditionOn_supported Good hGood).map selected hQ)

/-- If the deterministic output is contained in an exposed reservoir on the
conditioning event, its joint-inclusion probability is at most the
unconditioned reservoir probability divided by the success probability. -/
theorem conditionedSelectionLaw_probability_subset_le
    [DecidableEq I]
    (L : FiniteLaw Ω) (Good : Ω → Prop) (hGood : 0 < L.probability Good)
    (reservoir selected : Ω → Finset I)
    (hselected : ∀ ω, Good ω → selected ω ⊆ reservoir ω)
    (Q : Finset I) :
    (L.conditionedSelectionLaw Good hGood selected).probability
        (fun S ↦ Q ⊆ S) ≤
      L.probability (fun ω ↦ Q ⊆ reservoir ω) / L.probability Good := by
  rw [conditionedSelectionLaw, probability_map,
    L.conditionOn_probability Good (fun ω ↦ Q ⊆ selected ω) hGood]
  gcongr
  apply L.probability_mono
  intro ω hω
  exact (hω.2.trans (hselected ω hω.1))

/-- Weighted version of
`conditionedSelectionLaw_probability_subset_le`. -/
theorem conditionedSelectionLaw_probability_subset_le_of_bound
    [DecidableEq I]
    (L : FiniteLaw Ω) (Good : Ω → Prop) (hGood : 0 < L.probability Good)
    (reservoir selected : Ω → Finset I)
    (hselected : ∀ ω, Good ω → selected ω ⊆ reservoir ω)
    (weight : Finset I → ℝ≥0)
    (hreservoir : ∀ Q,
      L.probability (fun ω ↦ Q ⊆ reservoir ω) ≤ weight Q)
    (Q : Finset I) :
    (L.conditionedSelectionLaw Good hGood selected).probability
        (fun S ↦ Q ⊆ S) ≤ weight Q / L.probability Good := by
  exact (L.conditionedSelectionLaw_probability_subset_le Good hGood
    reservoir selected hselected Q).trans (by gcongr; exact hreservoir Q)

end FiniteLaw

/-- The image in `X` of the coordinates selected by a Bernoulli bit vector. -/
def encodedReservoir
    {J X : Type*} [Fintype J] [DecidableEq J] [DecidableEq X]
    (e : J ↪ X) (ω : J → Bool) : Finset X :=
  (FiniteLaw.selectedByBits ω).map e

lemma encodedReservoir_subset_range
    {J X : Type*} [Fintype J] [DecidableEq J] [DecidableEq X]
    (e : J ↪ X) (ω : J → Bool) :
    encodedReservoir e ω ⊆ (univ : Finset J).map e := by
  exact Finset.map_subset_map.2 (subset_univ _)

/-- Exact product upper bound for a family prescribed in the image of an
injective encoding of independent Bernoulli coordinates.  A family outside
the image has probability zero. -/
theorem independentBits_probability_subset_encodedReservoir_le
    {J X : Type*} [Fintype J] [DecidableEq J] [DecidableEq X]
    (p : J → ℝ≥0) (hp : ∀ j, p j ≤ 1) (e : J ↪ X) (Q : Finset X) :
    (FiniteLaw.independentBits p hp).probability
        (fun ω ↦ Q ⊆ encodedReservoir e ω) ≤
      ∏ j ∈ Q.preimage e e.injective.injOn, p j := by
  classical
  by_cases hQrange : Q ⊆ (univ : Finset J).map e
  · let S := Q.preimage e e.injective.injOn
    have hmap : S.map e = Q := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, hjS, rfl⟩ := mem_map.mp hx
        exact mem_preimage.mp hjS
      · intro hxQ
        obtain ⟨j, _hj, hjx⟩ := mem_map.mp (hQrange hxQ)
        subst x
        exact mem_map.mpr ⟨j, mem_preimage.mpr hxQ, rfl⟩
    have hevent : (fun ω ↦ Q ⊆ encodedReservoir e ω) =
        (fun ω ↦ S ⊆ FiniteLaw.selectedByBits ω) := by
      funext ω
      apply propext
      rw [encodedReservoir, ← hmap]
      exact Finset.map_subset_map
    rw [hevent, FiniteLaw.independentBits_probability_subset_selected]
  · have hfalse : (fun ω ↦ Q ⊆ encodedReservoir e ω) =
        (fun _ : J → Bool ↦ False) := by
      funext ω
      apply propext
      constructor
      · intro hQ
        exact (hQrange (hQ.trans (encodedReservoir_subset_range e ω))).elim
      · exact False.elim
    rw [hfalse, FiniteLaw.probability_false]
    exact (zero_le : (0 : ℝ≥0) ≤
      ∏ j ∈ Q.preimage e e.injective.injOn, p j)

/-- Constant-density specialization of the encoded-reservoir bound. -/
theorem independentBits_probability_subset_encodedReservoir_le_pow
    {J X : Type*} [Fintype J] [DecidableEq J] [DecidableEq X]
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (e : J ↪ X) (Q : Finset X) :
    (FiniteLaw.independentBits (fun _ : J ↦ sigma) (fun _ ↦ hsigma)).probability
        (fun ω ↦ Q ⊆ encodedReservoir e ω) ≤ sigma ^ Q.card := by
  classical
  by_cases hQrange : Q ⊆ (univ : Finset J).map e
  · have hcard : (Q.preimage e e.injective.injOn).card = Q.card := by
      have hmap : (Q.preimage e e.injective.injOn).map e = Q := by
        ext x
        constructor
        · intro hx
          obtain ⟨j, hj, rfl⟩ := mem_map.mp hx
          exact mem_preimage.mp hj
        · intro hxQ
          obtain ⟨j, _hj, hjx⟩ := mem_map.mp (hQrange hxQ)
          subst x
          exact mem_map.mpr ⟨j, mem_preimage.mpr hxQ, rfl⟩
      rw [← hmap]
      simp
    simpa [hcard] using
      (independentBits_probability_subset_encodedReservoir_le
        (fun _ : J ↦ sigma) (fun _ ↦ hsigma) e Q)
  · have hzero : (FiniteLaw.independentBits (fun _ : J ↦ sigma)
        (fun _ ↦ hsigma)).probability
          (fun ω ↦ Q ⊆ encodedReservoir e ω) = 0 := by
      apply le_antisymm
      · calc
          _ ≤ (FiniteLaw.independentBits (fun _ : J ↦ sigma)
              (fun _ ↦ hsigma)).probability (fun _ ↦ False) := by
                apply FiniteLaw.probability_mono
                intro ω hQ
                exact (hQrange
                  (hQ.trans (encodedReservoir_subset_range e ω))).elim
          _ = 0 := FiniteLaw.probability_false _
      · exact zero_le
    rw [hzero]
    exact zero_le

/-- A deterministic subfamily selected on a positive-probability good event
inherits the constant-density joint-inclusion estimate of an injectively
encoded independent reservoir. -/
theorem conditioned_encodedSelection_probability_subset_le
    {J X : Type*} [Fintype J] [Fintype X] [DecidableEq J] [DecidableEq X]
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (e : J ↪ X)
    (Good : (J → Bool) → Prop)
    (hGood : 0 < (FiniteLaw.independentBits (fun _ : J ↦ sigma)
      (fun _ ↦ hsigma)).probability Good)
    (selected : (J → Bool) → Finset X)
    (hselected : ∀ ω, Good ω → selected ω ⊆ encodedReservoir e ω)
    (Q : Finset X) :
    ((FiniteLaw.independentBits (fun _ : J ↦ sigma)
        (fun _ ↦ hsigma)).conditionedSelectionLaw Good hGood selected).probability
          (fun S ↦ Q ⊆ S) ≤
      sigma ^ Q.card /
        (FiniteLaw.independentBits (fun _ : J ↦ sigma)
          (fun _ ↦ hsigma)).probability Good := by
  apply FiniteLaw.conditionedSelectionLaw_probability_subset_le_of_bound
    _ Good hGood (encodedReservoir e) selected hselected
      (fun Q ↦ sigma ^ Q.card)
  intro R
  exact independentBits_probability_subset_encodedReservoir_le_pow
    sigma hsigma e R

/-- The reciprocal conditioning loss can be absorbed into the base of every
nonempty joint-inclusion power.  The empty family is handled by probability
at most one. -/
theorem conditioned_encodedSelection_probability_subset_le_pow
    {J X : Type*} [Fintype J] [Fintype X] [DecidableEq J] [DecidableEq X]
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (e : J ↪ X)
    (Good : (J → Bool) → Prop)
    (hGood : 0 < (FiniteLaw.independentBits (fun _ : J ↦ sigma)
      (fun _ ↦ hsigma)).probability Good)
    (selected : (J → Bool) → Finset X)
    (hselected : ∀ ω, Good ω → selected ω ⊆ encodedReservoir e ω)
    (Q : Finset X) :
    ((FiniteLaw.independentBits (fun _ : J ↦ sigma)
        (fun _ ↦ hsigma)).conditionedSelectionLaw Good hGood selected).probability
          (fun S ↦ Q ⊆ S) ≤
      (sigma /
        (FiniteLaw.independentBits (fun _ : J ↦ sigma)
          (fun _ ↦ hsigma)).probability Good) ^ Q.card := by
  let L := FiniteLaw.independentBits (fun _ : J ↦ sigma)
    (fun _ ↦ hsigma)
  by_cases hQempty : Q = ∅
  · subst Q
    simpa using (L.conditionedSelectionLaw Good hGood selected).probability_le_one
      (fun S ↦ (∅ : Finset X) ⊆ S)
  · have hcard : 0 < Q.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hQempty)
    have hprobLe : L.probability Good ≤ 1 := L.probability_le_one Good
    have hpowLe : (L.probability Good) ^ Q.card ≤ L.probability Good :=
      pow_le_of_le_one zero_le hprobLe hcard.ne'
    have hscale : sigma ^ Q.card / L.probability Good ≤
        (sigma / L.probability Good) ^ Q.card := by
      rw [div_pow]
      gcongr
    exact (conditioned_encodedSelection_probability_subset_le sigma hsigma e
      Good hGood selected hselected Q).trans hscale

/-- Pointwise existence on a positive-probability good event can be converted
into a genuine output law by deterministic classical choice.  This is the
finite-law form used after the simultaneous robust-matching argument. -/
theorem exists_conditioned_encodedSelectionLaw
    {J X : Type*} [Fintype J] [Fintype X] [DecidableEq J] [DecidableEq X]
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (e : J ↪ X)
    (Good : (J → Bool) → Prop)
    (hGood : 0 < (FiniteLaw.independentBits (fun _ : J ↦ sigma)
      (fun _ ↦ hsigma)).probability Good)
    (Valid : Finset X → Prop)
    (hexists : ∀ ω, Good ω → ∃ S : Finset X,
      S ⊆ encodedReservoir e ω ∧ Valid S) :
    ∃ L : FiniteLaw (Finset X),
      L.SupportedOn Valid ∧
      ∀ Q : Finset X,
        L.probability (fun S ↦ Q ⊆ S) ≤
          sigma ^ Q.card /
            (FiniteLaw.independentBits (fun _ : J ↦ sigma)
              (fun _ ↦ hsigma)).probability Good := by
  classical
  let selected : (J → Bool) → Finset X := fun ω ↦
    if hω : Good ω then Classical.choose (hexists ω hω) else ∅
  have hselected : ∀ ω, Good ω → selected ω ⊆ encodedReservoir e ω := by
    intro ω hω
    simpa only [selected, dif_pos hω] using
      (Classical.choose_spec (hexists ω hω)).1
  have hvalid : ∀ ω, Good ω → Valid (selected ω) := by
    intro ω hω
    simpa only [selected, dif_pos hω] using
      (Classical.choose_spec (hexists ω hω)).2
  let L := (FiniteLaw.independentBits (fun _ : J ↦ sigma)
    (fun _ ↦ hsigma)).conditionedSelectionLaw Good hGood selected
  refine ⟨L, ?_, ?_⟩
  · exact FiniteLaw.conditionedSelectionLaw_supported _ Good hGood
      selected Valid hvalid
  · intro Q
    exact conditioned_encodedSelection_probability_subset_le sigma hsigma e
      Good hGood selected hselected Q

/-- Per-element form of `exists_conditioned_encodedSelectionLaw`, with the
conditioning loss absorbed into the joint-inclusion base. -/
theorem exists_conditioned_encodedSelectionLaw_pow
    {J X : Type*} [Fintype J] [Fintype X] [DecidableEq J] [DecidableEq X]
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (e : J ↪ X)
    (Good : (J → Bool) → Prop)
    (hGood : 0 < (FiniteLaw.independentBits (fun _ : J ↦ sigma)
      (fun _ ↦ hsigma)).probability Good)
    (Valid : Finset X → Prop)
    (hexists : ∀ ω, Good ω → ∃ S : Finset X,
      S ⊆ encodedReservoir e ω ∧ Valid S) :
    ∃ L : FiniteLaw (Finset X),
      L.SupportedOn Valid ∧
      ∀ Q : Finset X,
        L.probability (fun S ↦ Q ⊆ S) ≤
          (sigma /
            (FiniteLaw.independentBits (fun _ : J ↦ sigma)
              (fun _ ↦ hsigma)).probability Good) ^ Q.card := by
  classical
  let selected : (J → Bool) → Finset X := fun ω ↦
    if hω : Good ω then Classical.choose (hexists ω hω) else ∅
  have hselected : ∀ ω, Good ω → selected ω ⊆ encodedReservoir e ω := by
    intro ω hω
    simpa only [selected, dif_pos hω] using
      (Classical.choose_spec (hexists ω hω)).1
  have hvalid : ∀ ω, Good ω → Valid (selected ω) := by
    intro ω hω
    simpa only [selected, dif_pos hω] using
      (Classical.choose_spec (hexists ω hω)).2
  let L := (FiniteLaw.independentBits (fun _ : J ↦ sigma)
    (fun _ ↦ hsigma)).conditionedSelectionLaw Good hGood selected
  refine ⟨L, ?_, ?_⟩
  · exact FiniteLaw.conditionedSelectionLaw_supported _ Good hGood
      selected Valid hvalid
  · intro Q
    exact conditioned_encodedSelection_probability_subset_le_pow
      sigma hsigma e Good hGood selected hselected Q

end

end Erdos207
