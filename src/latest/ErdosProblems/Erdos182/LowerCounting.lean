/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos182.Foundations
import ErdosProblems.Erdos182.Probability
import Mathlib

/-!
# Finite counting for the layered lower-bound construction

The Pyber--Rödl--Szemerédi lower-bound construction chooses, independently for
every vertex of its first layer and every later layer, one target in that later
layer.  This file isolates the purely finite union-bound step.  Its hypotheses
are deliberately stated as cardinal inequalities: the analytic part of the
construction can therefore estimate each bad-event fibre without introducing
measure-theoretic infrastructure.
-/

namespace Erdos182

open scoped BigOperators Classical

noncomputable section


/-! ## Counting fixed coordinates

For the graph construction it is useful to regard all layer vertices as
members of one ambient type `V`.  A coordinate says which source/later-layer
pair is being chosen, and `allowed c` is the corresponding target layer.  We
use the partial-function type native to `Finset.pi`; since its domain is
`Finset.univ`, it contains exactly the same information as a total function.
-/

section FixedCoordinates

variable {C V : Type*} [Fintype C]

/-- A choice at every coordinate of the finite type `C`.  The proof argument
records that the coordinate belongs to `univ` and is propositionally
irrelevant. -/
abbrev FiniteChoiceOutcome (C V : Type*) [Fintype C] :=
  (c : C) → c ∈ (Finset.univ : Finset C) → V

/-- All coordinatewise choices with the value at `c` restricted to
`allowed c`. -/
def finiteChoiceSpace (allowed : C → Finset V) :
    Finset (FiniteChoiceOutcome C V) := by
  classical
  exact Finset.univ.pi allowed

@[simp]
lemma mem_finiteChoiceSpace {allowed : C → Finset V}
    {ω : FiniteChoiceOutcome C V} :
    ω ∈ finiteChoiceSpace allowed ↔
      ∀ c, ω c (Finset.mem_univ c) ∈ allowed c := by
  classical
  simp [finiteChoiceSpace]

/-- The sample-space cardinality is the product of the coordinate-set
cardinalities. -/
lemma card_finiteChoiceSpace (allowed : C → Finset V) :
    (finiteChoiceSpace allowed).card = ∏ c, (allowed c).card := by
  classical
  simp [finiteChoiceSpace]

/-- Restrict the coordinates in `D` to prescribed values. -/
def fixedChoiceSpace (allowed : C → Finset V) (D : Finset C) (value : C → V) :
    Finset (FiniteChoiceOutcome C V) := by
  classical
  exact Finset.univ.pi fun c ↦ if c ∈ D then {value c} else allowed c

lemma mem_fixedChoiceSpace {allowed : C → Finset V} {D : Finset C}
    {value : C → V} {ω : FiniteChoiceOutcome C V} :
    ω ∈ fixedChoiceSpace allowed D value ↔
      (∀ c ∈ D, ω c (Finset.mem_univ c) = value c) ∧
      (∀ c ∉ D, ω c (Finset.mem_univ c) ∈ allowed c) := by
  classical
  simp only [fixedChoiceSpace, Finset.mem_pi, Finset.mem_univ]
  constructor
  · intro h
    constructor
    · intro c hc
      simpa [hc] using h c
    · intro c hc
      simpa [hc] using h c
  · rintro ⟨hfixed, hfree⟩ c
    by_cases hc : c ∈ D
    · simpa [hc] using hfixed c hc
    · simpa [hc] using hfree c hc

/-- Prescribing allowed values gives a subset of the unrestricted choice
space. -/
lemma fixedChoiceSpace_subset (allowed : C → Finset V) (D : Finset C)
    (value : C → V) (hvalue : ∀ c ∈ D, value c ∈ allowed c) :
    fixedChoiceSpace allowed D value ⊆ finiteChoiceSpace allowed := by
  classical
  intro ω hω
  rw [mem_finiteChoiceSpace]
  obtain ⟨hfixed, hfree⟩ := mem_fixedChoiceSpace.mp hω
  intro c
  by_cases hc : c ∈ D
  · rw [hfixed c hc]
    exact hvalue c hc
  · exact hfree c hc

/-- Fixing `r` distinct coordinates costs at least a factor `b^r`, provided
each of their coordinate sets has cardinality at least `b`.  This
division-free form remains valid even when some unrestricted coordinate sets
are empty. -/
theorem card_fixedChoiceSpace_mul_pow_le
    (allowed : C → Finset V) (D : Finset C) (value : C → V) (b : ℕ)
    (hlower : ∀ c ∈ D, b ≤ (allowed c).card) :
    (fixedChoiceSpace allowed D value).card * b ^ D.card ≤
      (finiteChoiceSpace allowed).card := by
  classical
  rw [card_finiteChoiceSpace]
  simp only [fixedChoiceSpace, Finset.card_pi]
  calc
    (∏ c, (if c ∈ D then ({value c} : Finset V) else allowed c).card) * b ^ D.card =
        (∏ c, (if c ∈ D then ({value c} : Finset V) else allowed c).card) *
          (∏ c, if c ∈ D then b else 1) := by simp
    _ = ∏ c, (if c ∈ D then ({value c} : Finset V) else allowed c).card *
          (if c ∈ D then b else 1) := by rw [Finset.prod_mul_distrib]
    _ ≤ ∏ c, (allowed c).card := by
      apply Finset.prod_le_prod'
      intro c _
      by_cases hc : c ∈ D
      · simpa [hc] using hlower c hc
      · simp [hc]

/-- A finite family of coordinate prescriptions. -/
structure CoordinateDemand (C V : Type*) where
  coords : Finset C
  value : C → V

/-- Outcomes satisfying one coordinate prescription. -/
def CoordinateDemand.outcomes (allowed : C → Finset V)
    (d : CoordinateDemand C V) : Finset (FiniteChoiceOutcome C V) :=
  fixedChoiceSpace allowed d.coords d.value

/-- Union-bound estimate for a family of `r`-coordinate prescriptions.  This
is the exact counting statement behind the factor
`binomial(number-of-candidate-edges, r) / b^r`. -/
theorem card_biUnion_coordinateDemand_mul_pow_le
    (allowed : C → Finset V) (family : Finset (CoordinateDemand C V))
    (r b : ℕ)
    (hcard : ∀ d ∈ family, d.coords.card = r)
    (hlower : ∀ d ∈ family, ∀ c ∈ d.coords, b ≤ (allowed c).card) :
    (family.biUnion (CoordinateDemand.outcomes allowed)).card * b ^ r ≤
      family.card * (finiteChoiceSpace allowed).card := by
  classical
  calc
    (family.biUnion (CoordinateDemand.outcomes allowed)).card * b ^ r ≤
        (∑ d ∈ family, (d.outcomes allowed).card) * b ^ r :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ d ∈ family, (d.outcomes allowed).card * b ^ r := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _d ∈ family, (finiteChoiceSpace allowed).card := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← hcard d hd]
      exact card_fixedChoiceSpace_mul_pow_le allowed d.coords d.value b
        (hlower d hd)
    _ = family.card * (finiteChoiceSpace allowed).card := by simp

/-- If the prescription family itself is bounded by a binomial coefficient,
the usual choose factor follows immediately. -/
theorem card_biUnion_coordinateDemand_mul_pow_le_choose
    (allowed : C → Finset V) (family : Finset (CoordinateDemand C V))
    (edgeCount r b : ℕ)
    (hfamily : family.card ≤ edgeCount.choose r)
    (hcard : ∀ d ∈ family, d.coords.card = r)
    (hlower : ∀ d ∈ family, ∀ c ∈ d.coords, b ≤ (allowed c).card) :
    (family.biUnion (CoordinateDemand.outcomes allowed)).card * b ^ r ≤
      edgeCount.choose r * (finiteChoiceSpace allowed).card := by
  exact (card_biUnion_coordinateDemand_mul_pow_le allowed family r b hcard hlower).trans
    (Nat.mul_le_mul_right _ hfamily)

/-- A semantic bad event inherits the demand-family bound as soon as every
bad outcome supplies one of the coordinate prescriptions. -/
theorem card_bad_mul_pow_le_choose
    (allowed : C → Finset V) (bad : Finset (FiniteChoiceOutcome C V))
    (family : Finset (CoordinateDemand C V)) (edgeCount r b : ℕ)
    (hbad : bad ⊆ family.biUnion (CoordinateDemand.outcomes allowed))
    (hfamily : family.card ≤ edgeCount.choose r)
    (hcard : ∀ d ∈ family, d.coords.card = r)
    (hlower : ∀ d ∈ family, ∀ c ∈ d.coords, b ≤ (allowed c).card) :
    bad.card * b ^ r ≤
      edgeCount.choose r * (finiteChoiceSpace allowed).card := by
  calc
    bad.card * b ^ r ≤
        (family.biUnion (CoordinateDemand.outcomes allowed)).card * b ^ r :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hbad)
    _ ≤ edgeCount.choose r * (finiteChoiceSpace allowed).card :=
      card_biUnion_coordinateDemand_mul_pow_le_choose
        allowed family edgeCount r b hfamily hcard hlower

end FixedCoordinates


section CandidateVertexSets

variable {U C V : Type*} [Fintype U] [Fintype C]

/-- Union the bad outcomes first over at most `choose(x,2).choose r` demanded
edge sets for each `x`-vertex candidate, and then over the `n.choose x`
candidate vertex sets.  This is the precise division-free version of

`P(bad at size x) ≤ n.choose x * (x.choose 2).choose r / b^r`.
-/
theorem card_bad_candidate_sets_mul_pow_le
    (allowed : C → Finset V) (x r b : ℕ)
    (family : Finset U → Finset (CoordinateDemand C V))
    (hfamily : ∀ S ∈ (Finset.univ : Finset U).powersetCard x,
      (family S).card ≤ (x.choose 2).choose r)
    (hcard : ∀ S ∈ (Finset.univ : Finset U).powersetCard x,
      ∀ d ∈ family S, d.coords.card = r)
    (hlower : ∀ S ∈ (Finset.univ : Finset U).powersetCard x,
      ∀ d ∈ family S, ∀ c ∈ d.coords, b ≤ (allowed c).card) :
    (((Finset.univ : Finset U).powersetCard x).biUnion fun S ↦
        (family S).biUnion (CoordinateDemand.outcomes allowed)).card * b ^ r ≤
      (Fintype.card U).choose x * (x.choose 2).choose r *
        (finiteChoiceSpace allowed).card := by
  classical
  calc
    (((Finset.univ : Finset U).powersetCard x).biUnion fun S ↦
        (family S).biUnion (CoordinateDemand.outcomes allowed)).card * b ^ r ≤
        (∑ S ∈ (Finset.univ : Finset U).powersetCard x,
          ((family S).biUnion (CoordinateDemand.outcomes allowed)).card) * b ^ r :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ S ∈ (Finset.univ : Finset U).powersetCard x,
        ((family S).biUnion (CoordinateDemand.outcomes allowed)).card * b ^ r := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _S ∈ (Finset.univ : Finset U).powersetCard x,
        (x.choose 2).choose r * (finiteChoiceSpace allowed).card := by
      apply Finset.sum_le_sum
      intro S hS
      exact card_biUnion_coordinateDemand_mul_pow_le_choose
        allowed (family S) (x.choose 2) r b (hfamily S hS)
          (hcard S hS) (hlower S hS)
    _ = (Fintype.card U).choose x * (x.choose 2).choose r *
        (finiteChoiceSpace allowed).card := by
      simp [Nat.mul_assoc]

/-- Semantic version of `card_bad_candidate_sets_mul_pow_le`.  For each
candidate vertex set `S`, `bad S` may be defined directly in graph-theoretic
terms; `hcover` extracts the `r` selected edges that witness its density. -/
theorem card_semantic_bad_candidate_sets_mul_pow_le
    (allowed : C → Finset V) (x r b : ℕ)
    (bad : Finset U → Finset (FiniteChoiceOutcome C V))
    (family : Finset U → Finset (CoordinateDemand C V))
    (hcover : ∀ S ∈ (Finset.univ : Finset U).powersetCard x,
      bad S ⊆ (family S).biUnion (CoordinateDemand.outcomes allowed))
    (hfamily : ∀ S ∈ (Finset.univ : Finset U).powersetCard x,
      (family S).card ≤ (x.choose 2).choose r)
    (hcard : ∀ S ∈ (Finset.univ : Finset U).powersetCard x,
      ∀ d ∈ family S, d.coords.card = r)
    (hlower : ∀ S ∈ (Finset.univ : Finset U).powersetCard x,
      ∀ d ∈ family S, ∀ c ∈ d.coords, b ≤ (allowed c).card) :
    (((Finset.univ : Finset U).powersetCard x).biUnion bad).card * b ^ r ≤
      (Fintype.card U).choose x * (x.choose 2).choose r *
        (finiteChoiceSpace allowed).card := by
  calc
    (((Finset.univ : Finset U).powersetCard x).biUnion bad).card * b ^ r ≤
        (((Finset.univ : Finset U).powersetCard x).biUnion fun S ↦
          (family S).biUnion (CoordinateDemand.outcomes allowed)).card * b ^ r := by
      apply Nat.mul_le_mul_right
      apply Finset.card_le_card
      intro ω hω
      obtain ⟨S, hS, hωS⟩ := Finset.mem_biUnion.mp hω
      exact Finset.mem_biUnion.mpr ⟨S, hS, hcover S hS hωS⟩
    _ ≤ (Fintype.card U).choose x * (x.choose 2).choose r *
        (finiteChoiceSpace allowed).card :=
      card_bad_candidate_sets_mul_pow_le
        allowed x r b family hfamily hcard hlower

/-- If the numerical union-bound coefficient is strictly smaller than
`b^r`, an admissible layered choice avoids every demanded edge set attached
to every `x`-vertex candidate.  The nonemptiness assumption is normally
discharged by the positivity of all target-layer sizes. -/
theorem exists_choice_avoiding_bad_candidate_sets
    (allowed : C → Finset V) (x r b : ℕ)
    (family : Finset U → Finset (CoordinateDemand C V))
    (hfamily : ∀ S ∈ (Finset.univ : Finset U).powersetCard x,
      (family S).card ≤ (x.choose 2).choose r)
    (hcard : ∀ S ∈ (Finset.univ : Finset U).powersetCard x,
      ∀ d ∈ family S, d.coords.card = r)
    (hlower : ∀ S ∈ (Finset.univ : Finset U).powersetCard x,
      ∀ d ∈ family S, ∀ c ∈ d.coords, b ≤ (allowed c).card)
    (hcoeff : (Fintype.card U).choose x * (x.choose 2).choose r < b ^ r)
    (hspace : (finiteChoiceSpace allowed).Nonempty) :
    ∃ ω ∈ finiteChoiceSpace allowed,
      ∀ S ∈ (Finset.univ : Finset U).powersetCard x,
        ω ∉ (family S).biUnion (CoordinateDemand.outcomes allowed) := by
  classical
  let bad : Finset (FiniteChoiceOutcome C V) :=
    ((Finset.univ : Finset U).powersetCard x).biUnion fun S ↦
      (family S).biUnion (CoordinateDemand.outcomes allowed)
  have hbound : bad.card * b ^ r ≤
      (Fintype.card U).choose x * (x.choose 2).choose r *
        (finiteChoiceSpace allowed).card := by
    simpa [bad] using card_bad_candidate_sets_mul_pow_le
      allowed x r b family hfamily hcard hlower
  have hspacepos : 0 < (finiteChoiceSpace allowed).card :=
    Finset.card_pos.mpr hspace
  have hp : 0 < b ^ r := by
    exact (lt_of_le_of_lt (Nat.zero_le _) hcoeff)
  have hmul : bad.card * b ^ r <
      (finiteChoiceSpace allowed).card * b ^ r := by
    calc
      bad.card * b ^ r ≤
          ((Fintype.card U).choose x * (x.choose 2).choose r) *
            (finiteChoiceSpace allowed).card := hbound
      _ < b ^ r * (finiteChoiceSpace allowed).card :=
        (Nat.mul_lt_mul_right hspacepos).mpr hcoeff
      _ = (finiteChoiceSpace allowed).card * b ^ r := Nat.mul_comm _ _
  have hbadlt : bad.card < (finiteChoiceSpace allowed).card :=
    (Nat.mul_lt_mul_right hp).mp hmul
  have hnsub : ¬ finiteChoiceSpace allowed ⊆ bad := by
    intro hsub
    exact (Nat.not_lt_of_ge (Finset.card_le_card hsub)) hbadlt
  have hex : ∃ ω, ω ∈ finiteChoiceSpace allowed ∧ ω ∉ bad := by
    by_contra hnot
    apply hnsub
    intro ω hωspace
    by_contra hωbad
    exact hnot ⟨ω, hωspace, hωbad⟩
  obtain ⟨ω, hωspace, hωbad⟩ := hex
  refine ⟨ω, hωspace, ?_⟩
  intro S hS hωS
  apply hωbad
  exact Finset.mem_biUnion.mpr ⟨S, hS, hωS⟩

end CandidateVertexSets

/-! ## Combining all scales -/

section MultiEventUnion

variable {Ω I : Type*} [Fintype I]

/-- A finite union of events of total relative cardinality less than one does
not cover a nonempty finite sample space.  This is the cardinal form of the
union bound used to combine every layer and every possible set size. -/
theorem exists_mem_avoiding_of_sum_card_div_lt_one
    (space : Finset Ω) (bad : I → Finset Ω)
    (hspace : space.Nonempty)
    (hsum : (∑ i, ((bad i).card : ℝ) / space.card) < 1) :
    ∃ ω ∈ space, ∀ i, ω ∉ bad i := by
  classical
  have hspacepos : (0 : ℝ) < space.card := by
    exact_mod_cast Finset.card_pos.mpr hspace
  have hcardUnion : ((Finset.univ : Finset I).biUnion bad).card ≤ ∑ i, (bad i).card :=
    Finset.card_biUnion_le
  have hsumCard : ((∑ i, (bad i).card : ℕ) : ℝ) < space.card := by
    have hrewrite : (∑ i, ((bad i).card : ℝ) / space.card) =
        ((∑ i, (bad i).card : ℕ) : ℝ) / space.card := by
      rw [Nat.cast_sum]
      simp_rw [Finset.sum_div]
    rw [hrewrite, div_lt_one hspacepos] at hsum
    exact hsum
  have hunionlt : ((Finset.univ : Finset I).biUnion bad).card < space.card := by
    exact_mod_cast (lt_of_le_of_lt hcardUnion (by exact_mod_cast hsumCard))
  have hnsub : ¬space ⊆ (Finset.univ : Finset I).biUnion bad := by
    intro h
    exact (Nat.not_lt_of_ge (Finset.card_le_card h)) hunionlt
  have hex : ∃ ω, ω ∈ space ∧ ω ∉ (Finset.univ : Finset I).biUnion bad := by
    by_contra hno
    apply hnsub
    intro ω hωspace
    by_contra hωbad
    exact hno ⟨ω, hωspace, hωbad⟩
  obtain ⟨ω, hωspace, hω⟩ := hex
  refine ⟨ω, hωspace, ?_⟩
  intro i hi
  exact hω (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)

/-- A convenient consequence when each event is bounded after multiplying by
its own positive denominator. -/
theorem exists_mem_avoiding_of_mul_bounds
    (space : Finset Ω) (bad : I → Finset Ω) (numer denom : I → ℕ)
    (hspace : space.Nonempty)
    (hdenom : ∀ i, 0 < denom i)
    (hbound : ∀ i, (bad i).card * denom i ≤ numer i * space.card)
    (hsum : (∑ i, (numer i : ℝ) / denom i) < 1) :
    ∃ ω ∈ space, ∀ i, ω ∉ bad i := by
  apply exists_mem_avoiding_of_sum_card_div_lt_one space bad hspace
  calc
    (∑ i, ((bad i).card : ℝ) / space.card) ≤
        ∑ i, (numer i : ℝ) / denom i := by
      apply Finset.sum_le_sum
      intro i _
      have hspos : (0 : ℝ) < space.card := by
        exact_mod_cast Finset.card_pos.mpr hspace
      have hdpos : (0 : ℝ) < denom i := by exact_mod_cast hdenom i
      rw [div_le_div_iff₀ hspos hdpos]
      exact_mod_cast hbound i
    _ < 1 := hsum

end MultiEventUnion

end

end Erdos182
