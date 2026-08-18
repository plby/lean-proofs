/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Basic
import ErdosProblems.Erdos186.PZ.Reduction.BoundedContext
import ErdosProblems.Erdos186.PZ.Reduction.Definition9
import ErdosProblems.Erdos186.PZ.Reduction.Replacement

/-!
# Lemma 11: the finite irreducibility consequence

Pham--Zakharov's definition of irreducibility is expressed relative to the
subset-sum dimension and the canonical bounding GAP attached to a finite
set.  This file makes that logical interface explicit, including both
orientations `x-a` and `a-x`, and proves the whole formal implication called
Lemma 11 in the paper.

The functions `dimension` and `boundingSet` are parameters because their
construction is the preceding CFP structure theorem.  Importantly, the
irreducibility predicate quantifies over *every* sufficiently large subset;
it does not contain, or mention, a common subset sum.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

/-- The two deviation orientations used on the two sides of the
intersection argument. -/
inductive Orientation
  | forward
  | reverse
  deriving DecidableEq, Repr

/-- `x-a` in the forward orientation and `a-x` in the reverse orientation. -/
def orientedDeviation {d : ℕ} (o : Orientation)
    (a x : LatticePoint d) : LatticePoint d :=
  match o with
  | .forward => x - a
  | .reverse => a - x

/-- Apply one of the two deviation maps to a finite set. -/
def orientedTranslate {d : ℕ} (o : Orientation) (a : LatticePoint d)
    (X : Finset (LatticePoint d)) : Finset (LatticePoint d) :=
  X.image (orientedDeviation o a)

theorem orientedDeviation_injective {d : ℕ} (o : Orientation)
    (a : LatticePoint d) : Function.Injective (orientedDeviation o a) := by
  intro x y hxy
  cases o with
  | forward =>
      change x - a = y - a at hxy
      exact sub_left_injective hxy
  | reverse =>
      change a - x = a - y at hxy
      exact sub_right_injective hxy

@[simp] theorem card_orientedTranslate {d : ℕ} (o : Orientation)
    (a : LatticePoint d) (X : Finset (LatticePoint d)) :
    (orientedTranslate o a X).card = X.card := by
  classical
  exact Finset.card_image_of_injective _ (orientedDeviation_injective o a)

/-- The forward deviation set is exactly the translate used by the concrete
replacement definition.  This identifies the two independently introduced
pieces of notation, rather than treating Lemma 11 as an unrelated interface. -/
theorem orientedTranslate_forward_eq_reductionTranslate {d : ℕ}
    (a : LatticePoint d) (X : Finset (LatticePoint d)) :
    orientedTranslate .forward a X = Reduction.translate (-a) X := by
  classical
  ext y
  simp only [orientedTranslate, orientedDeviation, Reduction.translate,
    Finset.mem_image]
  constructor <;> rintro ⟨x, hx, rfl⟩
  · exact ⟨x, hx, by simp [sub_eq_add_neg]⟩
  · exact ⟨x, hx, by simp [sub_eq_add_neg]⟩

/-- The rank and volume part of Lemma 11 that follows directly from the
repository's concrete Definition 9.  It applies to an actual dense subset of
the selected CFP core and an actual translation point in the selected GAP. -/
theorem lemma11_forward_rank_volume_of_reduction_irreducible
    (choice : Reduction.StructureChoice) {d : ℕ}
    {A : Finset (LatticePoint d)} (hA : A.Nonempty) {delta gamma : ℝ}
    (hirr : Reduction.IsIrreducible choice A hA delta gamma)
    (X : Finset (LatticePoint d))
    (hXsub : X ⊆ (choice.state A hA).structuredCore)
    (hXne : X.Nonempty)
    (hdense : delta * (A.card : ℝ) ≤ (X.card : ℝ))
    (a : LatticePoint d)
    (ha : a ∈ (choice.state A hA).progression.carrier) :
    let shifted := Reduction.translate (-a) X
    let next := choice.state shifted
      (Reduction.translate_nonempty (-a) hXne)
    next.rank = (choice.state A hA).rank ∧
      gamma * ((choice.state A hA).progression.volume : ℝ) ≤
        (next.progression.volume : ℝ) := by
  exact hirr X hXsub hXne hdense a ha

/-! ## The current coordinate-level Definition 9 API -/

/-- The part of Lemma 11 not contained in coordinate irreducibility: the
newly selected bounding progression is controlled by a translate of a fixed
ambient box.  This is the exact containment furnished by the no-dimension-
increase branch of Lemmas 6--8 in the paper. -/
def CoordinateBoundingSetsControlled
    (selector : Reduction.CFPSelector) {d : ℕ}
    (A : Finset (LatticePoint d)) (hA : A.Nonempty)
    (delta : ℝ)
    (controlledBox : Finset
      (LatticePoint (selector.chosen A hA).dimension)) : Prop :=
  let S := selector.chosen A hA
  ∀ (X : Finset (LatticePoint S.dimension)),
    X ⊆ S.identifiedCore → (hXne : X.Nonempty) →
      delta * (A.card : ℝ) ≤ (X.card : ℝ) →
        ∀ x ∈ (gapCoefficientBox S.progression).carrier,
          let shifted := Reduction.identifiedTranslate X x
          let T := selector.chosen shifted
            (Reduction.identifiedTranslate_nonempty hXne x)
          ∃ t : LatticePoint S.dimension,
            T.progression.carrier ⊆ PZ.translate t controlledBox

/-- **Lemma 11 in the repository's canonical coordinate language.**

Coordinate irreducibility proves the rank equality and the lower bound for
the new bounding progression.  The independent bounding-set-control output
of Lemmas 6--8 proves its containment in a translate of the controlled box.
-/
theorem lemma11_of_coordinate_irreducible
    (selector : Reduction.CFPSelector) {d : ℕ}
    {A : Finset (LatticePoint d)} (hA : A.Nonempty)
    {delta gamma : ℝ}
    {controlledBox : Finset
      (LatticePoint (selector.chosen A hA).dimension)}
    (hirr : Reduction.IsCoordinateIrreducible selector A hA delta gamma)
    (hcontrolled : CoordinateBoundingSetsControlled selector A hA delta
      controlledBox)
    (X : Finset
      (LatticePoint (selector.chosen A hA).dimension))
    (hXsub : X ⊆ (selector.chosen A hA).identifiedCore)
    (hXne : X.Nonempty)
    (hdense : delta * (A.card : ℝ) ≤ (X.card : ℝ))
    (x : LatticePoint (selector.chosen A hA).dimension)
    (hx : x ∈ (gapCoefficientBox
      (selector.chosen A hA).progression).carrier) :
    let shifted := Reduction.identifiedTranslate X x
    let T := selector.chosen shifted
      (Reduction.identifiedTranslate_nonempty hXne x)
    T.dimension = (selector.chosen A hA).dimension ∧
      gamma * ((selector.chosen A hA).progression.volume : ℝ) ≤
        (T.progression.volume : ℝ) ∧
      ∃ t : LatticePoint (selector.chosen A hA).dimension,
        T.progression.carrier ⊆ PZ.translate t controlledBox := by
  have hrankVolume := hirr X hXsub hXne hdense x hx
  have hbox := hcontrolled X hXsub hXne hdense x hx
  exact ⟨hrankVolume.1, hrankVolume.2, hbox⟩

/-- Bounding-set control in the genuine bounded CFP context.  Eligibility of
each shifted input is explicit, so this statement never asks the analytic
CFP theorem to select a witness outside its domain. -/
def BoundedCoordinateBoundingSetsControlled
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    (A : Finset (LatticePoint d)) (hA : selector.Eligible A)
    (delta : ℝ)
    (controlledBox : Finset
      (LatticePoint (selector.chosen A hA).dimension)) : Prop :=
  let S := selector.chosen A hA
  ∀ (X : Finset (LatticePoint S.dimension)),
    X ⊆ S.identifiedCore → (hXne : X.Nonempty) →
      delta * (A.card : ℝ) ≤ (X.card : ℝ) →
        ∀ x ∈ (gapCoefficientBox S.progression).carrier,
          let shifted := Reduction.identifiedTranslate X x
          ∀ hshift : selector.Eligible shifted,
            let T := selector.chosen shifted hshift
            ∃ t : LatticePoint S.dimension,
            T.progression.carrier ⊆ PZ.translate t controlledBox

/-- The bounded irreducibility predicate is vacuous if the selector's domain
contains none of the translated dense candidates.  This is not a defect of
the predicate itself: eligibility is deliberately explicit.  It records the
precise extra closure obligation that a post-CFP construction must discharge
before it can use bounded coordinate irreducibility on either balanced pool.
-/
theorem boundedCoordinateIrreducible_of_no_eligible_candidates
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} (hA : selector.Eligible A)
    (delta gamma : ℝ)
    (hnone :
      ∀ (X : Finset
          (LatticePoint (selector.chosen A hA).dimension)),
        X ⊆ (selector.chosen A hA).identifiedCore → X.Nonempty →
        delta * (A.card : ℝ) ≤ (X.card : ℝ) →
        ∀ x ∈ (gapCoefficientBox
          (selector.chosen A hA).progression).carrier,
          ¬ selector.Eligible (Reduction.identifiedTranslate X x)) :
    Reduction.IsBoundedCoordinateIrreducible selector A hA delta gamma := by
  simp only [Reduction.IsBoundedCoordinateIrreducible]
  intro X hX hXne hdense x hx hshift
  exact (hnone X hX hXne hdense x hx hshift).elim

/-- Candidate-domain closure supplies the eligibility proof hidden behind
the bounded quantifier, so irreducibility yields an actual selected side
progression with the same dimension and the required volume lower bound.
This is the nonvacuous rank/volume part of Lemma 11 for one translated pool.
-/
theorem boundedCoordinateIrreducible_rank_volume_of_candidateClosed
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta gamma : ℝ}
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (X : Finset
      (LatticePoint (selector.chosen A hA).dimension))
    (hXsub : X ⊆ (selector.chosen A hA).identifiedCore)
    (hXne : X.Nonempty)
    (hdense : delta * (A.card : ℝ) ≤ (X.card : ℝ))
    (x : LatticePoint (selector.chosen A hA).dimension)
    (hx : x ∈ (gapCoefficientBox
      (selector.chosen A hA).progression).carrier) :
    let shifted := Reduction.identifiedTranslate X x
    ∃ hshift : selector.Eligible shifted,
      let T := selector.chosen shifted hshift
      T.dimension = (selector.chosen A hA).dimension ∧
        gamma * ((selector.chosen A hA).progression.volume : ℝ) ≤
          (T.progression.volume : ℝ) := by
  let shifted := Reduction.identifiedTranslate X x
  have hshift : selector.Eligible shifted :=
    hclosed X hXsub hXne hdense x hx
  refine ⟨hshift, ?_⟩
  exact Reduction.boundedCoordinateIrreducible_rank_volume selector hirr
    X hXsub hXne hdense x hx hshift

/-- Bounded-context form of Lemma 11.  The rank/volume clauses are eliminated
from `IsBoundedCoordinateIrreducible`; only the independent bounding-set
containment from Lemmas 6--8 is supplied separately. -/
theorem lemma11_of_boundedCoordinateIrreducible
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} (hA : selector.Eligible A)
    {delta gamma : ℝ}
    {controlledBox : Finset
      (LatticePoint (selector.chosen A hA).dimension)}
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hcontrolled : BoundedCoordinateBoundingSetsControlled selector A hA
      delta controlledBox)
    (X : Finset
      (LatticePoint (selector.chosen A hA).dimension))
    (hXsub : X ⊆ (selector.chosen A hA).identifiedCore)
    (hXne : X.Nonempty)
    (hdense : delta * (A.card : ℝ) ≤ (X.card : ℝ))
    (x : LatticePoint (selector.chosen A hA).dimension)
    (hx : x ∈ (gapCoefficientBox
      (selector.chosen A hA).progression).carrier)
    (hshift : selector.Eligible (Reduction.identifiedTranslate X x)) :
    let T := selector.chosen (Reduction.identifiedTranslate X x) hshift
    T.dimension = (selector.chosen A hA).dimension ∧
      gamma * ((selector.chosen A hA).progression.volume : ℝ) ≤
        (T.progression.volume : ℝ) ∧
      ∃ t : LatticePoint (selector.chosen A hA).dimension,
        T.progression.carrier ⊆ PZ.translate t controlledBox := by
  have hrankVolume := Reduction.boundedCoordinateIrreducible_rank_volume
    selector hirr X hXsub hXne hdense x hx hshift
  have hbox := hcontrolled X hXsub hXne hdense x hx hshift
  exact ⟨hrankVolume.1, hrankVolume.2, hbox⟩

/-- The exact quantifier pattern of `(delta,gamma)`-irreducibility needed
in Lemma 11.  `referencePopulation` is the population used in the density
cutoff (the original set in the paper), while `referenceBoxSize` is `|B|`.
-/
def IsPZIrreducible {d : ℕ}
    (dimension : Finset (LatticePoint d) → ℕ)
    (boundingSet : Finset (LatticePoint d) → Finset (LatticePoint d))
    (delta gamma : ℝ) (referencePopulation referenceBoxSize rank : ℕ)
    (A : Finset (LatticePoint d)) : Prop :=
  ∀ (X : Finset (LatticePoint d)), X ⊆ A →
    ∀ (a : LatticePoint d) (o : Orientation),
      delta * referencePopulation < X.card →
        dimension (orientedTranslate o a X) = rank ∧
        gamma * referenceBoxSize ≤
          (boundingSet (orientedTranslate o a X)).card

/-- The independent no-dimension-increase output used in the final clause
of Lemma 11: every relevant bounding set is contained in a translate of a
fixed enlarged reference box `controlledBox`. -/
def BoundingSetsControlled {d : ℕ}
    (boundingSet : Finset (LatticePoint d) → Finset (LatticePoint d))
    (controlledBox A : Finset (LatticePoint d)) : Prop :=
  ∀ (X : Finset (LatticePoint d)), X ⊆ A →
    ∀ (a : LatticePoint d) (o : Orientation),
      ∃ t : LatticePoint d,
        boundingSet (orientedTranslate o a X) ⊆ PZ.translate t controlledBox

/-- **Pham--Zakharov Lemma 11 (exact finite implication).**

Two large disjoint pools have full subset-sum dimension, their canonical
bounding sets occupy at least a `gamma` fraction of the reference box, and
each lies in a translate of the controlled enlargement of that box.
-/
theorem lemma11_of_irreducible {d : ℕ}
    {dimension : Finset (LatticePoint d) → ℕ}
    {boundingSet : Finset (LatticePoint d) → Finset (LatticePoint d)}
    {delta gamma : ℝ} {referencePopulation referenceBoxSize rank : ℕ}
    {A A₁ A₂ controlledBox : Finset (LatticePoint d)}
    {a : LatticePoint d}
    (hirr : IsPZIrreducible dimension boundingSet delta gamma
      referencePopulation referenceBoxSize rank A)
    (hcontrolled : BoundingSetsControlled boundingSet controlledBox A)
    (hA₁ : A₁ ⊆ A) (hA₂ : A₂ ⊆ A)
    (hlarge₁ : delta * referencePopulation < A₁.card)
    (hlarge₂ : delta * referencePopulation < A₂.card) :
    dimension (orientedTranslate .forward a A₁) = rank ∧
      dimension (orientedTranslate .reverse a A₂) = rank ∧
      gamma * referenceBoxSize ≤
        (boundingSet (orientedTranslate .forward a A₁)).card ∧
      gamma * referenceBoxSize ≤
        (boundingSet (orientedTranslate .reverse a A₂)).card ∧
      (∃ t, boundingSet (orientedTranslate .forward a A₁) ⊆
        PZ.translate t controlledBox) ∧
      (∃ t, boundingSet (orientedTranslate .reverse a A₂) ⊆
        PZ.translate t controlledBox) := by
  have h₁ := hirr A₁ hA₁ a .forward hlarge₁
  have h₂ := hirr A₂ hA₂ a .reverse hlarge₂
  exact ⟨h₁.1, h₂.1, h₁.2, h₂.2,
    hcontrolled A₁ hA₁ a .forward,
    hcontrolled A₂ hA₂ a .reverse⟩

/-- The balanced cardinality lower bound is enough for Lemma 11 whenever
the density threshold lies strictly below it. -/
theorem lemma11_of_balanced_partition {d : ℕ}
    {dimension : Finset (LatticePoint d) → ℕ}
    {boundingSet : Finset (LatticePoint d) → Finset (LatticePoint d)}
    {delta gamma : ℝ} {referencePopulation referenceBoxSize rank : ℕ}
    {A A₁ A₂ controlledBox : Finset (LatticePoint d)}
    {a : LatticePoint d}
    (hirr : IsPZIrreducible dimension boundingSet delta gamma
      referencePopulation referenceBoxSize rank A)
    (hcontrolled : BoundingSetsControlled boundingSet controlledBox A)
    (hA₁ : A₁ ⊆ A) (hA₂ : A₂ ⊆ A)
    (hthreshold : delta * referencePopulation <
      (((A.card - 2) / 2 : ℕ) : ℝ))
    (hcard₁ : (A.card - 2) / 2 ≤ A₁.card)
    (hcard₂ : (A.card - 2) / 2 ≤ A₂.card) :
    dimension (orientedTranslate .forward a A₁) = rank ∧
      dimension (orientedTranslate .reverse a A₂) = rank ∧
      gamma * referenceBoxSize ≤
        (boundingSet (orientedTranslate .forward a A₁)).card ∧
      gamma * referenceBoxSize ≤
        (boundingSet (orientedTranslate .reverse a A₂)).card ∧
      (∃ t, boundingSet (orientedTranslate .forward a A₁) ⊆
        PZ.translate t controlledBox) ∧
      (∃ t, boundingSet (orientedTranslate .reverse a A₂) ⊆
        PZ.translate t controlledBox) := by
  apply lemma11_of_irreducible hirr hcontrolled hA₁ hA₂
  · exact hthreshold.trans_le (by exact_mod_cast hcard₁)
  · exact hthreshold.trans_le (by exact_mod_cast hcard₂)

end

end Erdos186.PZ.Intersection
