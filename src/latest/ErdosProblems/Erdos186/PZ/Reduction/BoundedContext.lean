/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Main
import ErdosProblems.Erdos186.PZ.Reduction.Definition9

/-!
# A bounded CFP context for the Pham--Zakharov reduction

The structure theorem is not applicable to every finite lattice set with
arbitrary parameters.  This file packages exactly the uniform constants and
the hypotheses of `CFP.NonemptyHigherDimensionalCorollary5`.  In particular, the
selector used below is defined only on an explicit predicate of eligible
inputs.  Thus none of the irreducibility statements assumes a CFP witness for
all finite sets.
-/

namespace Erdos186.PZ.Reduction

noncomputable section

/-- Uniform choices of the constants in the all-dimensional CFP corollary.
The constants may depend on the ambient dimension, `beta`, and `eta`, but not
on the box, set, or scale. -/
structure HigherDimensionalContext (β η : ℝ) where
  scaleNum : ℕ → ℕ
  scaleDen : ℕ → ℕ
  rankBound : ℕ → ℕ
  lossConstant : ℕ → ℕ
  scaleNum_pos : ∀ d, 0 < scaleNum d
  scaleDen_pos : ∀ d, 0 < scaleDen d
  lossConstant_pos : ∀ d, 0 < lossConstant d
  produce : ∀ {d : ℕ} (B : CFP.IntegerBox d)
      (A : Finset (LatticePoint d)) (s : ℕ),
    A.Nonempty →
    A ⊆ B.carrier →
    (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) β →
    Real.rpow (A.card : ℝ) η ≤ (s : ℝ) →
    (scaleDen d : ℝ) * (s : ℝ) * Real.logb 2 (A.card : ℝ) ≤
      (scaleNum d : ℝ) * (A.card : ℝ) →
    ∃ k loss : ℕ,
      Nonempty (CFP.FixedScaleWitness A s (rankBound d) k loss
        (scaleNum d) (scaleDen d)) ∧
      (loss : ℝ) ≤ (lossConstant d : ℝ) * (s : ℝ) *
        Real.logb 2 (A.card : ℝ) + 1

/-- A proof of the genuine higher-dimensional CFP statement supplies the
uniform context used by the reduction. -/
theorem exists_higherDimensionalContext
    (hCFP : CFP.NonemptyHigherDimensionalCorollary5)
    {β η : ℝ} (hβ : 1 < β) (hη : 0 < η) (hη1 : η < 1) :
    Nonempty (HigherDimensionalContext β η) := by
  classical
  have hex : ∀ d : ℕ, ∃ scaleNum scaleDen D lossConstant : ℕ,
      0 < scaleNum ∧ 0 < scaleDen ∧ 0 < lossConstant ∧
      ∀ (B : CFP.IntegerBox d) (A : Finset (LatticePoint d)) (s : ℕ),
        A.Nonempty →
        A ⊆ B.carrier →
        (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) β →
        Real.rpow (A.card : ℝ) η ≤ (s : ℝ) →
        (scaleDen : ℝ) * (s : ℝ) * Real.logb 2 (A.card : ℝ) ≤
          (scaleNum : ℝ) * (A.card : ℝ) →
        ∃ k loss : ℕ,
          Nonempty (CFP.FixedScaleWitness A s D k loss scaleNum scaleDen) ∧
          (loss : ℝ) ≤ (lossConstant : ℝ) * (s : ℝ) *
            Real.logb 2 (A.card : ℝ) + 1 :=
    fun d ↦ hCFP d β η hβ hη hη1
  choose scaleNum scaleDen rankBound lossConstant h using hex
  exact ⟨{
    scaleNum := scaleNum
    scaleDen := scaleDen
    rankBound := rankBound
    lossConstant := lossConstant
    scaleNum_pos := fun d ↦ (h d).1
    scaleDen_pos := fun d ↦ (h d).2.1
    lossConstant_pos := fun d ↦ (h d).2.2.1
    produce := fun B A s hnonempty hsub hbox hlower hupper ↦
      (h _).2.2.2 B A s hnonempty hsub hbox hlower hupper }⟩

/-- One input on which the fixed-parameter CFP corollary is applicable. -/
structure EligibleInput {β η : ℝ} (C : HigherDimensionalContext β η)
    {d : ℕ} (A : Finset (LatticePoint d)) where
  box : CFP.IntegerBox d
  scale : ℕ
  nonempty : A.Nonempty
  subset_box : A ⊆ box.carrier
  box_card_le : (box.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) β
  scale_lower : Real.rpow (A.card : ℝ) η ≤ (scale : ℝ)
  scale_upper : (C.scaleDen d : ℝ) * (scale : ℝ) *
      Real.logb 2 (A.card : ℝ) ≤ (C.scaleNum d : ℝ) * (A.card : ℝ)

/-- The fully quantified output selected at one eligible input, including the
loss estimate which is not part of `EnhancedCFPWitness`. -/
structure BoundedSelection {β η : ℝ} (C : HigherDimensionalContext β η)
    {d : ℕ} {A : Finset (LatticePoint d)} (I : EligibleInput C A) where
  dilation : ℕ
  loss : ℕ
  witness : CFP.FixedScaleWitness A I.scale (C.rankBound d) dilation loss
    (C.scaleNum d) (C.scaleDen d)
  loss_le : (loss : ℝ) ≤ (C.lossConstant d : ℝ) * (I.scale : ℝ) *
    Real.logb 2 (A.card : ℝ) + 1

namespace EligibleInput

variable {β η : ℝ} {C : HigherDimensionalContext β η}
  {d : ℕ} {A : Finset (LatticePoint d)}

/-- Select the bounded CFP output.  The only classical choice here eliminates
the existential conclusion of `NonemptyHigherDimensionalCorollary5`. -/
def selection (I : EligibleInput C A) : BoundedSelection C I := by
  classical
  let hex := C.produce I.box A I.scale I.nonempty I.subset_box I.box_card_le
    I.scale_lower I.scale_upper
  let k := Classical.choose hex
  let hk := Classical.choose_spec hex
  let loss := Classical.choose hk
  let hout := Classical.choose_spec hk
  exact {
    dilation := k
    loss := loss
    witness := Classical.choice hout.1
    loss_le := hout.2 }

/-- Forget the fixed constants and loss estimate, retaining the selected CFP
object consumed by the coordinate reduction. -/
def selectedCFP (I : EligibleInput C A) : SelectedCFP A where
  reserveBound := I.scale
  rankBound := C.rankBound d
  dilation := I.selection.dilation
  loss := I.selection.loss
  witness := I.selection.witness.enhanced

@[simp] theorem selectedCFP_scaleNum (I : EligibleInput C A) :
    I.selectedCFP.witness.scaleNum = C.scaleNum d :=
  I.selection.witness.scaleNum_eq

@[simp] theorem selectedCFP_scaleDen (I : EligibleInput C A) :
    I.selectedCFP.witness.scaleDen = C.scaleDen d :=
  I.selection.witness.scaleDen_eq

theorem selectedCFP_loss_le (I : EligibleInput C A) :
    (I.selectedCFP.loss : ℝ) ≤ (C.lossConstant d : ℝ) * (I.scale : ℝ) *
      Real.logb 2 (A.card : ℝ) + 1 :=
  I.selection.loss_le

end EligibleInput

/-- A canonical selector on a stated domain of eligible finite sets.  Unlike
`CFPSelector`, it has no output at an ineligible set. -/
structure BoundedCFPSelector {β η : ℝ} (C : HigherDimensionalContext β η) where
  Eligible : ∀ {d : ℕ}, Finset (LatticePoint d) → Prop
  input : ∀ {d : ℕ} (A : Finset (LatticePoint d)), Eligible A →
    EligibleInput C A

namespace BoundedCFPSelector

variable {β η : ℝ} {C : HigherDimensionalContext β η}
  (selector : BoundedCFPSelector C)

/-- The canonical selected witness at an eligible set. -/
def chosen {d : ℕ} (A : Finset (LatticePoint d))
    (hA : selector.Eligible A) : SelectedCFP A :=
  (selector.input A hA).selectedCFP

theorem eligible_nonempty {d : ℕ} {A : Finset (LatticePoint d)}
    (hA : selector.Eligible A) : A.Nonempty :=
  (selector.input A hA).nonempty

/-- Every selected CFP scale is at least the prescribed power of the current
population.  Lemma 10 uses exponent `1 - epsilon` throughout its run. -/
def UsesScaleExponent (exponent : ℝ) : Prop :=
  ∀ {d : ℕ} (A : Finset (LatticePoint d))
    (hA : selector.Eligible A),
    Real.rpow (A.card : ℝ) exponent ≤
      ((selector.input A hA).scale : ℝ)

/-- At one selected input, the selector's domain contains every dense
coordinate candidate appearing in Definition 9.  This is the local closure
needed to turn bounded irreducibility into the source's nonvacuous
irreducibility conclusion. -/
def CandidateClosedAt {d : ℕ} (A : Finset (LatticePoint d))
    (hA : selector.Eligible A) (δ : ℝ) : Prop :=
  let S := selector.chosen A hA
  ∀ (X : Finset (BoxPoint S.dimension)),
    X ⊆ S.identifiedCore → X.Nonempty →
    δ * (A.card : ℝ) ≤ (X.card : ℝ) →
    ∀ x ∈ (gapCoefficientBox S.progression).carrier,
      selector.Eligible (identifiedTranslate X x)

/-- A stronger global closure condition, useful when a selector is defined
on a class known a priori to be stable under every coordinate candidate. -/
def CandidateClosed (δ : ℝ) : Prop :=
  ∀ {d : ℕ} (A : Finset (LatticePoint d))
    (hA : selector.Eligible A), selector.CandidateClosedAt A hA δ

/-- No subset of the selected core can contain more than a `δ` fraction of
the input when `δ > 1`. -/
theorem not_dense_candidate_of_one_lt {d : ℕ}
    (A : Finset (LatticePoint d)) (hA : selector.Eligible A)
    {δ : ℝ} (hδ : 1 < δ)
    (X : Finset (BoxPoint (selector.chosen A hA).dimension))
    (hX : X ⊆ (selector.chosen A hA).identifiedCore) :
    ¬ δ * (A.card : ℝ) ≤ (X.card : ℝ) := by
  have hcard : X.card ≤ A.card := by
    calc
      X.card ≤ (selector.chosen A hA).identifiedCore.card :=
        Finset.card_le_card hX
      _ = (selector.chosen A hA).core.card :=
        (selector.chosen A hA).card_identifiedCore
      _ ≤ A.card := Finset.card_le_card
        (selector.chosen A hA).witness.core_subset
  have hcardReal : (X.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hcard
  have hApos : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast (selector.eligible_nonempty hA).card_pos
  intro hdense
  nlinarith

/-- Local candidate closure is likewise vacuous for `δ > 1`. -/
theorem candidateClosedAt_of_one_lt_delta {d : ℕ}
    (A : Finset (LatticePoint d)) (hA : selector.Eligible A)
    {δ : ℝ} (hδ : 1 < δ) :
    selector.CandidateClosedAt A hA δ := by
  intro X hX _hXne hdense
  exact False.elim ((selector.not_dense_candidate_of_one_lt
    A hA hδ X hX) hdense)

end BoundedCFPSelector

/-- The canonical bounded selector attached to a context: a set is in its
domain precisely when the four analytic CFP hypotheses, a containing box,
and a positive-cardinality proof have actually been supplied. -/
def HigherDimensionalContext.canonicalSelector {β η : ℝ}
    (C : HigherDimensionalContext β η) : BoundedCFPSelector C where
  Eligible A := Nonempty (EligibleInput C A)
  input _ hA := Classical.choice hA

/-- Definition 9 restricted exactly to the domain on which the analytic CFP
hypotheses have been verified.  The shifted set is quantified together with
its eligibility proof; no witness is requested outside that domain. -/
def IsBoundedCoordinateIrreducible {β η : ℝ}
    {C : HigherDimensionalContext β η} (selector : BoundedCFPSelector C)
    {d : ℕ} (A : Finset (LatticePoint d))
    (hA : selector.Eligible A) (δ γ : ℝ) : Prop :=
  let S := selector.chosen A hA
  ∀ (X : Finset (BoxPoint S.dimension)),
    X ⊆ S.identifiedCore → (hXne : X.Nonempty) →
      δ * (A.card : ℝ) ≤ (X.card : ℝ) →
        ∀ x ∈ (gapCoefficientBox S.progression).carrier,
          let shifted := identifiedTranslate X x
          ∀ hshift : selector.Eligible shifted,
            let T := selector.chosen shifted hshift
            T.dimension = S.dimension ∧
              γ * (S.progression.volume : ℝ) ≤
                (T.progression.volume : ℝ)

/-- For `δ > 1`, bounded coordinate irreducibility is immediate because
there are no dense candidates. -/
theorem BoundedCFPSelector.irreducible_of_one_lt_delta {β η : ℝ}
    {C : HigherDimensionalContext β η} (selector : BoundedCFPSelector C)
    {d : ℕ} (A : Finset (LatticePoint d)) (hA : selector.Eligible A)
    {δ γ : ℝ} (hδ : 1 < δ) :
    IsBoundedCoordinateIrreducible selector A hA δ γ := by
  intro X hX _hXne hdense
  exact False.elim ((selector.not_dense_candidate_of_one_lt
    A hA hδ X hX) hdense)

/-- Elimination form intended for the intersection argument (Lemma 11): an
eligible dense translated subset has the same selected rank and the required
GAP-volume lower bound. -/
theorem boundedCoordinateIrreducible_rank_volume {β η : ℝ}
    {C : HigherDimensionalContext β η} (selector : BoundedCFPSelector C)
    {d : ℕ} {A : Finset (LatticePoint d)}
    {hA : selector.Eligible A} {δ γ : ℝ}
    (hirr : IsBoundedCoordinateIrreducible selector A hA δ γ)
    (X : Finset (BoxPoint (selector.chosen A hA).dimension))
    (hXsub : X ⊆ (selector.chosen A hA).identifiedCore)
    (hXne : X.Nonempty)
    (hdense : δ * (A.card : ℝ) ≤ (X.card : ℝ))
    (x : BoxPoint (selector.chosen A hA).dimension)
    (hx : x ∈
      (gapCoefficientBox (selector.chosen A hA).progression).carrier)
    (hshift : selector.Eligible (identifiedTranslate X x)) :
    let T := selector.chosen (identifiedTranslate X x) hshift
    T.dimension = (selector.chosen A hA).dimension ∧
      γ * ((selector.chosen A hA).progression.volume : ℝ) ≤
        (T.progression.volume : ℝ) := by
  exact hirr X hXsub hXne hdense x hx hshift

/-- Nonvacuous elimination form of Definition 9.  Local candidate closure
constructs the analytic input for every dense translated subset, after which
bounded irreducibility gives the selected-rank equality and GAP-volume lower
bound. -/
theorem closedBoundedCoordinateIrreducible_rank_volume {β η : ℝ}
    {C : HigherDimensionalContext β η} (selector : BoundedCFPSelector C)
    {d : ℕ} {A : Finset (LatticePoint d)}
    {hA : selector.Eligible A} {δ γ : ℝ}
    (hclosed : selector.CandidateClosedAt A hA δ)
    (hirr : IsBoundedCoordinateIrreducible selector A hA δ γ)
    (X : Finset (BoxPoint (selector.chosen A hA).dimension))
    (hXsub : X ⊆ (selector.chosen A hA).identifiedCore)
    (hXne : X.Nonempty)
    (hdense : δ * (A.card : ℝ) ≤ (X.card : ℝ))
    (x : BoxPoint (selector.chosen A hA).dimension)
    (hx : x ∈
      (gapCoefficientBox (selector.chosen A hA).progression).carrier) :
    ∃ hshift : selector.Eligible (identifiedTranslate X x),
      let T := selector.chosen (identifiedTranslate X x) hshift
      T.dimension = (selector.chosen A hA).dimension ∧
        γ * ((selector.chosen A hA).progression.volume : ℝ) ≤
          (T.progression.volume : ℝ) := by
  let hshift : selector.Eligible (identifiedTranslate X x) :=
    hclosed X hXsub hXne hdense x hx
  exact ⟨hshift,
    hirr X hXsub hXne hdense x hx hshift⟩

/-- Concrete failure of bounded Definition 9. -/
structure BoundedIrreducibilityFailure {β η : ℝ}
    {C : HigherDimensionalContext β η} (selector : BoundedCFPSelector C)
    {d : ℕ} (A : Finset (LatticePoint d))
    (hA : selector.Eligible A) (δ γ : ℝ) where
  retained : Finset (BoxPoint (selector.chosen A hA).dimension)
  retained_subset : retained ⊆ (selector.chosen A hA).identifiedCore
  retained_nonempty : retained.Nonempty
  dense : δ * (A.card : ℝ) ≤ (retained.card : ℝ)
  translationPoint : BoxPoint (selector.chosen A hA).dimension
  translationPoint_mem : translationPoint ∈
    (gapCoefficientBox (selector.chosen A hA).progression).carrier
  shifted_eligible : selector.Eligible
    (identifiedTranslate retained translationPoint)
  fails :
    let T := selector.chosen (identifiedTranslate retained translationPoint)
      shifted_eligible
    T.dimension ≠ (selector.chosen A hA).dimension ∨
      (T.progression.volume : ℝ) <
        γ * ((selector.chosen A hA).progression.volume : ℝ)

/-- Negating bounded Definition 9 produces an actual eligible replacement,
and conversely. -/
theorem not_boundedCoordinateIrreducible_iff {β η : ℝ}
    {C : HigherDimensionalContext β η} (selector : BoundedCFPSelector C)
    {d : ℕ} (A : Finset (LatticePoint d))
    (hA : selector.Eligible A) (δ γ : ℝ) :
    ¬ IsBoundedCoordinateIrreducible selector A hA δ γ ↔
      Nonempty (BoundedIrreducibilityFailure selector A hA δ γ) := by
  classical
  let S := selector.chosen A hA
  constructor
  · intro hnot
    simp only [IsBoundedCoordinateIrreducible] at hnot
    push Not at hnot
    obtain ⟨X, hXsub, hXne, hdense, x, hx, hshift, hfail⟩ := hnot
    refine ⟨{
      retained := X
      retained_subset := hXsub
      retained_nonempty := hXne
      dense := hdense
      translationPoint := x
      translationPoint_mem := hx
      shifted_eligible := hshift
      fails := ?_ }⟩
    dsimp only
    by_cases hdim :
        (selector.chosen (identifiedTranslate X x) hshift).dimension =
          S.dimension
    · exact Or.inr (hfail hdim)
    · exact Or.inl hdim
  · rintro ⟨F⟩ hirr
    have hgood := hirr F.retained F.retained_subset F.retained_nonempty
      F.dense F.translationPoint F.translationPoint_mem F.shifted_eligible
    rcases F.fails with hdim | hvolume
    · exact hdim hgood.1
    · exact (not_lt_of_ge hgood.2) hvolume

namespace BoundedIrreducibilityFailure

variable {β η : ℝ} {C : HigherDimensionalContext β η}
  {selector : BoundedCFPSelector C} {d : ℕ}
  {A : Finset (LatticePoint d)} {hA : selector.Eligible A} {δ γ : ℝ}
  (F : BoundedIrreducibilityFailure selector A hA δ γ)

def nextPoints :
    Finset (BoxPoint (selector.chosen A hA).dimension) :=
  identifiedTranslate F.retained F.translationPoint

@[simp] theorem card_nextPoints : F.nextPoints.card = F.retained.card := by
  simp [nextPoints]

theorem nextPoints_nonempty : F.nextPoints.Nonempty :=
  identifiedTranslate_nonempty F.retained_nonempty F.translationPoint

theorem nextPoints_nonaveraging (hNA : IsBoxNonaveraging A) :
    IsBoxNonaveraging F.nextPoints := by
  have hcore : IsBoxNonaveraging
      (selector.chosen A hA).identifiedCore :=
    (selector.chosen A hA).identifiedCore_nonaveraging hNA
  exact PZ.isBoxNonaveraging_translate (-F.translationPoint)
    (PZ.isBoxNonaveraging_mono hcore F.retained_subset)

theorem dense_nextPoints :
    δ * (A.card : ℝ) ≤ (F.nextPoints.card : ℝ) := by
  simpa using F.dense

end BoundedIrreducibilityFailure

end

end Erdos186.PZ.Reduction
