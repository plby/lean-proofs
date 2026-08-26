/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 146. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/146#post-8253
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos146.ForbiddenGraph

set_option linter.mathlibStandardSet false

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos146

section HammingProfiles

abbrev HammingWord (dimension : ℕ) := Fin dimension → Bool

noncomputable def booleanWordOnes {ι : Type*} [Fintype ι]
    (word : ι → Bool) : Finset ι := by
  classical
  exact Finset.univ.filter (fun index => word index = true)

theorem booleanWordOnes_card_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (equivalence : ι ≃ κ)
    (word : κ → Bool) :
    (booleanWordOnes (fun index : ι => word (equivalence index))).card =
      (booleanWordOnes word).card := by
  classical
  apply Finset.card_bij
    (fun index _ => equivalence index)
  · intro index hindex
    have hone := (Finset.mem_filter.mp hindex).2
    unfold booleanWordOnes
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hone⟩
  · intro first _ second _ hequal
    exact equivalence.injective hequal
  · intro index hindex
    refine ⟨equivalence.symm index, ?_, equivalence.apply_symm_apply index⟩
    unfold booleanWordOnes
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hone := (Finset.mem_filter.mp hindex).2
    simpa using hone

noncomputable def booleanWordsOfWeight (ι : Type*) [Fintype ι]
    (weight : ℕ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => (booleanWordOnes word).card = weight)

noncomputable def booleanWordsOfWeightEquiv
    (ι : Type*) [Fintype ι] (weight : ℕ) :
    ↥(booleanWordsOfWeight ι weight) ≃
      ↥((Finset.univ : Finset ι).powersetCard weight) := by
  classical
  refine
    { toFun := fun word => ⟨booleanWordOnes word.val, ?_⟩
      invFun := fun support =>
        ⟨fun index => decide (index ∈ support.val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hword :
        word.val ∈
          (Finset.univ.filter
            (fun candidate : ι → Bool =>
              (booleanWordOnes candidate).card = weight)) := by
      simpa only [booleanWordsOfWeight] using word.property
    exact (Finset.mem_filter.mp hword).2
  · have hsupport :=
      (Finset.mem_powersetCard.mp support.property).2
    have hones :
        booleanWordOnes
          (fun index : ι => decide (index ∈ support.val)) = support.val := by
      ext index
      simp [booleanWordOnes]
    simp only [booleanWordsOfWeight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hones]
    exact hsupport
  · intro word
    apply Subtype.ext
    funext index
    cases hbit : word.val index <;>
      simp [booleanWordOnes, hbit]
  · intro support
    apply Subtype.ext
    ext index
    simp [booleanWordOnes]

theorem booleanWordsOfWeight_card
    (ι : Type*) [Fintype ι] (weight : ℕ) :
    (booleanWordsOfWeight ι weight).card =
      (Fintype.card ι).choose weight := by
  calc
    (booleanWordsOfWeight ι weight).card =
        Fintype.card ↥(booleanWordsOfWeight ι weight) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        ↥((Finset.univ : Finset ι).powersetCard weight) :=
      Fintype.card_congr (booleanWordsOfWeightEquiv ι weight)
    _ = ((Finset.univ : Finset ι).powersetCard weight).card :=
      Fintype.card_coe _
    _ = (Fintype.card ι).choose weight := by
      simp

abbrev ClassificationFiber
    {ι γ : Type*} (classify : ι → γ) (group : γ) :=
  {index : ι // classify index = group}

noncomputable def classificationGroup
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) : Finset ι :=
  Finset.univ.filter (fun index => classify index = group)

noncomputable def classifiedWordOnes
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) : Finset ι :=
  (classificationGroup classify group).filter
    (fun index => word index = true)

noncomputable def classifiedWordSupportEquiv
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) :
    ↥(booleanWordOnes
        (fun index : ClassificationFiber classify group => word index.val)) ≃
      ↥(classifiedWordOnes classify group word) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.val, ?_⟩
      invFun := fun index => ⟨⟨index.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hbit : word index.val.val = true := by
      have hmembership :
          index.val ∈
            (Finset.univ.filter
              (fun candidate : ClassificationFiber classify group =>
                word candidate.val = true)) := by
        simpa only [booleanWordOnes] using index.property
      exact (Finset.mem_filter.mp hmembership).2
    simp [classifiedWordOnes, classificationGroup,
      index.val.property, hbit]
  · have hmembership :
        index.val ∈
          (classificationGroup classify group).filter
            (fun candidate => word candidate = true) := by
      simpa only [classifiedWordOnes] using index.property
    have hgroup := (Finset.mem_filter.mp hmembership).1
    exact (Finset.mem_filter.mp hgroup).2
  · have hmembership :
        index.val ∈
          (classificationGroup classify group).filter
            (fun candidate => word candidate = true) := by
      simpa only [classifiedWordOnes] using index.property
    have hbit := (Finset.mem_filter.mp hmembership).2
    simp [booleanWordOnes, hbit]
  · intro index
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro index
    apply Subtype.ext
    rfl

theorem classifiedWordOnes_card
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) :
    (classifiedWordOnes classify group word).card =
      (booleanWordOnes
        (fun index : ClassificationFiber classify group => word index.val)).card := by
  calc
    (classifiedWordOnes classify group word).card =
        Fintype.card ↥(classifiedWordOnes classify group word) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        ↥(booleanWordOnes
          (fun index : ClassificationFiber classify group => word index.val)) :=
      Fintype.card_congr
        (classifiedWordSupportEquiv classify group word).symm
    _ = (booleanWordOnes
          (fun index : ClassificationFiber classify group => word index.val)).card :=
      Fintype.card_coe _

noncomputable def classifiedBooleanWords
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => ∀ group,
      (classifiedWordOnes classify group word).card = counts group)

noncomputable def classifiedBooleanWordsEquiv
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) :
    ↥(classifiedBooleanWords classify counts) ≃
      (∀ group : γ,
        ↥(booleanWordsOfWeight
          (ClassificationFiber classify group) (counts group))) := by
  classical
  refine
    { toFun := fun word group =>
        ⟨fun index => word.val index.val, ?_⟩
      invFun := fun pieces =>
        ⟨fun index => (pieces (classify index)).val ⟨index, rfl⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership :
        word.val ∈
          (Finset.univ.filter
            (fun candidate : ι → Bool =>
              ∀ group,
                (classifiedWordOnes classify group candidate).card =
                  counts group)) := by
      simpa only [classifiedBooleanWords] using word.property
    have hprofile := (Finset.mem_filter.mp hmembership).2 group
    simp only [booleanWordsOfWeight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (classifiedWordOnes_card classify group word.val).symm.trans
      hprofile
  · simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro group
    rw [classifiedWordOnes_card]
    have hrestriction :
        (fun index : ClassificationFiber classify group =>
          (pieces (classify index.val)).val
            ⟨index.val, rfl⟩) =
          (pieces group).val := by
      funext index
      rcases index with ⟨index, hindex⟩
      cases hindex
      rfl
    rw [hrestriction]
    have hmembership := (pieces group).property
    unfold booleanWordsOfWeight at hmembership
    exact (Finset.mem_filter.mp hmembership).2
  · intro word
    apply Subtype.ext
    funext index
    rfl
  · intro pieces
    funext group
    apply Subtype.ext
    funext index
    rcases index with ⟨index, hindex⟩
    cases hindex
    rfl

theorem classifiedBooleanWords_card
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) :
    (classifiedBooleanWords classify counts).card =
      ∏ group : γ,
        (Fintype.card (ClassificationFiber classify group)).choose
          (counts group) := by
  calc
    (classifiedBooleanWords classify counts).card =
        Fintype.card ↥(classifiedBooleanWords classify counts) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        (∀ group : γ,
          ↥(booleanWordsOfWeight
            (ClassificationFiber classify group) (counts group))) :=
      Fintype.card_congr (classifiedBooleanWordsEquiv classify counts)
    _ = ∏ group : γ,
          Fintype.card
            ↥(booleanWordsOfWeight
              (ClassificationFiber classify group) (counts group)) := by
      rw [Fintype.card_pi]
    _ = ∏ group : γ,
          (Fintype.card (ClassificationFiber classify group)).choose
            (counts group) := by
      apply Finset.prod_congr rfl
      intro group _
      rw [Fintype.card_coe,
        booleanWordsOfWeight_card]

abbrev PairBitType := Fin 3

abbrev PairTypeCountProfile (parentCount dimension : ℕ) :=
  PairBitType → Fin dimension → Fin (parentCount.choose 2 + 1)

theorem pairTypeCountProfile_card (parentCount dimension : ℕ) :
    Fintype.card (PairTypeCountProfile parentCount dimension) =
      (parentCount.choose 2 + 1) ^ (3 * dimension) := by
  simp [PairTypeCountProfile, pow_mul, Nat.mul_comm]

noncomputable def pairCoordinateBitType
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1) : PairBitType := by
  classical
  exact
    if ∀ parent ∈ pair.val, parents parent coordinate = false then 0
    else if ∀ parent ∈ pair.val, parents parent coordinate = true then 1
    else 2

noncomputable def pairTypeGroup
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) : Finset (PairLayer parentCount 1) := by
  classical
  exact Finset.univ.filter
    (fun pair => pairCoordinateBitType parents coordinate pair = bitType)

noncomputable def pairCoordinateClassification
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension) :
    PairLayer parentCount 1 × Fin dimension → PairBitType × Fin dimension :=
  fun index =>
    (pairCoordinateBitType parents index.2 index.1, index.2)

noncomputable def pairCoordinateClassificationFiberEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    ClassificationFiber
        (pairCoordinateClassification parents) (bitType, coordinate) ≃
      ↥(pairTypeGroup parents coordinate bitType) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.1, ?_⟩
      invFun := fun pair => ⟨(pair.val, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have htype := congrArg Prod.fst index.property
    have hcoordinate : index.val.2 = coordinate := by
      simpa [pairCoordinateClassification] using
        congrArg Prod.snd index.property
    simp only [pairTypeGroup, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simpa [pairCoordinateClassification, hcoordinate] using htype
  · have hmembership :
        pair.val ∈
          (Finset.univ.filter
            (fun candidate : PairLayer parentCount 1 =>
              pairCoordinateBitType parents coordinate candidate = bitType)) := by
      simpa only [pairTypeGroup] using pair.property
    have htype := (Finset.mem_filter.mp hmembership).2
    change
      (pairCoordinateBitType parents coordinate pair.val, coordinate) =
        (bitType, coordinate)
    exact Prod.ext htype rfl
  · intro index
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hcoordinate := congrArg Prod.snd index.property
      simpa [pairCoordinateClassification] using hcoordinate.symm
  · intro pair
    apply Subtype.ext
    rfl

theorem pairCoordinateClassificationFiber_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    Fintype.card
      (ClassificationFiber
        (pairCoordinateClassification parents) (bitType, coordinate)) =
      (pairTypeGroup parents coordinate bitType).card := by
  calc
    Fintype.card
        (ClassificationFiber
          (pairCoordinateClassification parents) (bitType, coordinate)) =
        Fintype.card ↥(pairTypeGroup parents coordinate bitType) :=
      Fintype.card_congr
        (pairCoordinateClassificationFiberEquiv parents bitType coordinate)
    _ = (pairTypeGroup parents coordinate bitType).card :=
      Fintype.card_coe _

theorem sum_pairTypeGroup_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      (pairTypeGroup parents coordinate bitType).card) =
      parentCount.choose 2 := by
  classical
  have hmaps :
      (((Finset.univ : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1))).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hpairs :
      (Finset.univ : Finset (PairLayer parentCount 1)).card =
        parentCount.choose 2 := by
    rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
      pairLayer_card_zero]
  calc
    (∑ bitType : PairBitType,
        (pairTypeGroup parents coordinate bitType).card) =
      (Finset.univ : Finset (PairLayer parentCount 1)).card := by
        simpa [pairTypeGroup] using hpartition.symm
    _ = parentCount.choose 2 := hpairs

theorem pairTypeGroup_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    (pairTypeGroup parents coordinate bitType).card ≤
      parentCount.choose 2 := by
  classical
  calc
    (pairTypeGroup parents coordinate bitType).card ≤
      (Finset.univ : Finset (PairLayer parentCount 1)).card := by
        unfold pairTypeGroup
        exact Finset.card_filter_le _ _
    _ = parentCount.choose 2 := by
      rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
        pairLayer_card_zero]

noncomputable def pairTypeGroupChildOnes
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) : Finset (PairLayer parentCount 1) := by
  classical
  exact (pairTypeGroup parents coordinate bitType).filter
    (fun pair => children pair coordinate = true)

theorem pairTypeGroupChildOnes_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    (pairTypeGroupChildOnes parents children coordinate bitType).card ≤
      (pairTypeGroup parents coordinate bitType).card := by
  classical
  unfold pairTypeGroupChildOnes
  exact Finset.card_filter_le _ _

def flattenPairChildArray
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    PairLayer parentCount 1 × Fin dimension → Bool :=
  fun index => children index.1 index.2

theorem pairChildClassificationOnes_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    (classifiedWordOnes
      (pairCoordinateClassification parents) (bitType, coordinate)
      (flattenPairChildArray children)).card =
        (pairTypeGroupChildOnes parents children coordinate bitType).card := by
  classical
  apply Finset.card_bij (fun index _ => index.1)
  · intro index hindex
    have hclassified :
        index ∈
          (classificationGroup (pairCoordinateClassification parents)
            (bitType, coordinate)).filter
              (fun candidate =>
                flattenPairChildArray children candidate = true) := by
      simpa only [classifiedWordOnes] using hindex
    have hparts := Finset.mem_filter.mp hclassified
    have hgroup := (Finset.mem_filter.mp hparts.1).2
    have htype := congrArg Prod.fst hgroup
    have hcoordinate := congrArg Prod.snd hgroup
    have hcoord : index.2 = coordinate := by
      simpa [pairCoordinateClassification] using hcoordinate
    simp only [pairTypeGroupChildOnes, Finset.mem_filter]
    constructor
    · simp only [pairTypeGroup, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa [pairCoordinateClassification, hcoord] using htype
    · simpa [flattenPairChildArray, hcoord] using hparts.2
  · intro first hfirst second hsecond hequal
    apply Prod.ext
    · exact hequal
    · have hfirst_group :=
        (Finset.mem_filter.mp hfirst).1
      have hsecond_group :=
        (Finset.mem_filter.mp hsecond).1
      have hfirst_class :=
        (Finset.mem_filter.mp hfirst_group).2
      have hsecond_class :=
        (Finset.mem_filter.mp hsecond_group).2
      have hfirst_coordinate := congrArg Prod.snd hfirst_class
      have hsecond_coordinate := congrArg Prod.snd hsecond_class
      simpa [pairCoordinateClassification] using
        hfirst_coordinate.trans hsecond_coordinate.symm
  · intro pair hpair
    refine ⟨(pair, coordinate), ?_, rfl⟩
    have hpair_parts := Finset.mem_filter.mp hpair
    have hpair_type := (Finset.mem_filter.mp hpair_parts.1).2
    change
      (pair, coordinate) ∈
        (classificationGroup (pairCoordinateClassification parents)
          (bitType, coordinate)).filter
            (fun index => flattenPairChildArray children index = true)
    apply Finset.mem_filter.mpr
    constructor
    · unfold classificationGroup
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Prod.ext hpair_type rfl
    · exact hpair_parts.2

noncomputable def pairChildCountProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    PairTypeCountProfile parentCount dimension := by
  intro bitType coordinate
  refine ⟨(pairTypeGroupChildOnes parents children coordinate bitType).card, ?_⟩
  have hones := pairTypeGroupChildOnes_card_le
    parents children coordinate bitType
  have hgroup := pairTypeGroup_card_le parents coordinate bitType
  omega

noncomputable def pairChildArraysOfProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    Finset (PairLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => pairChildCountProfile parents children = profile)

noncomputable def pairChildArraysOfProfileEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    ↥(pairChildArraysOfProfile parents profile) ≃
      ↥(classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)) := by
  classical
  refine
    { toFun := fun children =>
        ⟨flattenPairChildArray children.val, ?_⟩
      invFun := fun word =>
        ⟨fun pair coordinate => word.val (pair, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := children.property
    unfold pairChildArraysOfProfile at hmembership
    have hprofile := (Finset.mem_filter.mp hmembership).2
    simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rintro ⟨bitType, coordinate⟩
    rw [pairChildClassificationOnes_card]
    have hcount := congrArg
      (fun candidate : PairTypeCountProfile parentCount dimension =>
        (candidate bitType coordinate).val) hprofile
    simpa [pairChildCountProfile] using hcount
  · simp only [pairChildArraysOfProfile, Finset.mem_filter,
      Finset.mem_univ, true_and]
    funext bitType
    funext coordinate
    apply Fin.ext
    change
      (pairTypeGroupChildOnes parents
        (fun pair coordinate => word.val (pair, coordinate))
        coordinate bitType).card = (profile bitType coordinate).val
    have hmembership := word.property
    unfold classifiedBooleanWords at hmembership
    have hprofile :=
      (Finset.mem_filter.mp hmembership).2 (bitType, coordinate)
    rw [← pairChildClassificationOnes_card]
    have hflatten :
        flattenPairChildArray
          (fun pair coordinate => word.val (pair, coordinate)) =
            word.val := by
      funext index
      rcases index with ⟨pair, coordinate⟩
      rfl
    rw [hflatten]
    exact hprofile
  · intro children
    apply Subtype.ext
    funext pair
    funext coordinate
    rfl
  · intro word
    apply Subtype.ext
    funext index
    rcases index with ⟨pair, coordinate⟩
    rfl

theorem pairChildArraysOfProfile_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    (pairChildArraysOfProfile parents profile).card =
      ∏ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
  calc
    (pairChildArraysOfProfile parents profile).card =
      Fintype.card ↥(pairChildArraysOfProfile parents profile) :=
        (Fintype.card_coe _).symm
    _ = Fintype.card
      ↥(classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)) :=
        Fintype.card_congr
          (pairChildArraysOfProfileEquiv parents profile)
    _ = (classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)).card :=
        Fintype.card_coe _
    _ = ∏ index : PairBitType × Fin dimension,
        (Fintype.card
          (ClassificationFiber
            (pairCoordinateClassification parents) index)).choose
          (profile index.1 index.2).val :=
        classifiedBooleanWords_card
          (pairCoordinateClassification parents)
          (fun index : PairBitType × Fin dimension =>
            (profile index.1 index.2).val)
    _ = ∏ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
      apply Finset.prod_congr rfl
      rintro ⟨bitType, coordinate⟩ _
      rw [pairCoordinateClassificationFiber_card]

noncomputable def pairCoordinateConditionalEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℝ :=
  ∑ bitType : PairBitType,
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      binaryEntropy
        (((pairTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ))

noncomputable def pairChildArrayEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    pairCoordinateConditionalEntropy parents children coordinate) /
      (dimension : ℝ)

noncomputable def pairParentCoordinateOneCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun parent => parents parent coordinate)).card

theorem pairParentCoordinateOneCount_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    pairParentCoordinateOneCount parents coordinate ≤ parentCount := by
  classical
  unfold pairParentCoordinateOneCount booleanWordOnes
  calc
    (Finset.univ.filter
      (fun parent : Fin parentCount =>
        parents parent coordinate = true)).card ≤
        (Finset.univ : Finset (Fin parentCount)).card :=
      Finset.card_filter_le _ _
    _ = parentCount := by simp

noncomputable def pairParentCoordinateSupport
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) : Finset (Fin parentCount) := by
  classical
  exact Finset.univ.filter
    (fun parent => parents parent coordinate = outcome)

theorem pairParentCoordinateSupport_true_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate true).card =
      pairParentCoordinateOneCount parents coordinate := by
  rfl

theorem pairParentCoordinateSupport_card_add
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate false).card +
      (pairParentCoordinateSupport parents coordinate true).card =
        parentCount := by
  classical
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin parentCount)))
      (fun parent => parents parent coordinate = false)
  simpa [pairParentCoordinateSupport, Bool.not_eq_false] using hpartition

theorem pairParentCoordinateSupport_false_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate false).card =
      parentCount - pairParentCoordinateOneCount parents coordinate := by
  have hpartition := pairParentCoordinateSupport_card_add parents coordinate
  rw [pairParentCoordinateSupport_true_card] at hpartition
  omega

theorem pairCoordinateBitType_homogeneous_iff
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (outcome : Bool) :
    pairCoordinateBitType parents coordinate pair =
        (if outcome then (1 : PairBitType) else 0) ↔
      ∀ parent ∈ pair.val, parents parent coordinate = outcome := by
  classical
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp pair.property
  cases outcome <;> cases ha : parents a coordinate <;>
    cases hb : parents b coordinate <;>
    simp_all [pairCoordinateBitType]

noncomputable def pairTypeGroupHomogeneousEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) :
    ↥(pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)) ≃
      ↥((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2) := by
  classical
  refine
    { toFun := fun pair => ⟨pair.val.val, ?_⟩
      invFun := fun support =>
        ⟨⟨support.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := pair.property
    unfold pairTypeGroup at hmembership
    have htype := (Finset.mem_filter.mp hmembership).2
    have hhomogeneous :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair.val outcome).mp htype
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, pair.val.property⟩
    intro parent hparent
    unfold pairParentCoordinateSupport
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hhomogeneous parent hparent⟩
  · exact (Finset.mem_powersetCard.mp support.property).2
  · unfold pairTypeGroup
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (pairCoordinateBitType_homogeneous_iff
      parents coordinate
      ⟨support.val, (Finset.mem_powersetCard.mp support.property).2⟩
      outcome).mpr
    intro parent hparent
    have hsubset :=
      (Finset.mem_powersetCard.mp support.property).1
    have hsupport := hsubset hparent
    unfold pairParentCoordinateSupport at hsupport
    exact (Finset.mem_filter.mp hsupport).2
  · intro pair
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro support
    apply Subtype.ext
    rfl

theorem pairTypeGroup_homogeneous_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) :
    (pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)).card =
      (pairParentCoordinateSupport parents coordinate outcome).card.choose 2 := by
  calc
    (pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)).card =
      Fintype.card
        ↥(pairTypeGroup parents coordinate
          (if outcome then (1 : PairBitType) else 0)) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
      ↥((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2) :=
      Fintype.card_congr
        (pairTypeGroupHomogeneousEquiv parents coordinate outcome)
    _ = ((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2).card :=
      Fintype.card_coe _
    _ = (pairParentCoordinateSupport parents coordinate outcome).card.choose 2 :=
      Finset.card_powersetCard _ _

theorem pairTypeGroup_false_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 0).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate).choose 2 := by
  simpa [pairParentCoordinateSupport_false_card] using
    pairTypeGroup_homogeneous_card parents coordinate false

theorem pairTypeGroup_true_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 1).card =
      (pairParentCoordinateOneCount parents coordinate).choose 2 := by
  simpa [pairParentCoordinateSupport_true_card] using
    pairTypeGroup_homogeneous_card parents coordinate true

theorem pairTypeGroup_mixed_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 2).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate) *
        pairParentCoordinateOneCount parents coordinate := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  have htotal :
      (pairTypeGroup parents coordinate 0).card +
        (pairTypeGroup parents coordinate 1).card +
          (pairTypeGroup parents coordinate 2).card =
            parentCount.choose 2 := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      sum_pairTypeGroup_card parents coordinate
  rw [pairTypeGroup_false_card,
    pairTypeGroup_true_card] at htotal
  have htotal_real :
      (((parentCount -
          pairParentCoordinateOneCount parents coordinate).choose 2 : ℕ) : ℝ) +
        (((pairParentCoordinateOneCount parents coordinate).choose 2 : ℕ) : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) =
          (parentCount.choose 2 : ℝ) := by
    exact_mod_cast htotal
  rw [Nat.cast_choose_two, Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_sub hones] at htotal_real
  have hresult :
      ((pairTypeGroup parents coordinate 2).card : ℝ) =
        (((parentCount -
          pairParentCoordinateOneCount parents coordinate) *
            pairParentCoordinateOneCount parents coordinate : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hones]
    nlinarith
  exact_mod_cast hresult

def pairBitTypeOfOutcomes (left right : Bool) : PairBitType :=
  if left = false ∧ right = false then 0
  else if left = true ∧ right = true then 1
  else 2

noncomputable def pairCoordinateKernel
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : BinaryPairKernel where
  parentProbability :=
    (pairParentCoordinateOneCount parents coordinate : ℝ) /
      (parentCount : ℝ)
  parentProbability_nonneg := by
    positivity
  parentProbability_le_one := by
    have hpositive : 0 < (parentCount : ℝ) := by
      exact_mod_cast hparents
    apply (div_le_one hpositive).mpr
    exact_mod_cast pairParentCoordinateOneCount_le parents coordinate
  childProbability left right :=
    ((pairTypeGroupChildOnes parents children coordinate
      (pairBitTypeOfOutcomes left right)).card : ℝ) /
        ((pairTypeGroup parents coordinate
          (pairBitTypeOfOutcomes left right)).card : ℝ)
  childProbability_nonneg := by
    intro left right
    positivity
  childProbability_le_one := by
    intro left right
    let bitType := pairBitTypeOfOutcomes left right
    have hle := pairTypeGroupChildOnes_card_le
      parents children coordinate bitType
    by_cases hzero : (pairTypeGroup parents coordinate bitType).card = 0
    · simp [bitType, hzero]
    · have hpositive :
          0 < ((pairTypeGroup parents coordinate bitType).card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      apply (div_le_one hpositive).mpr
      exact_mod_cast hle

theorem pairCoordinateKernel_parentProbability
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairCoordinateKernel hparents parents children coordinate).parentProbability =
      (pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ) := by
  rfl

theorem pairCoordinateKernel_childProbability
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (left right : Bool) :
    (pairCoordinateKernel hparents parents children coordinate).childProbability
        left right =
      ((pairTypeGroupChildOnes parents children coordinate
        (pairBitTypeOfOutcomes left right)).card : ℝ) /
          ((pairTypeGroup parents coordinate
            (pairBitTypeOfOutcomes left right)).card : ℝ) := by
  rfl

noncomputable def pairChildCoordinateOneCount
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun pair => children pair coordinate)).card

theorem sum_pairTypeGroupChildOnes_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      (pairTypeGroupChildOnes parents children coordinate bitType).card) =
      pairChildCoordinateOneCount children coordinate := by
  classical
  let support : Finset (PairLayer parentCount 1) :=
    booleanWordOnes (fun pair => children pair coordinate)
  have hmaps :
      ((support : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1)).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (bitType : PairBitType) :
      support.filter
        (fun pair => pairCoordinateBitType parents coordinate pair = bitType) =
      pairTypeGroupChildOnes parents children coordinate bitType := by
    ext pair
    simp [support, booleanWordOnes,
      pairTypeGroupChildOnes, pairTypeGroup, and_comm]
  calc
    (∑ bitType : PairBitType,
      (pairTypeGroupChildOnes parents children coordinate bitType).card) =
      ∑ bitType : PairBitType,
        (support.filter
          (fun pair =>
            pairCoordinateBitType parents coordinate pair = bitType)).card := by
          apply Finset.sum_congr rfl
          intro bitType _
          rw [hfiber]
    _ = support.card := by
      exact hpartition.symm
    _ = pairChildCoordinateOneCount children coordinate := by
      rfl

theorem pairTypeGroup_probability_mul_childRatio
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ) /
        ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      ((pairTypeGroupChildOnes parents children
        coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  by_cases hgroup : (pairTypeGroup parents coordinate bitType).card = 0
  · have hchild :
        (pairTypeGroupChildOnes parents children
          coordinate bitType).card = 0 := by
      have hle := pairTypeGroupChildOnes_card_le
        parents children coordinate bitType
      omega
    simp [hgroup, hchild]
  · have hgroup_real :
        ((pairTypeGroup parents coordinate bitType).card : ℝ) ≠ 0 := by
      exact_mod_cast hgroup
    field_simp [hpair.ne', hgroup_real]

theorem withoutReplacementBinaryPairMass_eq_pairTypeGroup
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (left right : Bool) :
    withoutReplacementBinaryPairMass parentCount
        (pairParentCoordinateOneCount parents coordinate) left right =
      ((pairTypeGroup parents coordinate
        (pairBitTypeOfOutcomes left right)).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
          (if left = right then (1 : ℝ) else 1 / 2) := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  have hparent : 0 < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  cases left <;> cases right <;>
    simp [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount,
      pairBitTypeOfOutcomes,
      pairTypeGroup_false_card,
      pairTypeGroup_true_card,
      pairTypeGroup_mixed_card,
      Nat.cast_choose_two,
      Nat.cast_sub hones] <;>
    field_simp [hparent.ne', hparent_minus.ne']

theorem pairCoordinateKernel_empiricalConditionalEntropy
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalConditionalEntropy parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      pairCoordinateConditionalEntropy parents children coordinate := by
  unfold empiricalConditionalEntropy
    withoutReplacementBinaryPairExpectation
  simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
    hparents parents coordinate]
  simp [Fintype.univ_bool,
    pairCoordinateKernel_childProbability,
    pairBitTypeOfOutcomes,
    pairCoordinateConditionalEntropy,
    Fin.sum_univ_succ]
  ring

theorem pairCoordinateKernel_empiricalChildMarginal
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalChildMarginal parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      (pairChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 2 : ℝ) := by
  have hgroups :
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
        (pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ) := by
    calc
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
        ∑ bitType : PairBitType,
          ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
              (parentCount.choose 2 : ℝ) := by
          apply Finset.sum_congr rfl
          intro bitType _
          exact pairTypeGroup_probability_mul_childRatio
            hparents parents children coordinate bitType
      _ =
        (∑ bitType : PairBitType,
          ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ)) /
            (parentCount.choose 2 : ℝ) := by
          rw [Finset.sum_div]
      _ = (pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ) := by
          congr 1
          exact_mod_cast
            sum_pairTypeGroupChildOnes_card parents children coordinate
  calc
    empiricalChildMarginal parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ)) := by
      unfold empiricalChildMarginal
        withoutReplacementBinaryPairExpectation
      simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
        hparents parents coordinate]
      simp [Fintype.univ_bool,
        pairCoordinateKernel_childProbability,
        pairBitTypeOfOutcomes,
        Fin.sum_univ_succ]
      ring
    _ = (pairChildCoordinateOneCount children coordinate : ℝ) /
      (parentCount.choose 2 : ℝ) := hgroups

theorem pairTypeGroup_probability_mul_childComplement
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (1 -
        ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      (((pairTypeGroup parents coordinate bitType).card : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ)) /
          (parentCount.choose 2 : ℝ) := by
  calc
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (1 -
        ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) -
        (((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) := by
          ring
    _ = ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) := by
          rw [pairTypeGroup_probability_mul_childRatio
            hparents parents children coordinate bitType]
    _ = (((pairTypeGroup parents coordinate bitType).card : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ)) /
          (parentCount.choose 2 : ℝ) := by
          ring

theorem pairCoordinateKernel_empiricalAverageDisagreement
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      (((pairTypeGroupChildOnes parents children coordinate 0).card : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) / 2 +
        (((pairTypeGroup parents coordinate 1).card : ℝ) -
          ((pairTypeGroupChildOnes parents children coordinate 1).card : ℝ))) /
        (parentCount.choose 2 : ℝ) := by
  have hzero := pairTypeGroup_probability_mul_childRatio
    hparents parents children coordinate 0
  have hone := pairTypeGroup_probability_mul_childComplement
    hparents parents children coordinate 1
  calc
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ((pairTypeGroup parents coordinate 0).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
        (((pairTypeGroupChildOnes parents children
          coordinate 0).card : ℝ) /
            ((pairTypeGroup parents coordinate 0).card : ℝ)) +
      ((pairTypeGroup parents coordinate 2).card : ℝ) /
          (parentCount.choose 2 : ℝ) * (1 / 2 : ℝ) +
      ((pairTypeGroup parents coordinate 1).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
        (1 -
          ((pairTypeGroupChildOnes parents children
            coordinate 1).card : ℝ) /
              ((pairTypeGroup parents coordinate 1).card : ℝ)) := by
      unfold empiricalAverageDisagreement
        withoutReplacementBinaryPairExpectation
      simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
        hparents parents coordinate]
      simp [Fintype.univ_bool,
        pairCoordinateKernel_childProbability,
        pairBitTypeOfOutcomes,
        BinaryPairKernel.bitDisagreementProbability]
      ring
    _ =
      (((pairTypeGroupChildOnes parents children coordinate 0).card : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) / 2 +
        (((pairTypeGroup parents coordinate 1).card : ℝ) -
          ((pairTypeGroupChildOnes parents children coordinate 1).card : ℝ))) /
        (parentCount.choose 2 : ℝ) := by
      rw [hzero, hone]
      ring

noncomputable def pairCoordinatePairMismatchCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1) : ℕ := by
  classical
  exact (pair.val.filter
    (fun parent =>
      parents parent coordinate ≠ children pair coordinate)).card

theorem pairCoordinatePairMismatchCount_homogeneous
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (outcome : Bool)
    (hgroup :
      pairCoordinateBitType parents coordinate pair =
        (if outcome then (1 : PairBitType) else 0)) :
    pairCoordinatePairMismatchCount parents children coordinate pair =
      if children pair coordinate = outcome then 0 else 2 := by
  classical
  have hhomogeneous :=
    (pairCoordinateBitType_homogeneous_iff
      parents coordinate pair outcome).mp hgroup
  by_cases hchild : children pair coordinate = outcome
  · have hempty :
        pair.val.filter
          (fun parent =>
            parents parent coordinate ≠ children pair coordinate) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro parent hmember hdisagree
      exact hdisagree
        ((hhomogeneous parent hmember).trans hchild.symm)
    unfold pairCoordinatePairMismatchCount
    rw [hempty]
    simp [hchild]
  · have hfull :
        pair.val.filter
          (fun parent =>
            parents parent coordinate ≠ children pair coordinate) =
          pair.val := by
      ext parent
      constructor
      · intro hmember
        exact (Finset.mem_filter.mp hmember).1
      · intro hmember
        apply Finset.mem_filter.mpr
        refine ⟨hmember, ?_⟩
        intro hequal
        apply hchild
        exact hequal.symm.trans
          (hhomogeneous parent hmember)
    unfold pairCoordinatePairMismatchCount
    rw [hfull, if_neg hchild]
    exact pair.property

theorem pairCoordinatePairMismatchCount_mixed
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (hgroup : pairCoordinateBitType parents coordinate pair = 2) :
    pairCoordinatePairMismatchCount parents children coordinate pair = 1 := by
  classical
  have hnotfalse :
      ¬ ∀ parent ∈ pair.val, parents parent coordinate = false := by
    intro hfalse
    have hzero :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair false).mpr hfalse
    rw [hgroup] at hzero
    simp at hzero
  have hnottrue :
      ¬ ∀ parent ∈ pair.val, parents parent coordinate = true := by
    intro htrue
    have hone :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair true).mpr htrue
    rw [hgroup] at hone
    simp at hone
  have hexfalse :
      ∃ parent ∈ pair.val, parents parent coordinate = false := by
    by_contra hnone
    push Not at hnone
    apply hnottrue
    intro parent hparent
    have hbit := hnone parent hparent
    cases hvalue : parents parent coordinate <;>
      simp_all
  have hextrue :
      ∃ parent ∈ pair.val, parents parent coordinate = true := by
    by_contra hnone
    push Not at hnone
    apply hnotfalse
    intro parent hparent
    have hbit := hnone parent hparent
    cases hvalue : parents parent coordinate <;>
      simp_all
  obtain ⟨falseParent, hfalseParent, hfalseBit⟩ := hexfalse
  obtain ⟨trueParent, htrueParent, htrueBit⟩ := hextrue
  let mismatches : Finset (PairLayer parentCount 0) :=
    pair.val.filter
      (fun parent =>
        parents parent coordinate ≠ children pair coordinate)
  let agreements : Finset (PairLayer parentCount 0) :=
    pair.val.filter
      (fun parent =>
        ¬ parents parent coordinate ≠ children pair coordinate)
  have hmismatch : mismatches.Nonempty := by
    cases hchild : children pair coordinate
    · refine ⟨trueParent, ?_⟩
      simp [mismatches, htrueParent, htrueBit, hchild]
    · refine ⟨falseParent, ?_⟩
      simp [mismatches, hfalseParent, hfalseBit, hchild]
  have hagreement : agreements.Nonempty := by
    cases hchild : children pair coordinate
    · refine ⟨falseParent, ?_⟩
      simp [agreements, hfalseParent, hfalseBit, hchild]
    · refine ⟨trueParent, ?_⟩
      simp [agreements, htrueParent, htrueBit, hchild]
  have hpartition : mismatches.card + agreements.card = 2 := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := pair.val)
      (fun parent =>
        parents parent coordinate ≠ children pair coordinate)
    change mismatches.card + agreements.card = pair.val.card at hfilter
    simpa [pair.property] using hfilter
  have hmismatch_pos := Finset.card_pos.mpr hmismatch
  have hagreement_pos := Finset.card_pos.mpr hagreement
  change mismatches.card = 1
  omega

theorem pairCoordinatePairMismatchCount_sum_false
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 0,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 * (pairTypeGroupChildOnes parents children coordinate 0).card := by
  classical
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 0,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ pair ∈ pairTypeGroup parents coordinate 0,
        if children pair coordinate = true then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 0)) := by
          simpa only [pairTypeGroup] using hpair
        have hgroup := (Finset.mem_filter.mp hmembership).2
        have hterm := pairCoordinatePairMismatchCount_homogeneous
          parents children coordinate pair false hgroup
        cases hchild : children pair coordinate <;>
          simpa [hchild] using hterm
    _ = 2 * (pairTypeGroupChildOnes parents children coordinate 0).card := by
      rw [← Finset.sum_filter]
      simp [pairTypeGroupChildOnes, Nat.mul_comm]

theorem pairCoordinatePairMismatchCount_sum_true
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
  classical
  let zeroChildren : Finset (PairLayer parentCount 1) :=
    (pairTypeGroup parents coordinate 1).filter
      (fun pair => children pair coordinate = false)
  have hpartition :
      (pairTypeGroupChildOnes parents children coordinate 1).card +
        zeroChildren.card =
          (pairTypeGroup parents coordinate 1).card := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := pairTypeGroup parents coordinate 1)
      (fun pair => children pair coordinate = true)
    simpa [pairTypeGroupChildOnes, zeroChildren] using hfilter
  have hzero_card :
      zeroChildren.card =
        (pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card := by
    omega
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ pair ∈ pairTypeGroup parents coordinate 1,
        if children pair coordinate = false then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 1)) := by
          simpa only [pairTypeGroup] using hpair
        have hgroup := (Finset.mem_filter.mp hmembership).2
        have hterm := pairCoordinatePairMismatchCount_homogeneous
          parents children coordinate pair true hgroup
        cases hchild : children pair coordinate <;>
          simpa [hchild] using hterm
    _ = 2 * zeroChildren.card := by
      rw [← Finset.sum_filter]
      simp [zeroChildren, Nat.mul_comm]
    _ = 2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
      rw [hzero_card]

theorem pairCoordinatePairMismatchCount_sum_mixed
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 2,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      (pairTypeGroup parents coordinate 2).card := by
  classical
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 2,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ _pair ∈ pairTypeGroup parents coordinate 2, 1 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 2)) := by
          simpa only [pairTypeGroup] using hpair
        exact pairCoordinatePairMismatchCount_mixed
          parents children coordinate pair
            (Finset.mem_filter.mp hmembership).2
    _ = (pairTypeGroup parents coordinate 2).card := by
      simp

theorem sum_pairCoordinatePairMismatchCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair : PairLayer parentCount 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 * (pairTypeGroupChildOnes parents children coordinate 0).card +
      (pairTypeGroup parents coordinate 2).card +
      2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
  classical
  have hmaps :
      (((Finset.univ : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1))).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hfiber :=
    (Finset.sum_fiberwise_of_maps_to hmaps
      (fun pair =>
        pairCoordinatePairMismatchCount
          parents children coordinate pair)).symm
  have hpartition :
      (∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair) =
        (∑ pair ∈ pairTypeGroup parents coordinate 0,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) +
        (∑ pair ∈ pairTypeGroup parents coordinate 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) +
        (∑ pair ∈ pairTypeGroup parents coordinate 2,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) := by
    simpa [pairTypeGroup, Fin.sum_univ_succ, add_assoc] using hfiber
  rw [pairCoordinatePairMismatchCount_sum_false,
    pairCoordinatePairMismatchCount_sum_true,
    pairCoordinatePairMismatchCount_sum_mixed] at hpartition
  omega

theorem sum_pairCoordinatePairMismatchCount_eq_hammingDist
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    (∑ coordinate : Fin dimension,
      ∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair) =
      ∑ pair : PairLayer parentCount 1,
        ∑ parent ∈ pair.val,
          hammingDist (parents parent) (children pair) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pair _
  have hcount (coordinate : Fin dimension) :
      pairCoordinatePairMismatchCount parents children coordinate pair =
        ∑ parent ∈ pair.val,
          if parents parent coordinate ≠ children pair coordinate
            then 1 else 0 := by
    change
      (pair.val.filter
        (fun parent =>
          parents parent coordinate ≠ children pair coordinate)).card = _
    exact (Finset.sum_boole _ _).symm
  simp_rw [hcount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro parent _
  change
    (∑ coordinate : Fin dimension,
      if parents parent coordinate ≠ children pair coordinate
        then 1 else 0) =
      ((Finset.univ : Finset (Fin dimension)).filter
        (fun coordinate =>
          parents parent coordinate ≠ children pair coordinate)).card
  exact Finset.sum_boole _ _

theorem pairCoordinateKernel_empiricalAverageDisagreement_eq_mismatches
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ((∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair : ℕ) : ℝ) /
        (2 * (parentCount.choose 2 : ℝ)) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  have hone := pairTypeGroupChildOnes_card_le
    parents children coordinate 1
  rw [pairCoordinateKernel_empiricalAverageDisagreement
    hparents parents children coordinate,
    sum_pairCoordinatePairMismatchCount]
  push_cast [hone]
  field_simp [hpair.ne']

theorem pairCoordinateConditionalEntropy_empirical_bound
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    pairCoordinateConditionalEntropy parents children coordinate ≤
      kappa +
        logTwo 3 *
          empiricalAverageDisagreement parentCount
            (pairParentCoordinateOneCount parents coordinate)
            (pairCoordinateKernel (by omega)
              parents children coordinate) +
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
        empiricalEntropyError parentCount := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  let kernel : BinaryPairKernel :=
    pairCoordinateKernel (by omega) parents children coordinate
  have hkernel := empiricalConditionalEntropy_bound
    parentCount (pairParentCoordinateOneCount parents coordinate)
      hparents hones kernel
      (pairCoordinateKernel_parentProbability
        (by omega) parents children coordinate)
  change
    empiricalConditionalEntropy parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega)
          parents children coordinate) ≤ _ at hkernel
  rw [pairCoordinateKernel_empiricalConditionalEntropy
    (by omega) parents children coordinate] at hkernel
  rw [pairCoordinateKernel_empiricalChildMarginal
    (by omega) parents children coordinate] at hkernel
  change
    pairCoordinateConditionalEntropy parents children coordinate ≤
      kappa +
        logTwo 3 *
          empiricalAverageDisagreement parentCount
            (pairParentCoordinateOneCount parents coordinate)
            (pairCoordinateKernel (by omega)
              parents children coordinate) +
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
        empiricalEntropyError parentCount at hkernel
  exact hkernel

noncomputable def pairParentArrayEntropyPotential
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ))) /
      (dimension : ℝ)

noncomputable def pairChildArrayEntropyPotential
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 2 : ℝ))) /
      (dimension : ℝ)

noncomputable def pairChildArrayAverageDisagreement
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    empiricalAverageDisagreement parentCount
      (pairParentCoordinateOneCount parents coordinate)
      (pairCoordinateKernel (by omega) parents children coordinate)) /
    (dimension : ℝ)

theorem pairChildArrayAverageDisagreement_le_radius
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (radius : ℕ)
    (hedges :
      ∀ (pair : PairLayer parentCount 1)
        (parent : PairLayer parentCount 0),
        parent ∈ pair.val →
          hammingDist (parents parent) (children pair) ≤ radius) :
    pairChildArrayAverageDisagreement hparents parents children ≤
      (radius : ℝ) / (dimension : ℝ) := by
  classical
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ parentCount)
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have htotal :
      (∑ coordinate : Fin dimension,
        ∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) ≤
        2 * parentCount.choose 2 * radius := by
    calc
      (∑ coordinate : Fin dimension,
        ∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) =
        ∑ pair : PairLayer parentCount 1,
          ∑ parent ∈ pair.val,
            hammingDist (parents parent) (children pair) :=
        sum_pairCoordinatePairMismatchCount_eq_hammingDist
          parents children
      _ ≤ ∑ pair : PairLayer parentCount 1,
          ∑ _parent ∈ pair.val, radius := by
        apply Finset.sum_le_sum
        intro pair _
        apply Finset.sum_le_sum
        intro parent hparent
        exact hedges pair parent hparent
      _ = ∑ _pair : PairLayer parentCount 1, 2 * radius := by
        apply Finset.sum_congr rfl
        intro pair _
        simp [pair.property]
      _ = 2 * parentCount.choose 2 * radius := by
        simp [pairLayer_card_succ, pairLayer_card_zero,
          Nat.mul_assoc, Nat.mul_comm]
  have htotal_real :
      (∑ coordinate : Fin dimension,
        ((∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair : ℕ) : ℝ)) ≤
        2 * (parentCount.choose 2 : ℝ) * (radius : ℝ) := by
    exact_mod_cast htotal
  unfold pairChildArrayAverageDisagreement
  simp_rw [pairCoordinateKernel_empiricalAverageDisagreement_eq_mismatches
    (by omega : 2 ≤ parentCount) parents children]
  rw [← Finset.sum_div]
  apply (div_le_div_iff_of_pos_right hdimension_real).mpr
  apply (div_le_iff₀ (mul_pos (by norm_num) hpair)).mpr
  nlinarith

theorem pairChildArrayEntropy_empirical_bound
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    pairChildArrayEntropy parents children ≤
      kappa +
        logTwo 3 *
          pairChildArrayAverageDisagreement hparents parents children +
        (pairChildArrayEntropyPotential children -
          pairParentArrayEntropyPotential parents) / 2 +
        empiricalEntropyError parentCount := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have hsum :
      (∑ coordinate : Fin dimension,
        pairCoordinateConditionalEntropy parents children coordinate) ≤
      ∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount) := by
    apply Finset.sum_le_sum
    intro coordinate _
    exact pairCoordinateConditionalEntropy_empirical_bound
      hparents parents children coordinate
  have hnormalized :=
    (div_le_div_iff_of_pos_right hdimension_real).mpr hsum
  change pairChildArrayEntropy parents children ≤ _ at hnormalized
  let disagreementSum : ℝ :=
    ∑ coordinate : Fin dimension,
      empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega)
          parents children coordinate)
  let childEntropySum : ℝ :=
    ∑ coordinate : Fin dimension,
      binaryEntropy
        ((pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ))
  let parentEntropySum : ℝ :=
    ∑ coordinate : Fin dimension,
      binaryEntropy
        ((pairParentCoordinateOneCount parents coordinate : ℝ) /
          (parentCount : ℝ))
  have hentropy_sum :
      (∑ coordinate : Fin dimension,
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2) =
        (childEntropySum - parentEntropySum) / 2 := by
    dsimp [childEntropySum, parentEntropySum]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  have hsum_formula :
      (∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) =
        (dimension : ℝ) * kappa +
          logTwo 3 * disagreementSum +
          (childEntropySum - parentEntropySum) / 2 +
          (dimension : ℝ) * empiricalEntropyError parentCount := by
    calc
      (∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) =
        (∑ _coordinate : Fin dimension, kappa) +
          (∑ coordinate : Fin dimension,
            logTwo 3 *
              empiricalAverageDisagreement parentCount
                (pairParentCoordinateOneCount parents coordinate)
                (pairCoordinateKernel (by omega)
                  parents children coordinate)) +
          (∑ coordinate : Fin dimension,
            (binaryEntropy
                ((pairChildCoordinateOneCount children coordinate : ℝ) /
                  (parentCount.choose 2 : ℝ)) -
              binaryEntropy
                ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                  (parentCount : ℝ))) / 2) +
          (∑ _coordinate : Fin dimension,
            empiricalEntropyError parentCount) := by
            simp only [Finset.sum_add_distrib]
      _ = (dimension : ℝ) * kappa +
          logTwo 3 * disagreementSum +
          (childEntropySum - parentEntropySum) / 2 +
          (dimension : ℝ) * empiricalEntropyError parentCount := by
        rw [hentropy_sum]
        dsimp [disagreementSum]
        rw [← Finset.mul_sum]
        simp [nsmul_eq_mul]
  calc
    pairChildArrayEntropy parents children ≤
      (∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) /
            (dimension : ℝ) := hnormalized
    _ = kappa +
        logTwo 3 *
          pairChildArrayAverageDisagreement hparents parents children +
        (pairChildArrayEntropyPotential children -
          pairParentArrayEntropyPotential parents) / 2 +
        empiricalEntropyError parentCount := by
      change
        (∑ coordinate : Fin dimension,
          (kappa +
            logTwo 3 *
              empiricalAverageDisagreement parentCount
                (pairParentCoordinateOneCount parents coordinate)
                (pairCoordinateKernel (by omega)
                  parents children coordinate) +
            (binaryEntropy
                ((pairChildCoordinateOneCount children coordinate : ℝ) /
                  (parentCount.choose 2 : ℝ)) -
              binaryEntropy
                ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                  (parentCount : ℝ))) / 2 +
            empiricalEntropyError parentCount)) /
              (dimension : ℝ) =
          kappa +
            logTwo 3 * (disagreementSum / (dimension : ℝ)) +
            (childEntropySum / (dimension : ℝ) -
              parentEntropySum / (dimension : ℝ)) / 2 +
            empiricalEntropyError parentCount
      rw [hsum_formula]
      field_simp [hdimension_real.ne']

theorem pairCoordinateConditionalEntropy_mass
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (parentCount.choose 2 : ℝ) *
        pairCoordinateConditionalEntropy parents children coordinate =
      ∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ)) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  unfold pairCoordinateConditionalEntropy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bitType _
  field_simp [hpair.ne']

theorem pairCoordinateConditionalEntropy_log_mass
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      ((pairTypeGroup parents coordinate bitType).card : ℝ) *
        Real.binEntropy
          (((pairTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
            ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
      (parentCount.choose 2 : ℝ) * Real.log 2 *
        pairCoordinateConditionalEntropy parents children coordinate := by
  calc
    (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          Real.binEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) *
        Real.log 2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro bitType _
          unfold binaryEntropy
          field_simp [log_two_pos.ne']
    _ = (parentCount.choose 2 : ℝ) * Real.log 2 *
        pairCoordinateConditionalEntropy parents children coordinate := by
      rw [← pairCoordinateConditionalEntropy_mass
        hparents parents children coordinate]
      ring

theorem pairChildGroup_choose_product_entropy_bound
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    (∏ index : PairBitType × Fin dimension,
      ((pairTypeGroup parents index.2 index.1).card).choose
        ((pairTypeGroupChildOnes parents children index.2 index.1).card) : ℝ) ≤
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate)) := by
  have hproduct := choose_product_le_exp_binary_entropy
    (ι := PairBitType × Fin dimension)
    (fun index => (pairTypeGroup parents index.2 index.1).card)
    (fun index =>
      (pairTypeGroupChildOnes parents children index.2 index.1).card)
    (fun index => pairTypeGroupChildOnes_card_le
      parents children index.2 index.1)
  have hsum :
      (∑ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card : ℝ) *
          Real.binEntropy
            (((pairTypeGroupChildOnes parents children
                index.2 index.1).card : ℝ) /
              ((pairTypeGroup parents index.2 index.1).card : ℝ))) =
        (parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [pairCoordinateConditionalEntropy_log_mass
      hparents parents children]
    rw [Finset.mul_sum]
  rw [hsum] at hproduct
  exact hproduct

theorem pairChildArraysOfRealizedProfile_card_le
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    ((pairChildArraysOfProfile parents
        (pairChildCountProfile parents children)).card : ℝ) ≤
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate)) := by
  have hcard :
      ((pairChildArraysOfProfile parents
        (pairChildCountProfile parents children)).card : ℝ) =
        ∏ index : PairBitType × Fin dimension,
          (((pairTypeGroup parents index.2 index.1).card).choose
            ((pairTypeGroupChildOnes parents children
              index.2 index.1).card) : ℝ) := by
    exact_mod_cast
      pairChildArraysOfProfile_card parents
        (pairChildCountProfile parents children)
  rw [hcard]
  exact pairChildGroup_choose_product_entropy_bound
    hparents parents children

noncomputable def badPairChildArrays
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    Finset (PairLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => pairChildArrayEntropy parents children ≤ threshold)

theorem badPairChildArrays_card_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    ((badPairChildArrays parents threshold).card : ℝ) ≤
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold) := by
  classical
  let bound : ℝ :=
    Real.exp
      ((parentCount.choose 2 : ℝ) * Real.log 2 *
        (dimension : ℝ) * threshold)
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    exact (Real.exp_pos _).le
  have hmaps :
      ((badPairChildArrays parents threshold :
        Finset (PairLayer parentCount 1 → HammingWord dimension)) :
        Set (PairLayer parentCount 1 → HammingWord dimension)).MapsTo
        (pairChildCountProfile parents)
        (Finset.univ : Finset (PairTypeCountProfile parentCount dimension)) := by
    intro children _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (profile : PairTypeCountProfile parentCount dimension) :
      (((badPairChildArrays parents threshold).filter
        (fun children => pairChildCountProfile parents children = profile)).card : ℝ) ≤
        bound := by
    by_cases hnonempty :
        ((badPairChildArrays parents threshold).filter
          (fun children =>
            pairChildCountProfile parents children = profile)).Nonempty
    · obtain ⟨children, hchildren⟩ := hnonempty
      have hparts := Finset.mem_filter.mp hchildren
      have hprofile : pairChildCountProfile parents children = profile :=
        hparts.2
      have hbad : pairChildArrayEntropy parents children ≤ threshold := by
        have hmembership :
            children ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 →
                    HammingWord dimension =>
                  pairChildArrayEntropy parents candidate ≤ threshold)) := by
          simpa only [badPairChildArrays] using hparts.1
        exact (Finset.mem_filter.mp hmembership).2
      have hsubset :
          (badPairChildArrays parents threshold).filter
              (fun candidate =>
                pairChildCountProfile parents candidate = profile) ⊆
            pairChildArraysOfProfile parents profile := by
        intro candidate hcandidate
        have hcandidate_profile := (Finset.mem_filter.mp hcandidate).2
        unfold pairChildArraysOfProfile
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcandidate_profile⟩
      have hcard :
          (((badPairChildArrays parents threshold).filter
            (fun candidate =>
              pairChildCountProfile parents candidate = profile)).card : ℝ) ≤
            ((pairChildArraysOfProfile parents profile).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hrealized :
          ((pairChildArraysOfProfile parents profile).card : ℝ) ≤
            Real.exp
              ((parentCount.choose 2 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  pairCoordinateConditionalEntropy
                    parents children coordinate)) := by
        rw [← hprofile]
        exact pairChildArraysOfRealizedProfile_card_le
          hparents parents children
      have hdimension_real : 0 < (dimension : ℝ) := by
        exact_mod_cast hdimension
      have hsum :
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate) ≤
              (dimension : ℝ) * threshold := by
        unfold pairChildArrayEntropy at hbad
        have hcleared := (div_le_iff₀ hdimension_real).mp hbad
        nlinarith
      have hcoefficient :
          0 ≤ (parentCount.choose 2 : ℝ) * Real.log 2 :=
        mul_nonneg (Nat.cast_nonneg _) log_two_pos.le
      have hexponential :
          Real.exp
              ((parentCount.choose 2 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  pairCoordinateConditionalEntropy
                    parents children coordinate)) ≤ bound := by
        dsimp [bound]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hsum hcoefficient]
      exact hcard.trans (hrealized.trans hexponential)
    · have hempty :
          (badPairChildArrays parents threshold).filter
            (fun children =>
              pairChildCountProfile parents children = profile) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simpa [hempty] using hbound_nonneg
  calc
    ((badPairChildArrays parents threshold).card : ℝ) =
        ∑ profile : PairTypeCountProfile parentCount dimension,
          (((badPairChildArrays parents threshold).filter
            (fun children =>
              pairChildCountProfile parents children = profile)).card : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _profile : PairTypeCountProfile parentCount dimension, bound := by
      exact Finset.sum_le_sum (fun profile _ => hfiber profile)
    _ = (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
          Real.exp
            ((parentCount.choose 2 : ℝ) * Real.log 2 *
              (dimension : ℝ) * threshold) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        pairTypeCountProfile_card]

end HammingProfiles

end Erdos146
