/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.ExternalGreenRenewal
import ErdosProblems.Erdos1165.HLOZGapEstimate
import ErdosProblems.Erdos1165.ShiftedPrefixBridge
import ErdosProblems.Erdos1165.SpatialInsertionConditional

/-!
# Finite thinning transport for the external walk

This file proves the finite product-law transport which connects the two
deleted finite prefixes of the canonical simple random walk to the IID
retained-block chain.  The proof is entirely finite: consecutive pairs of
fair directions are uniform among the sixteen blocks, deletion separates a
word according to its retained-coordinate set, and conditional on that set
the retained word is uniform among the fifteen allowed blocks.

The terminal incomplete direction is harmless because the thick-site count
is restricted to the checkerboard class of the block endpoints.  In the
shifted orientation the random starting point is also harmless, by translation
invariance of distinct-site local-time counts.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.ExternalCountTransport

open LazyDecomposition ExternalWalk ExternalOnePoint ExternalGreenRenewal
open ExternalThickCount ExternalProposition44 HLOZGapEstimate
open PathInsertion SpatialInsertionFiber ShiftedPrefixBridge

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The finite law of paired directions -/

/-- Pair `q` successive two-direction blocks, starting at direction `a`. -/
def pairedSegment (a q : ℕ) (ω : StepPath) : Fin q → PathInsertion.Block :=
  fun j ↦ (ω (a + 2 * (j : ℕ)), ω (a + 2 * (j : ℕ) + 1))

lemma measurable_pairedSegment (a q : ℕ) : Measurable (pairedSegment a q) := by
  exact measurable_pi_lambda _ fun j ↦
    Measurable.prod (measurable_pi_apply (a + 2 * (j : ℕ)))
      (measurable_pi_apply (a + 2 * (j : ℕ) + 1))

lemma pairedSegment_eq_iff_stepBlock_eq (a q : ℕ) (ω : StepPath)
    (w : Fin q → PathInsertion.Block) :
    pairedSegment a q ω = w ↔
      stepBlock a (2 * q) ω = flattenBlockVector w := by
  constructor
  · intro h
    funext j
    have hj := congrFun h ⟨j.val / 2, by omega⟩
    have hdiv : (2 * (j.val / 2)) + j.val % 2 = j.val := by omega
    have hmod : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
    rcases hmod with hmod | hmod
    · have heq : a + j.val = a + 2 * (j.val / 2) := by omega
      simpa [stepBlock, flattenBlockVector, hmod, pairedSegment, heq] using
        congrArg Prod.fst hj
    · have heq : a + j.val = a + 2 * (j.val / 2) + 1 := by omega
      simpa [stepBlock, flattenBlockVector, hmod, pairedSegment, heq] using
        congrArg Prod.snd hj
  · intro h
    funext j
    apply Prod.ext
    · have hj := congrFun h ⟨2 * j.val, by omega⟩
      simpa [stepBlock, flattenBlockVector, pairedSegment] using hj
    · have hj := congrFun h ⟨2 * j.val + 1, by omega⟩
      have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
      have hadd : a + (2 * j.val + 1) = a + 2 * j.val + 1 := by omega
      simpa [stepBlock, flattenBlockVector, pairedSegment, hdiv, hadd] using hj

/-- Every deterministic segment of `q` paired fair directions is uniform on
the `16^q` block words. -/
theorem fairSteps_map_pairedSegment (a q : ℕ) :
    fairSteps.map (pairedSegment a q) =
      ProbabilityTheory.uniformOn (Set.univ : Set (Fin q → PathInsertion.Block)) := by
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_apply (measurable_pairedSegment a q) (measurableSet_singleton w)]
  change fairSteps {ω | pairedSegment a q ω = w} = _
  rw [show {ω | pairedSegment a q ω = w} =
      stepBlock a (2 * q) ⁻¹' {flattenBlockVector w} by
    ext ω
    exact pairedSegment_eq_iff_stepBlock_eq a q ω w]
  rw [← Measure.map_apply (measurable_stepBlock a (2 * q))
      (measurableSet_singleton (flattenBlockVector w)), fairSteps_map_stepBlock]
  rw [fairBlock, Measure.infinitePi_singleton_of_fintype]
  simp only [fairStep_singleton, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [ProbabilityTheory.uniformOn_univ]
  simp only [Measure.count_singleton]
  rw [pow_mul]
  rw [Fintype.card_fun, Fintype.card_fin, PathInsertion.card_block]
  push_cast
  simp only [div_eq_mul_inv, one_mul]
  rw [ENNReal.inv_pow]
  congr 1
  rw [← ENNReal.inv_pow]
  norm_num

/-! ## Endpoint lists and checkerboard filtering -/

/-- The initial point followed by the endpoint of every two-step block. -/
def blockEndpointPath (x : Point) : List PathInsertion.Block → List Point
  | [] => [x]
  | b :: bs => x :: blockEndpointPath (PathInsertion.blockEnd x b) bs

@[simp] lemma blockEndpointPath_nil (x : Point) : blockEndpointPath x [] = [x] := rfl

@[simp] lemma blockEndpointPath_cons (x : Point) (b : PathInsertion.Block)
    (bs : List PathInsertion.Block) :
    blockEndpointPath x (b :: bs) =
      x :: blockEndpointPath (PathInsertion.blockEnd x b) bs := rfl

lemma orientationClass_iff_compatible (o : Orientation) (x : Point) :
    orientationClass o x ↔ OrientationCompatible o x := by
  cases o <;> rfl

lemma orientationCompatible_blockEnd {o : Orientation} {x : Point}
    (hx : OrientationCompatible o x) (b : PathInsertion.Block) :
    OrientationCompatible o (PathInsertion.blockEnd x b) := by
  have hpar := SpatialInsertionFiber.pointParity_blockEnd x b
  cases o with
  | even => exact hpar.trans hx
  | shifted => exact hpar.trans hx

lemma not_orientationClass_blockMiddle {o : Orientation} {x : Point}
    (hx : OrientationCompatible o x) (b : PathInsertion.Block) :
    ¬ orientationClass o (PathInsertion.blockMiddle x b) := by
  have hpar : pointParity (PathInsertion.blockMiddle x b) = pointParity x + 1 := by
    rw [PathInsertion.blockMiddle, pointParity_add, pointParity_directionVector]
  cases o with
  | even =>
      change EvenPoint x at hx
      change ¬EvenPoint (PathInsertion.blockMiddle x b)
      rw [EvenPoint, hpar, hx]
      decide
  | shifted =>
      change OddPoint x at hx
      change ¬OddPoint (PathInsertion.blockMiddle x b)
      rw [OddPoint, hpar, hx]
      decide

lemma blockPath_filter_orientationClass {o : Orientation} (x : Point)
    (hx : OrientationCompatible o x) (bs : List PathInsertion.Block) :
    (blockPath x bs).filter (orientationClass o) = blockEndpointPath x bs := by
  induction bs generalizing x with
  | nil =>
      change [x].filter (orientationClass o) = [x]
      simp [(orientationClass_iff_compatible o x).2 hx]
  | cons b bs ih =>
      have hend := orientationCompatible_blockEnd hx b
      have hxclass := (orientationClass_iff_compatible o x).2 hx
      have hmiddle := not_orientationClass_blockMiddle hx b
      have hpath : blockPath x (b :: bs) =
          x :: PathInsertion.blockMiddle x b ::
            (blockPath (PathInsertion.blockEnd x b) bs) := rfl
      rw [hpath]
      simp only [List.filter_cons]
      simp only [hxclass, decide_true, hmiddle, decide_false, if_true]
      rw [ih (PathInsertion.blockEnd x b) hend]
      simp [blockEndpointPath]

lemma blockEndpointPath_append_singleton (x : Point)
    (bs : List PathInsertion.Block) (b : PathInsertion.Block) :
    blockEndpointPath x (bs ++ [b]) =
      blockEndpointPath x bs ++ [followBlocks x (bs ++ [b])] := by
  induction bs generalizing x with
  | nil => simp [blockEndpointPath, followBlocks]
  | cons a bs ih =>
      simp only [List.cons_append, blockEndpointPath, followBlocks, List.foldl_cons,
        List.cons_append]
      rw [ih]
      rfl

lemma removableBlock_agree (o : Orientation) :
    ExternalWalk.removableBlock o = PathInsertion.removableBlock o := by
  cases o <;> rfl

/-- The two development layers use definitionally identical block types but
package the non-removability proof in separate namespaces. -/
def toPathRetained (o : Orientation) (b : ExternalWalk.RetainedBlock o) :
    PathInsertion.RetainedBlock o :=
  ⟨b.1, by simpa [← removableBlock_agree o] using b.2⟩

@[simp] lemma coe_toPathRetained (o : Orientation)
    (b : ExternalWalk.RetainedBlock o) :
    ((toPathRetained o b : PathInsertion.RetainedBlock o) : PathInsertion.Block) = b.1 := rfl

def pathRetainedPrefix (o : Orientation) (n : ℕ)
    (η : ℕ → ExternalWalk.RetainedBlock o) :
    Fin n → PathInsertion.RetainedBlock o :=
  fun j ↦ toPathRetained o (η j)

lemma followBlocks_retainedPrefix (o : Orientation) (x : Point)
    (η : ℕ → ExternalWalk.RetainedBlock o) (n : ℕ) :
    followBlocks x (retainedWord (pathRetainedPrefix o n η)) =
      x + externalPosition o η n := by
  induction n with
  | zero => simp [retainedWord, pathRetainedPrefix, followBlocks]
  | succ n ih =>
      rw [retainedWord, List.ofFn_succ_last]
      change followBlocks x
          (retainedWord (pathRetainedPrefix o n η) ++
            [(toPathRetained o (η n) : PathInsertion.Block)]) = _
      rw [followBlocks_append]
      simp only [followBlocks, List.foldl_cons, List.foldl_nil]
      change PathInsertion.blockEnd
          (followBlocks x (retainedWord (pathRetainedPrefix o n η)))
          (toPathRetained o (η n) : PathInsertion.Block) = _
      rw [ih, externalPosition_succ]
      simp only [PathInsertion.blockEnd, ExternalWalk.retainedDisplacement,
        ExternalWalk.blockDisplacement]
      abel

/-- The endpoint list of the first `n` retained blocks is exactly the usual
external-chain position list. -/
theorem blockEndpointPath_retainedPrefix (o : Orientation)
    (η : ℕ → ExternalWalk.RetainedBlock o) (n : ℕ) :
    blockEndpointPath (0, 0) (retainedWord (pathRetainedPrefix o n η)) =
      externalPositionList o η n := by
  induction n with
  | zero => simp [retainedWord, pathRetainedPrefix, externalPositionList]
  | succ n ih =>
      rw [retainedWord, List.ofFn_succ_last]
      change blockEndpointPath (0, 0)
          (retainedWord (pathRetainedPrefix o n η) ++
            [(toPathRetained o (η n) : PathInsertion.Block)]) = _
      rw [blockEndpointPath_append_singleton, ih]
      rw [followBlocks_append]
      simp only [followBlocks, List.foldl_cons, List.foldl_nil]
      change externalPositionList o η n ++
          [PathInsertion.blockEnd
            (followBlocks (0, 0) (retainedWord (pathRetainedPrefix o n η)))
            (toPathRetained o (η n) : PathInsertion.Block)] = _
      rw [followBlocks_retainedPrefix]
      have hlast : PathInsertion.blockEnd ((0, 0) + externalPosition o η n)
          (toPathRetained o (η n) : PathInsertion.Block) =
          externalPosition o η (n + 1) := by
        have hz : (0, 0) + externalPosition o η n = externalPosition o η n := by
          ext <;> simp
        rw [hz, externalPosition_succ]
        simp only [PathInsertion.blockEnd, ExternalWalk.retainedDisplacement,
          ExternalWalk.blockDisplacement, coe_toPathRetained]
        rw [add_assoc]
      rw [hlast]
      change externalPositionList o η n ++ [externalPosition o η (n + 1)] =
        List.ofFn (fun j : Fin (n + 2) ↦ externalPosition o η j)
      rw [List.ofFn_succ_last]
      rfl

/-! ## Thick counts ignore opposite-checkerboard points -/

lemma count_filter_eq_of_mem {α : Type*} [DecidableEq α]
    (p : List α) (P : α → Prop) [DecidablePred P] {x : α} (hx : P x) :
    (p.filter P).count x = p.count x := by
  exact List.count_filter (decide_eq_true hx)

lemma listThickCount_filter_eq_candidateCount
    (p : List Point) (P : Point → Prop) [DecidablePred P] (k : ℕ) :
    listThickCount (p.filter P) k =
      ((p.toFinset.filter P).filter fun x ↦ k ≤ p.count x).card := by
  unfold listThickCount
  congr 1
  ext x
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hxmem, hxP⟩, hxcount⟩
    have hc : List.count x (List.filter (fun y ↦ decide (P y)) p) =
        List.count x p :=
      List.count_filter (p := fun y ↦ decide (P y)) (decide_eq_true hxP)
    rw [hc] at hxcount
    exact ⟨⟨hxmem, hxP⟩, hxcount⟩
  · rintro ⟨⟨hxmem, hxP⟩, hxcount⟩
    refine ⟨⟨hxmem, hxP⟩, ?_⟩
    have hc : List.count x (List.filter (fun y ↦ decide (P y)) p) =
        List.count x p :=
      List.count_filter (p := fun y ↦ decide (P y)) (decide_eq_true hxP)
    rw [hc]
    exact hxcount

lemma orientedExternalThickCount_eq_filtered (o : Orientation)
    (s : WalkPath) (n k : ℕ) :
    orientedExternalThickCount o s n k =
      listThickCount
        ((orientedExternalPath o (pathPrefix s n)).filter (orientationClass o)) k := by
  rw [listThickCount_filter_eq_candidateCount]
  unfold orientedExternalThickCount candidateCount orientedExternalVisitedSites
    orientedLargeEvent orientedExternalLocalTime listLocalTime
  apply congrArg Finset.card
  ext x
  simp

/-! ## Exact finite thinning by retained-coordinate sets -/

/-- Block words with exactly `j` retained coordinates. -/
def BlockWordsWithCount (o : Orientation) (q j : ℕ) :=
  {u : Fin q → ExternalWalk.Block // (retainedIndices o u).card = j}

/-- A retained-coordinate set together with the retained values in increasing
coordinate order. -/
def SupportAndRetainedWord (o : Orientation) (q j : ℕ) :=
  {s : Finset (Fin q) // s ∈ Finset.univ.powersetCard j} ×
    (Fin j → ExternalWalk.RetainedBlock o)

noncomputable instance (o : Orientation) (q j : ℕ) :
    Fintype (BlockWordsWithCount o q j) := by
  unfold BlockWordsWithCount
  infer_instance

noncomputable instance (o : Orientation) (q j : ℕ) :
    Fintype (SupportAndRetainedWord o q j) := by
  unfold SupportAndRetainedWord
  infer_instance

/-- The exact finite thinning equivalence: after fixing the number retained,
a block word is uniquely its retained-coordinate set and retained word. -/
noncomputable def blockWordsWithCountEquiv (o : Orientation) (q j : ℕ) :
    BlockWordsWithCount o q j ≃ SupportAndRetainedWord o q j where
  toFun u :=
    (⟨retainedIndices o u.1, by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, u.2⟩⟩,
      extractRetainedWord o u.1 u.2)
  invFun p :=
    let hs : p.1.1.card = j := (Finset.mem_powersetCard.mp p.1.2).2
    ⟨inflateRetainedWord o p.1.1 hs p.2,
      by rw [retainedIndices_inflateRetainedWord o p.1.1 hs p.2]; exact hs⟩
  left_inv u := by
    apply Subtype.ext
    exact inflateRetainedWord_extractRetainedWord o u.1 u.2
  right_inv p := by
    rcases p with ⟨⟨s, hs⟩, v⟩
    apply Prod.ext
    · apply Subtype.ext
      exact retainedIndices_inflateRetainedWord o s
        (Finset.mem_powersetCard.mp hs).2 v
    · exact extractRetainedWord_inflateRetainedWord o s
        (Finset.mem_powersetCard.mp hs).2 v

def extractedWordOfCount (o : Orientation) {q j : ℕ}
    (u : BlockWordsWithCount o q j) :
    Fin j → ExternalWalk.RetainedBlock o :=
  extractRetainedWord o u.val u.property

@[simp] theorem blockWordsWithCountEquiv_retainedWord
    (o : Orientation) (q j : ℕ) (u : BlockWordsWithCount o q j) :
    (blockWordsWithCountEquiv o q j u).2 =
      extractedWordOfCount o u := rfl

/-- Retained words satisfying a length-indexed property. -/
def GoodRetainedWords (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (j : ℕ) :=
  {v : Fin j → ExternalWalk.RetainedBlock o // B j v}

/-- Block words with prescribed retained count whose extracted word satisfies
the same property. -/
def GoodBlockWordsWithCount (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (q j : ℕ) :=
  {u : BlockWordsWithCount o q j //
    B j (extractedWordOfCount o u)}

noncomputable instance (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (j : ℕ) :
    Fintype (GoodRetainedWords o B j) := by
  unfold GoodRetainedWords
  infer_instance

noncomputable instance (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (q j : ℕ) :
    Fintype (GoodBlockWordsWithCount o B q j) := by
  unfold GoodBlockWordsWithCount
  infer_instance

/-- Restriction of the thinning equivalence to any retained-word property. -/
noncomputable def goodBlockWordsWithCountEquiv (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (q j : ℕ) :
    GoodBlockWordsWithCount o B q j ≃
      {s : Finset (Fin q) // s ∈ Finset.univ.powersetCard j} ×
        GoodRetainedWords o B j where
  toFun u :=
    ((blockWordsWithCountEquiv o q j u.1).1,
      ⟨(blockWordsWithCountEquiv o q j u.1).2, by
        simpa [extractedWordOfCount] using u.2⟩)
  invFun p :=
    ⟨(blockWordsWithCountEquiv o q j).symm (p.1, p.2.1), by
      have hword : extractedWordOfCount o
          ((blockWordsWithCountEquiv o q j).symm (p.1, p.2.1)) = p.2.1 := by
        calc
          _ = (blockWordsWithCountEquiv o q j
              ((blockWordsWithCountEquiv o q j).symm (p.1, p.2.1))).2 :=
            (blockWordsWithCountEquiv_retainedWord o q j _).symm
          _ = p.2.1 := congrArg Prod.snd
            ((blockWordsWithCountEquiv o q j).apply_symm_apply (p.1, p.2.1))
      rw [hword]
      exact p.2.2⟩
  left_inv u := by
    apply Subtype.ext
    exact (blockWordsWithCountEquiv o q j).symm_apply_apply u.1
  right_inv p := by
    rcases p with ⟨s, ⟨v, hv⟩⟩
    have hpair := (blockWordsWithCountEquiv o q j).apply_symm_apply (s, v)
    have hs : (blockWordsWithCountEquiv o q j
        ((blockWordsWithCountEquiv o q j).symm (s, v))).1 = s :=
      congrArg Prod.fst hpair
    have hv' : (blockWordsWithCountEquiv o q j
        ((blockWordsWithCountEquiv o q j).symm (s, v))).2 = v :=
      congrArg Prod.snd hpair
    apply Prod.ext
    · exact hs
    · apply Subtype.ext
      exact hv'

theorem card_goodBlockWordsWithCount (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (q j : ℕ) :
    Fintype.card (GoodBlockWordsWithCount o B q j) =
      q.choose j * Fintype.card (GoodRetainedWords o B j) := by
  classical
  rw [Fintype.card_congr (goodBlockWordsWithCountEquiv o B q j), Fintype.card_prod]
  congr 1
  rw [Fintype.card_subtype]
  have hfilter :
      (Finset.univ.filter fun s : Finset (Fin q) ↦
        s ∈ (Finset.univ : Finset (Fin q)).powersetCard j) =
        (Finset.univ : Finset (Fin q)).powersetCard j := by
    ext s
    simp
  rw [hfilter]
  rw [Finset.card_powersetCard]
  simp

/-- A raw block word has a good extracted word if its (uniquely determined)
retained count and increasing retained subword satisfy `B`.  The existential
packaging avoids any non-canonical dependent cast. -/
def HasGoodExtracted (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop)
    {q : ℕ} (u : Fin q → ExternalWalk.Block) : Prop :=
  ∃ (j : ℕ) (hu : (retainedIndices o u).card = j),
    B j (extractRetainedWord o u hu)

def GoodBlockWords (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (q : ℕ) :=
  {u : Fin q → ExternalWalk.Block // HasGoodExtracted o B u}

noncomputable instance (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (q : ℕ) :
    Fintype (GoodBlockWords o B q) := by
  unfold GoodBlockWords
  infer_instance

def GoodBlockWordsAtCount (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (q j : ℕ) :=
  {u : GoodBlockWords o B q // (retainedIndices o u.1).card = j}

noncomputable instance (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (q j : ℕ) :
    Fintype (GoodBlockWordsAtCount o B q j) := by
  unfold GoodBlockWordsAtCount
  infer_instance

/-- The `j`-th retained-count fibre of the raw good words is the previously
counted fixed-count subtype. -/
noncomputable def goodBlockWordsAtCountEquiv (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (q j : ℕ) :
    GoodBlockWordsAtCount o B q j ≃ GoodBlockWordsWithCount o B q j where
  toFun u :=
    ⟨⟨u.1.1, u.2⟩, by
      rcases u.1.2 with ⟨j', hj', hB⟩
      have hjj : j' = j := hj'.symm.trans u.2
      cases hjj
      exact hB⟩
  invFun u :=
    ⟨⟨u.1.1, ⟨j, u.1.2, by simpa [extractedWordOfCount] using u.2⟩⟩, u.1.2⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Exact finite binomial thinning count for an arbitrary retained-word
property. -/
theorem card_goodBlockWords (o : Orientation)
    (B : ∀ j, (Fin j → ExternalWalk.RetainedBlock o) → Prop) (q : ℕ) :
    Fintype.card (GoodBlockWords o B q) =
      ∑ j ∈ Finset.range (q + 1),
        q.choose j * Fintype.card (GoodRetainedWords o B j) := by
  classical
  change Fintype.card {u : Fin q → ExternalWalk.Block //
    HasGoodExtracted o B u} = _
  rw [Fintype.card_subtype]
  change (Finset.univ.filter fun u : Fin q → ExternalWalk.Block ↦
      HasGoodExtracted o B u).card = _
  calc
    (Finset.univ.filter fun u : Fin q → ExternalWalk.Block ↦
        HasGoodExtracted o B u).card =
        ∑ j ∈ Finset.range (q + 1),
          ((Finset.univ.filter fun u : Fin q → ExternalWalk.Block ↦
              HasGoodExtracted o B u).filter fun u ↦
                (retainedIndices o u).card = j).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro u hu
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by
        simpa using Finset.card_le_univ (retainedIndices o u)))
    _ = ∑ j ∈ Finset.range (q + 1),
        q.choose j * Fintype.card (GoodRetainedWords o B j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← card_goodBlockWordsWithCount o B q j]
      rw [← Fintype.card_congr (goodBlockWordsAtCountEquiv o B q j)]
      rw [Finset.filter_filter]
      change (Finset.univ.filter fun u : Fin q → ExternalWalk.Block ↦
          HasGoodExtracted o B u ∧ (retainedIndices o u).card = j).card =
        Fintype.card (GoodBlockWordsAtCount o B q j)
      rw [← Fintype.card_subtype]
      exact (Fintype.card_congr
        (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun u : Fin q → ExternalWalk.Block ↦ HasGoodExtracted o B u)
          (fun u ↦ (retainedIndices o u).card = j))).symm

/-! ## The extension-monotone thick-word property -/

/-- Position list associated with a finite retained word. -/
def finiteExternalPositionList (o : Orientation) {j : ℕ}
    (v : Fin j → ExternalWalk.RetainedBlock o) : List Point :=
  blockEndpointPath (0, 0)
    (retainedWord (fun i ↦ toPathRetained o (v i)))

def thickWordProperty (o : Orientation) (J k : ℕ)
    (j : ℕ) (v : Fin j → ExternalWalk.RetainedBlock o) : Prop :=
  J < listThickCount (finiteExternalPositionList o v) k

lemma finiteExternalPositionList_externalPrefix (o : Orientation)
    (η : ℕ → ExternalWalk.RetainedBlock o) (j : ℕ) :
    finiteExternalPositionList o (externalPrefix o j η) =
      externalPositionList o η j := by
  exact blockEndpointPath_retainedPrefix o η j

lemma listThickCount_mono_of_prefix {α : Type*} [BEq α] [LawfulBEq α]
    [DecidableEq α] {p q : List α} (hpq : p <+: q) (k : ℕ) :
    listThickCount p k ≤ listThickCount q k := by
  unfold listThickCount
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, List.mem_toFinset] at hx ⊢
  exact ⟨hpq.mem hx.1, hx.2.trans (hpq.count_le x)⟩

lemma externalPositionList_take (o : Orientation)
    (η : ℕ → ExternalWalk.RetainedBlock o) {j N : ℕ} (hjN : j ≤ N) :
    (externalPositionList o η N).take (j + 1) = externalPositionList o η j := by
  apply List.ext_get
  · simp [externalPositionList, hjN]
  · intro r hr₁ hr₂
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_take]
    unfold externalPositionList
    rw [List.getElem_ofFn, List.getElem_ofFn]

lemma externalPositionList_prefix (o : Orientation)
    (η : ℕ → ExternalWalk.RetainedBlock o) {j N : ℕ} (hjN : j ≤ N) :
    externalPositionList o η j <+: externalPositionList o η N := by
  rw [← externalPositionList_take o η hjN]
  exact List.take_prefix _ _

lemma externalThickCount_mono_time (o : Orientation)
    (η : ℕ → ExternalWalk.RetainedBlock o) {j N k : ℕ} (hjN : j ≤ N) :
    externalThickCount o η j k ≤ externalThickCount o η N k := by
  exact listThickCount_mono_of_prefix (externalPositionList_prefix o η hjN) k

/-- A concrete retained block available in both orientations, used only to
extend finite words past their last coordinate. -/
def defaultRetainedBlock (o : Orientation) : ExternalWalk.RetainedBlock o :=
  ⟨(2, 2), by cases o <;> decide⟩

def extendRetainedWord (o : Orientation) {N : ℕ}
    (v : Fin N → ExternalWalk.RetainedBlock o) :
    ℕ → ExternalWalk.RetainedBlock o :=
  fun n ↦ if h : n < N then v ⟨n, h⟩ else defaultRetainedBlock o

@[simp] lemma externalPrefix_extendRetainedWord (o : Orientation) {N : ℕ}
    (v : Fin N → ExternalWalk.RetainedBlock o) :
    externalPrefix o N (extendRetainedWord o v) = v := by
  funext i
  simp [externalPrefix, extendRetainedWord, i.isLt]

lemma finiteExternalPositionList_append_prefix (o : Orientation)
    {j r : ℕ} (v : Fin j → ExternalWalk.RetainedBlock o)
    (w : Fin r → ExternalWalk.RetainedBlock o) :
    finiteExternalPositionList o v <+:
      finiteExternalPositionList o (Fin.append v w) := by
  let η := extendRetainedWord o (Fin.append v w)
  have hprefix := externalPositionList_prefix o η
    (show j ≤ j + r from Nat.le_add_right j r)
  rw [← finiteExternalPositionList_externalPrefix o η j,
    ← finiteExternalPositionList_externalPrefix o η (j + r)] at hprefix
  have hfull : externalPrefix o (j + r) η = Fin.append v w :=
    externalPrefix_extendRetainedWord o (Fin.append v w)
  have hfirst : externalPrefix o j η = v := by
    funext i
    change (if h : (i : ℕ) < j + r then Fin.append v w ⟨i, h⟩
      else defaultRetainedBlock o) = v i
    have hi : (i : ℕ) < j + r := by omega
    rw [dif_pos hi]
    have heq : (⟨(i : ℕ), hi⟩ : Fin (j + r)) = Fin.castAdd r i := by
      apply Fin.ext
      rfl
    rw [heq, Fin.append_left]
  simpa [hfull, hfirst] using hprefix

lemma thickWordProperty_append (o : Orientation) (J k : ℕ)
    {j r : ℕ} {v : Fin j → ExternalWalk.RetainedBlock o}
    (w : Fin r → ExternalWalk.RetainedBlock o)
    (hv : thickWordProperty o J k j v) :
    thickWordProperty o J k (j + r) (Fin.append v w) := by
  exact hv.trans_le
    (listThickCount_mono_of_prefix (finiteExternalPositionList_append_prefix o v w) k)

/-- Append arbitrary fresh retained blocks to a thick retained word. -/
def appendThickWord (o : Orientation) (J k j r : ℕ) :
    GoodRetainedWords o (thickWordProperty o J k) j ×
        (Fin r → ExternalWalk.RetainedBlock o) →
      GoodRetainedWords o (thickWordProperty o J k) (j + r) :=
  fun p ↦ ⟨Fin.append p.1.1 p.2,
    thickWordProperty_append o J k p.2 p.1.2⟩

lemma appendThickWord_injective (o : Orientation) (J k j r : ℕ) :
    Function.Injective (appendThickWord o J k j r) := by
  rintro ⟨v, a⟩ ⟨w, b⟩ h
  have happ : Fin.append v.1 a = Fin.append w.1 b := congrArg Subtype.val h
  have hv : v.1 = w.1 := by
    funext i
    have hi := congrFun happ (Fin.castAdd r i)
    simpa only [Fin.append_left] using hi
  have hab : a = b := by
    funext i
    have hi := congrFun happ (Fin.natAdd j i)
    simpa only [Fin.append_right] using hi
  apply Prod.ext
  · apply Subtype.ext
    exact hv
  · exact hab

/-- Prefix extension gives the cardinal inequality needed to dominate every
short retained word by length `j+r`. -/
theorem card_goodRetainedWords_mul_pow_le (o : Orientation) (J k j r : ℕ) :
    Fintype.card (GoodRetainedWords o (thickWordProperty o J k) j) * 15 ^ r ≤
      Fintype.card (GoodRetainedWords o (thickWordProperty o J k) (j + r)) := by
  have hcard := Fintype.card_le_of_injective
    (appendThickWord o J k j r) (appendThickWord_injective o J k j r)
  simpa [Fintype.card_prod, Fintype.card_fun, ExternalWalk.card_retainedBlock] using hcard

lemma pow_split_of_le {j N : ℕ} (hjN : j ≤ N) :
    (15 : ℕ) ^ N = 15 ^ (N - j) * 15 ^ j := by
  rw [← pow_add, Nat.sub_add_cancel hjN]

/-- Cross-multiplied finite thinning domination.  It contains no division and
is therefore convenient both for natural-cardinality and `ℝ≥0∞` probability
calculations. -/
theorem card_goodBlockWords_mul_pow_le (o : Orientation) (J k q N : ℕ)
    (hqN : q ≤ N) :
    Fintype.card (GoodBlockWords o (thickWordProperty o J k) q) * 15 ^ N ≤
      Fintype.card (GoodRetainedWords o (thickWordProperty o J k) N) * 16 ^ q := by
  rw [card_goodBlockWords]
  rw [Finset.sum_mul]
  calc
    (∑ j ∈ Finset.range (q + 1),
        q.choose j * Fintype.card
          (GoodRetainedWords o (thickWordProperty o J k) j) * 15 ^ N) ≤
        ∑ j ∈ Finset.range (q + 1),
          Fintype.card (GoodRetainedWords o (thickWordProperty o J k) N) *
            (15 ^ j * q.choose j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      have hjq : j ≤ q := Nat.le_of_lt_succ (by simpa using hj)
      have hjN : j ≤ N := hjq.trans hqN
      have hshort := card_goodRetainedWords_mul_pow_le o J k j (N - j)
      rw [Nat.add_sub_of_le hjN] at hshort
      rw [pow_split_of_le hjN]
      calc
        q.choose j * Fintype.card
              (GoodRetainedWords o (thickWordProperty o J k) j) *
            (15 ^ (N - j) * 15 ^ j) =
            (q.choose j * 15 ^ j) *
              (Fintype.card (GoodRetainedWords o (thickWordProperty o J k) j) *
                15 ^ (N - j)) := by ac_rfl
        _ ≤ (q.choose j * 15 ^ j) *
              Fintype.card (GoodRetainedWords o (thickWordProperty o J k) N) :=
          Nat.mul_le_mul_left _ hshort
        _ = Fintype.card (GoodRetainedWords o (thickWordProperty o J k) N) *
              (15 ^ j * q.choose j) := by ac_rfl
    _ = Fintype.card (GoodRetainedWords o (thickWordProperty o J k) N) *
        ∑ j ∈ Finset.range (q + 1), 15 ^ j * q.choose j := by
      rw [Finset.mul_sum]
    _ = Fintype.card (GoodRetainedWords o (thickWordProperty o J k) N) *
        16 ^ q := by
      congr 1
      simpa using (add_pow (15 : ℕ) 1 q).symm

/-! ## The extracted word is the pathwise deleted word -/

lemma filter_finRange_eq_retainedEnumeration (o : Orientation) {q j : ℕ}
    (u : Fin q → ExternalWalk.Block) (hu : (retainedIndices o u).card = j) :
    (List.finRange q).filter (fun i ↦ u i ≠ ExternalWalk.removableBlock o) =
      List.ofFn fun k : Fin j ↦
        (↑((retainedIndices o u).orderIsoOfFin hu k) : Fin q) := by
  apply List.SortedLT.eq_of_mem_iff
  · exact (List.Pairwise.filter
      (fun i ↦ decide (u i ≠ ExternalWalk.removableBlock o))
      (List.sortedLT_finRange q).pairwise).sortedLT
  · rw [List.sortedLT_ofFn_iff]
    exact (retainedIndices o u).orderIsoOfFin hu |>.strictMono
  · intro i
    rw [List.mem_filter, List.mem_ofFn]
    simp only [List.mem_finRange, true_and, decide_eq_true_eq]
    constructor
    · intro hi
      let si : retainedIndices o u := ⟨i, (mem_retainedIndices o u i).2 hi⟩
      refine ⟨((retainedIndices o u).orderIsoOfFin hu).symm si, ?_⟩
      exact congrArg Subtype.val
        (((retainedIndices o u).orderIsoOfFin hu).apply_symm_apply si)
    · rintro ⟨k, hk⟩
      rw [← hk]
      exact (mem_retainedIndices o u _).1
        (((retainedIndices o u).orderIsoOfFin hu k).property)

/-- Filtering a block word by the pathwise deletion predicate gives exactly
the increasing retained word used in the finite thinning equivalence. -/
theorem deleteRemovableBlocks_eq_extractedWord (o : Orientation) {q j : ℕ}
    (u : Fin q → ExternalWalk.Block) (hu : (retainedIndices o u).card = j) :
    PathInsertion.deleteRemovableBlocks o (List.ofFn u) =
      retainedWord (fun k ↦ toPathRetained o (extractRetainedWord o u hu k)) := by
  unfold PathInsertion.deleteRemovableBlocks retainedWord
  rw [List.ofFn_eq_map, List.filter_map]
  have hpred :
      ((fun b : ExternalWalk.Block ↦ decide (b ≠ PathInsertion.removableBlock o)) ∘ u) =
        (fun i ↦ decide (u i ≠ ExternalWalk.removableBlock o)) := by
    funext i
    simp [removableBlock_agree]
  change List.map u
      (List.filter
        ((fun b : ExternalWalk.Block ↦ decide (b ≠ PathInsertion.removableBlock o)) ∘ u)
        (List.finRange q)) = _
  rw [hpred, filter_finRange_eq_retainedEnumeration o u hu]
  rw [List.map_ofFn]
  rfl

/-! ## Translation invariance and the two deterministic oriented prefixes -/

lemma listThickCount_map_of_injective {α β : Type*}
    [BEq α] [LawfulBEq α] [DecidableEq α]
    [BEq β] [LawfulBEq β] [DecidableEq β]
    (p : List α) (f : α → β) (hf : Function.Injective f) (k : ℕ) :
    listThickCount (p.map f) k = listThickCount p k := by
  unfold listThickCount
  have hfin : ((p.map f).toFinset.filter fun y ↦ k ≤ (p.map f).count y) =
      (p.toFinset.filter fun x ↦ k ≤ p.count x).image f := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_filter] at hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (by simpa using hy.1)
      rw [Finset.mem_image]
      exact ⟨x, by
        rw [Finset.mem_filter]
        exact ⟨by simpa using hx,
          by simpa [List.count_map_of_injective p f hf x] using hy.2⟩, rfl⟩
    · intro hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨by simpa using
          (List.mem_map.mpr ⟨x, (by simpa using hx.1), rfl⟩),
        by simpa [List.count_map_of_injective p f hf x] using hx.2⟩
  rw [hfin, Finset.card_image_of_injective _ hf]

lemma addPoint_injective (x : Point) : Function.Injective (fun y : Point ↦ x + y) := by
  intro a b h
  exact add_left_cancel h

lemma blockEndpointPath_add (x y : Point) (bs : List PathInsertion.Block) :
    blockEndpointPath (x + y) bs =
      (blockEndpointPath y bs).map fun z ↦ x + z := by
  induction bs generalizing y with
  | nil => simp [blockEndpointPath]
  | cons b bs ih =>
      simp only [blockEndpointPath, List.map_cons]
      congr 1
      have hend : PathInsertion.blockEnd (x + y) b =
          x + PathInsertion.blockEnd y b := by
        simp only [PathInsertion.blockEnd]
        abel
      rw [hend, ih]

lemma listThickCount_blockEndpointPath_translate (x : Point)
    (bs : List PathInsertion.Block) (k : ℕ) :
    listThickCount (blockEndpointPath x bs) k =
      listThickCount (blockEndpointPath (0, 0) bs) k := by
  have hz : x + (0, 0) = x := by ext <;> simp
  rw [← hz, blockEndpointPath_add]
  exact listThickCount_map_of_injective _ _ (addPoint_injective x) k

lemma list_ofFn_pairedSegment_zero (ω : StepPath) (n : ℕ) :
    List.ofFn (pairedSegment 0 (n / 2) ω) = completePrefixBlocks ω n := by
  unfold completePrefixBlocks
  apply congrArg List.ofFn
  funext i
  simp [pairedSegment]

lemma list_ofFn_pairedSegment_one (ω : StepPath) (n : ℕ) :
    List.ofFn (pairedSegment 1 ((n - 1) / 2) ω) = shiftedCompletePrefixBlocks ω n := by
  unfold shiftedCompletePrefixBlocks completeSegmentBlocks
  apply congrArg List.ofFn
  funext i
  simp [pairedSegment]

lemma orientedExternalPath_even_blocks (ω : StepPath) (n : ℕ) :
    orientedExternalPath .even (pathPrefix (trajectory ω) n) =
      blockPath (0, 0)
          (PathInsertion.deleteRemovableBlocks .even
            (List.ofFn (pairedSegment 0 (n / 2) ω))) ++
        prefixRemainder ω n := by
  unfold orientedExternalPath finiteExternalPath
  change externalPath .even (finitePathList (pathPrefix (trajectory ω) n)) = _
  rw [prefixPath_eq_blockPath_append_remainder,
    list_ofFn_pairedSegment_zero]
  unfold prefixRemainder
  by_cases hmod : n % 2 = 0
  · simp [hmod, PathInsertion.externalPath_blockPath]
  · simp only [hmod, if_false]
    exact externalPath_blockPath_append_singleton .even (0, 0) (trajectory ω n)
      (completePrefixBlocks ω n)

lemma orientedExternalPath_shifted_blocks (ω : StepPath) (n : ℕ) (hn : 0 < n) :
    orientedExternalPath .shifted (pathPrefix (trajectory ω) n) =
      blockPath (trajectory ω 1)
          (PathInsertion.deleteRemovableBlocks .shifted
            (List.ofFn (pairedSegment 1 ((n - 1) / 2) ω))) ++
        shiftedPrefixRemainder ω n := by
  unfold orientedExternalPath shiftedExternalPath
  rw [shiftedInput_eq_segmentPath ω n hn, segmentPath_eq_blockPath_append_remainder,
    ← shiftedCompletePrefixBlocks, ← list_ofFn_pairedSegment_one]
  unfold shiftedPrefixRemainder segmentRemainder
  by_cases hmod : (n - 1) % 2 = 0
  · simp [hmod, PathInsertion.externalPath_blockPath]
  · simp only [hmod, if_false]
    exact externalPath_blockPath_append_singleton .shifted (trajectory ω 1)
      (trajectory ω (1 + (n - 1)))
      (List.ofFn (pairedSegment 1 ((n - 1) / 2) ω))

lemma filter_prefixRemainder_even (ω : StepPath) (n : ℕ) :
    (prefixRemainder ω n).filter (orientationClass .even) = [] := by
  unfold prefixRemainder
  by_cases hmod : n % 2 = 0
  · simp [hmod]
  · have hn : n = 2 * (n / 2) + 1 := by
      have hdiv := Nat.div_add_mod n 2
      omega
    have hodd := trajectory_odd_time ω (n / 2)
    have hnot : ¬EvenPoint (trajectory ω n) := by
      rw [hn]
      intro heven
      rw [OddPoint, heven] at hodd
      exact zero_ne_one hodd
    simp [hmod, orientationClass, hnot]

lemma filter_shiftedPrefixRemainder (ω : StepPath) (n : ℕ) :
    (shiftedPrefixRemainder ω n).filter (orientationClass .shifted) = [] := by
  unfold shiftedPrefixRemainder segmentRemainder
  by_cases hmod : (n - 1) % 2 = 0
  · simp [hmod]
  · have hn : n - 1 = 2 * ((n - 1) / 2) + 1 := by
      have hdiv := Nat.div_add_mod (n - 1) 2
      omega
    have heven := trajectory_even_time ω (((n - 1) / 2) + 1)
    have htime : 1 + (n - 1) = 2 * (((n - 1) / 2) + 1) := by omega
    have hnot : ¬OddPoint (trajectory ω (1 + (n - 1))) := by
      rw [htime]
      intro hodd
      rw [EvenPoint, hodd] at heven
      exact one_ne_zero heven
    simp [hmod, orientationClass, hnot]

lemma even_orientedExternalThickCount_eq_deletedBlocks
    (ω : StepPath) (n k : ℕ) :
    orientedExternalThickCount .even (trajectory ω) n k =
      listThickCount
        (blockEndpointPath (0, 0)
          (PathInsertion.deleteRemovableBlocks .even
            (List.ofFn (pairedSegment 0 (n / 2) ω)))) k := by
  rw [orientedExternalThickCount_eq_filtered,
    orientedExternalPath_even_blocks, List.filter_append,
    filter_prefixRemainder_even, List.append_nil]
  rw [blockPath_filter_orientationClass]
  simp [OrientationCompatible, EvenPoint, pointParity]

lemma shifted_orientedExternalThickCount_eq_deletedBlocks
    (ω : StepPath) (n k : ℕ) (hn : 0 < n) :
    orientedExternalThickCount .shifted (trajectory ω) n k =
      listThickCount
        (blockEndpointPath (trajectory ω 1)
          (PathInsertion.deleteRemovableBlocks .shifted
            (List.ofFn (pairedSegment 1 ((n - 1) / 2) ω)))) k := by
  rw [orientedExternalThickCount_eq_filtered,
    orientedExternalPath_shifted_blocks ω n hn, List.filter_append,
    filter_shiftedPrefixRemainder, List.append_nil]
  rw [blockPath_filter_orientationClass]
  exact trajectory_odd_time ω 0

lemma even_thick_iff_hasGoodExtracted (ω : StepPath) (n J k : ℕ) :
    J < orientedExternalThickCount .even (trajectory ω) n k ↔
      HasGoodExtracted .even (thickWordProperty .even J k)
        (pairedSegment 0 (n / 2) ω) := by
  let u := pairedSegment 0 (n / 2) ω
  rw [even_orientedExternalThickCount_eq_deletedBlocks]
  constructor
  · intro h
    let j := (retainedIndices .even u).card
    let hu : (retainedIndices .even u).card = j := rfl
    refine ⟨j, hu, ?_⟩
    unfold thickWordProperty finiteExternalPositionList
    rw [← deleteRemovableBlocks_eq_extractedWord .even u hu]
    exact h
  · rintro ⟨j, hu, h⟩
    unfold thickWordProperty finiteExternalPositionList at h
    rw [← deleteRemovableBlocks_eq_extractedWord .even u hu] at h
    exact h

lemma shifted_thick_iff_hasGoodExtracted (ω : StepPath) (n J k : ℕ) (hn : 0 < n) :
    J < orientedExternalThickCount .shifted (trajectory ω) n k ↔
      HasGoodExtracted .shifted (thickWordProperty .shifted J k)
        (pairedSegment 1 ((n - 1) / 2) ω) := by
  let u := pairedSegment 1 ((n - 1) / 2) ω
  rw [shifted_orientedExternalThickCount_eq_deletedBlocks ω n k hn]
  constructor
  · intro h
    let j := (retainedIndices .shifted u).card
    let hu : (retainedIndices .shifted u).card = j := rfl
    refine ⟨j, hu, ?_⟩
    unfold thickWordProperty finiteExternalPositionList
    rw [← deleteRemovableBlocks_eq_extractedWord .shifted u hu]
    rw [listThickCount_blockEndpointPath_translate] at h
    exact h
  · rintro ⟨j, hu, h⟩
    unfold thickWordProperty finiteExternalPositionList at h
    rw [← deleteRemovableBlocks_eq_extractedWord .shifted u hu] at h
    rw [listThickCount_blockEndpointPath_translate]
    exact h

/-! ## Exact finite masses and stochastic domination -/

def goodBlockFinset (o : Orientation) (J k q : ℕ) :
    Finset (Fin q → ExternalWalk.Block) :=
  Finset.univ.filter (HasGoodExtracted o (thickWordProperty o J k))

def goodRetainedFinset (o : Orientation) (J k N : ℕ) :
    Finset (Fin N → ExternalWalk.RetainedBlock o) :=
  Finset.univ.filter (thickWordProperty o J k N)

noncomputable def filterUnivSubtypeEquiv {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] :
    ↥(Finset.univ.filter P) ≃ {x : α // P x} where
  toFun x := ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
  invFun x := ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

lemma card_goodBlockFinset (o : Orientation) (J k q : ℕ) :
    (goodBlockFinset o J k q).card =
      Fintype.card (GoodBlockWords o (thickWordProperty o J k) q) := by
  calc
    (goodBlockFinset o J k q).card =
        Nat.card ↥(goodBlockFinset o J k q) :=
      (Nat.card_eq_finsetCard _).symm
    _ = Nat.card (GoodBlockWords o (thickWordProperty o J k) q) :=
      Nat.card_congr (filterUnivSubtypeEquiv
        (HasGoodExtracted o (thickWordProperty o J k)))
    _ = _ := Nat.card_eq_fintype_card

lemma card_goodRetainedFinset (o : Orientation) (J k N : ℕ) :
    (goodRetainedFinset o J k N).card =
      Fintype.card (GoodRetainedWords o (thickWordProperty o J k) N) := by
  calc
    (goodRetainedFinset o J k N).card =
        Nat.card ↥(goodRetainedFinset o J k N) :=
      (Nat.card_eq_finsetCard _).symm
    _ = Nat.card (GoodRetainedWords o (thickWordProperty o J k) N) :=
      Nat.card_congr (filterUnivSubtypeEquiv (thickWordProperty o J k N))
    _ = _ := Nat.card_eq_fintype_card

theorem fairSteps_hasGood_pairedSegment (o : Orientation)
    (a J k q : ℕ) :
    fairSteps {ω | HasGoodExtracted o (thickWordProperty o J k)
        (pairedSegment a q ω)} =
      (Fintype.card (GoodBlockWords o (thickWordProperty o J k) q) : ℝ≥0∞) /
        16 ^ q := by
  let G := goodBlockFinset o J k q
  have hG : MeasurableSet (G : Set (Fin q → ExternalWalk.Block)) := by
    measurability
  calc
    fairSteps {ω | HasGoodExtracted o (thickWordProperty o J k)
        (pairedSegment a q ω)} =
        (fairSteps.map (pairedSegment a q)) G := by
      rw [Measure.map_apply (measurable_pairedSegment a q) hG]
      congr 1
      ext ω
      simp [G, goodBlockFinset]
    _ = ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin q → ExternalWalk.Block)) G := by
      rw [fairSteps_map_pairedSegment]
    _ = (G.card : ℝ≥0∞) / 16 ^ q := by
      rw [ProbabilityTheory.uniformOn_univ, Measure.count_apply_finset]
      congr 2
      simp
    _ = _ := by rw [card_goodBlockFinset]

theorem externalBlocks_externalThickCount_mass (o : Orientation)
    (J k N : ℕ) :
    externalBlocks o {η | J < externalThickCount o η N k} =
      (Fintype.card (GoodRetainedWords o (thickWordProperty o J k) N) : ℝ≥0∞) /
        15 ^ N := by
  let G := goodRetainedFinset o J k N
  have hG : MeasurableSet (G : Set (Fin N → ExternalWalk.RetainedBlock o)) := by
    measurability
  have hevent : {η | J < externalThickCount o η N k} =
      externalPrefix o N ⁻¹' (G : Set (Fin N → ExternalWalk.RetainedBlock o)) := by
    ext η
    change J < externalThickCount o η N k ↔
      externalPrefix o N η ∈ goodRetainedFinset o J k N
    simp only [goodRetainedFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold externalThickCount thickWordProperty
    rw [finiteExternalPositionList_externalPrefix]
  calc
    externalBlocks o {η | J < externalThickCount o η N k} =
        (externalBlocks o).map (externalPrefix o N) G := by
      rw [hevent, Measure.map_apply (measurable_externalPrefix o N) hG]
    _ = externalBlockLaw o N G := by rw [externalBlocks_map_externalPrefix]
    _ = ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin N → ExternalWalk.RetainedBlock o)) G := by
      rw [externalBlockLaw_eq_uniform]
    _ = (G.card : ℝ≥0∞) / 15 ^ N := by
      rw [ProbabilityTheory.uniformOn_univ, Measure.count_apply_finset]
      congr 2
      simp
    _ = _ := by rw [card_goodRetainedFinset]

theorem fairSteps_hasGood_pairedSegment_le_externalBlocks
    (o : Orientation) (a J k q N : ℕ) (hqN : q ≤ N) :
    fairSteps {ω | HasGoodExtracted o (thickWordProperty o J k)
        (pairedSegment a q ω)} ≤
      externalBlocks o {η | J < externalThickCount o η N k} := by
  rw [fairSteps_hasGood_pairedSegment,
    externalBlocks_externalThickCount_mass]
  let A := Fintype.card (GoodBlockWords o (thickWordProperty o J k) q)
  let B := Fintype.card (GoodRetainedWords o (thickWordProperty o J k) N)
  have hcrossNat : A * 15 ^ N ≤ B * 16 ^ q :=
    card_goodBlockWords_mul_pow_le o J k q N hqN
  have hcross : (A : ℝ≥0∞) * 15 ^ N ≤ (B : ℝ≥0∞) * 16 ^ q := by
    exact_mod_cast hcrossNat
  have h16zero : (16 : ℝ≥0∞) ^ q ≠ 0 := by positivity
  have h16top : (16 : ℝ≥0∞) ^ q ≠ ∞ := by simp
  rw [ENNReal.div_le_iff h16zero h16top]
  have hrearrange : (B : ℝ≥0∞) / 15 ^ N * 16 ^ q =
      ((B : ℝ≥0∞) * 16 ^ q) / 15 ^ N := by
    simp only [ENNReal.div_eq_inv_mul]
    ac_rfl
  rw [hrearrange]
  apply (ENNReal.le_div_iff_mul_le (by left; positivity) (by left; simp)).2
  exact hcross

lemma measurable_orientedExternalThickCount (o : Orientation) (n k : ℕ) :
    Measurable fun s : WalkPath ↦ orientedExternalThickCount o s n k := by
  let F : (Fin (n + 1) → Point) → ℕ := fun u ↦
    candidateCount
      (fun _ ↦ (orientedExternalPath o u).toFinset.filter (orientationClass o))
      (fun x ↦ {v | k ≤ listLocalTime (orientedExternalPath o v) x}) u
  have hF : Measurable F := measurable_of_countable F
  exact hF.comp (measurable_pathPrefix n)

lemma measurableSet_orientedExternalThickCount_gt (o : Orientation)
    (n k J : ℕ) :
    MeasurableSet {s : WalkPath | J < orientedExternalThickCount o s n k} := by
  exact measurableSet_lt measurable_const (measurable_orientedExternalThickCount o n k)

/-! ## Transport from the canonical walk -/

/-- In the even deletion, the first `n / 2` complete direction pairs contain
all relevant checkerboard endpoints through ordinary time `n`.  Deleting the
removable pairs and then forgetting how many pairs survived is stochastically
dominated by running the IID retained-block chain for `n` blocks. -/
theorem simpleRandomWalk_even_orientedExternalThickCount_le
    (n J k : ℕ) :
    simpleRandomWalk {s |
        J < orientedExternalThickCount .even s n k} ≤
      externalBlocks .even {η |
        J < externalThickCount .even η n k} := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (measurableSet_orientedExternalThickCount_gt .even n k J)]
  have hevent :
      trajectory ⁻¹' {s : WalkPath |
          J < orientedExternalThickCount .even s n k} =
        {ω : StepPath |
          HasGoodExtracted .even (thickWordProperty .even J k)
            (pairedSegment 0 (n / 2) ω)} := by
    ext ω
    exact even_thick_iff_hasGoodExtracted ω n J k
  rw [hevent]
  exact fairSteps_hasGood_pairedSegment_le_externalBlocks
    .even 0 J k (n / 2) n (Nat.div_le_self n 2)

/-- The analogous transport for the shifted deletion.  For a positive
ordinary-time horizon, the complete shifted pairs start at direction one;
the initial point of their endpoint chain is removed by translation
invariance. -/
theorem simpleRandomWalk_shifted_orientedExternalThickCount_le
    (n J k : ℕ) (hn : 0 < n) :
    simpleRandomWalk {s |
        J < orientedExternalThickCount .shifted s n k} ≤
      externalBlocks .shifted {η |
        J < externalThickCount .shifted η n k} := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (measurableSet_orientedExternalThickCount_gt .shifted n k J)]
  have hevent :
      trajectory ⁻¹' {s : WalkPath |
          J < orientedExternalThickCount .shifted s n k} =
        {ω : StepPath |
          HasGoodExtracted .shifted (thickWordProperty .shifted J k)
            (pairedSegment 1 ((n - 1) / 2) ω)} := by
    ext ω
    exact shifted_thick_iff_hasGoodExtracted ω n J k hn
  rw [hevent]
  apply fairSteps_hasGood_pairedSegment_le_externalBlocks
  omega

/-- The exact path-to-IID external-chain transport required by the checked
HLOZ Proposition 4.4 assembly.  This theorem uses only the finite thinning
law above; in particular it does not assume the one-point tail estimate
(7.4), nor any consequence of Proposition 4.4. -/
theorem externalCountTransport44 (o : Orientation) (m : ℕ) :
    HLOZGapEstimate.ExternalCountTransport44 o m := by
  unfold HLOZGapEstimate.ExternalCountTransport44
  cases o with
  | even =>
      exact simpleRandomWalk_even_orientedExternalThickCount_le
        (hlozCutoff44 m) (hlozSiteBudget44 m) (hlozThickLevel44 m)
  | shifted =>
      apply simpleRandomWalk_shifted_orientedExternalThickCount_le
      exact levelCutoffTime_pos hlozDelta44 m

/-- Eventual form consumed directly by the gap-screening assembly. -/
theorem eventually_externalCountTransport44 (o : Orientation) :
    ∀ᶠ m : ℕ in Filter.atTop, HLOZGapEstimate.ExternalCountTransport44 o m :=
  Filter.Eventually.of_forall (externalCountTransport44 o)

end

end Erdos1165.ExternalCountTransport
