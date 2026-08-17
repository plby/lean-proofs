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

import ErdosProblems.Erdos636.Crowd
import ErdosProblems.Erdos636.MarkedPacking
import ErdosProblems.Erdos636.OuterAssembly
import ErdosProblems.Erdos636.RoundedParameters
import ErdosProblems.Erdos636.Structural
import ErdosProblems.Erdos636.Switching

/-!
# The two switching stages in the Kwan--Sudakov outer assembly

This file is the finite interface between the structural and balanced
augmentation packages for Erdős Problem 636.  It records, without any
asymptotic notation, the following steps of the paper.

* Equal switching cells can be ordered and switched one vertex at a time.
* The first separated-switching lemma turns the structural discrepancy into
  a separated path.
* `Crowd.BlockCrowdData` supplies simultaneous crowd anchors on all time
  blocks.
* A *single* deletion outcome supplies many good augmentation windows and an
  `L¹` error budget.  A deterministic estimate converts that budget to the
  exceptional-jump budget required by the second switching lemma.
* The second separated path is packaged as
  `OuterAssembly.SeparatedWindows`, and pointwise rounded outputs are chosen
  simultaneously to form `OuterAssembly.RoundedAssemblyInput`.

The genuinely probabilistic balanced-augmentation assertion is exposed as
the structure `SharedAugmentationOutcome`.  Consequently a future proof of
that assertion has one precise target and no part of the deterministic
outer assembly has to be repeated.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636.OuterSwitching

open OuterAssembly RoundedParameters

universe u w

noncomputable section

/-! ## Ordering the two switching cells -/

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The canonical ordering of a finset of known cardinality. -/
def finsetOrdering (W : Finset V) (n : ℕ) (hW : W.card = n) : Fin n → V :=
  fun i ↦ ((Finset.equivFin W).symm (Fin.cast hW.symm i)).1

lemma finsetOrdering_mem (W : Finset V) (n : ℕ) (hW : W.card = n)
    (i : Fin n) : finsetOrdering W n hW i ∈ W :=
  ((Finset.equivFin W).symm (Fin.cast hW.symm i)).2

lemma finsetOrdering_injective (W : Finset V) (n : ℕ) (hW : W.card = n) :
    Function.Injective (finsetOrdering W n hW) := by
  intro i j hij
  apply Fin.cast_injective
  apply (Finset.equivFin W).symm.injective
  exact Subtype.ext hij

lemma finsetOrdering_surjective_on (W : Finset V) (n : ℕ)
    (hW : W.card = n) :
    ∀ v ∈ W, ∃ i : Fin n, finsetOrdering W n hW i = v := by
  intro v hv
  let x : W := ⟨v, hv⟩
  let j : Fin W.card := Finset.equivFin W x
  refine ⟨Fin.cast hW j, ?_⟩
  simp [finsetOrdering, x, j]

/-- An explicit pair of orderings of two disjoint equally-sized switching
cells.  The orderings are deterministic; the probabilistic concentration
argument is represented later by the extra control fields in the shared
augmentation outcome. -/
structure SwitchingOrderings (Wminus Wplus : Finset V) (nW : ℕ) where
  minus : Fin nW → V
  plus : Fin nW → V
  minus_injective : Function.Injective minus
  plus_injective : Function.Injective plus
  minus_mem : ∀ i, minus i ∈ Wminus
  plus_mem : ∀ i, plus i ∈ Wplus
  minus_surjective : ∀ v ∈ Wminus, ∃ i, minus i = v
  plus_surjective : ∀ v ∈ Wplus, ∃ i, plus i = v

/-- Construct switching orderings for two equal finite cells. -/
def switchingOrderingsOfCard
    (Wminus Wplus : Finset V) (nW : ℕ)
    (hminus : Wminus.card = nW) (hplus : Wplus.card = nW) :
    SwitchingOrderings Wminus Wplus nW where
  minus := finsetOrdering Wminus nW hminus
  plus := finsetOrdering Wplus nW hplus
  minus_injective := finsetOrdering_injective Wminus nW hminus
  plus_injective := finsetOrdering_injective Wplus nW hplus
  minus_mem := finsetOrdering_mem Wminus nW hminus
  plus_mem := finsetOrdering_mem Wplus nW hplus
  minus_surjective := finsetOrdering_surjective_on Wminus nW hminus
  plus_surjective := finsetOrdering_surjective_on Wplus nW hplus

/-- The ordered switching state at time `i`: the first `i` plus-vertices
have entered and the first `i` minus-vertices have left. -/
def SwitchingOrderings.state {Wminus Wplus : Finset V} {nW : ℕ}
    (O : SwitchingOrderings Wminus Wplus nW) (i : ℕ) : Finset V :=
  ((Finset.univ.filter fun j : Fin nW ↦ i ≤ j).image O.minus) ∪
    ((Finset.univ.filter fun j : Fin nW ↦ j < i).image O.plus)

lemma SwitchingOrderings.state_zero {Wminus Wplus : Finset V} {nW : ℕ}
    (O : SwitchingOrderings Wminus Wplus nW) : O.state 0 = Wminus := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hv
      exact O.minus_mem i
    · simp at hv
  · intro hv
    obtain ⟨i, rfl⟩ := O.minus_surjective v hv
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

lemma SwitchingOrderings.state_last {Wminus Wplus : Finset V} {nW : ℕ}
    (O : SwitchingOrderings Wminus Wplus nW) : O.state nW = Wplus := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hv
      exfalso
      have hi' : nW ≤ i := (Finset.mem_filter.mp hi).2
      exact (not_lt_of_ge hi') i.isLt
    · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hv
      exact O.plus_mem i
  · intro hv
    obtain ⟨i, rfl⟩ := O.plus_surjective v hv
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

lemma SwitchingOrderings.state_subset_union
    {Wminus Wplus : Finset V} {nW : ℕ}
    (O : SwitchingOrderings Wminus Wplus nW) (i : ℕ) :
    O.state i ⊆ Wminus ∪ Wplus := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_union_left _ (O.minus_mem j)
  · obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_union_right _ (O.plus_mem j)

lemma SwitchingOrderings.state_card
    {Wminus Wplus : Finset V} {nW : ℕ}
    (O : SwitchingOrderings Wminus Wplus nW)
    (hdisj : Disjoint Wminus Wplus) (i : ℕ) :
    (O.state i).card = nW := by
  let A : Finset (Fin nW) := Finset.univ.filter fun j ↦ i ≤ j
  let B : Finset (Fin nW) := Finset.univ.filter fun j ↦ j < i
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro j hjA hjB
    have ha := (Finset.mem_filter.mp hjA).2
    have hb := (Finset.mem_filter.mp hjB).2
    omega
  have hUnion : A ∪ B = Finset.univ := by
    ext j
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨fun _ ↦ trivial, fun _ ↦ le_or_gt i (j : ℕ)⟩
  have hImageDisj : Disjoint (A.image O.minus) (B.image O.plus) := by
    rw [Finset.disjoint_left]
    intro v hvMinus hvPlus
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hvMinus
    obtain ⟨b, _hb, hab⟩ := Finset.mem_image.mp hvPlus
    exact Finset.disjoint_left.mp hdisj (O.minus_mem a)
      (hab ▸ O.plus_mem b)
  change (A.image O.minus ∪ B.image O.plus).card = nW
  rw [Finset.card_union_of_disjoint hImageDisj,
    Finset.card_image_of_injective _ O.minus_injective,
    Finset.card_image_of_injective _ O.plus_injective]
  rw [← Finset.card_union_of_disjoint hAB, hUnion]
  simp

lemma SwitchingOrderings.disjoint_state_of_disjoint_union
    {Wminus Wplus U : Finset V} {nW : ℕ}
    (O : SwitchingOrderings Wminus Wplus nW)
    (h : Disjoint (Wminus ∪ Wplus) U) (i : ℕ) :
    Disjoint (O.state i) U :=
  Finset.disjoint_of_subset_left (O.state_subset_union i) h

/-- A structural witness always supplies the two ordered switching cells. -/
def orderingsOfStructuralWitness {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) :
    SwitchingOrderings S.Wminus S.Wplus nW :=
  switchingOrderingsOfCard S.Wminus S.Wplus nW S.card_Wminus S.card_Wplus

/-- The exact uniform degree-control predicate used after the concentration
argument.  It deliberately keeps the deterministic comparison path
`expected` explicit. -/
structure UniformDegreeControlledOrderings {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (error : ℝ) extends SwitchingOrderings S.Wminus S.Wplus nW where
  expected : ℕ → ℝ
  degree_control : ∀ i ≤ nW, ∀ x ∈ S.matching,
    |(degreeInto G (toSwitchingOrderings.state i) x : ℝ) - expected i| ≤ error

/-- A coarse deterministic uniform control, useful as a sanity check on the
interface.  The paper's permutation concentration replaces the error
`K*nW` by `sqrt(scale)*log(scale)`. -/
def coarseUniformDegreeControlledOrderings {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) :
    UniformDegreeControlledOrderings S (K * nW : ℕ) := by
  let O := orderingsOfStructuralWitness S
  refine {
    toSwitchingOrderings := O
    expected := fun _ ↦ 0
    degree_control := ?_ }
  intro i hi x hx
  rw [sub_zero, abs_of_nonneg (by positivity)]
  exact_mod_cast (calc
    degreeInto G (O.state i) x ≤ x.card * (O.state i).card :=
      (by
        rw [degreeInto]
        calc
          ∑ v ∈ x, (Erdos88.neighborsIn G v (O.state i)).card ≤
              ∑ _v ∈ x, (O.state i).card := by
            apply Finset.sum_le_sum
            intro v _hv
            apply Finset.card_le_card
            intro z hz
            exact (Erdos88.mem_neighborsIn.mp hz).1
          _ = x.card * (O.state i).card := by simp)
    _ = S.k * nW := by rw [O.state_card S.disjoint_Wminus_Wplus,
      S.matching_uniform x hx]
    _ ≤ K * nW := Nat.mul_le_mul_right nW S.k_le)

/-! ## The first separated path -/

/-- The exact output of one application of the separated-switching lemma. -/
structure SeparatedPath (τ m : ℕ) (p : ℕ → ℝ) (sigma : ℝ) where
  index : Fin (m + 1) → ℕ
  strictMono : StrictMono index
  index_zero : index 0 = 0
  index_last : index (Fin.last m) = τ
  step : ∀ j : Fin m,
    sigma ≤ p (index j.succ) - p (index j.castSucc)

/-- Positive consecutive increments separate every pair of values in a
finite chain. -/
lemma sigma_le_abs_sub_of_chain
    {m : ℕ} (q : Fin (m + 1) → ℝ) {sigma : ℝ}
    (hsigma : 0 < sigma)
    (hstep : ∀ j : Fin m, sigma ≤ q j.succ - q j.castSucc)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    sigma ≤ |q i - q j| := by
  have hqStrict : StrictMono q := by
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    have hk := hstep k
    linarith
  have hforward : ∀ {a b : Fin (m + 1)}, a < b →
      sigma ≤ |q a - q b| := by
    intro a b hab
    have ham : a.val < m := by omega
    let k : Fin m := ⟨a.val, ham⟩
    have hkcast : k.castSucc = a := by ext; rfl
    have hksucc : k.succ ≤ b := by
      rw [Fin.mk_le_mk]
      exact Nat.succ_le_of_lt (Fin.val_fin_lt.mpr hab)
    have hmono : q k.succ ≤ q b := hqStrict.monotone hksucc
    have hs := hstep k
    rw [hkcast] at hs
    have habq : q a ≤ q b := hqStrict.monotone hab.le
    rw [abs_of_nonpos (sub_nonpos.mpr habq)]
    linarith
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hforward hij
  · simpa [abs_sub_comm] using hforward hji

/-- The weighted structural score along an ordered switching path. -/
def structuralSwitchingScore {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (O : SwitchingOrderings S.Wminus S.Wplus nW) (i : ℕ) : ℝ :=
  weightedScore G alpha S.U0 (O.state i)

lemma structuralSwitchingScore_rise {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (O : SwitchingOrderings S.Wminus S.Wplus nW) :
    aDisc * scale * Real.sqrt scale ≤
      structuralSwitchingScore S O nW - structuralSwitchingScore S O 0 := by
  rw [structuralSwitchingScore, structuralSwitchingScore,
    O.state_zero, O.state_last]
  exact S.discrepancy

/-- Package the conclusion of `Switching.separatedSwitchingSubsequence`. -/
noncomputable def separatedPathOfBudget
    {τ m : ℕ} (p : ℕ → ℝ) {lam kappa rho sigma : ℝ}
    (hm : 1 ≤ m) (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hrise : lam ≤ p τ - p 0)
    (hlarge : Switching.largeIncrementSum p rho τ ≤ kappa)
    (hbudget : (m : ℝ) * (rho + sigma) + kappa ≤ lam) :
    SeparatedPath τ m p sigma := by
  let h := Switching.separatedSwitchingSubsequence
    p hm hrho hsigma hrise hlarge hbudget
  exact {
    index := Classical.choose h
    strictMono := (Classical.choose_spec h).1
    index_zero := (Classical.choose_spec h).2.1
    index_last := (Classical.choose_spec h).2.2.1
    step := (Classical.choose_spec h).2.2.2 }

/-- First switching directly from a structural witness.  The only remaining
input is the exceptional-jump estimate, which is exactly what the crowd
blocks and degree-concentration argument establish. -/
noncomputable def firstSeparatedPathOfStructuralWitness
    {G : SimpleGraph V} {scale nW ell K m : ℕ}
    {alpha aDisc aDiv b kappa rho sigma : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (O : SwitchingOrderings S.Wminus S.Wplus nW)
    (hm : 1 ≤ m) (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hlarge : Switching.largeIncrementSum
      (structuralSwitchingScore S O) rho nW ≤ kappa)
    (hbudget : (m : ℝ) * (rho + sigma) + kappa ≤
      aDisc * scale * Real.sqrt scale) :
    SeparatedPath nW m (structuralSwitchingScore S O) sigma :=
  separatedPathOfBudget (structuralSwitchingScore S O) hm hrho hsigma
    (structuralSwitchingScore_rise S O) hlarge hbudget

/-! ## Crowd blocks -/

/-- The fully explicit result of applying the crowd lemma on every block. -/
structure CrowdExtraction {R B : Type*} [Fintype R] [Fintype B]
    (D : Crowd.BlockCrowdData B R) where
  anchor : B → R
  crowd : B → ℕ → Finset R
  crowd_eq : ∀ b t, crowd b t = D.nearby b t (anchor b)
  crowd_large : ∀ b t, t ≤ D.last b →
    D.threshold b ≤ (crowd b t).card

/-- `BlockCrowdData` gives all block anchors and all crowd subfamilies at
once; this is the dependent-choice step used before the first switching. -/
noncomputable def crowdExtraction {R B : Type*} [Fintype R] [Fintype B]
    (D : Crowd.BlockCrowdData B R) : CrowdExtraction D := by
  let h := Crowd.exists_block_anchors_and_crowds D
  exact {
    anchor := Classical.choose h
    crowd := Classical.choose (Classical.choose_spec h)
    crowd_eq := (Classical.choose_spec (Classical.choose_spec h)).1
    crowd_large := (Classical.choose_spec (Classical.choose_spec h)).2 }

/-! ## Turning an `L¹` error budget into a jump budget -/

lemma largeIncrement_le_two_abs_error
    (p base error : ℕ → ℝ) {jump : ℝ} (hjump : 0 ≤ jump)
    (i : ℕ) (hbase : |base i| ≤ jump)
    (hdecomp : p (i + 1) - p i = base i + error i) :
    Switching.largeIncrement p (2 * jump) i ≤ 2 * |error i| := by
  rw [Switching.largeIncrement]
  split_ifs with hlarge
  · have hbaseLower := (abs_le.mp hbase).1
    have hbaseUpper := (abs_le.mp hbase).2
    have herrPos : 0 < error i := by linarith
    rw [abs_of_pos herrPos]
    linarith
  · positivity

lemma largeIncrementSum_le_two_sum_abs_error
    (p base error : ℕ → ℝ) {τ : ℕ} {jump : ℝ}
    (hjump : 0 ≤ jump)
    (hbase : ∀ i < τ, |base i| ≤ jump)
    (hdecomp : ∀ i < τ,
      p (i + 1) - p i = base i + error i) :
    Switching.largeIncrementSum p (2 * jump) τ ≤
      2 * ∑ i ∈ Finset.range τ, |error i| := by
  rw [Switching.largeIncrementSum, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi ↦
    largeIncrement_le_two_abs_error p base error hjump i
      (hbase i (Finset.mem_range.mp hi))
      (hdecomp i (Finset.mem_range.mp hi))

/-! ## A common deletion outcome and the second switching -/

/-- Deterministic data left after fixing one successful deletion outcome.

`goodTime` enumerates the augmentation windows which are good for that
*same* deletion.  The centre increments are split into a controlled
deterministic part and a random error.  The displayed `L¹` bound is exactly
what Markov's inequality supplies in the paper. -/
structure SharedAugmentationOutcome {DState : Type w}
    (spectrum : Finset ℕ) (n : ℕ) where
  sharedDeletion : DState
  last : ℕ
  sourceLast : ℕ
  goodTime : Fin (last + 1) → ℕ
  goodTime_strictMono : StrictMono goodTime
  goodTime_le : ∀ i, goodTime i ≤ sourceLast
  center : ℕ → ℝ
  deterministicIncrement : ℕ → ℝ
  randomError : ℕ → ℝ
  jumpBound : ℝ
  errorBudget : ℝ
  jumpBound_nonneg : 0 ≤ jumpBound
  deterministicIncrement_bound : ∀ i < last,
    |deterministicIncrement i| ≤ jumpBound
  increment_decomposition : ∀ i < last,
    center (i + 1) - center i =
      deterministicIncrement i + randomError i
  randomError_l1 :
    ∑ i ∈ Finset.range last, |randomError i| ≤ errorBudget
  piece : ℕ → Finset ℕ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  in_window : ∀ i ≤ last, ∀ e ∈ piece i,
    |(e : ℝ) - center i| ≤ radius
  piece_subset : ∀ i ≤ last, piece i ⊆ spectrum

/-- This is the precise abstract interface expected from the balanced
augmentation theorem: for the whole retained switching path it returns one
deletion outcome and all its good windows, not a separately chosen deletion
for every time. -/
def BalancedAugmentationInterface {State : Type*} {DState : Type w}
    (spectrum : State → Finset ℕ) (n : ℕ) : Prop :=
  ∀ path : Finset State, Nonempty (SharedAugmentationOutcome
    (DState := DState) (path.biUnion spectrum) n)

lemma SharedAugmentationOutcome.largeIncrementSum_le
    {DState : Type w} {spectrum : Finset ℕ} {n : ℕ}
    (O : SharedAugmentationOutcome (DState := DState) spectrum n) :
    Switching.largeIncrementSum O.center (2 * O.jumpBound) O.last ≤
      2 * O.errorBudget := by
  calc
    Switching.largeIncrementSum O.center (2 * O.jumpBound) O.last ≤
        2 * ∑ i ∈ Finset.range O.last, |O.randomError i| :=
      largeIncrementSum_le_two_sum_abs_error O.center
        O.deterministicIncrement O.randomError O.jumpBound_nonneg
        O.deterministicIncrement_bound O.increment_decomposition
    _ ≤ 2 * O.errorBudget :=
      mul_le_mul_of_nonneg_left O.randomError_l1 (by norm_num)

/-- Apply the second separated-switching lemma to a fixed shared
augmentation outcome and package its good windows. -/
noncomputable def SharedAugmentationOutcome.separatedWindows
    {DState : Type w} {spectrum : Finset ℕ} {n m : ℕ}
    (O : SharedAugmentationOutcome (DState := DState) spectrum n)
    {lam sigma : ℝ} (hm : 1 ≤ m) (hjump : 0 < O.jumpBound)
    (hsigma : 0 < sigma) (hrise : lam ≤ O.center O.last - O.center 0)
    (hbudget : (m : ℝ) * (2 * O.jumpBound + sigma) +
      2 * O.errorBudget ≤ lam)
    (hseparate : 2 * O.radius < sigma) :
    SeparatedWindows spectrum := by
  let P : SeparatedPath O.last m O.center sigma :=
    separatedPathOfBudget O.center hm (mul_pos two_pos hjump) hsigma
      hrise O.largeIncrementSum_le hbudget
  let I : Finset ℕ := Finset.univ.image P.index
  exact {
    index := I
    piece := O.piece
    center := O.center
    radius := O.radius
    radius_nonneg := O.radius_nonneg
    separated := by
      intro i hi j hj hij
      obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hj
      have hab : a ≠ b := fun h ↦ hij (congrArg P.index h)
      have hcenterStrict : StrictMono (fun r ↦ O.center (P.index r)) := by
        rw [Fin.strictMono_iff_lt_succ]
        intro r
        have hs := P.step r
        linarith
      have hdist := sigma_le_abs_sub_of_chain
        (fun r ↦ O.center (P.index r)) hsigma P.step hab
      rcases lt_or_gt_of_ne hab with hablt | hbalt
      · left
        have hcent : O.center (P.index a) < O.center (P.index b) :=
          hcenterStrict hablt
        rw [abs_of_nonpos (sub_nonpos.mpr hcent.le)] at hdist
        linarith
      · right
        have hcent : O.center (P.index b) < O.center (P.index a) :=
          hcenterStrict hbalt
        rw [abs_of_nonneg (sub_nonneg.mpr hcent.le)] at hdist
        linarith
    in_window := by
      intro i hi e he
      obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hi
      exact O.in_window (P.index a) (by
        calc
          P.index a ≤ P.index (Fin.last m) :=
            P.strictMono.monotone (Fin.le_last a)
          _ = O.last := P.index_last) e he
    piece_subset := by
      intro i hi
      obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hi
      exact O.piece_subset (P.index a) (by
        calc
          P.index a ≤ P.index (Fin.last m) :=
            P.strictMono.monotone (Fin.le_last a)
          _ = O.last := P.index_last) }

lemma SharedAugmentationOutcome.card_index_separatedWindows
    {DState : Type w} {spectrum : Finset ℕ} {n m : ℕ}
    (O : SharedAugmentationOutcome (DState := DState) spectrum n)
    {lam sigma : ℝ} (hm : 1 ≤ m) (hjump : 0 < O.jumpBound)
    (hsigma : 0 < sigma) (hrise : lam ≤ O.center O.last - O.center 0)
    (hbudget : (m : ℝ) * (2 * O.jumpBound + sigma) +
      2 * O.errorBudget ≤ lam)
    (hseparate : 2 * O.radius < sigma) :
    (O.separatedWindows hm hjump hsigma hrise hbudget hseparate).index.card =
      m + 1 := by
  simp only [SharedAugmentationOutcome.separatedWindows]
  rw [Finset.card_image_of_injective]
  · simp
  · exact (separatedPathOfBudget O.center hm (mul_pos two_pos hjump) hsigma
      hrise O.largeIncrementSum_le hbudget).strictMono.injective

lemma SharedAugmentationOutcome.piece_large_separatedWindows
    {DState : Type w} {spectrum : Finset ℕ} {n m : ℕ}
    (O : SharedAugmentationOutcome (DState := DState) spectrum n)
    {lam sigma d : ℝ} (hm : 1 ≤ m) (hjump : 0 < O.jumpBound)
    (hsigma : 0 < sigma) (hrise : lam ≤ O.center O.last - O.center 0)
    (hbudget : (m : ℝ) * (2 * O.jumpBound + sigma) +
      2 * O.errorBudget ≤ lam)
    (hseparate : 2 * O.radius < sigma)
    (hpiece : ∀ i ≤ O.last, d * n ≤ ((O.piece i).card : ℝ)) :
    ∀ i ∈ (O.separatedWindows hm hjump hsigma hrise hbudget hseparate).index,
      d * n ≤ (((O.separatedWindows hm hjump hsigma hrise hbudget
        hseparate).piece i).card : ℝ) := by
  intro i hi
  let P : SeparatedPath O.last m O.center sigma :=
    separatedPathOfBudget O.center hm (mul_pos two_pos hjump) hsigma
      hrise O.largeIncrementSum_le hbudget
  change i ∈ Finset.univ.image P.index at hi
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hi
  apply hpiece
  calc
    P.index a ≤ P.index (Fin.last m) :=
      P.strictMono.monotone (Fin.le_last a)
    _ = O.last := P.index_last

/-- Quantitative output of the shared-deletion and two-switching package. -/
theorem SharedAugmentationOutcome.large_spectrum_of_secondSwitching
    {DState : Type w} {spectrum : Finset ℕ} {n m : ℕ}
    (O : SharedAugmentationOutcome (DState := DState) spectrum n)
    {lam sigma b d : ℝ} (hm : 1 ≤ m) (hjump : 0 < O.jumpBound)
    (hsigma : 0 < sigma) (hrise : lam ≤ O.center O.last - O.center 0)
    (hbudget : (m : ℝ) * (2 * O.jumpBound + sigma) +
      2 * O.errorBudget ≤ lam)
    (hseparate : 2 * O.radius < sigma)
    (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hindex : b * Real.sqrt n ≤ (m + 1 : ℕ))
    (hpiece : ∀ i ≤ O.last, d * n ≤ ((O.piece i).card : ℝ)) :
    (b * d) * n * Real.sqrt n ≤ (spectrum.card : ℝ) := by
  let W := O.separatedWindows hm hjump hsigma hrise hbudget hseparate
  apply W.large_spectrum n b d hb hd
  · simpa [W, O.card_index_separatedWindows hm hjump hsigma hrise
      hbudget hseparate] using hindex
  · exact O.piece_large_separatedWindows hm hjump hsigma hrise hbudget
      hseparate hpiece

/-! ## The marked-centre packing form used in the final paper assembly -/

/-- Turn positive-proportion good augmentation windows and a global
perturbation budget into a separated-window family.  Unlike the second
switching constructor above, this form does not require changing the small
constant which defines the deletion density: the marked packing lemma pays
only the fixed factor `ceil(R/s) + 2`. -/
theorem exists_separatedWindows_of_markedPacking
    (spectrum : Finset ℕ) (x r : ℕ → ℝ) (piece : ℕ → Finset ℕ)
    (t n : ℕ) {s R theta windowRadius d : ℝ}
    (hs : 0 < s) (hR : 0 < R) (htheta : 0 < theta)
    (hr : ∀ u ∈ Finset.Icc 1 t, 0 ≤ r u)
    (hgrowth : ∀ {j k : ℕ}, j < k → k ≤ t →
      ((k - j : ℕ) : ℝ) * s - ∑ u ∈ Finset.Ioc j k, r u ≤ x k - x j)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range (t + 1))
    (hmarked : theta * t ≤ (J.card : ℝ))
    (herror : ∑ u ∈ Finset.Icc 1 t, r u ≤ theta / 2 * t * s)
    (hwindowRadius : 0 ≤ windowRadius)
    (hseparate : 2 * windowRadius < R)
    (hwindow : ∀ i ∈ J, ∀ e ∈ piece i,
      |(e : ℝ) - x i| ≤ windowRadius)
    (hsubset : ∀ i ∈ J, piece i ⊆ spectrum)
    (hpiece : ∀ i ∈ J, d * n ≤ ((piece i).card : ℝ)) :
    ∃ W : SeparatedWindows spectrum,
      theta / (2 * (⌈R / s⌉₊ + 2 : ℕ)) * t ≤ (W.index.card : ℝ) ∧
      ∀ i ∈ W.index, d * n ≤ ((W.piece i).card : ℝ) := by
  obtain ⟨J', hJ'J, hJ'sep, hJ'card⟩ :=
    MarkedPacking.exists_separated_subset_linear x r t hs hR htheta hr
      (by intro j k hjk hkt; exact hgrowth hjk hkt) J hJ hmarked herror
  let W : SeparatedWindows spectrum := {
    index := J'
    piece := piece
    center := x
    radius := windowRadius
    radius_nonneg := hwindowRadius
    separated := by
      intro i hi j hj hij
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · left
        have hgap := hJ'sep hi hj hijlt
        linarith
      · right
        have hgap := hJ'sep hj hi hjilt
        linarith
    in_window := fun i hi ↦ hwindow i (hJ'J hi)
    piece_subset := fun i hi ↦ hsubset i (hJ'J hi) }
  refine ⟨W, ?_, ?_⟩
  · exact hJ'card
  · intro i hi
    exact hpiece i (hJ'J hi)

/-! ## Pointwise construction and exact rounded outer choice -/

/-- The successful choice at one outer parameter. -/
structure PointwiseWindows (n K : ℕ) (cW c₀ delta₀ b d : ℝ)
    (spectra : ℕ → Finset ℕ) (ell : ℕ) where
  k : ℕ
  branch : Bool
  k_pos : 1 ≤ k
  k_le : k ≤ K
  windows : SeparatedWindows
    (spectra (ProfileReduction.selectedOffsetOrder (deletionSize c₀ n)
      (fun _ ↦ assemblyOffset cW c₀ delta₀ n k)
      (fun _ ↦ branch) ell))
  index_large : b * Real.sqrt n ≤ (windows.index.card : ℝ)
  piece_large : ∀ i ∈ windows.index,
    d * n ≤ ((windows.piece i).card : ℝ)

/-- Turn one fixed shared deletion outcome into the pointwise rounded object
consumed by the outer dependent-choice theorem. -/
noncomputable def pointwiseWindowsOfSharedOutcome
    {DState : Type w} {n K ell k m : ℕ}
    {cW c₀ delta₀ b d lam sigma : ℝ} {branch : Bool}
    {spectra : ℕ → Finset ℕ}
    (hkpos : 1 ≤ k) (hkle : k ≤ K)
    (O : SharedAugmentationOutcome (DState := DState)
      (spectra (ProfileReduction.selectedOffsetOrder (deletionSize c₀ n)
        (fun _ ↦ assemblyOffset cW c₀ delta₀ n k)
        (fun _ ↦ branch) ell)) n)
    (hm : 1 ≤ m) (hjump : 0 < O.jumpBound) (hsigma : 0 < sigma)
    (hrise : lam ≤ O.center O.last - O.center 0)
    (hbudget : (m : ℝ) * (2 * O.jumpBound + sigma) +
      2 * O.errorBudget ≤ lam)
    (hseparate : 2 * O.radius < sigma)
    (hindex : b * Real.sqrt n ≤ (m + 1 : ℕ))
    (hpiece : ∀ i ≤ O.last, d * n ≤ ((O.piece i).card : ℝ)) :
    PointwiseWindows n K cW c₀ delta₀ b d spectra ell where
  k := k
  branch := branch
  k_pos := hkpos
  k_le := hkle
  windows := O.separatedWindows hm hjump hsigma hrise hbudget hseparate
  index_large := by
    simpa [O.card_index_separatedWindows hm hjump hsigma hrise hbudget
      hseparate] using hindex
  piece_large := O.piece_large_separatedWindows hm hjump hsigma hrise hbudget
    hseparate hpiece

/-- Empty windows, used only to totalize the dependent choice away from the
outer parameter interval. -/
def emptySeparatedWindows (spectrum : Finset ℕ) : SeparatedWindows spectrum where
  index := ∅
  piece := fun _ ↦ ∅
  center := fun _ ↦ 0
  radius := 0
  radius_nonneg := le_rfl
  separated := by simp
  in_window := by simp
  piece_subset := by simp

private structure BarePointChoice (n : ℕ) (cW c₀ delta₀ : ℝ)
    (spectra : ℕ → Finset ℕ) (ell : ℕ) where
  k : ℕ
  branch : Bool
  windows : SeparatedWindows
    (spectra (ProfileReduction.selectedOffsetOrder (deletionSize c₀ n)
      (fun _ ↦ assemblyOffset cW c₀ delta₀ n k)
      (fun _ ↦ branch) ell))

/-- Simultaneously choose the structural value, successful branch, and
second-switching windows at every outer parameter.  The resulting order is
the exact rounded order used by `OuterAssembly`, including the dependence of
`k` on `ell`. -/
theorem nonempty_roundedAssemblyInput_of_pointwiseWindows
    {n K : ℕ} {cW c c₀ delta₀ deltaZ b d : ℝ}
    {spectra : ℕ → Finset ℕ}
    (B : Bounds c c₀ delta₀ deltaZ K n) (hK : 0 < K)
    (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hpoint : ∀ ell ∈ outerParameterInterval c n,
      Nonempty (PointwiseWindows n K cW c₀ delta₀ b d spectra ell)) :
    Nonempty (RoundedAssemblyInput n K cW c₀ delta₀ (c / 2) (b * d)
      spectra) := by
  let Choice := BarePointChoice n cW c₀ delta₀ spectra
  have hex : ∀ ell, ∃ A : Choice ell,
      ell ∈ outerParameterInterval c n →
        1 ≤ A.k ∧ A.k ≤ K ∧
        b * Real.sqrt n ≤ (A.windows.index.card : ℝ) ∧
        ∀ i ∈ A.windows.index,
          d * n ≤ ((A.windows.piece i).card : ℝ) := by
    intro ell
    by_cases hell : ell ∈ outerParameterInterval c n
    · let P := Classical.choice (hpoint ell hell)
      exact ⟨⟨P.k, P.branch, P.windows⟩, fun _ ↦
        ⟨P.k_pos, P.k_le, P.index_large, P.piece_large⟩⟩
    · let q := ProfileReduction.selectedOffsetOrder (deletionSize c₀ n)
          (fun _ ↦ assemblyOffset cW c₀ delta₀ n 1)
          (fun _ ↦ false) ell
      exact ⟨⟨1, false, emptySeparatedWindows (spectra q)⟩,
        fun h ↦ (hell h).elim⟩
  let A : ∀ ell, Choice ell := fun ell ↦ Classical.choose (hex ell)
  have hA : ∀ ell, ell ∈ outerParameterInterval c n →
      1 ≤ (A ell).k ∧ (A ell).k ≤ K ∧
      b * Real.sqrt n ≤ ((A ell).windows.index.card : ℝ) ∧
      ∀ i ∈ (A ell).windows.index,
        d * n ≤ (((A ell).windows.piece i).card : ℝ) :=
    fun ell ↦ Classical.choose_spec (hex ell)
  let k : ℕ → ℕ := fun ell ↦ (A ell).k
  let branch : ℕ → Bool := fun ell ↦ (A ell).branch
  let windows : ∀ ell, SeparatedWindows
      (spectra (ProfileReduction.selectedOffsetOrder (deletionSize c₀ n)
        (fun ell ↦ assemblyOffset cW c₀ delta₀ n (k ell)) branch ell)) :=
    fun ell ↦ (A ell).windows
  refine ⟨roundedAssemblyInputOfSeparatedWindows
    (outerParameterInterval c n) k branch B.parameter_linear ?_ ?_ ?_
      windows hb hd ?_ ?_⟩
  · intro ell hell
    have hthree := B.reservoir_large false ell hell
    have hthree' : 3 * deletionSize c₀ n ≤ ell := by
      simpa [branchScale] using hthree
    omega
  · intro ell hell
    exact (hA ell hell).1
  · intro ell hell
    exact (hA ell hell).2.1
  · intro ell hell
    exact (hA ell hell).2.2.1
  · intro ell hell i hi
    exact (hA ell hell).2.2.2 i hi

end

end Erdos636.OuterSwitching
