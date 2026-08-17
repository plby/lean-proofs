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
import ErdosProblems.Erdos636.Hypergeometric
import ErdosProblems.Erdos636.MarkedPacking
import ErdosProblems.Erdos636.OuterSwitching
import ErdosProblems.Erdos636.Structural
import ErdosProblems.Erdos636.Switching

/-!
# The outer switching path for Erdős Problem 636

This file is the finite interface between the structural witness and the
first switching argument in Kwan--Sudakov.  It has three layers.

* `permutationPrefix` and `RawPath` give the literal one-vertex-at-a-time
  path from `Wminus` to `Wplus`, with exactly constant cardinality.
* `Hypergeometric.exists_sampler_simultaneously_close` is a finite union
  bound around the fixed-slice concentration theorem.  It is designed for
  the family of all `(time, matching-edge)` degree statistics, while using
  one compatible tuple of permutations at every time.
* `CrowdSchedule` feeds the balanced path to the blockwise crowd lemma.
  The resulting `OuterPath` has a matching crowd at every time and an
  explicit exceptional-transition budget for its centre.  The last theorem
  applies `Switching.separatedSwitchingSubsequence` without any further
  rounding convention.

The asymptotic application takes a block count of order
`n^(1/4) log^3 n`, a degree jump of order `sqrt n log n`, and hence the
displayed product budget is `o(n^(3/2))`.  Here all three quantities remain
literal finite parameters; the main theorem only has to verify their
coarse numerical inequalities.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace OuterSwitchingPath

universe u v

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

open Erdos88.BooleanSlices

/-! ## Compatible prefixes and the exact switch path -/

/-- The first `r` values of a permutation of a finite set.  Outside the
natural range we use the whole set; all switching statements below only use
`r ≤ I.card`. -/
def permutationPrefix (I : Finset V)
    (sigma : Equiv.Perm (Fin I.card)) (r : ℕ) : Finset V :=
  if hr : r ≤ I.card then
    signedSlicePositiveSupport I r 0 (by omega) (Finset.equivFin I).symm sigma
  else I

lemma permutationPrefix_eq_of_le (I : Finset V)
    (sigma : Equiv.Perm (Fin I.card)) {r : ℕ} (hr : r ≤ I.card) :
    permutationPrefix I sigma r =
      signedSlicePositiveSupport I r 0 (by omega) (Finset.equivFin I).symm sigma := by
  simp [permutationPrefix, hr]

lemma permutationPrefix_subset (I : Finset V)
    (sigma : Equiv.Perm (Fin I.card)) (r : ℕ) :
    permutationPrefix I sigma r ⊆ I := by
  by_cases hr : r ≤ I.card
  · rw [permutationPrefix_eq_of_le I sigma hr]
    exact signedSlicePositiveSupport_subset I r 0 (by omega)
      (Finset.equivFin I).symm sigma
  · simp [permutationPrefix, hr]

@[simp] lemma card_permutationPrefix_of_le (I : Finset V)
    (sigma : Equiv.Perm (Fin I.card)) {r : ℕ} (hr : r ≤ I.card) :
    (permutationPrefix I sigma r).card = r := by
  rw [permutationPrefix_eq_of_le I sigma hr]
  exact card_signedSlicePositiveSupport I r 0 (by omega)
    (Finset.equivFin I).symm sigma

@[simp] lemma permutationPrefix_zero (I : Finset V)
    (sigma : Equiv.Perm (Fin I.card)) :
    permutationPrefix I sigma 0 = ∅ := by
  apply Finset.card_eq_zero.mp
  exact card_permutationPrefix_of_le I sigma (Nat.zero_le _)

@[simp] lemma permutationPrefix_card (I : Finset V)
    (sigma : Equiv.Perm (Fin I.card)) :
    permutationPrefix I sigma I.card = I := by
  have hcard := card_permutationPrefix_of_le I sigma (le_rfl : I.card ≤ I.card)
  exact Finset.eq_of_subset_of_card_le (permutationPrefix_subset I sigma I.card)
    (by simpa [hcard])

/-- Two permutations of the structural endpoint sets determine a literal
fixed-cardinality switching path. -/
structure RawPath {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) where
  minusPermutation : Equiv.Perm (Fin S.Wminus.card)
  plusPermutation : Equiv.Perm (Fin S.Wplus.card)

/-- The state at time `i`.  For `i > nW` it is harmlessly frozen by the
out-of-range convention in `permutationPrefix`. -/
def RawPath.W {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S) (i : ℕ) : Finset V :=
  permutationPrefix S.Wminus P.minusPermutation (nW - i) ∪
    permutationPrefix S.Wplus P.plusPermutation i

lemma RawPath.disjoint_parts {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S) (i : ℕ) :
    Disjoint
      (permutationPrefix S.Wminus P.minusPermutation (nW - i))
      (permutationPrefix S.Wplus P.plusPermutation i) := by
  exact S.disjoint_Wminus_Wplus.mono
    (permutationPrefix_subset _ _ _) (permutationPrefix_subset _ _ _)

@[simp] lemma RawPath.card_W {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S) {i : ℕ} (hi : i ≤ nW) :
    (P.W i).card = nW := by
  rw [RawPath.W, Finset.card_union_of_disjoint (P.disjoint_parts i)]
  have hminus : nW - i ≤ S.Wminus.card := by
    rw [S.card_Wminus]
    omega
  have hplus : i ≤ S.Wplus.card := by
    rw [S.card_Wplus]
    exact hi
  rw [card_permutationPrefix_of_le _ _ hminus,
    card_permutationPrefix_of_le _ _ hplus]
  omega

@[simp] lemma RawPath.W_zero {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S) : P.W 0 = S.Wminus := by
  rw [RawPath.W, Nat.sub_zero, permutationPrefix_zero, Finset.union_empty]
  simpa only [S.card_Wminus] using
    permutationPrefix_card S.Wminus P.minusPermutation

@[simp] lemma RawPath.W_last {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S) : P.W nW = S.Wplus := by
  rw [RawPath.W, Nat.sub_self, permutationPrefix_zero, Finset.empty_union]
  simpa only [S.card_Wplus] using
    permutationPrefix_card S.Wplus P.plusPermutation

lemma RawPath.disjoint_W_U0 {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S) (i : ℕ) : Disjoint (P.W i) S.U0 := by
  rw [RawPath.W, Finset.disjoint_union_left]
  exact ⟨S.disjoint_Wminus_U0.mono_left (permutationPrefix_subset _ _ _),
    S.disjoint_Wplus_U0.mono_left (permutationPrefix_subset _ _ _)⟩

lemma RawPath.disjoint_W_A {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S) (i : ℕ) : Disjoint (P.W i) S.A := by
  have hbase := S.disjoint_A_base
  have hminus : Disjoint S.A S.Wminus :=
    hbase.mono_right (Finset.subset_union_left.trans Finset.subset_union_left)
  have hplus : Disjoint S.A S.Wplus :=
    hbase.mono_right (Finset.subset_union_right.trans Finset.subset_union_left)
  rw [RawPath.W, disjoint_comm, Finset.disjoint_union_right]
  exact ⟨hminus.mono_right (permutationPrefix_subset _ _ _),
    hplus.mono_right (permutationPrefix_subset _ _ _)⟩

/-! ## A simultaneous fixed-slice concentration adapter -/

namespace Hypergeometric

open Erdos88.Concentration

/-- A finite union bound which preserves compatibility of all sampled
prefixes.  Each statistic may use different fixed slice sizes, but all are
decoded from the same tuple of bucket permutations.

This is the form used for the outer path: the index `j` packages a side, a
time, and a matching edge. -/
theorem exists_sampler_simultaneously_close
    {A : Type u} [Fintype A] [DecidableEq A]
    {J : Type v} [Fintype J] [Nonempty J] {K : ℕ}
    (P : BucketPartition A (Fin K))
    (plus minus : J → Fin K → ℕ)
    (hcount : ∀ j k,
      plus j k + minus j k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (g : (j : J) → ProductSignedSlicePoint P (plus j) (minus j) → ℝ)
    (a t : ℝ)
    (hL : ∀ j,
      0 < Finset.univ.sum (fun k : Fin K ↦ plus j k + minus j k))
    (ha : 0 < a) (ht : 0 ≤ t)
    (hswitch : ∀ j X Y,
      IsProductSignedSwitch P X Y → |g j X - g j Y| ≤ a)
    (hunion : (Fintype.card J : ℝ) *
      (2 * Real.exp (-t ^ 2 /
        (2 * (Finset.univ.sum (fun k : Fin K ↦
          plus (Classical.choice inferInstance) k +
            minus (Classical.choice inferInstance) k)) * a ^ 2))) < 1)
    (hsameMass : ∀ j,
      Finset.univ.sum (fun k : Fin K ↦ plus j k + minus j k) =
        Finset.univ.sum (fun k : Fin K ↦
          plus (Classical.choice inferInstance) k +
            minus (Classical.choice inferInstance) k)) :
    ∃ sigma : ProductSignedSliceSampler P, ∀ j,
      |g j (productSignedSliceDecode P (plus j) (minus j)
          (hcount j) e sigma) -
        Erdos88.Concentration.uniformExpectation (g j)| < t := by
  classical
  let j0 : J := Classical.choice inferInstance
  let mass : ℕ := Finset.univ.sum (fun k : Fin K ↦
    plus j0 k + minus j0 k)
  let prob : ℝ := 2 * Real.exp (-t ^ 2 / (2 * mass * a ^ 2))
  let bad : J → Finset (ProductSignedSliceSampler P) := fun j ↦
    Finset.univ.filter fun sigma ↦
      t ≤ |g j (productSignedSliceDecode P (plus j) (minus j)
        (hcount j) e sigma) -
          Erdos88.Concentration.uniformExpectation (g j)|
  have hbad (j : J) :
      ((bad j).card : ℝ) ≤
        prob * Fintype.card (ProductSignedSliceSampler P) := by
    have htail := Erdos636.Hypergeometric.productSignedSlice_two_sided_probability
      P (plus j) (minus j) (hcount j) e (g j) a t
        (hL j) ha ht (hswitch j)
    have hdecode := uniformProbability_productSignedSliceDecode
      P (plus j) (minus j) (hcount j) e
        (fun X ↦ t ≤
          |g j X - Erdos88.Concentration.uniformExpectation (g j)|)
    rw [← hdecode, uniformProbability] at htail
    have hmass : Finset.univ.sum (fun k : Fin K ↦
        plus j k + minus j k) = mass := by
      simpa [mass, j0] using hsameMass j
    rw [hmass] at htail
    have hcardpos : (0 : ℝ) < Fintype.card (ProductSignedSliceSampler P) := by
      exact_mod_cast Fintype.card_pos
    apply (div_le_iff₀ hcardpos).mp
    simpa [bad, prob] using htail
  let allBad : Finset (ProductSignedSliceSampler P) := Finset.univ.biUnion bad
  have hallBad : ((allBad.card : ℕ) : ℝ) <
      Fintype.card (ProductSignedSliceSampler P) := by
    calc
      ((allBad.card : ℕ) : ℝ) ≤
          ∑ j, ((bad j).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j : J,
          prob * Fintype.card (ProductSignedSliceSampler P) := by
        apply Finset.sum_le_sum
        intro j _hj
        exact hbad j
      _ = (Fintype.card J : ℝ) * prob *
          Fintype.card (ProductSignedSliceSampler P) := by simp; ring
      _ < Fintype.card (ProductSignedSliceSampler P) := by
        have hsamp : (0 : ℝ) < Fintype.card (ProductSignedSliceSampler P) := by
          exact_mod_cast Fintype.card_pos
        have hfactor : (Fintype.card J : ℝ) * prob < 1 := by
          simpa [prob, mass, j0] using hunion
        simpa [mul_assoc] using mul_lt_mul_of_pos_right hfactor hsamp
  have hallBadNat : allBad.card <
      (Finset.univ : Finset (ProductSignedSliceSampler P)).card := by
    exact_mod_cast hallBad
  obtain ⟨sigma, _hsigma, hsigmaBad⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hallBadNat
  refine ⟨sigma, ?_⟩
  intro j
  have hnot : sigma ∉ bad j := by
    intro h
    exact hsigmaBad (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, h⟩)
  simpa [bad] using hnot

end Hypergeometric

/-! ## Blockwise crowd extraction -/

/-- The matching edges of a structural witness, regarded as a finite type of
particles. -/
abbrev Particle {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) :=
  {x // x ∈ S.matching}

/-- Geometry connecting an abstract blockwise use of `Crowd` to the concrete
outer switch path.  The cell construction and its exact counting inequality
live in `data`; the remaining fields only identify local block times with
global switching times and interpret `nearby` as a degree window.

Keeping this record separate is useful in the asymptotic application: the
hypergeometric step proves a uniform global deviation bound, after which a
coarse interval cell decomposition fills these fields. -/
structure CrowdSchedule {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (P : RawPath S) (blocks mu window : ℕ) where
  data : Crowd.BlockCrowdData (Fin blocks) (Particle S)
  globalTime : Fin blocks → ℕ → ℕ
  blockOf : ℕ → Fin blocks
  localOf : ℕ → ℕ
  local_le : ∀ i ≤ nW, localOf i ≤ data.last (blockOf i)
  time_eq : ∀ i ≤ nW, globalTime (blockOf i) (localOf i) = i
  threshold_le : ∀ q, mu ≤ data.threshold q
  nearby_degree : ∀ q t, t ≤ data.last q → ∀ x y,
    y ∈ data.nearby q t x →
      |(degreeInto G (P.W (globalTime q t)) y.1 : ℤ) -
        degreeInto G (P.W (globalTime q t)) x.1| ≤ window

/-- The exact output of the crowd stage.  `anchor i` is one matching edge,
and `crowd i` is the retained submatching around it. -/
structure CrowdedPath {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (mu window : ℕ) where
  raw : RawPath S
  W : ℕ → Finset V := raw.W
  W_eq : W = raw.W := by rfl
  anchor : ℕ → Finset V
  crowd : ℕ → Finset (Finset V)
  anchor_mem : ∀ i ≤ nW, anchor i ∈ S.matching
  crowd_subset : ∀ i ≤ nW, crowd i ⊆ S.matching
  crowd_large : ∀ i ≤ nW, mu ≤ (crowd i).card
  degree_window : ∀ i ≤ nW, ∀ x ∈ crowd i,
    |(degreeInto G (W i) x : ℤ) - degreeInto G (W i) (anchor i)| ≤ window

@[simp] lemma CrowdedPath.W_zero {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window) :
    Q.W 0 = S.Wminus := by
  rw [Q.W_eq]
  exact Q.raw.W_zero

@[simp] lemma CrowdedPath.W_last {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window) :
    Q.W nW = S.Wplus := by
  rw [Q.W_eq]
  exact Q.raw.W_last

@[simp] lemma CrowdedPath.card_W {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) :
    (Q.W i).card = nW := by
  rw [Q.W_eq]
  exact Q.raw.card_W hi

/-- Apply the blockwise crowd lemma and forget the particle subtype. -/
theorem exists_crowdedPath_of_schedule
    {G : SimpleGraph V} {scale nW ell K blocks mu window : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (P : RawPath S) (C : CrowdSchedule S P blocks mu window) :
    Nonempty (CrowdedPath S mu window) := by
  classical
  obtain ⟨anchorBlock, crowdBlock, hcrowdEq, hcrowdLarge⟩ :=
    Crowd.exists_block_anchors_and_crowds C.data
  let anchor : ℕ → Finset V := fun i ↦ (anchorBlock (C.blockOf i)).1
  let crowd : ℕ → Finset (Finset V) := fun i ↦
    (crowdBlock (C.blockOf i) (C.localOf i)).image Subtype.val
  refine ⟨{
    raw := P
    anchor := anchor
    crowd := crowd
    anchor_mem := ?_
    crowd_subset := ?_
    crowd_large := ?_
    degree_window := ?_ }⟩
  · intro i hi
    exact (anchorBlock (C.blockOf i)).2
  · intro i hi x hx
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  · intro i hi
    have hcard : (crowd i).card =
        (crowdBlock (C.blockOf i) (C.localOf i)).card := by
      exact Finset.card_image_of_injective _ Subtype.val_injective
    rw [hcard]
    exact (C.threshold_le (C.blockOf i)).trans
      (hcrowdLarge (C.blockOf i) (C.localOf i) (C.local_le i hi))
  · intro i hi x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hyNear : y ∈ C.data.nearby (C.blockOf i) (C.localOf i)
        (anchorBlock (C.blockOf i)) := by
      rw [← hcrowdEq (C.blockOf i) (C.localOf i)]
      exact hy
    have h := C.nearby_degree (C.blockOf i) (C.localOf i)
      (C.local_le i hi) (anchorBlock (C.blockOf i)) y hyNear
    simpa [anchor, C.time_eq i hi] using h

/-! ## Centres and an explicit exceptional-jump budget -/

/-- The deterministic centre used before the deletion/augmentation sample is
revealed.  Its anchor term represents `nZ` matching edges having degrees in
the retained crowd window. -/
def CrowdedPath.center {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    (nZ : ℕ) (i : ℕ) : ℝ :=
  weightedScore G alpha S.U0 (Q.W i) +
    nZ * degreeInto G (Q.W i) (Q.anchor i)

lemma CrowdedPath.center_last_sub_zero {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window nZ : ℕ} (Q : CrowdedPath S mu window) :
    Q.center nZ nW - Q.center nZ 0 =
      weightedScore G alpha S.U0 S.Wplus -
          weightedScore G alpha S.U0 S.Wminus +
        (nZ : ℝ) * ((S.dPlus : ℝ) - S.dMinus) := by
  have hzero := S.degree_Wminus (Q.anchor 0) (Q.anchor_mem 0 (Nat.zero_le _))
  have hlast := S.degree_Wplus (Q.anchor nW) (Q.anchor_mem nW le_rfl)
  simp only [CrowdedPath.center, Q.W_zero, Q.W_last]
  rw [hzero, hlast]
  push_cast
  ring

/-- The structural discrepancy remains a rise after adding the anchor term,
up to its exact endpoint loss. -/
lemma CrowdedPath.rise_le_center_sub {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b lam : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window nZ : ℕ} (Q : CrowdedPath S mu window)
    (hlam : lam + (nZ : ℝ) * |(S.dPlus : ℝ) - S.dMinus| ≤
      aDisc * scale * Real.sqrt scale) :
    lam ≤ Q.center nZ nW - Q.center nZ 0 := by
  rw [Q.center_last_sub_zero]
  have hdisc := S.discrepancy
  have habs : -|(S.dPlus : ℝ) - S.dMinus| ≤
      (S.dPlus : ℝ) - S.dMinus := neg_abs_le _
  have hnZ : (0 : ℝ) ≤ nZ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left habs hnZ]

/-- Bounding all nonexceptional positive increments by `rho` and every
exceptional absolute increment by `jump` gives the exact product budget
`exceptional.card * jump`. -/
lemma largeIncrementSum_le_exceptional_budget
    (p : ℕ → ℝ) (tau : ℕ) {rho jump : ℝ}
    (exceptional : Finset ℕ) (hsub : exceptional ⊆ Finset.range tau)
    (hjump : 0 ≤ jump)
    (hregular : ∀ i < tau, i ∉ exceptional →
      p (i + 1) - p i ≤ rho)
    (hexceptional : ∀ i ∈ exceptional,
      |p (i + 1) - p i| ≤ jump) :
    Switching.largeIncrementSum p rho tau ≤
      (exceptional.card : ℝ) * jump := by
  classical
  rw [Switching.largeIncrementSum]
  calc
    ∑ i ∈ Finset.range tau, Switching.largeIncrement p rho i ≤
        ∑ i ∈ Finset.range tau, if i ∈ exceptional then jump else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hie : i ∈ exceptional
      · rw [if_pos hie, Switching.largeIncrement]
        split_ifs with hlarge
        · exact (le_abs_self _).trans (hexceptional i hie)
        · exact hjump
      · rw [if_neg hie, Switching.largeIncrement]
        split_ifs with hlarge
        · exact (not_lt_of_ge
            (hregular i (Finset.mem_range.mp hi) hie) hlarge).elim
        · rfl
    _ = ∑ _i ∈ exceptional, jump := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      exact and_iff_right_of_imp (fun hi ↦ Finset.mem_range.mp (hsub hi))
    _ = (exceptional.card : ℝ) * jump := by simp

/-- Direct application of the separated-switching theorem to a crowded
outer path with an explicit exceptional set. -/
theorem CrowdedPath.exists_separatedSwitchingSubsequence
    {G : SimpleGraph V} {scale nW ell K m : ℕ}
    {alpha aDisc aDiv b lam rho sigma jump : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window nZ : ℕ} (Q : CrowdedPath S mu window)
    (exceptional : Finset ℕ) (hsub : exceptional ⊆ Finset.range nW)
    (hm : 1 ≤ m) (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hjump : 0 ≤ jump)
    (hrise : lam ≤ Q.center nZ nW - Q.center nZ 0)
    (hregular : ∀ i < nW, i ∉ exceptional →
      Q.center nZ (i + 1) - Q.center nZ i ≤ rho)
    (hexceptional : ∀ i ∈ exceptional,
      |Q.center nZ (i + 1) - Q.center nZ i| ≤ jump)
    (hbudget : (m : ℝ) * (rho + sigma) +
      (exceptional.card : ℝ) * jump ≤ lam) :
    ∃ idx : Fin (m + 1) → ℕ,
      StrictMono idx ∧ idx 0 = 0 ∧ idx (Fin.last m) = nW ∧
        ∀ j : Fin m, sigma ≤
          Q.center nZ (idx j.succ) - Q.center nZ (idx j.castSucc) := by
  have hlarge : Switching.largeIncrementSum (Q.center nZ) rho nW ≤
      (exceptional.card : ℝ) * jump :=
    largeIncrementSum_le_exceptional_budget (Q.center nZ) nW
      (exceptional := exceptional) hsub hjump hregular hexceptional
  exact Switching.separatedSwitchingSubsequence (Q.center nZ) hm hrho hsigma
    hrise hlarge hbudget

/-! ## Perturbed marked-centre packing -/

/-- Feed a switching subsequence into the marked-packing layer.  The
perturbed centres `x` may include the later deletion/augmentation exposure;
`r` is its charged error along the switching subsequence. -/
theorem CrowdedPath.exists_markedSeparatedSubset
    {G : SimpleGraph V} {scale nW ell K m : ℕ}
    {alpha aDisc aDiv b sigma R theta : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window nZ : ℕ} (Q : CrowdedPath S mu window)
    (idx : Fin (m + 1) → ℕ)
    (x r : ℕ → ℝ) (marked : Finset ℕ)
    (hsigma : 0 < sigma) (hR : 0 < R) (htheta : 0 < theta)
    (hr : ∀ u ∈ Finset.Icc 1 m, 0 ≤ r u)
    (hgrowth : ∀ {j k : ℕ}, j < k → k ≤ m →
      ((k - j : ℕ) : ℝ) * sigma -
          ∑ u ∈ Finset.Ioc j k, r u ≤ x k - x j)
    (hmarkedRange : marked ⊆ Finset.range (m + 1))
    (hmarked : theta * m ≤ (marked.card : ℝ))
    (herror : (∑ u ∈ Finset.Icc 1 m, r u) ≤
      theta / 2 * m * sigma) :
    ∃ kept : Finset ℕ,
      kept ⊆ marked ∧ MarkedPacking.SeparatedInOrder x R kept ∧
        theta / (2 * (⌈R / sigma⌉₊ + 2 : ℕ)) * m ≤
          (kept.card : ℝ) := by
  exact MarkedPacking.exists_separated_subset_linear x r m hsigma hR htheta
    hr (by intro j k hjk hkm; exact hgrowth hjk hkm)
    marked hmarkedRange hmarked herror

/-! ## Exact fixed-order pointwise output -/

/-- Package the marked crowd path directly as the pointwise fixed-order
window object consumed by `KwanSudakov.hasRoundedAssembly_of_pointwiseWindows`.

All probabilistic work has been reduced to the displayed finite conditions:
`marked` is the positive-density set of times for one shared augmentation
outcome, `r` is its charged perturbation, and `piece i` is the corresponding
submatching of fixed-order edge counts.  The cardinal inequality is the
literal `Omega(sqrt n)` requirement; no asymptotic or rounding convention is
hidden in the constructor. -/
theorem CrowdedPath.nonempty_pointwiseWindows_of_markedPacking
    {n scale nW ell K k nZ : ℕ}
    {cW c0 delta0 bIndex dPiece : ℝ} {branch : Bool}
    {G : SimpleGraph (Fin n)}
    {spectra : ℕ → Finset ℕ}
    {alpha aDisc aDiv bStruct : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv bStruct}
    {mu degreeWindow : ℕ} (Q : CrowdedPath S mu degreeWindow)
    (hkpos : 1 ≤ k) (hkle : k ≤ K)
    (r : ℕ → ℝ) (piece : ℕ → Finset ℕ) (marked : Finset ℕ)
    {s R theta radius : ℝ}
    (hs : 0 < s) (hR : 0 < R) (htheta : 0 < theta)
    (hr : ∀ u ∈ Finset.Icc 1 nW, 0 ≤ r u)
    (hgrowth : ∀ {j q : ℕ}, j < q → q ≤ nW →
      ((q - j : ℕ) : ℝ) * s -
          ∑ u ∈ Finset.Ioc j q, r u ≤
        Q.center nZ q - Q.center nZ j)
    (hmarkedRange : marked ⊆ Finset.range (nW + 1))
    (hmarked : theta * nW ≤ (marked.card : ℝ))
    (herror : ∑ u ∈ Finset.Icc 1 nW, r u ≤ theta / 2 * nW * s)
    (hradius : 0 ≤ radius) (hseparate : 2 * radius < R)
    (hwindow : ∀ i ∈ marked, ∀ e ∈ piece i,
      |(e : ℝ) - Q.center nZ i| ≤ radius)
    (hsubset : ∀ i ∈ marked, piece i ⊆
      spectra
        (ProfileReduction.selectedOffsetOrder
          (OuterAssembly.deletionSize c0 n)
          (fun _ ↦ OuterAssembly.assemblyOffset cW c0 delta0 n k)
          (fun _ ↦ branch) ell))
    (hpiece : ∀ i ∈ marked, dPiece * n ≤ ((piece i).card : ℝ))
    (hindex : bIndex * Real.sqrt n ≤
      theta / (2 * (⌈R / s⌉₊ + 2 : ℕ)) * nW) :
    Nonempty (OuterSwitching.PointwiseWindows n K cW c0 delta0
      bIndex dPiece spectra ell) := by
  obtain ⟨W, hWcard, hWpiece⟩ :=
    OuterSwitching.exists_separatedWindows_of_markedPacking
      (spectra
        (ProfileReduction.selectedOffsetOrder
          (OuterAssembly.deletionSize c0 n)
          (fun _ ↦ OuterAssembly.assemblyOffset cW c0 delta0 n k)
          (fun _ ↦ branch) ell))
      (Q.center nZ) r piece nW n hs hR htheta hr
        (by intro j q hjq hqn; exact hgrowth hjq hqn)
        marked hmarkedRange hmarked herror hradius hseparate
        (by intro i hi e he; exact hwindow i hi e he)
        (by intro i hi; exact hsubset i hi)
        (by intro i hi; exact hpiece i hi)
  refine ⟨{
    k := k
    branch := branch
    k_pos := hkpos
    k_le := hkle
    windows := W
    index_large := hindex.trans hWcard
    piece_large := hWpiece }⟩

end

end OuterSwitchingPath
end Erdos636
