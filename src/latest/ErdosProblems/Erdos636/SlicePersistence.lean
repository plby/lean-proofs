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

import ErdosProblems.Erdos636.AntiConcentration
import ErdosProblems.Erdos636.CollisionCounting
import ErdosProblems.Erdos636.Hypergeometric
import ErdosProblems.Erdos636.SetDiversity
import ErdosProblems.Erdos636.SliceMoments

/-!
# Persistence and collision bounds on a uniform graph slice

This file supplies the graph-facing probability estimates used in the first
random exposure of Kwan--Sudakov.  A sample is represented by
`Fourier.BoolSlice V ell`; `sampleFinset` is its uniformly distributed
`ell`-element vertex set.

The persistence theorem is a one-bucket specialization of the checked
permutation bounded-differences inequality.  The collision theorem turns a
linear support difference into an `l1` coefficient bound and then applies
the checked balanced-slice anti-concentration theorem.  The signed population
sum is exposed explicitly: the small-sum and large-sum cases are therefore
available to the structural argument without an omitted variance hypothesis.
-/

open scoped BigOperators

namespace Erdos636
namespace SlicePersistence

open Classical Finset SimpleGraph
open Erdos88
open Erdos88.Concentration
open Erdos88.Fourier

universe u v

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The vertex set encoded by a Boolean-slice point. -/
def sampleFinset (ell : ℕ) (omega : BoolSlice V ell) : Finset V :=
  boolFunEquivFinset V omega.1

@[simp] lemma mem_sampleFinset {ell : ℕ} {omega : BoolSlice V ell} {x : V} :
    x ∈ sampleFinset ell omega ↔ omega.1 x := by
  simp [sampleFinset, boolFunEquivFinset]

@[simp] lemma card_sampleFinset (ell : ℕ) (omega : BoolSlice V ell) :
    (sampleFinset ell omega).card = ell := by
  exact omega.2

/-- Uniform expectations are invariant under a finite equivalence. -/
lemma uniformExpectation_equiv {A : Type u} {B : Type v}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (e : A ≃ B) (f : B → ℝ) :
    uniformExpectation (fun a ↦ f (e a)) = uniformExpectation f := by
  unfold uniformExpectation
  rw [Fintype.card_congr e]
  congr 1
  exact e.sum_comp f

/-- The repository's explicit real uniform expectation agrees with
`Fintype.expect`. -/
lemma uniformExpectation_eq_fintypeExpect {A : Type u}
    [Fintype A] [Nonempty A] (f : A → ℝ) :
    uniformExpectation f = 𝔼 a, f a := by
  unfold uniformExpectation
  rw [Fintype.expect_eq_sum_div_card]

/-- Event probability is the expectation of its indicator. -/
lemma uniformProbability_eq_indicatorExpectation {A : Type u}
    [Fintype A] [Nonempty A] (P : A → Prop) :
    uniformProbability P =
      uniformExpectation (fun a ↦ if P a then (1 : ℝ) else 0) := by
  classical
  unfold uniformProbability uniformExpectation
  congr 1
  rw [Finset.sum_ite]
  simp

/-- Uniform event probabilities are invariant under a finite equivalence. -/
lemma uniformProbability_equiv {A : Type u} {B : Type v}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (e : A ≃ B) (P : B → Prop) :
    uniformProbability (fun a ↦ P (e a)) = uniformProbability P := by
  classical
  rw [uniformProbability_eq_indicatorExpectation,
    uniformProbability_eq_indicatorExpectation]
  exact uniformExpectation_equiv e (fun b ↦ if P b then (1 : ℝ) else 0)

/-- The constant one-bucket partition. -/
def oneBucket (V : Type u) [Fintype V] [DecidableEq V] :
    BooleanSlices.BucketPartition V (Fin 1) where
  bucket := fun _ ↦ 0

@[simp] lemma oneBucket_fiber (V : Type u) [Fintype V] [DecidableEq V]
    (k : Fin 1) : (oneBucket V).fiber k = Finset.univ := by
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  ext x
  simp [oneBucket, BooleanSlices.BucketPartition.fiber]

/-- A one-bucket signed slice with no negative coordinates is exactly a
Boolean slice.  Keeping this equivalence explicit permits concentration and
Fourier anti-concentration to be used on the same sample space. -/
def boolSliceEquivOneBucketSigned (ell : ℕ) (hell : ell ≤ Fintype.card V) :
    BoolSlice V ell ≃
      BooleanSlices.ProductSignedSlicePoint (oneBucket V)
        (fun _ ↦ ell) (fun _ ↦ 0) where
  toFun omega := fun k ↦
    ⟨(sampleFinset ell omega, ∅), by
      rw [BooleanSlices.mem_signedSlice]
      refine ⟨?_, ?_, ?_, card_sampleFinset ell omega, rfl⟩
      · rw [oneBucket_fiber]
        exact Finset.subset_univ _
      · exact Finset.empty_subset _
      · show Disjoint (sampleFinset ell omega) ∅
        exact Finset.disjoint_empty_right (sampleFinset ell omega)
      ⟩
  invFun S :=
    ⟨fun x ↦ decide (x ∈ (S 0).1.1), by
      change (Finset.univ.filter fun x ↦ decide (x ∈ (S 0).1.1)).card = ell
      have hset : (Finset.univ.filter fun x ↦ decide (x ∈ (S 0).1.1)) =
          (S 0).1.1 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      rw [hset]
      exact (BooleanSlices.mem_signedSlice.mp (S 0).2).2.2.2.1⟩
  left_inv omega := by
    apply Subtype.ext
    funext x
    cases h : omega.1 x <;> simp [sampleFinset, boolFunEquivFinset, h]
  right_inv S := by
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    apply Subtype.ext
    apply Prod.ext
    · ext x
      simp only [sampleFinset, boolFunEquivFinset, Equiv.coe_fn_mk,
        Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    · have hzero : (S 0).1.2.card = 0 :=
        (BooleanSlices.mem_signedSlice.mp (S 0).2).2.2.2.2
      exact (Finset.card_eq_zero.mp hzero).symm

/-- The finset presentation of `BoolSlice`, with its ambient-subset proof. -/
def boolSliceEquivBooleanSlicePoint (ell : ℕ) :
    BoolSlice V ell ≃
      BooleanSlices.BooleanSlicePoint (Finset.univ : Finset V) ell :=
  (boolSliceEquivFinsetLen V ell).trans
    { toFun := fun S ↦ ⟨S.1, by
        rw [BooleanSlices.mem_booleanSlice]
        exact ⟨Finset.subset_univ _, S.2⟩⟩
      invFun := fun S ↦ ⟨S.1, (BooleanSlices.mem_booleanSlice.mp S.2).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

@[simp] lemma boolSliceEquivBooleanSlicePoint_val (ell : ℕ)
    (omega : BoolSlice V ell) :
    (boolSliceEquivBooleanSlicePoint ell omega).1 = sampleFinset ell omega := rfl

/-- Cardinality of a fixed test set inside the sampled `ell`-set. -/
def intersectionCount (D : Finset V) (ell : ℕ) (omega : BoolSlice V ell) : ℝ :=
  ((sampleFinset ell omega ∩ D).card : ℝ)

/-! ## One-bucket bounded differences -/

/-- The positive support of the unique bucket. -/
def signedSampleFinset (ell : ℕ)
    (S : BooleanSlices.ProductSignedSlicePoint (oneBucket V)
      (fun _ ↦ ell) (fun _ ↦ 0)) : Finset V :=
  (S 0).1.1

@[simp] lemma oneBucket_value_eq_one_iff (ell : ℕ)
    (S : BooleanSlices.ProductSignedSlicePoint (oneBucket V)
      (fun _ ↦ ell) (fun _ ↦ 0)) (v : V) :
    BooleanSlices.productSignedSliceValue (oneBucket V) S v = 1 ↔
      v ∈ signedSampleFinset ell S := by
  change BooleanSlices.signedSliceValue (S 0) v = 1 ↔ v ∈ (S 0).1.1
  exact BooleanSlices.signedSliceValue_eq_one_iff (S 0) v

/-- Under one legal signed-slice switch, every newly selected element other
than the two switched coordinates was already selected. -/
lemma signedSample_inter_subset_switch_union (D : Finset V) (ell : ℕ)
    {S T : BooleanSlices.ProductSignedSlicePoint (oneBucket V)
      (fun _ ↦ ell) (fun _ ↦ 0)}
    (h : BooleanSlices.IsProductSignedSwitch (oneBucket V) S T) :
    ∃ i j : V, i ≠ j ∧
      signedSampleFinset ell T ∩ D ⊆
        (signedSampleFinset ell S ∩ D) ∪ {i, j} := by
  obtain ⟨k, i, j, _hi, _hj, hij, hswap⟩ := h
  refine ⟨i, j, hij, ?_⟩
  intro v hv
  have hvT : v ∈ signedSampleFinset ell T := (Finset.mem_inter.mp hv).1
  have hvD : v ∈ D := (Finset.mem_inter.mp hv).2
  by_cases hvi : v = i
  · subst v
    exact Finset.mem_union_right _ (by simp)
  by_cases hvj : v = j
  · subst v
    exact Finset.mem_union_right _ (by simp)
  apply Finset.mem_union_left
  apply Finset.mem_inter.mpr
  refine ⟨?_, hvD⟩
  have hvalue :
      BooleanSlices.productSignedSliceValue (oneBucket V) T v =
        BooleanSlices.productSignedSliceValue (oneBucket V) S v := by
    simpa [hvi, hvj] using hswap v
  apply (oneBucket_value_eq_one_iff ell S v).mp
  rw [← hvalue]
  exact (oneBucket_value_eq_one_iff ell T v).mpr hvT

/-- A legal switch changes a fixed intersection count by at most two. -/
lemma abs_signedSample_inter_card_sub_le_two (D : Finset V) (ell : ℕ)
    {S T : BooleanSlices.ProductSignedSlicePoint (oneBucket V)
      (fun _ ↦ ell) (fun _ ↦ 0)}
    (h : BooleanSlices.IsProductSignedSwitch (oneBucket V) S T) :
    abs (((signedSampleFinset ell S ∩ D).card : ℝ) -
        (signedSampleFinset ell T ∩ D).card) ≤ 2 := by
  obtain ⟨i, j, hij, hsub⟩ := signedSample_inter_subset_switch_union D ell h
  have hTS : (signedSampleFinset ell T ∩ D).card ≤
      (signedSampleFinset ell S ∩ D).card + 2 := by
    calc
      (signedSampleFinset ell T ∩ D).card ≤
          ((signedSampleFinset ell S ∩ D) ∪ {i, j}).card :=
        Finset.card_le_card hsub
      _ ≤ (signedSampleFinset ell S ∩ D).card +
          ({i, j} : Finset V).card :=
        Finset.card_union_le _ _
      _ = (signedSampleFinset ell S ∩ D).card + 2 := by simp [hij]
  obtain ⟨i', j', hij', hsub'⟩ := signedSample_inter_subset_switch_union D ell
    (BooleanSlices.isProductSignedSwitch_symm (oneBucket V) h)
  have hST : (signedSampleFinset ell S ∩ D).card ≤
      (signedSampleFinset ell T ∩ D).card + 2 := by
    calc
      (signedSampleFinset ell S ∩ D).card ≤
          ((signedSampleFinset ell T ∩ D) ∪ {i', j'}).card :=
        Finset.card_le_card hsub'
      _ ≤ (signedSampleFinset ell T ∩ D).card +
          ({i', j'} : Finset V).card :=
        Finset.card_union_le _ _
      _ = (signedSampleFinset ell T ∩ D).card + 2 := by simp [hij']
  have hTSreal : ((signedSampleFinset ell T ∩ D).card : ℝ) ≤
      (signedSampleFinset ell S ∩ D).card + 2 := by exact_mod_cast hTS
  have hSTreal : ((signedSampleFinset ell S ∩ D).card : ℝ) ≤
      (signedSampleFinset ell T ∩ D).card + 2 := by exact_mod_cast hST
  rw [abs_le]
  constructor <;> linarith

/-- Two-sided exponential concentration for intersection with a fixed set
on a uniform `ell`-slice.  The constant `8 ell` comes from the conservative
switch Lipschitz constant two. -/
theorem signedSlice_intersection_two_sided_probability
    (D : Finset V) (ell : ℕ) (hell : ell ≤ Fintype.card V)
    (hellPos : 0 < ell) (t : ℝ) (ht : 0 ≤ t) :
    let P := oneBucket V
    let plus : Fin 1 → ℕ := fun _ ↦ ell
    let minus : Fin 1 → ℕ := fun _ ↦ 0
    letI : Nonempty (BooleanSlices.ProductSignedSlicePoint P plus minus) :=
      BooleanSlices.productSignedSlicePoint_nonempty P plus minus (by
        intro k
        simpa [P, plus, minus, oneBucket_fiber] using hell)
    uniformProbability (fun S ↦
        t ≤ |((signedSampleFinset ell S ∩ D).card : ℝ) -
          uniformExpectation (fun T ↦
            ((signedSampleFinset ell T ∩ D).card : ℝ))|) ≤
      2 * Real.exp (-t ^ 2 / (8 * ell)) := by
  classical
  dsimp only
  let e : ∀ k : Fin 1,
      Fin ((oneBucket V).fiber k).card ≃ ↑((oneBucket V).fiber k) :=
    fun k ↦ ((oneBucket V).fiber k).equivFin.symm
  have hcount : ∀ k : Fin 1,
      ell + 0 ≤ ((oneBucket V).fiber k).card := by
    intro k
    simpa [oneBucket_fiber] using hell
  have htail := Erdos636.Hypergeometric.productSignedSlice_two_sided_probability
    (oneBucket V) (fun _ : Fin 1 ↦ ell) (fun _ ↦ 0) hcount e
      (fun S ↦ ((signedSampleFinset ell S ∩ D).card : ℝ)) 2 t
      (by simpa using hellPos) (by norm_num) ht
      (fun S T hST ↦ abs_signedSample_inter_card_sub_le_two D ell hST)
  have hsum : ∑ k : Fin 1, ((fun _ : Fin 1 ↦ ell) k + (fun _ ↦ 0) k) = ell := by
    simp
  rw [hsum] at htail
  convert htail using 1 <;> ring_nf

/-! ## The same tail on `Fourier.BoolSlice` -/

/-- Exact mean of a fixed-set intersection in the Boolean-slice model. -/
theorem uniformExpectation_intersectionCount (D : Finset V) (ell : ℕ)
    (hell : ell ≤ Fintype.card V) [Nonempty (BoolSlice V ell)]
    (hV : 0 < Fintype.card V) :
    uniformExpectation (intersectionCount D ell) =
      (ell : ℝ) / Fintype.card V * D.card := by
  let e := boolSliceEquivBooleanSlicePoint (V := V) ell
  let : Nonempty
      (BooleanSlices.BooleanSlicePoint (Finset.univ : Finset V) ell) :=
    SliceMoments.nonempty_booleanSlicePoint Finset.univ ell (by simpa using hell)
  rw [uniformExpectation_eq_fintypeExpect]
  calc
    (𝔼 omega : BoolSlice V ell, intersectionCount D ell omega) =
        𝔼 S : BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset V) ell,
            ((S.1.filter fun x ↦ x ∈ D).card : ℝ) := by
      apply Fintype.expect_equiv e
      intro omega
      simp only [intersectionCount, e, boolSliceEquivBooleanSlicePoint_val]
      congr 1
    _ = (ell : ℝ) / Fintype.card V * D.card := by
      simpa using SliceMoments.expectation_card_filter_booleanSlicePoint
        (Finset.univ : Finset V) ell (fun x ↦ x ∈ D) hell
          (Finset.card_pos.mp (by simpa using hV))

/-- Two-sided concentration, transported to the Fourier Boolean-slice
model used by anti-concentration. -/
theorem slice_intersection_two_sided_probability
    (D : Finset V) (ell : ℕ) (hell : ell ≤ Fintype.card V)
    [Nonempty (BoolSlice V ell)] (hellPos : 0 < ell)
    (t : ℝ) (ht : 0 ≤ t) :
    uniformProbability (fun omega : BoolSlice V ell ↦
        t ≤ |intersectionCount D ell omega -
          uniformExpectation (intersectionCount D ell)|) ≤
      2 * Real.exp (-t ^ 2 / (8 * ell)) := by
  let E := boolSliceEquivOneBucketSigned (V := V) ell hell
  let f : BooleanSlices.ProductSignedSlicePoint (oneBucket V)
      (fun _ ↦ ell) (fun _ ↦ 0) → ℝ :=
    fun S ↦ ((signedSampleFinset ell S ∩ D).card : ℝ)
  let : Nonempty (BooleanSlices.ProductSignedSlicePoint (oneBucket V)
      (fun _ ↦ ell) (fun _ ↦ 0)) :=
    ⟨E (Classical.choice (inferInstance : Nonempty (BoolSlice V ell)))⟩
  have hpoint (omega : BoolSlice V ell) :
      intersectionCount D ell omega = f (E omega) := by
    rfl
  have hmean : uniformExpectation (intersectionCount D ell) =
      uniformExpectation f := by
    have hfun : intersectionCount D ell = fun omega ↦ f (E omega) := by
      funext omega
      exact hpoint omega
    rw [hfun]
    exact uniformExpectation_equiv E f
  let Q := fun S : BooleanSlices.ProductSignedSlicePoint (oneBucket V)
      (fun _ ↦ ell) (fun _ ↦ 0) ↦
        t ≤ |f S - uniformExpectation f|
  have hprob : uniformProbability (fun omega : BoolSlice V ell ↦
      t ≤ |intersectionCount D ell omega -
        uniformExpectation (intersectionCount D ell)|) =
      uniformProbability Q := by
    have hevent : (fun omega : BoolSlice V ell ↦
        t ≤ |intersectionCount D ell omega -
          uniformExpectation (intersectionCount D ell)|) =
        fun omega ↦ Q (E omega) := by
      funext omega
      simp only [Q, hpoint, hmean]
    rw [hevent]
    exact uniformProbability_equiv E Q
  rw [hprob]
  simpa [Q, f] using signedSlice_intersection_two_sided_probability
    D ell hell hellPos t ht

/-- If `q` is at most half the exact intersection mean, falling below `q`
has exponentially small probability. -/
theorem support_persistence_failure_probability_le
    (D : Finset V) (ell : ℕ) (hell : ell ≤ Fintype.card V)
    [Nonempty (BoolSlice V ell)] (hellPos : 0 < ell)
    (q : ℝ) (hq : 0 ≤ q)
    (hhalf : 2 * q ≤ uniformExpectation (intersectionCount D ell)) :
    uniformProbability (fun omega : BoolSlice V ell ↦
        intersectionCount D ell omega < q) ≤
      2 * Real.exp (-q ^ 2 / (8 * ell)) := by
  calc
    uniformProbability (fun omega : BoolSlice V ell ↦
        intersectionCount D ell omega < q) ≤
        uniformProbability (fun omega : BoolSlice V ell ↦
          q ≤ |intersectionCount D ell omega -
            uniformExpectation (intersectionCount D ell)|) := by
      apply uniformProbability_mono
      intro omega homega
      have hneg : intersectionCount D ell omega -
          uniformExpectation (intersectionCount D ell) ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      linarith
    _ ≤ 2 * Real.exp (-q ^ 2 / (8 * ell)) :=
      slice_intersection_two_sided_probability D ell hell hellPos q hq

/-- Density-normalized persistence.  If `D` occupies at least a `theta`
fraction of the population, a uniform slice retains at least half of the
corresponding linear amount except with an exponential tail. -/
theorem support_persistence_density_failure_probability_le
    (D : Finset V) (ell : ℕ) (hell : ell ≤ Fintype.card V)
    [Nonempty (BoolSlice V ell)] (hellPos : 0 < ell)
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hD : theta * Fintype.card V ≤ D.card) :
    uniformProbability (fun omega : BoolSlice V ell ↦
        intersectionCount D ell omega < theta * ell / 2) ≤
      2 * Real.exp (-(theta * ell / 2) ^ 2 / (8 * ell)) := by
  have hV : 0 < Fintype.card V := by
    exact lt_of_lt_of_le hellPos hell
  apply support_persistence_failure_probability_le D ell hell hellPos
    (theta * ell / 2) (by positivity)
  rw [uniformExpectation_intersectionCount D ell hell hV]
  have hVreal : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
  have hD' : theta ≤ (D.card : ℝ) / Fintype.card V := by
    apply (le_div_iff₀ hVreal).2
    simpa [mul_comm] using hD
  have hellnonneg : (0 : ℝ) ≤ ell := by positivity
  calc
    2 * (theta * (ell : ℝ) / 2) = (ell : ℝ) * theta := by ring
    _ ≤ (ell : ℝ) * ((D.card : ℝ) / Fintype.card V) :=
      mul_le_mul_of_nonneg_left hD' hellnonneg
    _ = (ell : ℝ) / Fintype.card V * D.card := by ring

/-! ## A finite family of persistence tests -/

/-- Union bound for a finite family of events, expressed in the repository's
uniform-probability model. -/
theorem uniformProbability_exists_mem_le {Omega : Type u} [Fintype Omega]
    [Nonempty Omega] {Iota : Type v} (tests : Finset Iota)
    (bad : Iota → Omega → Prop) (p : ℝ)
    (hbad : ∀ i ∈ tests, uniformProbability (bad i) ≤ p) :
    uniformProbability (fun omega ↦ ∃ i ∈ tests, bad i omega) ≤
      tests.card * p := by
  classical
  calc
    uniformProbability (fun omega ↦ ∃ i ∈ tests, bad i omega) ≤
        uniformProbability (fun omega ↦
          (1 : ℝ) ≤ CollisionCounting.eventCount tests bad omega) := by
      apply uniformProbability_mono
      intro omega homega
      obtain ⟨i, hi, hbadomega⟩ := homega
      exact_mod_cast (show 1 ≤ CollisionCounting.eventCount tests bad omega by
        rw [Nat.one_le_iff_ne_zero, CollisionCounting.eventCount]
        exact Finset.card_ne_zero.mpr ⟨i, by simp [hi, hbadomega]⟩)
    _ ≤ tests.card * p / 1 :=
      CollisionCounting.uniformProbability_eventCount_ge_le
        tests bad p 1 (by norm_num) hbad
    _ = tests.card * p := by ring

/-- One-shot persistence for every member of a finite family.  The density
hypothesis supplies every pointwise hypergeometric tail; the displayed
finite budget is the sole remaining numerical condition. -/
theorem support_persistence_family_failure_probability_lt_half
    {Iota : Type v} (tests : Finset Iota) (support : Iota → Finset V)
    (ell : ℕ) (hell : ell ≤ Fintype.card V)
    [Nonempty (BoolSlice V ell)] (hellPos : 0 < ell)
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hsupport : ∀ i ∈ tests,
      theta * Fintype.card V ≤ (support i).card)
    (hbudget :
      tests.card *
          (2 * Real.exp (-(theta * ell / 2) ^ 2 / (8 * ell))) <
        (1 : ℝ) / 2) :
    uniformProbability (fun omega : BoolSlice V ell ↦
        ∃ i ∈ tests,
          intersectionCount (support i) ell omega < theta * ell / 2) <
      (1 : ℝ) / 2 := by
  apply lt_of_le_of_lt
    (uniformProbability_exists_mem_le tests
      (fun i omega ↦
        intersectionCount (support i) ell omega < theta * ell / 2)
      (2 * Real.exp (-(theta * ell / 2) ^ 2 / (8 * ell))) ?_)
    hbudget
  intro i hi
  exact support_persistence_density_failure_probability_le
    (support i) ell hell hellPos theta htheta (hsupport i hi)

end

end SlicePersistence
end Erdos636
