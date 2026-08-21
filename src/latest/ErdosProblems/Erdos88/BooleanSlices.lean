/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib
import ErdosProblems.Erdos88.Concentration
import ErdosProblems.Erdos88.Invariance
import ErdosProblems.Erdos88.Probability

/-!
# Products of Boolean slices

Finite probability language for Section 11 of Kwan--Sah--Sauermann--Sawhney.
A slice point is represented by its positive-coordinate set.  The exact
Gaussian mean and variance computations at the end use only the first four
joint moments, stated explicitly in `HasStandardGaussianMoments`.
-/

open scoped BigOperators ComplexConjugate symmDiff

namespace Erdos88
namespace BooleanSlices

universe u v

section Slices

variable {α : Type u} {κ : Type v} [Fintype α] [DecidableEq α]

/-- A partition of a finite coordinate type.  Fibers are automatically
pairwise disjoint and cover the coordinate type. -/
structure BucketPartition (α κ : Type*) [Fintype α] [DecidableEq α] where
  bucket : α → κ

namespace BucketPartition

variable (P : BucketPartition α κ)

/-- The coordinates in bucket `k`. -/
def fiber [DecidableEq κ] (k : κ) : Finset α :=
  Finset.univ.filter fun i ↦ P.bucket i = k

@[simp] lemma mem_fiber [DecidableEq κ] (k : κ) (i : α) :
    i ∈ P.fiber k ↔ P.bucket i = k := by simp [fiber]

@[simp] lemma mem_ownFiber [DecidableEq κ] (i : α) :
    i ∈ P.fiber (P.bucket i) := by simp

lemma fiber_disjoint [DecidableEq κ] {k h : κ} (hkh : k ≠ h) :
    Disjoint (P.fiber k) (P.fiber h) := by
  rw [Finset.disjoint_left]
  intro i hik hih
  exact hkh (((P.mem_fiber _ _).mp hik).symm.trans ((P.mem_fiber _ _).mp hih))

lemma biUnion_fiber [Fintype κ] [DecidableEq κ] :
    Finset.univ.biUnion P.fiber = Finset.univ := by
  ext i
  simp [fiber]

end BucketPartition

/-- The Boolean slice on `I` having exactly `ell` positive coordinates. -/
def booleanSlice (I : Finset α) (ell : ℕ) : Finset (Finset α) :=
  I.powersetCard ell

/-- A point in one Boolean slice, packaged as a finite probability space. -/
def BooleanSlicePoint (I : Finset α) (ell : ℕ) : Type u :=
  {S : Finset α // S ∈ booleanSlice I ell}

noncomputable instance (I : Finset α) (ell : ℕ) :
    Fintype (BooleanSlicePoint I ell) :=
  Fintype.ofFinset (booleanSlice I ell) fun _ ↦ Iff.rfl

@[simp] lemma mem_booleanSlice {I : Finset α} {ell : ℕ} {S : Finset α} :
    S ∈ booleanSlice I ell ↔ S ⊆ I ∧ S.card = ell := by
  simp [booleanSlice, and_comm]

lemma booleanSlice_nonempty_iff {I : Finset α} {ell : ℕ} :
    (booleanSlice I ell).Nonempty ↔ ell ≤ I.card := by simp [booleanSlice]

lemma card_booleanSlice (I : Finset α) (ell : ℕ) :
    (booleanSlice I ell).card = I.card.choose ell := by simp [booleanSlice]

@[simp] lemma card_booleanSlicePoint (I : Finset α) (ell : ℕ) :
    Fintype.card (BooleanSlicePoint I ell) = I.card.choose ell := by
  calc
    Fintype.card (BooleanSlicePoint I ell) = (booleanSlice I ell).card := by
      exact Fintype.card_ofFinset (booleanSlice I ell) fun _ ↦ Iff.rfl
    _ = I.card.choose ell := card_booleanSlice I ell

/-- The `{-1,1}` vector encoded by its positive-coordinate set. -/
def signOfSet (S : Finset α) (i : α) : ℝ :=
  if i ∈ S then 1 else -1

@[simp] lemma signOfSet_eq_one_iff (S : Finset α) (i : α) :
    signOfSet S i = 1 ↔ i ∈ S := by
  by_cases hi : i ∈ S <;> simp [signOfSet, hi] <;> norm_num

@[simp] lemma signOfSet_eq_neg_one_iff (S : Finset α) (i : α) :
    signOfSet S i = -1 ↔ i ∉ S := by
  by_cases hi : i ∈ S <;> simp [signOfSet, hi] <;> norm_num

@[simp] lemma signOfSet_sq (S : Finset α) (i : α) :
    signOfSet S i ^ 2 = 1 := by
  by_cases hi : i ∈ S <;> simp [signOfSet, hi]

lemma abs_signOfSet (S : Finset α) (i : α) :
    |signOfSet S i| = 1 := by
  by_cases hi : i ∈ S <;> simp [signOfSet, hi]

/-- Support of a product of Boolean slices. -/
def productBooleanSlice [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ) : Finset (Finset α) :=
  Finset.univ.filter fun S ↦ ∀ k, (S ∩ P.fiber k).card = ell k

@[simp] lemma mem_productBooleanSlice [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ) (S : Finset α) :
    S ∈ productBooleanSlice P ell ↔
      ∀ k, (S ∩ P.fiber k).card = ell k := by
  simp [productBooleanSlice]

lemma productBooleanSlice_nonempty [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card) :
    (productBooleanSlice P ell).Nonempty := by
  classical
  choose T hT using fun k ↦ booleanSlice_nonempty_iff.mpr (hell k)
  refine ⟨Finset.univ.biUnion fun k ↦ T k, ?_⟩
  rw [mem_productBooleanSlice]
  intro k
  have hTk : T k ⊆ P.fiber k := (mem_booleanSlice.mp (hT k)).1
  have hcard : (T k).card = ell k := (mem_booleanSlice.mp (hT k)).2
  have hinter : (Finset.univ.biUnion fun h ↦ T h) ∩ P.fiber k = T k := by
    ext i
    constructor
    · intro hi
      have hiP : i ∈ P.fiber k := (Finset.mem_inter.mp hi).2
      obtain ⟨h, _hh, hih⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hi).1
      have hb : P.bucket i = h := (P.mem_fiber h i).mp ((mem_booleanSlice.mp (hT h)).1 hih)
      have hbk : P.bucket i = k := (P.mem_fiber k i).mp hiP
      have : h = k := hb.symm.trans hbk
      simpa [this] using hih
    · intro hi
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hi⟩, hTk hi⟩
  rw [hinter, hcard]

/-- The finite probability space underlying a product of Boolean slices.
An element is its set of positive coordinates together with the proof of
all prescribed bucket counts. -/
def ProductSlicePoint [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ) : Type u :=
  {S : Finset α // S ∈ productBooleanSlice P ell}

noncomputable instance [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ) :
    Fintype (ProductSlicePoint P ell) :=
  Fintype.ofFinset (productBooleanSlice P ell) fun _ ↦ Iff.rfl

lemma productSlicePoint_nonempty [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card) :
    Nonempty (ProductSlicePoint P ell) := by
  obtain ⟨S, hS⟩ := productBooleanSlice_nonempty P ell hell
  exact ⟨⟨S, hS⟩⟩

/-- Restricting a global product-slice point to each bucket is an exact
equivalence with the dependent product of the individual slice spaces. -/
noncomputable def productSliceEquiv [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ) :
    ProductSlicePoint P ell ≃ ∀ k, BooleanSlicePoint (P.fiber k) (ell k) where
  toFun S k := ⟨S.1 ∩ P.fiber k, by
    rw [mem_booleanSlice]
    exact ⟨Finset.inter_subset_right,
      (mem_productBooleanSlice P ell S.1).mp S.2 k⟩⟩
  invFun T := ⟨Finset.univ.biUnion fun k ↦ (T k).1, by
    rw [mem_productBooleanSlice]
    intro k
    have hinter :
        (Finset.univ.biUnion fun h ↦ (T h).1) ∩ P.fiber k = (T k).1 := by
      ext i
      constructor
      · intro hi
        obtain ⟨hiU, hik⟩ := Finset.mem_inter.mp hi
        obtain ⟨h, _hh, hih⟩ := Finset.mem_biUnion.mp hiU
        have hihFiber : i ∈ P.fiber h :=
          (mem_booleanSlice.mp (T h).2).1 hih
        have hb_h : P.bucket i = h := (P.mem_fiber h i).mp hihFiber
        have hb_k : P.bucket i = k := (P.mem_fiber k i).mp hik
        have : h = k := hb_h.symm.trans hb_k
        exact this ▸ hih
      · intro hi
        exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr
          ⟨k, Finset.mem_univ _, hi⟩, (mem_booleanSlice.mp (T k).2).1 hi⟩
    rw [hinter, (mem_booleanSlice.mp (T k).2).2]
  ⟩
  left_inv S := by
    apply Subtype.ext
    ext i
    constructor
    · intro hi
      obtain ⟨k, _hk, hik⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_inter.mp hik).1
    · intro hi
      exact Finset.mem_biUnion.mpr ⟨P.bucket i, Finset.mem_univ _,
        Finset.mem_inter.mpr ⟨hi, P.mem_ownFiber i⟩⟩
  right_inv T := by
    funext k
    apply Subtype.ext
    ext i
    constructor
    · intro hi
      obtain ⟨hiU, hik⟩ := Finset.mem_inter.mp hi
      obtain ⟨h, _hh, hih⟩ := Finset.mem_biUnion.mp hiU
      have hihFiber : i ∈ P.fiber h :=
        (mem_booleanSlice.mp (T h).2).1 hih
      have hb_h : P.bucket i = h := (P.mem_fiber h i).mp hihFiber
      have hb_k : P.bucket i = k := (P.mem_fiber k i).mp hik
      have : h = k := hb_h.symm.trans hb_k
      exact this ▸ hih
    · intro hi
      exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_univ _, hi⟩, (mem_booleanSlice.mp (T k).2).1 hi⟩

@[simp] lemma card_productSlicePoint [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ) :
    Fintype.card (ProductSlicePoint P ell) =
      ∏ k, (P.fiber k).card.choose (ell k) := by
  rw [Fintype.card_congr (productSliceEquiv P ell), Fintype.card_pi]
  simp

/-- Uniform expectation on a product slice is transported exactly to the
dependent product of the uniform one-bucket slice spaces. -/
lemma productSlice_expect_equiv [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ)
    {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (g : ProductSlicePoint P ell → M) :
    (𝔼 S, g S) =
      𝔼 T : (∀ k, BooleanSlicePoint (P.fiber k) (ell k)),
        g ((productSliceEquiv P ell).symm T) := by
  apply Fintype.expect_equiv (productSliceEquiv P ell) _ _
  intro S
  simp

/-! ### Signed ternary slices

The coupling proof reveals coordinates on which two sign vectors disagree.
Those coordinates carry a fixed number of `+1` and `-1` labels in each
bucket, with all other coordinates labelled `0`.  This is the precise
finite space to which the slice bounded-difference inequality applies. -/

/-- One signed ternary slice, encoded by disjoint positive and negative
coordinate sets of prescribed sizes. -/
def signedSlice (I : Finset α) (plus minus : ℕ) :
    Finset (Finset α × Finset α) :=
  Finset.univ.filter fun S ↦
    S.1 ⊆ I ∧ S.2 ⊆ I ∧ Disjoint S.1 S.2 ∧
      S.1.card = plus ∧ S.2.card = minus

def SignedSlicePoint (I : Finset α) (plus minus : ℕ) : Type u :=
  {S : Finset α × Finset α // S ∈ signedSlice I plus minus}

noncomputable instance (I : Finset α) (plus minus : ℕ) :
    Fintype (SignedSlicePoint I plus minus) :=
  Fintype.ofFinset (signedSlice I plus minus) fun _ ↦ Iff.rfl

@[simp] lemma mem_signedSlice {I : Finset α} {plus minus : ℕ}
    {S : Finset α × Finset α} :
    S ∈ signedSlice I plus minus ↔
      S.1 ⊆ I ∧ S.2 ⊆ I ∧ Disjoint S.1 S.2 ∧
        S.1.card = plus ∧ S.2.card = minus := by
  simp [signedSlice]

lemma signedSlicePoint_nonempty {I : Finset α} {plus minus : ℕ}
    (hcount : plus + minus ≤ I.card) :
    Nonempty (SignedSlicePoint I plus minus) := by
  classical
  have hplus : plus ≤ I.card := le_trans (Nat.le_add_right plus minus) hcount
  obtain ⟨P, hPI, hPcard⟩ := Finset.exists_subset_card_eq hplus
  have hminus : minus ≤ (I \ P).card := by
    rw [Finset.card_sdiff_of_subset hPI, hPcard]
    omega
  obtain ⟨N, hNI, hNcard⟩ := Finset.exists_subset_card_eq hminus
  refine ⟨⟨(P, N), mem_signedSlice.mpr ⟨hPI, ?_, ?_, hPcard, hNcard⟩⟩⟩
  · exact hNI.trans Finset.sdiff_subset
  · rw [Finset.disjoint_left]
    intro i hiP hiN
    exact (Finset.mem_sdiff.mp (hNI hiN)).2 hiP

/-- Ternary value associated to disjoint positive and negative supports. -/
def signedSliceValue {I : Finset α} {plus minus : ℕ}
    (S : SignedSlicePoint I plus minus) (i : α) : ℝ :=
  if i ∈ S.1.1 then 1 else if i ∈ S.1.2 then -1 else 0

@[simp] lemma signedSliceValue_eq_one_iff {I : Finset α} {plus minus : ℕ}
    (S : SignedSlicePoint I plus minus) (i : α) :
    signedSliceValue S i = 1 ↔ i ∈ S.1.1 := by
  by_cases hiP : i ∈ S.1.1
  · simp [signedSliceValue, hiP] <;> norm_num
  · by_cases hiN : i ∈ S.1.2
    · simp [signedSliceValue, hiP, hiN] <;> norm_num
    · simp [signedSliceValue, hiP, hiN] <;> norm_num

@[simp] lemma signedSliceValue_eq_neg_one_iff
    {I : Finset α} {plus minus : ℕ}
    (S : SignedSlicePoint I plus minus) (i : α) :
    signedSliceValue S i = -1 ↔ i ∈ S.1.2 := by
  have hdisj := (mem_signedSlice.mp S.2).2.2.1
  by_cases hiP : i ∈ S.1.1
  · have hiN : i ∉ S.1.2 := Finset.disjoint_left.mp hdisj hiP
    simp [signedSliceValue, hiP, hiN] <;> norm_num
  · by_cases hiN : i ∈ S.1.2
    · simp [signedSliceValue, hiP, hiN] <;> norm_num
    · simp [signedSliceValue, hiP, hiN] <;> norm_num

/-- Product of independently uniform signed slices over all buckets. -/
abbrev ProductSignedSlicePoint [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ) : Type (max u v) :=
  ∀ k, SignedSlicePoint (P.fiber k) (plus k) (minus k)

lemma productSignedSlicePoint_nonempty [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card) :
    Nonempty (ProductSignedSlicePoint P plus minus) := by
  classical
  exact ⟨fun k ↦ Classical.choice (signedSlicePoint_nonempty (hcount k))⟩

/-- Global ternary vector obtained by reading the signed slice in the
unique bucket containing the coordinate. -/
def productSignedSliceValue [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) {plus minus : κ → ℕ}
    (S : ProductSignedSlicePoint P plus minus) (i : α) : ℝ :=
  signedSliceValue (S (P.bucket i)) i

/-- Two product-slice points are related by one legal switch when their
global ternary vectors differ by interchanging two coordinates in a single
bucket.  This relation is the Lipschitz adjacency used in KSSS Lemma 4.17. -/
def IsProductSignedSwitch [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) {plus minus : κ → ℕ}
    (S T : ProductSignedSlicePoint P plus minus) : Prop :=
  ∃ (k : κ) (i j : α), i ∈ P.fiber k ∧ j ∈ P.fiber k ∧ i ≠ j ∧
    ∀ v, productSignedSliceValue P T v =
      if v = i then productSignedSliceValue P S j
      else if v = j then productSignedSliceValue P S i
      else productSignedSliceValue P S v

lemma isProductSignedSwitch_symm [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) {plus minus : κ → ℕ}
    {S T : ProductSignedSlicePoint P plus minus}
    (h : IsProductSignedSwitch P S T) : IsProductSignedSwitch P T S := by
  classical
  obtain ⟨k, i, j, hi, hj, hij, hswap⟩ := h
  refine ⟨k, i, j, hi, hj, hij, ?_⟩
  intro v
  by_cases hvi : v = i
  · subst v
    simp only [if_pos]
    have hj := hswap j
    simp [hij, hij.symm] at hj
    exact hj.symm
  · by_cases hvj : v = j
    · subst v
      simp only [hvi, if_false, if_pos]
      have hi := hswap i
      simp [hij] at hi
      exact hi.symm
    · simp only [hvi, hvj, if_false]
      have hv := hswap v
      simp [hvi, hvj] at hv
      exact hv.symm

/-- A signed slice is obtained by first choosing its positive support and
then choosing its negative support from the remaining coordinates. -/
noncomputable def signedSliceChoiceEquiv (I : Finset α) (plus minus : ℕ) :
    SignedSlicePoint I plus minus ≃
      Σ P : BooleanSlicePoint I plus, BooleanSlicePoint (I \ P.1) minus where
  toFun S :=
    ⟨⟨S.1.1, mem_booleanSlice.mpr ⟨(mem_signedSlice.mp S.2).1,
        (mem_signedSlice.mp S.2).2.2.2.1⟩⟩,
      ⟨S.1.2, mem_booleanSlice.mpr ⟨by
        intro i hiN
        rw [Finset.mem_sdiff]
        exact ⟨(mem_signedSlice.mp S.2).2.1 hiN, fun hiP ↦
          Finset.disjoint_left.mp (mem_signedSlice.mp S.2).2.2.1 hiP hiN⟩,
        (mem_signedSlice.mp S.2).2.2.2.2⟩⟩⟩
  invFun T :=
    ⟨(T.1.1, T.2.1), mem_signedSlice.mpr ⟨
      (mem_booleanSlice.mp T.1.2).1, by
        intro i hi
        exact (Finset.mem_sdiff.mp ((mem_booleanSlice.mp T.2.2).1 hi)).1, by
        rw [Finset.disjoint_left]
        intro i hiP hiN
        exact (Finset.mem_sdiff.mp ((mem_booleanSlice.mp T.2.2).1 hiN)).2 hiP,
      (mem_booleanSlice.mp T.1.2).2, (mem_booleanSlice.mp T.2.2).2⟩⟩
  left_inv S := by
    apply Subtype.ext
    apply Prod.ext <;> rfl
  right_inv T := by
    rcases T with ⟨⟨P, hP⟩, ⟨N, hN⟩⟩
    rfl

@[simp] lemma card_signedSlicePoint (I : Finset α) (plus minus : ℕ) :
    Fintype.card (SignedSlicePoint I plus minus) =
      I.card.choose plus * (I.card - plus).choose minus := by
  rw [Fintype.card_congr (signedSliceChoiceEquiv I plus minus), Fintype.card_sigma]
  calc
    (∑ P : BooleanSlicePoint I plus,
        Fintype.card (BooleanSlicePoint (I \ P.1) minus)) =
        ∑ _P : BooleanSlicePoint I plus, (I.card - plus).choose minus := by
      apply Finset.sum_congr rfl
      intro P _
      rw [card_booleanSlicePoint, Finset.card_sdiff_of_subset
        (mem_booleanSlice.mp P.2).1, (mem_booleanSlice.mp P.2).2]
    _ = Fintype.card (BooleanSlicePoint I plus) *
        (I.card - plus).choose minus := by simp
    _ = I.card.choose plus * (I.card - plus).choose minus := by
      rw [card_booleanSlicePoint]

@[simp] lemma card_productSignedSlicePoint [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ) :
    Fintype.card (ProductSignedSlicePoint P plus minus) =
      ∏ k, (P.fiber k).card.choose (plus k) *
        ((P.fiber k).card - plus k).choose (minus k) := by
  rw [Fintype.card_pi]
  simp

/-! ### Permutation sampler for signed slices -/

/-- The consecutive block of `minus` slots immediately after the first
`plus` slots, embedded into a set of `N` slots. -/
def finIntervalEmbedding (N plus minus : ℕ) (hcount : plus + minus ≤ N) :
    Fin minus ↪ Fin N where
  toFun i := ⟨plus + i, lt_of_lt_of_le (Nat.add_lt_add_left i.isLt plus) hcount⟩
  inj' i j hij := by
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val hij)

/-- The coordinate embedding obtained by first applying a permutation of
the slots and then the fixed enumeration of `I`. -/
def decodedCoordinateEmbedding (I : Finset α)
    (e : Fin I.card ≃ ↑I) (σ : Equiv.Perm (Fin I.card)) : Fin I.card ↪ α :=
  σ.toEmbedding.trans
    (e.toEmbedding.trans (Function.Embedding.subtype fun i : α ↦ i ∈ I))

/-- Positive support decoded from the first `plus` slots of a permutation. -/
def signedSlicePositiveSupport (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (σ : Equiv.Perm (Fin I.card)) : Finset α :=
  Finset.univ.map ((Fin.castLEEmb
    (le_trans (Nat.le_add_right plus minus) hcount)).trans
      (decodedCoordinateEmbedding I e σ))

/-- Negative support decoded from the `minus` slots following the positive
slots of a permutation. -/
def signedSliceNegativeSupport (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (σ : Equiv.Perm (Fin I.card)) : Finset α :=
  Finset.univ.map ((finIntervalEmbedding I.card plus minus hcount).trans
    (decodedCoordinateEmbedding I e σ))

lemma signedSlicePositiveSupport_subset (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (σ : Equiv.Perm (Fin I.card)) :
    signedSlicePositiveSupport I plus minus hcount e σ ⊆ I := by
  intro i hi
  rw [signedSlicePositiveSupport, Finset.mem_map] at hi
  obtain ⟨j, _hj, rfl⟩ := hi
  exact (e (σ (Fin.castLE
    (le_trans (Nat.le_add_right plus minus) hcount) j))).2

lemma signedSliceNegativeSupport_subset (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (σ : Equiv.Perm (Fin I.card)) :
    signedSliceNegativeSupport I plus minus hcount e σ ⊆ I := by
  intro i hi
  rw [signedSliceNegativeSupport, Finset.mem_map] at hi
  obtain ⟨j, _hj, rfl⟩ := hi
  exact (e (σ (finIntervalEmbedding I.card plus minus hcount j))).2

@[simp] lemma card_signedSlicePositiveSupport (I : Finset α)
    (plus minus : ℕ) (hcount : plus + minus ≤ I.card)
    (e : Fin I.card ≃ ↑I) (σ : Equiv.Perm (Fin I.card)) :
    (signedSlicePositiveSupport I plus minus hcount e σ).card = plus := by
  simp [signedSlicePositiveSupport]

@[simp] lemma card_signedSliceNegativeSupport (I : Finset α)
    (plus minus : ℕ) (hcount : plus + minus ≤ I.card)
    (e : Fin I.card ≃ ↑I) (σ : Equiv.Perm (Fin I.card)) :
    (signedSliceNegativeSupport I plus minus hcount e σ).card = minus := by
  simp [signedSliceNegativeSupport]

lemma signedSliceSupports_disjoint (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (σ : Equiv.Perm (Fin I.card)) :
    Disjoint (signedSlicePositiveSupport I plus minus hcount e σ)
      (signedSliceNegativeSupport I plus minus hcount e σ) := by
  rw [Finset.disjoint_left]
  intro i hiP hiN
  rw [signedSlicePositiveSupport, Finset.mem_map] at hiP
  rw [signedSliceNegativeSupport, Finset.mem_map] at hiN
  obtain ⟨p, _hp, hp⟩ := hiP
  obtain ⟨m, _hm, hm⟩ := hiN
  have hslots :
      Fin.castLE (le_trans (Nat.le_add_right plus minus) hcount) p =
        finIntervalEmbedding I.card plus minus hcount m := by
    apply (decodedCoordinateEmbedding I e σ).injective
    exact hp.trans hm.symm
  have hvals := congrArg Fin.val hslots
  change p.val = plus + m.val at hvals
  omega

/-- Decode a permutation into the signed slice obtained by labelling its
first `plus` images positive and its next `minus` images negative. -/
noncomputable def signedSliceDecode (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (σ : Equiv.Perm (Fin I.card)) : SignedSlicePoint I plus minus :=
  ⟨(signedSlicePositiveSupport I plus minus hcount e σ,
      signedSliceNegativeSupport I plus minus hcount e σ),
    mem_signedSlice.mpr ⟨
      signedSlicePositiveSupport_subset I plus minus hcount e σ,
      signedSliceNegativeSupport_subset I plus minus hcount e σ,
      signedSliceSupports_disjoint I plus minus hcount e σ,
      card_signedSlicePositiveSupport I plus minus hcount e σ,
      card_signedSliceNegativeSupport I plus minus hcount e σ⟩⟩

/-- Independent permutation samplers for all buckets. -/
abbrev ProductSignedSliceSampler [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) :=
  ∀ k, Equiv.Perm (Fin (P.fiber k).card)

/-- Decode all bucket permutations independently. -/
noncomputable def productSignedSliceDecode [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (σ : ProductSignedSliceSampler P) : ProductSignedSlicePoint P plus minus :=
  fun k ↦ signedSliceDecode (P.fiber k) (plus k) (minus k)
    (hcount k) (e k) (σ k)

/-- Lift a finset contained in `I` to the subtype `↑I`. -/
def finsetLift (I S : Finset α) : Finset ↑I :=
  Finset.univ.filter fun i ↦ (i : α) ∈ S

lemma map_finsetLift (I S : Finset α) (hS : S ⊆ I) :
    (finsetLift I S).map (Function.Embedding.subtype fun i : α ↦ i ∈ I) = S := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact (Finset.mem_filter.mp hj).2
  · intro hi
    rw [Finset.mem_map]
    exact ⟨⟨i, hS hi⟩, by simp [finsetLift, hi], rfl⟩

@[simp] lemma card_finsetLift (I S : Finset α) (hS : S ⊆ I) :
    (finsetLift I S).card = S.card := by
  rw [← Finset.card_map (Function.Embedding.subtype fun i : α ↦ i ∈ I),
    map_finsetLift I S hS]

lemma disjoint_finsetLift (I A B : Finset α) (hAB : Disjoint A B) :
    Disjoint (finsetLift I A) (finsetLift I B) := by
  rw [Finset.disjoint_left]
  intro i hiA hiB
  exact Finset.disjoint_left.mp hAB
    (Finset.mem_filter.mp hiA).2 (Finset.mem_filter.mp hiB).2

/-- A permutation can simultaneously carry two disjoint finite colour
classes to any other two disjoint classes of the same respective sizes. -/
lemma exists_perm_map_disjoint_pair { β : Type* } [Fintype β] [DecidableEq β]
    (A B C D : Finset β) (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hAC : A.card = C.card) (hBD : B.card = D.card) :
    ∃ ρ : Equiv.Perm β,
      A.map ρ.toEmbedding = C ∧ B.map ρ.toEmbedding = D := by
  classical
  have hABset : Disjoint (↑A : Set β) (↑B : Set β) := by
    rw [Set.disjoint_left]
    intro i hiA hiB
    exact Finset.disjoint_left.mp hAB hiA hiB
  have hCDset : Disjoint (↑C : Set β) (↑D : Set β) := by
    rw [Set.disjoint_left]
    intro i hiC hiD
    exact Finset.disjoint_left.mp hCD hiC hiD
  let eA : (↑A : Set β) ≃ (↑C : Set β) := A.equivOfCardEq hAC
  let eB : (↑B : Set β) ≃ (↑D : Set β) := B.equivOfCardEq hBD
  let eU : ↑((A : Set β) ∪ (B : Set β)) ≃
      ↑((C : Set β) ∪ (D : Set β)) :=
    (Equiv.Set.union hABset).trans
      ((Equiv.sumCongr eA eB).trans (Equiv.Set.union hCDset).symm)
  let ρ : Equiv.Perm β := eU.extendSubtype
  refine ⟨ρ, ?_, ?_⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro i hi
      rw [Finset.mem_map] at hi
      obtain ⟨j, hjA, rfl⟩ := hi
      have hjU : j ∈ ((A : Set β) ∪ (B : Set β)) := Or.inl hjA
      change ρ j ∈ C
      change eU.extendSubtype j ∈ C
      rw [Equiv.extendSubtype_apply_of_mem eU j hjU]
      change ((eU ⟨j, hjU⟩ :
        ↑((C : Set β) ∪ (D : Set β))) : β) ∈ C
      have he : eU ⟨j, hjU⟩ = (Equiv.Set.union hCDset).symm
          (Sum.inl (eA ⟨j, hjA⟩)) := by
        simp only [eU, Equiv.trans_apply]
        rw [Equiv.Set.union_apply_left hABset hjA]
        have hinner : (Equiv.sumCongr eA eB)
            (Sum.inl (⟨(⟨j, hjU⟩ :
              ↑((A : Set β) ∪ (B : Set β))).1, hjA⟩ : (↑A : Set β))) =
              Sum.inl (eA ⟨j, hjA⟩) := by
          change Sum.inl (eA _) = Sum.inl (eA _)
          congr 2
        exact congrArg (Equiv.Set.union hCDset).symm hinner
      rw [he]
      rw [Equiv.Set.union_symm_apply_left]
      exact (eA ⟨j, hjA⟩).property
    · simp [hAC]
  · apply Finset.eq_of_subset_of_card_le
    · intro i hi
      rw [Finset.mem_map] at hi
      obtain ⟨j, hjB, rfl⟩ := hi
      have hjU : j ∈ ((A : Set β) ∪ (B : Set β)) := Or.inr hjB
      change ρ j ∈ D
      change eU.extendSubtype j ∈ D
      rw [Equiv.extendSubtype_apply_of_mem eU j hjU]
      change ((eU ⟨j, hjU⟩ :
        ↑((C : Set β) ∪ (D : Set β))) : β) ∈ D
      have he : eU ⟨j, hjU⟩ = (Equiv.Set.union hCDset).symm
          (Sum.inr (eB ⟨j, hjB⟩)) := by
        simp only [eU, Equiv.trans_apply]
        rw [Equiv.Set.union_apply_right hABset hjB]
        have hinner : (Equiv.sumCongr eA eB)
            (Sum.inr (⟨(⟨j, hjU⟩ :
              ↑((A : Set β) ∪ (B : Set β))).1, hjB⟩ : (↑B : Set β))) =
              Sum.inr (eB ⟨j, hjB⟩) := by
          change Sum.inr (eB _) = Sum.inr (eB _)
          congr 2
        exact congrArg (Equiv.Set.union hCDset).symm hinner
      rw [he]
      rw [Equiv.Set.union_symm_apply_right]
      exact (eB ⟨j, hjB⟩).property
    · simp [hBD]

/-- The first `plus` slots in a signed-slice permutation sampler. -/
def signedPositiveSlots (N plus minus : ℕ) (hcount : plus + minus ≤ N) :
    Finset (Fin N) :=
  Finset.univ.map (Fin.castLEEmb
    (le_trans (Nat.le_add_right plus minus) hcount))

/-- The `minus` slots immediately following the positive slots. -/
def signedNegativeSlots (N plus minus : ℕ) (hcount : plus + minus ≤ N) :
    Finset (Fin N) :=
  Finset.univ.map (finIntervalEmbedding N plus minus hcount)

@[simp] lemma card_signedPositiveSlots (N plus minus : ℕ)
    (hcount : plus + minus ≤ N) :
    (signedPositiveSlots N plus minus hcount).card = plus := by
  simp [signedPositiveSlots]

@[simp] lemma card_signedNegativeSlots (N plus minus : ℕ)
    (hcount : plus + minus ≤ N) :
    (signedNegativeSlots N plus minus hcount).card = minus := by
  simp [signedNegativeSlots]

lemma signedSlots_disjoint (N plus minus : ℕ) (hcount : plus + minus ≤ N) :
    Disjoint (signedPositiveSlots N plus minus hcount)
      (signedNegativeSlots N plus minus hcount) := by
  rw [Finset.disjoint_left]
  intro i hiP hiN
  rw [signedPositiveSlots, Finset.mem_map] at hiP
  rw [signedNegativeSlots, Finset.mem_map] at hiN
  obtain ⟨p, _hp, hp⟩ := hiP
  obtain ⟨m, _hm, hm⟩ := hiN
  have hvals := congrArg Fin.val (hp.trans hm.symm)
  change p.val = plus + m.val at hvals
  omega

/-- Pull a support contained in `I` back to slots using the fixed
enumeration of `I`. -/
def signedSupportSlots (I S : Finset α) (e : Fin I.card ≃ ↑I) :
    Finset (Fin I.card) :=
  (finsetLift I S).map e.symm.toEmbedding

@[simp] lemma card_signedSupportSlots (I S : Finset α)
    (e : Fin I.card ≃ ↑I) (hS : S ⊆ I) :
    (signedSupportSlots I S e).card = S.card := by
  simp [signedSupportSlots, card_finsetLift I S hS]

lemma signedSupportSlots_disjoint (I A B : Finset α)
    (e : Fin I.card ≃ ↑I) (hAB : Disjoint A B) :
    Disjoint (signedSupportSlots I A e) (signedSupportSlots I B e) := by
  rw [Finset.disjoint_left]
  intro i hiA hiB
  rw [signedSupportSlots, Finset.mem_map] at hiA hiB
  obtain ⟨a, ha, hai⟩ := hiA
  obtain ⟨b, hb, hbi⟩ := hiB
  have hab : a = b := e.symm.injective (hai.trans hbi.symm)
  subst b
  exact Finset.disjoint_left.mp (disjoint_finsetLift I A B hAB) ha hb

lemma map_signedSupportSlots (I S : Finset α)
    (e : Fin I.card ≃ ↑I) (hS : S ⊆ I) :
    (signedSupportSlots I S e).map
        (e.toEmbedding.trans (Function.Embedding.subtype fun i : α ↦ i ∈ I)) = S := by
  rw [signedSupportSlots, Finset.map_map]
  have hemb : e.symm.toEmbedding.trans
      (e.toEmbedding.trans (Function.Embedding.subtype fun i : α ↦ i ∈ I)) =
      Function.Embedding.subtype (fun i : α ↦ i ∈ I) := by
    ext i
    simp
  rw [hemb, map_finsetLift I S hS]

lemma signedSlicePositiveSupport_eq_slots_map (I : Finset α)
    (plus minus : ℕ) (hcount : plus + minus ≤ I.card)
    (e : Fin I.card ≃ ↑I) (σ : Equiv.Perm (Fin I.card)) :
    signedSlicePositiveSupport I plus minus hcount e σ =
      (signedPositiveSlots I.card plus minus hcount).map
        (decodedCoordinateEmbedding I e σ) := by
  rw [signedSlicePositiveSupport, signedPositiveSlots, Finset.map_map]

lemma signedSliceNegativeSupport_eq_slots_map (I : Finset α)
    (plus minus : ℕ) (hcount : plus + minus ≤ I.card)
    (e : Fin I.card ≃ ↑I) (σ : Equiv.Perm (Fin I.card)) :
    signedSliceNegativeSupport I plus minus hcount e σ =
      (signedNegativeSlots I.card plus minus hcount).map
        (decodedCoordinateEmbedding I e σ) := by
  rw [signedSliceNegativeSupport, signedNegativeSlots, Finset.map_map]

/-- Every signed slice is obtained from the explicit permutation decoder. -/
lemma signedSliceDecode_surjective (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I) :
    Function.Surjective (signedSliceDecode I plus minus hcount e) := by
  intro S
  rcases mem_signedSlice.mp S.2 with ⟨hPI, hNI, hPN, hPcard, hNcard⟩
  let AP := signedPositiveSlots I.card plus minus hcount
  let AN := signedNegativeSlots I.card plus minus hcount
  let CP := signedSupportSlots I S.1.1 e
  let CN := signedSupportSlots I S.1.2 e
  have hAPAN : Disjoint AP AN := signedSlots_disjoint I.card plus minus hcount
  have hCPCN : Disjoint CP CN := signedSupportSlots_disjoint I S.1.1 S.1.2 e hPN
  have hAPCP : AP.card = CP.card := by
    simp [AP, CP, card_signedSupportSlots I S.1.1 e hPI, hPcard]
  have hANCN : AN.card = CN.card := by
    simp [AN, CN, card_signedSupportSlots I S.1.2 e hNI, hNcard]
  obtain ⟨σ, hσP, hσN⟩ :=
    exists_perm_map_disjoint_pair AP AN CP CN hAPAN hCPCN hAPCP hANCN
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change signedSlicePositiveSupport I plus minus hcount e σ = S.1.1
    rw [signedSlicePositiveSupport_eq_slots_map]
    change AP.map (decodedCoordinateEmbedding I e σ) = S.1.1
    rw [decodedCoordinateEmbedding, ← Finset.map_map, hσP]
    exact map_signedSupportSlots I S.1.1 e hPI
  · change signedSliceNegativeSupport I plus minus hcount e σ = S.1.2
    rw [signedSliceNegativeSupport_eq_slots_map]
    change AN.map (decodedCoordinateEmbedding I e σ) = S.1.2
    rw [decodedCoordinateEmbedding, ← Finset.map_map, hσN]
    exact map_signedSupportSlots I S.1.2 e hNI

/-- A decoder fiber is equivalently described by the images of its two
distinguished slot classes. -/
lemma signedSliceDecode_eq_iff_slots (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (σ : Equiv.Perm (Fin I.card)) (S : SignedSlicePoint I plus minus) :
    signedSliceDecode I plus minus hcount e σ = S ↔
      (signedPositiveSlots I.card plus minus hcount).map σ.toEmbedding =
          signedSupportSlots I S.1.1 e ∧
      (signedNegativeSlots I.card plus minus hcount).map σ.toEmbedding =
          signedSupportSlots I S.1.2 e := by
  rcases mem_signedSlice.mp S.2 with ⟨hPI, hNI, _hPN, _hPcard, _hNcard⟩
  let eI : Fin I.card ↪ α :=
    e.toEmbedding.trans (Function.Embedding.subtype fun i : α ↦ i ∈ I)
  constructor
  · intro h
    have hP : signedSlicePositiveSupport I plus minus hcount e σ = S.1.1 := by
      exact congrArg (fun T : SignedSlicePoint I plus minus ↦ T.1.1) h
    have hN : signedSliceNegativeSupport I plus minus hcount e σ = S.1.2 := by
      exact congrArg (fun T : SignedSlicePoint I plus minus ↦ T.1.2) h
    constructor
    · apply Finset.map_injective eI
      calc
        ((signedPositiveSlots I.card plus minus hcount).map σ.toEmbedding).map eI =
            signedSlicePositiveSupport I plus minus hcount e σ := by
          rw [Finset.map_map, signedSlicePositiveSupport_eq_slots_map]
          rfl
        _ = S.1.1 := hP
        _ = (signedSupportSlots I S.1.1 e).map eI :=
          (map_signedSupportSlots I S.1.1 e hPI).symm
    · apply Finset.map_injective eI
      calc
        ((signedNegativeSlots I.card plus minus hcount).map σ.toEmbedding).map eI =
            signedSliceNegativeSupport I plus minus hcount e σ := by
          rw [Finset.map_map, signedSliceNegativeSupport_eq_slots_map]
          rfl
        _ = S.1.2 := hN
        _ = (signedSupportSlots I S.1.2 e).map eI :=
          (map_signedSupportSlots I S.1.2 e hNI).symm
  · rintro ⟨hP, hN⟩
    apply Subtype.ext
    apply Prod.ext
    · change signedSlicePositiveSupport I plus minus hcount e σ = S.1.1
      rw [signedSlicePositiveSupport_eq_slots_map]
      change (signedPositiveSlots I.card plus minus hcount).map
        (σ.toEmbedding.trans eI) = S.1.1
      rw [← Finset.map_map, hP]
      exact map_signedSupportSlots I S.1.1 e hPI
    · change signedSliceNegativeSupport I plus minus hcount e σ = S.1.2
      rw [signedSliceNegativeSupport_eq_slots_map]
      change (signedNegativeSlots I.card plus minus hcount).map
        (σ.toEmbedding.trans eI) = S.1.2
      rw [← Finset.map_map, hN]
      exact map_signedSupportSlots I S.1.2 e hNI

/-- All fibers of the signed-slice permutation decoder have equal
cardinality.  Left multiplication by a suitable two-colour orbit
permutation gives the explicit equivalence of fibers. -/
lemma card_signedSliceDecode_fiber_eq (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (S T : SignedSlicePoint I plus minus) :
    Nat.card {σ : Equiv.Perm (Fin I.card) //
        signedSliceDecode I plus minus hcount e σ = S} =
      Nat.card {σ : Equiv.Perm (Fin I.card) //
        signedSliceDecode I plus minus hcount e σ = T} := by
  classical
  rcases mem_signedSlice.mp S.2 with ⟨hSPI, hSNI, hSPN, hSPcard, hSNcard⟩
  rcases mem_signedSlice.mp T.2 with ⟨hTPI, hTNI, hTPN, hTPcard, hTNcard⟩
  let SP := signedSupportSlots I S.1.1 e
  let SN := signedSupportSlots I S.1.2 e
  let TP := signedSupportSlots I T.1.1 e
  let TN := signedSupportSlots I T.1.2 e
  have hSdisj : Disjoint SP SN := signedSupportSlots_disjoint I S.1.1 S.1.2 e hSPN
  have hTdisj : Disjoint TP TN := signedSupportSlots_disjoint I T.1.1 T.1.2 e hTPN
  have hPcard : SP.card = TP.card := by
    simp [SP, TP, card_signedSupportSlots I S.1.1 e hSPI,
      card_signedSupportSlots I T.1.1 e hTPI, hSPcard, hTPcard]
  have hNcard : SN.card = TN.card := by
    simp [SN, TN, card_signedSupportSlots I S.1.2 e hSNI,
      card_signedSupportSlots I T.1.2 e hTNI, hSNcard, hTNcard]
  obtain ⟨ρ, hρP, hρN⟩ :=
    exists_perm_map_disjoint_pair SP SN TP TN hSdisj hTdisj hPcard hNcard
  have hρP_inv : TP.map ρ.symm.toEmbedding = SP := by
    rw [← hρP, Finset.map_map]
    simpa using Finset.map_refl SP
  have hρN_inv : TN.map ρ.symm.toEmbedding = SN := by
    rw [← hρN, Finset.map_map]
    simpa using Finset.map_refl SN
  let E : {σ : Equiv.Perm (Fin I.card) //
        signedSliceDecode I plus minus hcount e σ = S} ≃
      {σ : Equiv.Perm (Fin I.card) //
        signedSliceDecode I plus minus hcount e σ = T} := {
    toFun := fun σ ↦ ⟨ρ * σ.1, by
      apply (signedSliceDecode_eq_iff_slots I plus minus hcount e _ T).2
      have hσ := (signedSliceDecode_eq_iff_slots I plus minus hcount e σ.1 S).1 σ.2
      constructor
      · calc
          (signedPositiveSlots I.card plus minus hcount).map
              (ρ * σ.1).toEmbedding =
              ((signedPositiveSlots I.card plus minus hcount).map
                σ.1.toEmbedding).map ρ.toEmbedding := by
                rw [Finset.map_map]
                rfl
          _ = SP.map ρ.toEmbedding := by rw [hσ.1]
          _ = TP := hρP
      · calc
          (signedNegativeSlots I.card plus minus hcount).map
              (ρ * σ.1).toEmbedding =
              ((signedNegativeSlots I.card plus minus hcount).map
                σ.1.toEmbedding).map ρ.toEmbedding := by
                rw [Finset.map_map]
                rfl
          _ = SN.map ρ.toEmbedding := by rw [hσ.2]
          _ = TN := hρN⟩
    invFun := fun τ ↦ ⟨ρ⁻¹ * τ.1, by
      apply (signedSliceDecode_eq_iff_slots I plus minus hcount e _ S).2
      have hτ := (signedSliceDecode_eq_iff_slots I plus minus hcount e τ.1 T).1 τ.2
      constructor
      · calc
          (signedPositiveSlots I.card plus minus hcount).map
              (ρ⁻¹ * τ.1).toEmbedding =
              ((signedPositiveSlots I.card plus minus hcount).map
                τ.1.toEmbedding).map ρ.symm.toEmbedding := by
                rw [Finset.map_map]
                rfl
          _ = TP.map ρ.symm.toEmbedding := by rw [hτ.1]
          _ = SP := hρP_inv
      · calc
          (signedNegativeSlots I.card plus minus hcount).map
              (ρ⁻¹ * τ.1).toEmbedding =
              ((signedNegativeSlots I.card plus minus hcount).map
                τ.1.toEmbedding).map ρ.symm.toEmbedding := by
                rw [Finset.map_map]
                rfl
          _ = TN.map ρ.symm.toEmbedding := by rw [hτ.2]
          _ = SN := hρN_inv⟩
    left_inv := by
      intro σ
      apply Subtype.ext
      simp
    right_inv := by
      intro τ
      apply Subtype.ext
      simp
  }
  exact Nat.card_congr E

/-- Every finite type is the disjoint union of the fibers of a map. -/
def totalEquivSigmaFiber {A B : Type*} (f : A → B) :
    A ≃ Σ b, {a : A // f a = b} where
  toFun a := ⟨f a, a, rfl⟩
  invFun a := a.2.1
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨b, a, ha⟩
    subst b
    rfl

/-- Exact cardinality of every fiber of the signed-slice decoder. -/
lemma card_signedSliceDecode_fiber (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (S : SignedSlicePoint I plus minus) :
    Nat.card {σ : Equiv.Perm (Fin I.card) //
        signedSliceDecode I plus minus hcount e σ = S} =
      plus.factorial * minus.factorial *
        (I.card - plus - minus).factorial := by
  classical
  let d := signedSliceDecode I plus minus hcount e
  let c := Nat.card {σ : Equiv.Perm (Fin I.card) // d σ = S}
  have htotal : Nat.card (Equiv.Perm (Fin I.card)) =
      Nat.card (SignedSlicePoint I plus minus) * c := by
    calc
      Nat.card (Equiv.Perm (Fin I.card)) =
          Nat.card (Σ T : SignedSlicePoint I plus minus,
            {σ : Equiv.Perm (Fin I.card) // d σ = T}) :=
        Nat.card_congr (totalEquivSigmaFiber d)
      _ = ∑ T : SignedSlicePoint I plus minus,
          Nat.card {σ : Equiv.Perm (Fin I.card) // d σ = T} :=
        Nat.card_sigma
      _ = ∑ _T : SignedSlicePoint I plus minus, c := by
        apply Finset.sum_congr rfl
        intro T _
        exact card_signedSliceDecode_fiber_eq I plus minus hcount e T S
      _ = Nat.card (SignedSlicePoint I plus minus) * c := by
        rw [Nat.card_eq_fintype_card]
        simp
  have hplus : plus ≤ I.card :=
    le_trans (Nat.le_add_right plus minus) hcount
  have hminus : minus ≤ I.card - plus := by omega
  let factor := plus.factorial * minus.factorial *
    (I.card - plus - minus).factorial
  have hfactorial : Nat.card (SignedSlicePoint I plus minus) * factor =
      I.card.factorial := by
    rw [Nat.card_eq_fintype_card, card_signedSlicePoint]
    dsimp [factor]
    calc
      (I.card.choose plus * (I.card - plus).choose minus) *
          (plus.factorial * minus.factorial *
            (I.card - plus - minus).factorial) =
          (I.card.choose plus * plus.factorial) *
            ((I.card - plus).choose minus * minus.factorial *
              (I.card - plus - minus).factorial) := by ring
      _ = (I.card.choose plus * plus.factorial) *
          (I.card - plus).factorial := by
        rw [Nat.choose_mul_factorial_mul_factorial hminus]
      _ = I.card.factorial := by
        exact Nat.choose_mul_factorial_mul_factorial hplus
  have hperm : Nat.card (Equiv.Perm (Fin I.card)) = I.card.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hspos : 0 < Nat.card (SignedSlicePoint I plus minus) := by
    rw [Nat.card_eq_fintype_card]
    letI : Nonempty (SignedSlicePoint I plus minus) :=
      signedSlicePoint_nonempty hcount
    exact Fintype.card_pos
  change c = factor
  apply Nat.eq_of_mul_eq_mul_left hspos
  calc
    Nat.card (SignedSlicePoint I plus minus) * c =
        Nat.card (Equiv.Perm (Fin I.card)) := htotal.symm
    _ = I.card.factorial := hperm
    _ = Nat.card (SignedSlicePoint I plus minus) * factor := hfactorial.symm

/-- A finite map with fibers of cardinality `c` pushes counting measure
forward to `c` times counting measure. -/
lemma sum_comp_eq_card_fiber_mul_sum {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (d : A → B) (c : ℕ)
    (hcard : ∀ b, Nat.card {a : A // d a = b} = c)
    (g : B → ℝ) :
    ∑ a, g (d a) = (c : ℝ) * ∑ b, g b := by
  classical
  calc
    ∑ a, g (d a) =
        ∑ b : B, ∑ a ∈ (Finset.univ : Finset A) with d a = b, g b :=
      (Finset.sum_fiberwise' Finset.univ d g).symm
    _ = ∑ b : B, (c : ℝ) * g b := by
      apply Finset.sum_congr rfl
      intro b _
      have hfilter : ((Finset.univ : Finset A).filter fun a ↦ d a = b).card = c := by
        rw [← hcard b, Nat.card_eq_fintype_card]
        simp [Fintype.card_subtype]
      simp [hfilter]
    _ = (c : ℝ) * ∑ b : B, g b := by rw [Finset.mul_sum]

/-- Exact uniform pushforward identity for one signed slice. -/
lemma sum_signedSliceDecode (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (g : SignedSlicePoint I plus minus → ℝ) :
    ∑ σ : Equiv.Perm (Fin I.card),
        g (signedSliceDecode I plus minus hcount e σ) =
      (plus.factorial * minus.factorial *
        (I.card - plus - minus).factorial : ℕ) *
        ∑ S : SignedSlicePoint I plus minus, g S := by
  classical
  exact sum_comp_eq_card_fiber_mul_sum
    (signedSliceDecode I plus minus hcount e)
    (plus.factorial * minus.factorial *
      (I.card - plus - minus).factorial)
    (card_signedSliceDecode_fiber I plus minus hcount e) g

/-- A product-decoder fiber is the dependent product of its one-bucket
fibers. -/
noncomputable def productSignedSliceDecodeFiberEquiv [Fintype κ]
    [DecidableEq κ] (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (S : ProductSignedSlicePoint P plus minus) :
    {σ : ProductSignedSliceSampler P //
      productSignedSliceDecode P plus minus hcount e σ = S} ≃
      ∀ k, {τ : Equiv.Perm (Fin (P.fiber k).card) //
        signedSliceDecode (P.fiber k) (plus k) (minus k)
          (hcount k) (e k) τ = S k} where
  toFun σ k := ⟨σ.1 k, by
    have hk := congrArg (fun T : ProductSignedSlicePoint P plus minus ↦ T k) σ.2
    simpa [productSignedSliceDecode] using hk⟩
  invFun τ := ⟨fun k ↦ (τ k).1, by
    funext k
    exact (τ k).2⟩
  left_inv σ := by
    apply Subtype.ext
    funext k
    rfl
  right_inv τ := by
    funext k
    apply Subtype.ext
    rfl

/-- The common fiber factor of the product signed-slice decoder. -/
def productSignedSliceFiberFactor [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ) : ℕ :=
  ∏ k, (plus k).factorial * (minus k).factorial *
    ((P.fiber k).card - plus k - minus k).factorial

lemma productSignedSliceFiberFactor_pos [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ) :
    0 < productSignedSliceFiberFactor P plus minus := by
  apply Finset.prod_pos
  intro k _
  positivity

/-- Exact common fiber cardinality for the product decoder. -/
lemma card_productSignedSliceDecode_fiber [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (S : ProductSignedSlicePoint P plus minus) :
    Nat.card {σ : ProductSignedSliceSampler P //
      productSignedSliceDecode P plus minus hcount e σ = S} =
        productSignedSliceFiberFactor P plus minus := by
  rw [Nat.card_congr
    (productSignedSliceDecodeFiberEquiv P plus minus hcount e S), Nat.card_pi]
  apply Finset.prod_congr rfl
  intro k _
  exact card_signedSliceDecode_fiber (P.fiber k) (plus k) (minus k)
    (hcount k) (e k) (S k)

/-- Exact counting-measure pushforward for the product decoder. -/
lemma sum_productSignedSliceDecode [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (g : ProductSignedSlicePoint P plus minus → ℝ) :
    ∑ σ : ProductSignedSliceSampler P,
        g (productSignedSliceDecode P plus minus hcount e σ) =
      productSignedSliceFiberFactor P plus minus *
        ∑ S : ProductSignedSlicePoint P plus minus, g S := by
  classical
  exact sum_comp_eq_card_fiber_mul_sum
    (productSignedSliceDecode P plus minus hcount e)
    (productSignedSliceFiberFactor P plus minus)
    (card_productSignedSliceDecode_fiber P plus minus hcount e) g

/-- Normalizing a positive constant-fiber pushforward preserves uniform
expectation exactly. -/
lemma uniformExpectation_comp_of_card_fiber {A B : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] [DecidableEq B]
    (d : A → B) (c : ℕ) (hc : 0 < c)
    (hcard : ∀ b, Nat.card {a : A // d a = b} = c)
    (g : B → ℝ) :
    Concentration.uniformExpectation (fun a ↦ g (d a)) =
      Concentration.uniformExpectation g := by
  have hsum := sum_comp_eq_card_fiber_mul_sum d c hcard g
  have hden : (Fintype.card A : ℝ) = c * Fintype.card B := by
    simpa using sum_comp_eq_card_fiber_mul_sum d c hcard (fun _ ↦ (1 : ℝ))
  rw [Concentration.uniformExpectation, Concentration.uniformExpectation, hsum, hden]
  exact mul_div_mul_left _ _ (by exact_mod_cast hc.ne')

/-- The analogous constant-fiber identity for uniform event probability. -/
lemma uniformProbability_comp_of_card_fiber {A B : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] [DecidableEq B]
    (d : A → B) (c : ℕ) (hc : 0 < c)
    (hcard : ∀ b, Nat.card {a : A // d a = b} = c)
    (Q : B → Prop) :
    Concentration.uniformProbability (fun a ↦ Q (d a)) =
      Concentration.uniformProbability Q := by
  classical
  have hden : (Fintype.card A : ℝ) = c * Fintype.card B := by
    simpa using sum_comp_eq_card_fiber_mul_sum d c hcard (fun _ ↦ (1 : ℝ))
  have hnum :
      (((Finset.univ : Finset A).filter fun a ↦ Q (d a)).card : ℝ) =
        c * (((Finset.univ : Finset B).filter Q).card : ℝ) := by
    simpa using sum_comp_eq_card_fiber_mul_sum d c hcard
      (fun b ↦ if Q b then (1 : ℝ) else 0)
  rw [Concentration.uniformProbability, Concentration.uniformProbability, hnum, hden]
  exact mul_div_mul_left _ _ (by exact_mod_cast hc.ne')

/-- The explicit permutation sampler has exactly the uniform law on one
signed slice. -/
lemma uniformExpectation_signedSliceDecode (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (g : SignedSlicePoint I plus minus → ℝ) :
    Concentration.uniformExpectation
        (fun σ ↦ g (signedSliceDecode I plus minus hcount e σ)) =
      Concentration.uniformExpectation g := by
  classical
  letI : Nonempty (SignedSlicePoint I plus minus) :=
    signedSlicePoint_nonempty hcount
  exact uniformExpectation_comp_of_card_fiber
    (signedSliceDecode I plus minus hcount e)
    (plus.factorial * minus.factorial *
      (I.card - plus - minus).factorial)
    (by positivity)
    (card_signedSliceDecode_fiber I plus minus hcount e) g

lemma uniformProbability_signedSliceDecode (I : Finset α) (plus minus : ℕ)
    (hcount : plus + minus ≤ I.card) (e : Fin I.card ≃ ↑I)
    (Q : SignedSlicePoint I plus minus → Prop) :
    Concentration.uniformProbability
        (fun σ ↦ Q (signedSliceDecode I plus minus hcount e σ)) =
      Concentration.uniformProbability Q := by
  classical
  letI : Nonempty (SignedSlicePoint I plus minus) :=
    signedSlicePoint_nonempty hcount
  exact uniformProbability_comp_of_card_fiber
    (signedSliceDecode I plus minus hcount e)
    (plus.factorial * minus.factorial *
      (I.card - plus - minus).factorial)
    (by positivity)
    (card_signedSliceDecode_fiber I plus minus hcount e) Q

/-- Exact uniform-law identification for the product sampler. -/
lemma uniformExpectation_productSignedSliceDecode [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (g : ProductSignedSlicePoint P plus minus → ℝ) :
    Concentration.uniformExpectation
        (fun σ ↦ g (productSignedSliceDecode P plus minus hcount e σ)) =
      Concentration.uniformExpectation g := by
  classical
  letI : Nonempty (ProductSignedSlicePoint P plus minus) :=
    productSignedSlicePoint_nonempty P plus minus hcount
  exact uniformExpectation_comp_of_card_fiber
    (productSignedSliceDecode P plus minus hcount e)
    (productSignedSliceFiberFactor P plus minus)
    (productSignedSliceFiberFactor_pos P plus minus)
    (card_productSignedSliceDecode_fiber P plus minus hcount e) g

lemma uniformProbability_productSignedSliceDecode [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (Q : ProductSignedSlicePoint P plus minus → Prop) :
    Concentration.uniformProbability
        (fun σ ↦ Q (productSignedSliceDecode P plus minus hcount e σ)) =
      Concentration.uniformProbability Q := by
  classical
  letI : Nonempty (ProductSignedSlicePoint P plus minus) :=
    productSignedSlicePoint_nonempty P plus minus hcount
  exact uniformProbability_comp_of_card_fiber
    (productSignedSliceDecode P plus minus hcount e)
    (productSignedSliceFiberFactor P plus minus)
    (productSignedSliceFiberFactor_pos P plus minus)
    (card_productSignedSliceDecode_fiber P plus minus hcount e) Q

end Slices
end BooleanSlices
end Erdos88

namespace Erdos88
namespace BooleanSlices


section KSSSConditions

variable {n m : ℕ}

/-- The real-power convention used in the quantitative statements of
KSSS Section 11.  Keeping the cast at one named definition prevents the
integer and real powers in the source estimates from being conflated. -/
noncomputable def scale (n : ℕ) (a : ℝ) : ℝ := Real.rpow (n : ℝ) a

lemma scale_nonneg (n : ℕ) (a : ℝ) : 0 ≤ scale n a :=
  Real.rpow_nonneg (Nat.cast_nonneg n) a

lemma scale_pos {n : ℕ} (hn : 0 < n) (a : ℝ) : 0 < scale n a := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma scale_mul {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    scale n a * scale n b = scale n (a + b) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (Real.rpow_add hnR a b).symm

lemma scale_sq {n : ℕ} (hn : 0 ≤ n) (a : ℝ) :
    scale n a ^ 2 = scale n (a * 2) := by
  unfold scale
  exact (Real.rpow_mul_natCast (x := (n : ℝ)) (by exact_mod_cast hn) a 2).symm

lemma scale_mono_exponent {n : ℕ} (hn : 1 ≤ n) {a b : ℝ} (hab : a ≤ b) :
    scale n a ≤ scale n b := by
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hab

/-- The equal-bucket and bucket-count hypotheses in KSSS Lemma 11.1. -/
def IsKSSSPartition (δ : ℝ) (P : BucketPartition (Fin n) (Fin m)) : Prop :=
  (∀ k h, (P.fiber k).card = (P.fiber h).card) ∧
    scale n δ / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * scale n δ

/-- A vector of prescribed slice sizes is in the near-balanced window from
KSSS Lemmas 11.1--11.3. -/
def IsNearBalanced (δ : ℝ) (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) : Prop :=
  ∀ k, |(ell k : ℝ) - ((P.fiber k).card : ℝ) / 2| ≤
    scale n ((1 - δ) / 2) * Real.log n

/-- Conditions (a)--(d) in KSSS Lemma 11.1, including both the row and
column conditions in every matrix block. -/
def HasKSSSBalancedCoefficients (δ : ℝ)
    (P : BucketPartition (Fin n) (Fin m)) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, F i j = F j i) ∧
    (∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ)) ∧
    (∀ i j, |F i j| ≤ 1) ∧
    (∀ k, ∑ i ∈ P.fiber k, f i = 0) ∧
    (∀ k h i, i ∈ P.fiber k → ∑ j ∈ P.fiber h, F i j = 0) ∧
    (∀ k h j, j ∈ P.fiber h → ∑ i ∈ P.fiber k, F i j = 0)

end KSSSConditions

section QuadraticPolynomial

variable {n : ℕ}

def linearPart (f x : Fin n → ℝ) : ℝ := ∑ i, f i * x i

/-- Full ordered-double-sum convention `xᵀFx`. -/
def quadraticPart (F : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * F i j * x j

def quadraticPolynomial (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  f₀ + linearPart f x + quadraticPart F x

def trace (F : Fin n → Fin n → ℝ) : ℝ := ∑ i, F i i
def vectorSqNorm (f : Fin n → ℝ) : ℝ := ∑ i, f i ^ 2
def frobeniusSq (F : Fin n → Fin n → ℝ) : ℝ := ∑ i, ∑ j, F i j ^ 2

lemma vectorSqNorm_le (f : Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) : vectorSqNorm f ≤ n * B ^ 2 := by
  calc
    vectorSqNorm f ≤ ∑ _i : Fin n, B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (f i)) hB).2 (hf i)
    _ = n * B ^ 2 := by simp

lemma frobeniusSq_le (F : Fin n → Fin n → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hF : ∀ i j, |F i j| ≤ A) : frobeniusSq F ≤ n ^ 2 * A ^ 2 := by
  calc
    frobeniusSq F ≤ ∑ _i : Fin n, ∑ _j : Fin n, A ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (F i j)) hA).2 (hF i j)
    _ = n ^ 2 * A ^ 2 := by simp; ring

/-- Coarse but exponent-sharp bound for the Gaussian variance target in
KSSS Lemma 11.1. -/
lemma gaussianVarianceTarget_le_ksss (δ : ℝ) (hδ : 0 ≤ δ) (hn : 1 ≤ n)
    (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1) :
    2 * frobeniusSq F + vectorSqNorm f ≤ 3 * scale n (2 + 6 * δ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := zero_le_one.trans hnR
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hBsq : scale n (1 / 2 + 3 * δ) ^ 2 = scale n (1 + 6 * δ) := by
    unfold scale
    calc
      ((n : ℝ) ^ (1 / 2 + 3 * δ)) ^ 2 =
          (n : ℝ) ^ ((1 / 2 + 3 * δ) * 2) :=
        (Real.rpow_mul_natCast hn0 (1 / 2 + 3 * δ) 2).symm
      _ = (n : ℝ) ^ (1 + 6 * δ) := by congr 1 <;> ring
  have hmul : (n : ℝ) * scale n (1 + 6 * δ) = scale n (2 + 6 * δ) := by
    unfold scale
    calc
      (n : ℝ) * (n : ℝ) ^ (1 + 6 * δ) =
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 + 6 * δ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ (1 + (1 + 6 * δ)) :=
        (Real.rpow_add hnpos _ _).symm
      _ = (n : ℝ) ^ (2 + 6 * δ) := by congr 1 <;> ring
  have hnpow : (n : ℝ) ^ 2 ≤ scale n (2 + 6 * δ) := by
    unfold scale
    calc
      (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) :=
        (Real.rpow_natCast (n : ℝ) 2).symm
      _ ≤ (n : ℝ) ^ (2 + 6 * δ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have hFrob : frobeniusSq F ≤ scale n (2 + 6 * δ) := by
    exact (frobeniusSq_le F 1 (by norm_num) hF).trans (by simpa using hnpow)
  have hfNorm : vectorSqNorm f ≤ scale n (2 + 6 * δ) := by
    calc
      vectorSqNorm f ≤ n * scale n (1 / 2 + 3 * δ) ^ 2 :=
        vectorSqNorm_le f (scale n (1 / 2 + 3 * δ))
          (scale_nonneg n (1 / 2 + 3 * δ)) hf
      _ = scale n (2 + 6 * δ) := by rw [hBsq, hmul]
  linarith

@[simp] lemma linearPart_zero (x : Fin n → ℝ) : linearPart 0 x = 0 := by simp [linearPart]
@[simp] lemma quadraticPart_zero (x : Fin n → ℝ) : quadraticPart 0 x = 0 := by
  simp [quadraticPart]

lemma quadraticPart_diag_sign (F : Fin n → Fin n → ℝ) (S : Finset (Fin n)) :
    ∑ i, F i i * signOfSet S i ^ 2 = trace F := by simp [trace]

/-- Pointwise perturbation identity used by both slice couplings. -/
lemma quadraticPolynomial_sub (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) :
    quadraticPolynomial f₀ f F x - quadraticPolynomial f₀ f F y =
      ∑ i, f i * (x i - y i) +
        ∑ i, ∑ j, F i j * (x i * x j - y i * y j) := by
  have hlin : (∑ i, f i * (x i - y i)) = linearPart f x - linearPart f y := by
    rw [linearPart, linearPart, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hquad : (∑ i, ∑ j, F i j * (x i * x j - y i * y j)) =
      quadraticPart F x - quadraticPart F y := by
    rw [quadraticPart, quadraticPart, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hlin, hquad]
  simp only [quadraticPolynomial]
  ring

/-- The quadratic random variable on the positive-coordinate-set encoding
of a product of Boolean slices. -/
def sliceQuadratic (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  quadraticPolynomial f₀ f F (signOfSet S)

/-- The KSSS quadratic polynomial as a random variable on the explicit
finite uniform product-slice sample space. -/
def productSliceQuadratic {m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (S : ProductSlicePoint P ell) : ℝ :=
  sliceQuadratic f₀ f F S.1

/-- The independent-Rademacher analogue used in KSSS Lemmas 11.3 and
11.6, on the concrete uniform Boolean-cube sample space. -/
def rademacherQuadratic (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (ξ : Fin n → Bool) : ℝ :=
  quadraticPolynomial f₀ f F (fun i ↦ if ξ i = true then 1 else -1)

/-- Deterministic range bound for the difference of two sign evaluations.
It controls the exceptional event when the high-probability coupling fails. -/
lemma abs_sliceQuadratic_sub_le (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A)
    (S T : Finset (Fin n)) :
    |sliceQuadratic f₀ f F S - sliceQuadratic f₀ f F T| ≤
      2 * n * B + 2 * n ^ 2 * A := by
  rw [sliceQuadratic, sliceQuadratic,
    quadraticPolynomial_sub]
  have hsign (i : Fin n) :
      |signOfSet S i - signOfSet T i| ≤ 2 := by
    calc
      |signOfSet S i - signOfSet T i| ≤
          |signOfSet S i| + |signOfSet T i| := abs_sub _ _
      _ = 2 := by rw [abs_signOfSet, abs_signOfSet]; norm_num
  have hprod (i j : Fin n) :
      |signOfSet S i * signOfSet S j -
          signOfSet T i * signOfSet T j| ≤ 2 := by
    calc
      |signOfSet S i * signOfSet S j -
          signOfSet T i * signOfSet T j| ≤
          |signOfSet S i * signOfSet S j| +
            |signOfSet T i * signOfSet T j| := abs_sub _ _
      _ = 2 := by norm_num [abs_mul, abs_signOfSet]
  calc
    |(∑ i, f i * (signOfSet S i - signOfSet T i)) +
        ∑ i, ∑ j, F i j *
          (signOfSet S i * signOfSet S j - signOfSet T i * signOfSet T j)| ≤
        |∑ i, f i * (signOfSet S i - signOfSet T i)| +
          |∑ i, ∑ j, F i j *
            (signOfSet S i * signOfSet S j - signOfSet T i * signOfSet T j)| :=
      abs_add_le _ _
    _ ≤ (∑ _i : Fin n, 2 * B) +
        ∑ _i : Fin n, ∑ _j : Fin n, 2 * A := by
      gcongr
      · calc
          |∑ i, f i * (signOfSet S i - signOfSet T i)| ≤
              ∑ i, |f i * (signOfSet S i - signOfSet T i)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, 2 * B := by
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul]
            nlinarith only [mul_le_mul (hf i) (hsign i)
              (abs_nonneg _) hB]
      · calc
          |∑ i, ∑ j, F i j *
              (signOfSet S i * signOfSet S j -
                signOfSet T i * signOfSet T j)| ≤
              ∑ i, |∑ j, F i j *
                (signOfSet S i * signOfSet S j -
                  signOfSet T i * signOfSet T j)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, 2 * A := by
            apply Finset.sum_le_sum
            intro i _
            calc
              |∑ j, F i j *
                  (signOfSet S i * signOfSet S j -
                    signOfSet T i * signOfSet T j)| ≤
                  ∑ j, |F i j *
                    (signOfSet S i * signOfSet S j -
                      signOfSet T i * signOfSet T j)| :=
                Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ _j : Fin n, 2 * A := by
                apply Finset.sum_le_sum
                intro j _
                rw [abs_mul]
                nlinarith only [mul_le_mul (hF i j) (hprod i j)
                  (abs_nonneg _) hA]
    _ = 2 * n * B + 2 * n ^ 2 * A := by simp; ring

end QuadraticPolynomial

end BooleanSlices
end Erdos88

namespace Erdos88
namespace BooleanSlices

section TwoStageSliceCoupling

variable {α : Type u} {κ : Type v} [Fintype α] [DecidableEq α]

/-- A Boolean slice is inhabited exactly in the range in which its prescribed
cardinality fits in the ambient set.  This packaged form is convenient for
the dependent two-stage sampler below. -/
lemma booleanSlicePoint_nonempty {I : Finset α} {ell : ℕ}
    (hell : ell ≤ I.card) : Nonempty (BooleanSlicePoint I ell) := by
  obtain ⟨S, hS⟩ := booleanSlice_nonempty_iff.mpr hell
  exact ⟨⟨S, hS⟩⟩

/-- Relabel a Boolean slice along an embedding carrying its ambient finite
set to a new ambient finite set. -/
noncomputable def booleanSliceMap {I J : Finset α} {ell : ℕ}
    (ρ : α ↪ α) (hIJ : I.map ρ = J) (S : BooleanSlicePoint I ell) :
    BooleanSlicePoint J ell := by
  classical
  refine ⟨S.1.map ρ, mem_booleanSlice.mpr ⟨?_, ?_⟩⟩
  · intro x hx
    rw [← hIJ]
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr
      ⟨y, (mem_booleanSlice.mp S.2).1 hy, rfl⟩
  · rw [Finset.card_map]
    exact (mem_booleanSlice.mp S.2).2

/-- A permutation preserving an ambient finite set acts by an equivalence on
every Boolean slice over that set. -/
noncomputable def booleanSlicePermEquiv (I : Finset α) (ell : ℕ)
    (ρ : Equiv.Perm α) (hI : I.map ρ.toEmbedding = I) :
    BooleanSlicePoint I ell ≃ BooleanSlicePoint I ell := by
  classical
  have hIinv : I.map ρ.symm.toEmbedding = I := by
    calc
      I.map ρ.symm.toEmbedding =
          (I.map ρ.toEmbedding).map ρ.symm.toEmbedding := by rw [hI]
      _ = I := by
        rw [Finset.map_map]
        simpa using Finset.map_refl I
  exact {
    toFun := booleanSliceMap ρ.toEmbedding hI
    invFun := booleanSliceMap ρ.symm.toEmbedding hIinv
    left_inv := by
      intro S
      apply Subtype.ext
      simp [booleanSliceMap, Finset.map_map]
    right_inv := by
      intro S
      apply Subtype.ext
      simp [booleanSliceMap, Finset.map_map]
  }

/-- Relabeling by a permutation gives an equivalence between slices over
two ambient finite sets that the permutation carries to one another. -/
noncomputable def booleanSliceEquivOfPerm {I J : Finset α} (ell : ℕ)
    (ρ : Equiv.Perm α) (hIJ : I.map ρ.toEmbedding = J) :
    BooleanSlicePoint I ell ≃ BooleanSlicePoint J ell := by
  classical
  have hJI : J.map ρ.symm.toEmbedding = I := by
    calc
      J.map ρ.symm.toEmbedding =
          (I.map ρ.toEmbedding).map ρ.symm.toEmbedding := by rw [hIJ]
      _ = I := by
        rw [Finset.map_map]
        simpa using Finset.map_refl I
  exact {
    toFun := booleanSliceMap ρ.toEmbedding hIJ
    invFun := booleanSliceMap ρ.symm.toEmbedding hJI
    left_inv := by
      intro S
      apply Subtype.ext
      simp [booleanSliceMap, Finset.map_map]
    right_inv := by
      intro S
      apply Subtype.ext
      simp [booleanSliceMap, Finset.map_map]
  }

/-- One-bucket outcome in the coupling used in the proof of KSSS Lemma 11.2.
First an exceptional set `R` of size `r` is chosen.  Independently, the left
and right vectors choose `a` and `b` positive signs inside `R`, while the two
vectors use the same set of `h` positive signs on `I \ R`. -/
def TwoStageSlicePoint (I : Finset α) (r a b h : ℕ) : Type u :=
  Σ R : BooleanSlicePoint I r,
    BooleanSlicePoint R.1 a ×
      BooleanSlicePoint R.1 b × BooleanSlicePoint (I \ R.1) h

/-- A permutation preserving the ambient bucket relabels every stage of the
two-stage slice sampler.  The complement component is transported along the
same permutation, so this is an equivalence of the full dependent sample
space rather than just its first-stage slice. -/
noncomputable def twoStageSlicePermEquiv
    (I : Finset α) (r a b h : ℕ)
    (ρ : Equiv.Perm α) (hI : I.map ρ.toEmbedding = I) :
    TwoStageSlicePoint I r a b h ≃ TwoStageSlicePoint I r a b h := by
  classical
  let base : BooleanSlicePoint I r ≃ BooleanSlicePoint I r :=
    booleanSlicePermEquiv I r ρ hI
  refine Equiv.sigmaCongr base (fun R ↦ ?_)
  have hR : R.1.map ρ.toEmbedding = (base R).1 := by
    rfl
  have hcomp : (I \ R.1).map ρ.toEmbedding = I \ (base R).1 := by
    rw [Finset.map_sdiff, hI, hR]
  exact Equiv.prodCongr
    (booleanSliceEquivOfPerm a ρ hR)
    (Equiv.prodCongr
      (booleanSliceEquivOfPerm b ρ hR)
      (booleanSliceEquivOfPerm h ρ hcomp))

@[simp] lemma twoStageSlicePermEquiv_first_val
    (I : Finset α) (r a b h : ℕ)
    (ρ : Equiv.Perm α) (hI : I.map ρ.toEmbedding = I)
    (ω : TwoStageSlicePoint I r a b h) :
    (twoStageSlicePermEquiv I r a b h ρ hI ω).1.1 =
      ω.1.1.map ρ.toEmbedding := by
  rfl

@[simp] lemma twoStageSlicePermEquiv_left_val
    (I : Finset α) (r a b h : ℕ)
    (ρ : Equiv.Perm α) (hI : I.map ρ.toEmbedding = I)
    (ω : TwoStageSlicePoint I r a b h) :
    (twoStageSlicePermEquiv I r a b h ρ hI ω).2.1.1 =
      ω.2.1.1.map ρ.toEmbedding := by
  rfl

@[simp] lemma twoStageSlicePermEquiv_right_val
    (I : Finset α) (r a b h : ℕ)
    (ρ : Equiv.Perm α) (hI : I.map ρ.toEmbedding = I)
    (ω : TwoStageSlicePoint I r a b h) :
    (twoStageSlicePermEquiv I r a b h ρ hI ω).2.2.1.1 =
      ω.2.2.1.1.map ρ.toEmbedding := by
  rfl

@[simp] lemma twoStageSlicePermEquiv_shared_val
    (I : Finset α) (r a b h : ℕ)
    (ρ : Equiv.Perm α) (hI : I.map ρ.toEmbedding = I)
    (ω : TwoStageSlicePoint I r a b h) :
    (twoStageSlicePermEquiv I r a b h ρ hI ω).2.2.2.1 =
      ω.2.2.2.1.map ρ.toEmbedding := by
  rfl

@[simp] lemma booleanSlicePermEquiv_val
    (I : Finset α) (ell : ℕ)
    (ρ : Equiv.Perm α) (hI : I.map ρ.toEmbedding = I)
    (S : BooleanSlicePoint I ell) :
    (booleanSlicePermEquiv I ell ρ hI S).1 = S.1.map ρ.toEmbedding := by
  rfl

noncomputable instance (I : Finset α) (r a b h : ℕ) :
    Fintype (TwoStageSlicePoint I r a b h) := by
  classical
  let encode : TwoStageSlicePoint I r a b h →
      Finset α × Finset α × Finset α × Finset α :=
    fun ω ↦ (ω.1.1, ω.2.1.1, ω.2.2.1.1, ω.2.2.2.1)
  exact Fintype.ofInjective encode (by
    intro ω τ heq
    have hR := congrArg (fun z ↦ z.1) heq
    have hA := congrArg (fun z ↦ z.2.1) heq
    have hB := congrArg (fun z ↦ z.2.2.1) heq
    have hC := congrArg (fun z ↦ z.2.2.2) heq
    cases ω with
    | mk R data =>
      cases τ with
      | mk R' data' =>
        have hR' : R = R' := Subtype.ext hR
        subst R'
        rcases data with ⟨A, B, C⟩
        rcases data' with ⟨A', B', C'⟩
        have hA' : A = A' := Subtype.ext hA
        have hB' : B = B' := Subtype.ext hB
        have hC' : C = C' := Subtype.ext hC
        subst A'
        subst B'
        subst C'
        rfl)

lemma twoStageSlicePoint_nonempty (I : Finset α) (r a b h : ℕ)
    (hr : r ≤ I.card) (ha : a ≤ r) (hb : b ≤ r)
    (hh : h ≤ I.card - r) : Nonempty (TwoStageSlicePoint I r a b h) := by
  let R : BooleanSlicePoint I r :=
    Classical.choice (booleanSlicePoint_nonempty hr)
  have hRI : R.1 ⊆ I := (mem_booleanSlice.mp R.2).1
  have hRcard : R.1.card = r := (mem_booleanSlice.mp R.2).2
  have haR : a ≤ R.1.card := by simpa [hRcard] using ha
  have hbR : b ≤ R.1.card := by simpa [hRcard] using hb
  have hcomp : (I \ R.1).card = I.card - r := by
    rw [Finset.card_sdiff_of_subset hRI, hRcard]
  have hhcomp : h ≤ (I \ R.1).card := by simpa [hcomp] using hh
  let A : BooleanSlicePoint R.1 a :=
    Classical.choice (booleanSlicePoint_nonempty haR)
  let B : BooleanSlicePoint R.1 b :=
    Classical.choice (booleanSlicePoint_nonempty hbR)
  let C : BooleanSlicePoint (I \ R.1) h :=
    Classical.choice (booleanSlicePoint_nonempty hhcomp)
  exact ⟨⟨R, A, B, C⟩⟩

/-- The left Boolean-slice point produced by a one-bucket two-stage outcome. -/
def twoStageSliceLeft (I : Finset α) (r a b h : ℕ)
    (ω : TwoStageSlicePoint I r a b h) : BooleanSlicePoint I (a + h) := by
  let R : Finset α := ω.1.1
  let A : Finset α := ω.2.1.1
  let C : Finset α := ω.2.2.2.1
  have hR : R ⊆ I ∧ R.card = r := mem_booleanSlice.mp ω.1.2
  have hA : A ⊆ R ∧ A.card = a := mem_booleanSlice.mp ω.2.1.2
  have hC : C ⊆ I \ R ∧ C.card = h := mem_booleanSlice.mp ω.2.2.2.2
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro i hiA hiC
    exact (Finset.mem_sdiff.mp (hC.1 hiC)).2 (hA.1 hiA)
  exact ⟨A ∪ C, mem_booleanSlice.mpr ⟨
    Finset.union_subset (hA.1.trans hR.1)
      (hC.1.trans Finset.sdiff_subset),
    by rw [Finset.card_union_of_disjoint hAC, hA.2, hC.2]⟩⟩

/-- The right Boolean-slice point produced by a one-bucket two-stage outcome. -/
def twoStageSliceRight (I : Finset α) (r a b h : ℕ)
    (ω : TwoStageSlicePoint I r a b h) : BooleanSlicePoint I (b + h) := by
  let R : Finset α := ω.1.1
  let B : Finset α := ω.2.2.1.1
  let C : Finset α := ω.2.2.2.1
  have hR : R ⊆ I ∧ R.card = r := mem_booleanSlice.mp ω.1.2
  have hB : B ⊆ R ∧ B.card = b := mem_booleanSlice.mp ω.2.2.1.2
  have hC : C ⊆ I \ R ∧ C.card = h := mem_booleanSlice.mp ω.2.2.2.2
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro i hiB hiC
    exact (Finset.mem_sdiff.mp (hC.1 hiC)).2 (hB.1 hiB)
  exact ⟨B ∪ C, mem_booleanSlice.mpr ⟨
    Finset.union_subset (hB.1.trans hR.1)
      (hC.1.trans Finset.sdiff_subset),
    by rw [Finset.card_union_of_disjoint hBC, hB.2, hC.2]⟩⟩

/-- Relabeling the two-stage sample relabels its left marginal. -/
lemma twoStageSliceLeft_permEquiv
    (I : Finset α) (r a b h : ℕ)
    (ρ : Equiv.Perm α) (hI : I.map ρ.toEmbedding = I)
    (ω : TwoStageSlicePoint I r a b h) :
    twoStageSliceLeft I r a b h (twoStageSlicePermEquiv I r a b h ρ hI ω) =
      booleanSlicePermEquiv I (a + h) ρ hI
        (twoStageSliceLeft I r a b h ω) := by
  classical
  apply Subtype.ext
  change
    (twoStageSlicePermEquiv I r a b h ρ hI ω).2.1.1 ∪
        (twoStageSlicePermEquiv I r a b h ρ hI ω).2.2.2.1 =
      (booleanSlicePermEquiv I (a + h) ρ hI
        (twoStageSliceLeft I r a b h ω)).1
  rw [twoStageSlicePermEquiv_left_val,
    twoStageSlicePermEquiv_shared_val, booleanSlicePermEquiv_val]
  change ω.2.1.1.map ρ.toEmbedding ∪
      ω.2.2.2.1.map ρ.toEmbedding =
    (ω.2.1.1 ∪ ω.2.2.2.1).map ρ.toEmbedding
  rw [Finset.map_union]

/-- Relabeling the two-stage sample relabels its right marginal. -/
lemma twoStageSliceRight_permEquiv
    (I : Finset α) (r a b h : ℕ)
    (ρ : Equiv.Perm α) (hI : I.map ρ.toEmbedding = I)
    (ω : TwoStageSlicePoint I r a b h) :
    twoStageSliceRight I r a b h (twoStageSlicePermEquiv I r a b h ρ hI ω) =
      booleanSlicePermEquiv I (b + h) ρ hI
        (twoStageSliceRight I r a b h ω) := by
  classical
  apply Subtype.ext
  change
    (twoStageSlicePermEquiv I r a b h ρ hI ω).2.2.1.1 ∪
        (twoStageSlicePermEquiv I r a b h ρ hI ω).2.2.2.1 =
      (booleanSlicePermEquiv I (b + h) ρ hI
        (twoStageSliceRight I r a b h ω)).1
  rw [twoStageSlicePermEquiv_right_val,
    twoStageSlicePermEquiv_shared_val, booleanSlicePermEquiv_val]
  change ω.2.2.1.1.map ρ.toEmbedding ∪
      ω.2.2.2.1.map ρ.toEmbedding =
    (ω.2.2.1.1 ∪ ω.2.2.2.1).map ρ.toEmbedding
  rw [Finset.map_union]

/-- Any two points in the same Boolean slice are related by a permutation
that preserves the ambient finite set. -/
lemma exists_perm_preserving_map_booleanSlice
    (I : Finset α) (ell : ℕ)
    (S T : BooleanSlicePoint I ell) :
    ∃ (ρ : Equiv.Perm α) (hI : I.map ρ.toEmbedding = I),
      booleanSlicePermEquiv I ell ρ hI S = T := by
  classical
  have hSI : S.1 ⊆ I := (mem_booleanSlice.mp S.2).1
  have hTI : T.1 ⊆ I := (mem_booleanSlice.mp T.2).1
  have hScard : S.1.card = ell := (mem_booleanSlice.mp S.2).2
  have hTcard : T.1.card = ell := (mem_booleanSlice.mp T.2).2
  have hcompCard : (I \ S.1).card = (I \ T.1).card := by
    rw [Finset.card_sdiff_of_subset hSI, Finset.card_sdiff_of_subset hTI,
      hScard, hTcard]
  obtain ⟨ρ, hST, hcomp⟩ := exists_perm_map_disjoint_pair
    S.1 (I \ S.1) T.1 (I \ T.1)
    Finset.disjoint_sdiff Finset.disjoint_sdiff
    (hScard.trans hTcard.symm) hcompCard
  have hI : I.map ρ.toEmbedding = I := by
    calc
      I.map ρ.toEmbedding = (S.1 ∪ (I \ S.1)).map ρ.toEmbedding := by
        rw [Finset.union_sdiff_of_subset hSI]
      _ = S.1.map ρ.toEmbedding ∪ (I \ S.1).map ρ.toEmbedding := by
        rw [Finset.map_union]
      _ = T.1 ∪ (I \ T.1) := by rw [hST, hcomp]
      _ = I := Finset.union_sdiff_of_subset hTI
  refine ⟨ρ, hI, ?_⟩
  apply Subtype.ext
  exact hST

/-- All fibers of the left marginal of a two-stage bucket have equal finite
cardinality. -/
lemma card_twoStageSliceLeft_fiber_eq
    (I : Finset α) (r a b h : ℕ)
    (S T : BooleanSlicePoint I (a + h)) :
    Nat.card {ω : TwoStageSlicePoint I r a b h //
        twoStageSliceLeft I r a b h ω = S} =
      Nat.card {ω : TwoStageSlicePoint I r a b h //
        twoStageSliceLeft I r a b h ω = T} := by
  classical
  obtain ⟨ρ, hI, hST⟩ :=
    exists_perm_preserving_map_booleanSlice I (a + h) S T
  let e := twoStageSlicePermEquiv I r a b h ρ hI
  let p := booleanSlicePermEquiv I (a + h) ρ hI
  let E : {ω : TwoStageSlicePoint I r a b h //
        twoStageSliceLeft I r a b h ω = S} ≃
      {ω : TwoStageSlicePoint I r a b h //
        twoStageSliceLeft I r a b h ω = T} := {
    toFun := fun ω ↦ ⟨e ω.1, by
      calc
        twoStageSliceLeft I r a b h (e ω.1) =
            p (twoStageSliceLeft I r a b h ω.1) := by
              exact twoStageSliceLeft_permEquiv I r a b h ρ hI ω.1
        _ = p S := congrArg p ω.2
        _ = T := hST⟩
    invFun := fun τ ↦ ⟨e.symm τ.1, by
      apply p.injective
      calc
        p (twoStageSliceLeft I r a b h (e.symm τ.1)) =
            twoStageSliceLeft I r a b h (e (e.symm τ.1)) := by
              exact (twoStageSliceLeft_permEquiv I r a b h ρ hI
                (e.symm τ.1)).symm
        _ = T := by rw [e.apply_symm_apply, τ.2]
        _ = p S := hST.symm⟩
    left_inv := by
      intro ω
      apply Subtype.ext
      exact e.symm_apply_apply ω.1
    right_inv := by
      intro τ
      apply Subtype.ext
      exact e.apply_symm_apply τ.1
  }
  exact Nat.card_congr E

/-- All fibers of the right marginal of a two-stage bucket have equal finite
cardinality. -/
lemma card_twoStageSliceRight_fiber_eq
    (I : Finset α) (r a b h : ℕ)
    (S T : BooleanSlicePoint I (b + h)) :
    Nat.card {ω : TwoStageSlicePoint I r a b h //
        twoStageSliceRight I r a b h ω = S} =
      Nat.card {ω : TwoStageSlicePoint I r a b h //
        twoStageSliceRight I r a b h ω = T} := by
  classical
  obtain ⟨ρ, hI, hST⟩ :=
    exists_perm_preserving_map_booleanSlice I (b + h) S T
  let e := twoStageSlicePermEquiv I r a b h ρ hI
  let p := booleanSlicePermEquiv I (b + h) ρ hI
  let E : {ω : TwoStageSlicePoint I r a b h //
        twoStageSliceRight I r a b h ω = S} ≃
      {ω : TwoStageSlicePoint I r a b h //
        twoStageSliceRight I r a b h ω = T} := {
    toFun := fun ω ↦ ⟨e ω.1, by
      calc
        twoStageSliceRight I r a b h (e ω.1) =
            p (twoStageSliceRight I r a b h ω.1) := by
              exact twoStageSliceRight_permEquiv I r a b h ρ hI ω.1
        _ = p S := congrArg p ω.2
        _ = T := hST⟩
    invFun := fun τ ↦ ⟨e.symm τ.1, by
      apply p.injective
      calc
        p (twoStageSliceRight I r a b h (e.symm τ.1)) =
            twoStageSliceRight I r a b h (e (e.symm τ.1)) := by
              exact (twoStageSliceRight_permEquiv I r a b h ρ hI
                (e.symm τ.1)).symm
        _ = T := by rw [e.apply_symm_apply, τ.2]
        _ = p S := hST.symm⟩
    left_inv := by
      intro ω
      apply Subtype.ext
      exact e.symm_apply_apply ω.1
    right_inv := by
      intro τ
      apply Subtype.ext
      exact e.apply_symm_apply τ.1
  }
  exact Nat.card_congr E

/-- The product of the one-bucket two-stage sample spaces.  Its uniform law
is exactly the independent sampling procedure in the proof of Lemma 11.2. -/
def ProductTwoStageSlicePoint [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ) : Type (max u v) :=
  ∀ k, TwoStageSlicePoint (P.fiber k) (r k) (a k) (b k) (h k)

noncomputable instance [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ) :
    Fintype (ProductTwoStageSlicePoint P r a b h) := by
  classical
  unfold ProductTwoStageSlicePoint
  infer_instance

lemma productTwoStageSlicePoint_nonempty [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k) :
    Nonempty (ProductTwoStageSlicePoint P r a b h) := by
  exact ⟨fun k ↦ Classical.choice
    (twoStageSlicePoint_nonempty (P.fiber k) (r k) (a k) (b k) (h k)
      (hr k) (ha k) (hb k) (hh k))⟩

/-- Left marginal of the product two-stage sampler. -/
noncomputable def productTwoStageSliceLeft [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h) :
    ProductSlicePoint P (fun k ↦ a k + h k) :=
  (productSliceEquiv P (fun k ↦ a k + h k)).symm
    (fun k ↦ twoStageSliceLeft (P.fiber k) (r k) (a k) (b k) (h k) (ω k))

/-- Right marginal of the product two-stage sampler. -/
noncomputable def productTwoStageSliceRight [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h) :
    ProductSlicePoint P (fun k ↦ b k + h k) :=
  (productSliceEquiv P (fun k ↦ b k + h k)).symm
    (fun k ↦ twoStageSliceRight (P.fiber k) (r k) (a k) (b k) (h k) (ω k))

/-- A fiber of the left product marginal is the dependent product of its
one-bucket fibers. -/
noncomputable def productTwoStageSliceLeftFiberEquiv
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (S : ProductSlicePoint P (fun k ↦ a k + h k)) :
    {ω : ProductTwoStageSlicePoint P r a b h //
      productTwoStageSliceLeft P r a b h ω = S} ≃
      ∀ k, {τ : TwoStageSlicePoint (P.fiber k)
          (r k) (a k) (b k) (h k) //
        twoStageSliceLeft (P.fiber k) (r k) (a k) (b k) (h k) τ =
          productSliceEquiv P (fun j ↦ a j + h j) S k} where
  toFun ω k := ⟨ω.1 k, by
    have hk := congrArg
      (fun T : ProductSlicePoint P (fun j ↦ a j + h j) ↦
        productSliceEquiv P (fun j ↦ a j + h j) T k) ω.2
    simpa [productTwoStageSliceLeft] using hk⟩
  invFun τ := ⟨fun k ↦ (τ k).1, by
    apply (productSliceEquiv P (fun j ↦ a j + h j)).injective
    funext k
    simpa [productTwoStageSliceLeft] using (τ k).2⟩
  left_inv ω := by
    apply Subtype.ext
    funext k
    rfl
  right_inv τ := by
    funext k
    apply Subtype.ext
    rfl

/-- A fiber of the right product marginal is the dependent product of its
one-bucket fibers. -/
noncomputable def productTwoStageSliceRightFiberEquiv
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (S : ProductSlicePoint P (fun k ↦ b k + h k)) :
    {ω : ProductTwoStageSlicePoint P r a b h //
      productTwoStageSliceRight P r a b h ω = S} ≃
      ∀ k, {τ : TwoStageSlicePoint (P.fiber k)
          (r k) (a k) (b k) (h k) //
        twoStageSliceRight (P.fiber k) (r k) (a k) (b k) (h k) τ =
          productSliceEquiv P (fun j ↦ b j + h j) S k} where
  toFun ω k := ⟨ω.1 k, by
    have hk := congrArg
      (fun T : ProductSlicePoint P (fun j ↦ b j + h j) ↦
        productSliceEquiv P (fun j ↦ b j + h j) T k) ω.2
    simpa [productTwoStageSliceRight] using hk⟩
  invFun τ := ⟨fun k ↦ (τ k).1, by
    apply (productSliceEquiv P (fun j ↦ b j + h j)).injective
    funext k
    simpa [productTwoStageSliceRight] using (τ k).2⟩
  left_inv ω := by
    apply Subtype.ext
    funext k
    rfl
  right_inv τ := by
    funext k
    apply Subtype.ext
    rfl

/-- All fibers of the left product marginal have equal cardinality. -/
lemma card_productTwoStageSliceLeft_fiber_eq
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (S T : ProductSlicePoint P (fun k ↦ a k + h k)) :
    Nat.card {ω : ProductTwoStageSlicePoint P r a b h //
        productTwoStageSliceLeft P r a b h ω = S} =
      Nat.card {ω : ProductTwoStageSlicePoint P r a b h //
        productTwoStageSliceLeft P r a b h ω = T} := by
  rw [Nat.card_congr (productTwoStageSliceLeftFiberEquiv P r a b h S),
    Nat.card_congr (productTwoStageSliceLeftFiberEquiv P r a b h T),
    Nat.card_pi, Nat.card_pi]
  apply Finset.prod_congr rfl
  intro k _
  exact card_twoStageSliceLeft_fiber_eq
    (P.fiber k) (r k) (a k) (b k) (h k)
      (productSliceEquiv P (fun j ↦ a j + h j) S k)
      (productSliceEquiv P (fun j ↦ a j + h j) T k)

/-- All fibers of the right product marginal have equal cardinality. -/
lemma card_productTwoStageSliceRight_fiber_eq
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (S T : ProductSlicePoint P (fun k ↦ b k + h k)) :
    Nat.card {ω : ProductTwoStageSlicePoint P r a b h //
        productTwoStageSliceRight P r a b h ω = S} =
      Nat.card {ω : ProductTwoStageSlicePoint P r a b h //
        productTwoStageSliceRight P r a b h ω = T} := by
  rw [Nat.card_congr (productTwoStageSliceRightFiberEquiv P r a b h S),
    Nat.card_congr (productTwoStageSliceRightFiberEquiv P r a b h T),
    Nat.card_pi, Nat.card_pi]
  apply Finset.prod_congr rfl
  intro k _
  exact card_twoStageSliceRight_fiber_eq
    (P.fiber k) (r k) (a k) (b k) (h k)
      (productSliceEquiv P (fun j ↦ b j + h j) S k)
      (productSliceEquiv P (fun j ↦ b j + h j) T k)

/-- A signed slice with no negative coordinates is exactly a Boolean slice. -/
noncomputable def signedSliceZeroEquiv (I : Finset α) (ell : ℕ) :
    SignedSlicePoint I ell 0 ≃ BooleanSlicePoint I ell where
  toFun S := ⟨S.1.1, mem_booleanSlice.mpr ⟨
    (mem_signedSlice.mp S.2).1,
    (mem_signedSlice.mp S.2).2.2.2.1⟩⟩
  invFun S := ⟨(S.1, ∅), mem_signedSlice.mpr ⟨
    (mem_booleanSlice.mp S.2).1, Finset.empty_subset I,
    Finset.disjoint_empty_right S.1, (mem_booleanSlice.mp S.2).2, rfl⟩⟩
  left_inv S := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (Finset.card_eq_zero.mp (mem_signedSlice.mp S.2).2.2.2.2).symm
  right_inv S := by
    apply Subtype.ext
    rfl

/-- Coordinatewise zero-negative equivalence, followed by reassembly of the
bucket restrictions into a global product-slice point. -/
noncomputable def productSignedSliceZeroEquiv [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ) :
    ProductSignedSlicePoint P ell (fun _ ↦ 0) ≃ ProductSlicePoint P ell :=
  (Equiv.piCongrRight fun k ↦ signedSliceZeroEquiv (P.fiber k) (ell k)).trans
    (productSliceEquiv P ell).symm

/-- The standard independent-permutation sampler for a product of Boolean
slices, obtained from the already verified signed-slice decoder. -/
noncomputable def productSlicePermutationDecode [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (σ : ProductSignedSliceSampler P) : ProductSlicePoint P ell :=
  productSignedSliceZeroEquiv P ell
    (productSignedSliceDecode P ell (fun _ ↦ 0)
      (fun k ↦ by simpa using hell k) e σ)

/-- The product permutation decoder has exactly the uniform product-slice
law.  This is the marginal certificate used for each side of the coupling. -/
lemma uniformExpectation_productSlicePermutationDecode
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (g : ProductSlicePoint P ell → ℝ) :
    Concentration.uniformExpectation (fun σ ↦
        g (productSlicePermutationDecode P ell hell e σ)) =
      Concentration.uniformExpectation g := by
  let E := productSignedSliceZeroEquiv P ell
  have hdecode := uniformExpectation_productSignedSliceDecode P ell
    (fun _ ↦ 0) (fun k ↦ by simpa using hell k) e (fun S ↦ g (E S))
  calc
    Concentration.uniformExpectation (fun σ ↦
        g (productSlicePermutationDecode P ell hell e σ)) =
        Concentration.uniformExpectation (fun S ↦ g (E S)) := by
      simpa only [productSlicePermutationDecode, E] using hdecode
    _ = Concentration.uniformExpectation g := by
      unfold Concentration.uniformExpectation
      rw [Fintype.card_congr E]
      congr 1
      exact E.sum_comp g

/-- Event probabilities are likewise transported exactly by the Boolean
product-slice permutation decoder. -/
lemma uniformProbability_productSlicePermutationDecode
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (Q : ProductSlicePoint P ell → Prop) :
    Concentration.uniformProbability (fun σ ↦
        Q (productSlicePermutationDecode P ell hell e σ)) =
      Concentration.uniformProbability Q := by
  classical
  have hmean := uniformExpectation_productSlicePermutationDecode
    P ell hell e (fun T ↦ if Q T then (1 : ℝ) else 0)
  simpa [Concentration.uniformProbability, Concentration.uniformExpectation,
    Finset.sum_ite] using hmean

/-- Complex-valued version of the constant-fiber counting identity. -/
lemma sum_comp_eq_card_fiber_mul_sum_complex {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B]
    (d : A → B) (c : ℕ)
    (hcard : ∀ b, Nat.card {a : A // d a = b} = c)
    (g : B → ℂ) :
    ∑ a, g (d a) = (c : ℂ) * ∑ b, g b := by
  classical
  calc
    ∑ a, g (d a) =
        ∑ b : B, ∑ a ∈ (Finset.univ : Finset A) with d a = b, g b :=
      (Finset.sum_fiberwise' Finset.univ d g).symm
    _ = ∑ b : B, (c : ℂ) * g b := by
      apply Finset.sum_congr rfl
      intro b _
      have hfilter :
          ((Finset.univ : Finset A).filter fun a ↦ d a = b).card = c := by
        rw [← hcard b, Nat.card_eq_fintype_card]
        simp [Fintype.card_subtype]
      simp [hfilter]
    _ = (c : ℂ) * ∑ b : B, g b := by rw [Finset.mul_sum]

/-- A positive constant-fiber map preserves finite uniform expectations of
complex-valued tests. -/
lemma complexExpectation_comp_of_card_fiber {A B : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] [DecidableEq B]
    (d : A → B) (c : ℕ) (hc : 0 < c)
    (hcard : ∀ b, Nat.card {a : A // d a = b} = c)
    (g : B → ℂ) :
    (𝔼 a, g (d a)) = 𝔼 b, g b := by
  have hsum := sum_comp_eq_card_fiber_mul_sum_complex d c hcard g
  have hden : (Fintype.card A : ℂ) = c * Fintype.card B := by
    exact_mod_cast (show Fintype.card A = c * Fintype.card B by
      exact_mod_cast (show (Fintype.card A : ℝ) = c * Fintype.card B by
        simpa using sum_comp_eq_card_fiber_mul_sum d c hcard
          (fun _ ↦ (1 : ℝ))))
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card,
    hsum, hden]
  exact mul_div_mul_left _ _ (by exact_mod_cast hc.ne')

/-- The Boolean product-slice permutation decoder preserves all
complex-valued test expectations, the exact marginal condition used by
`FiniteUniformCoupling`. -/
lemma complexExpectation_productSlicePermutationDecode
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (g : ProductSlicePoint P ell → ℂ) :
    (𝔼 σ, g (productSlicePermutationDecode P ell hell e σ)) =
      𝔼 S, g S := by
  classical
  let E := productSignedSliceZeroEquiv P ell
  let hcount : ∀ k, ell k + 0 ≤ (P.fiber k).card :=
    fun k ↦ by simpa using hell k
  let d := productSignedSliceDecode P ell (fun _ ↦ 0) hcount e
  have hdecode : (𝔼 σ, (g ∘ E) (d σ)) = 𝔼 S, (g ∘ E) S := by
    letI : Nonempty (ProductSignedSlicePoint P ell (fun _ ↦ 0)) :=
      productSignedSlicePoint_nonempty P ell (fun _ ↦ 0) hcount
    exact complexExpectation_comp_of_card_fiber d
      (productSignedSliceFiberFactor P ell (fun _ ↦ 0))
      (productSignedSliceFiberFactor_pos P ell (fun _ ↦ 0))
      (card_productSignedSliceDecode_fiber P ell (fun _ ↦ 0) hcount e) (g ∘ E)
  calc
    (𝔼 σ, g (productSlicePermutationDecode P ell hell e σ)) =
        𝔼 σ, (g ∘ E) (d σ) := by rfl
    _ = 𝔼 S, (g ∘ E) S := hdecode
    _ = 𝔼 T, g T := by
      apply Fintype.expect_equiv E
      intro S
      rfl

/-- If all fibers of a map from a nonempty finite type have the same
cardinality, that common cardinality is positive. -/
lemma exists_positive_common_fiber {A B : Type*}
    [Fintype A] [Nonempty A] [Fintype B]
    (d : A → B)
    (heq : ∀ x y, Nat.card {a : A // d a = x} =
      Nat.card {a : A // d a = y}) :
    ∃ c : ℕ, 0 < c ∧ ∀ y, Nat.card {a : A // d a = y} = c := by
  classical
  let a₀ : A := Classical.choice (inferInstance : Nonempty A)
  let b₀ : B := d a₀
  let c : ℕ := Nat.card {a : A // d a = b₀}
  have hc : 0 < c := by
    dsimp only [c]
    rw [Nat.card_eq_fintype_card]
    letI : Nonempty {a : A // d a = b₀} := ⟨⟨a₀, rfl⟩⟩
    exact Fintype.card_pos
  exact ⟨c, hc, fun y ↦ heq y b₀⟩

/-- The left marginal of the product two-stage sampler is exactly uniform. -/
lemma complexExpectation_productTwoStageSliceLeft
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (g : ProductSlicePoint P (fun k ↦ a k + h k) → ℂ) :
    (𝔼 ω, g (productTwoStageSliceLeft P r a b h ω)) =
      𝔼 S, g S := by
  classical
  have hell : ∀ k, a k + h k ≤ (P.fiber k).card := by
    intro k
    calc
      a k + h k ≤ r k + ((P.fiber k).card - r k) :=
        Nat.add_le_add (ha k) (hh k)
      _ = (P.fiber k).card := Nat.add_sub_of_le (hr k)
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  letI : Nonempty (ProductSlicePoint P (fun k ↦ a k + h k)) :=
    productSlicePoint_nonempty P (fun k ↦ a k + h k) hell
  obtain ⟨c, hc, hcard⟩ := exists_positive_common_fiber
    (productTwoStageSliceLeft P r a b h)
    (card_productTwoStageSliceLeft_fiber_eq P r a b h)
  exact complexExpectation_comp_of_card_fiber
    (productTwoStageSliceLeft P r a b h) c hc hcard g

/-- The right marginal of the product two-stage sampler is exactly uniform. -/
lemma complexExpectation_productTwoStageSliceRight
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (g : ProductSlicePoint P (fun k ↦ b k + h k) → ℂ) :
    (𝔼 ω, g (productTwoStageSliceRight P r a b h ω)) =
      𝔼 S, g S := by
  classical
  have hell : ∀ k, b k + h k ≤ (P.fiber k).card := by
    intro k
    calc
      b k + h k ≤ r k + ((P.fiber k).card - r k) :=
        Nat.add_le_add (hb k) (hh k)
      _ = (P.fiber k).card := Nat.add_sub_of_le (hr k)
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  letI : Nonempty (ProductSlicePoint P (fun k ↦ b k + h k)) :=
    productSlicePoint_nonempty P (fun k ↦ b k + h k) hell
  obtain ⟨c, hc, hcard⟩ := exists_positive_common_fiber
    (productTwoStageSliceRight P r a b h)
    (card_productTwoStageSliceRight_fiber_eq P r a b h)
  exact complexExpectation_comp_of_card_fiber
    (productTwoStageSliceRight P r a b h) c hc hcard g

/-- A finite uniform coupling with an explicitly positive finite sample
space.  The latent sample index is retained because multiple sample points
may decode to the same pair of slice points. -/
structure FiniteUniformCoupling (A B : Type*) [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] where
  size : ℕ
  size_pos : 0 < size
  left : Fin size → A
  right : Fin size → B
  left_uniform : ∀ g : A → ℂ, (𝔼 ω, g (left ω)) = 𝔼 a, g a
  right_uniform : ∀ g : B → ℂ, (𝔼 ω, g (right ω)) = 𝔼 b, g b

/-- Reindex any finite uniform joint sample space by a `Fin` type, producing
the explicit coupling object used by the transfer lemmas. -/
noncomputable def FiniteUniformCoupling.ofMaps
    {Ω A B : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (left : Ω → A) (right : Ω → B)
    (hleft : ∀ g : A → ℂ, (𝔼 ω, g (left ω)) = 𝔼 a, g a)
    (hright : ∀ g : B → ℂ, (𝔼 ω, g (right ω)) = 𝔼 b, g b) :
    FiniteUniformCoupling A B where
  size := Fintype.card Ω
  size_pos := Fintype.card_pos
  left i := left ((Fintype.equivFin Ω).symm i)
  right i := right ((Fintype.equivFin Ω).symm i)
  left_uniform g := by
    calc
      (𝔼 i, g (left ((Fintype.equivFin Ω).symm i))) =
          𝔼 ω, g (left ω) := by
        symm
        apply Fintype.expect_equiv (Fintype.equivFin Ω)
        intro ω
        simp
      _ = 𝔼 a, g a := hleft g
  right_uniform g := by
    calc
      (𝔼 i, g (right ((Fintype.equivFin Ω).symm i))) =
          𝔼 ω, g (right ω) := by
        symm
        apply Fintype.expect_equiv (Fintype.equivFin Ω)
        intro ω
        simp
      _ = 𝔼 b, g b := hright g

/-- The exact two-stage coupling used in KSSS Lemma 11.2.  In every bucket
it first samples the exceptional set, then independent left/right slices
inside it and one shared slice outside it.  The preceding orbit argument
proves that both assembled product-slice marginals are uniform. -/
noncomputable def productTwoStageSliceCoupling
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k) :
    letI : Nonempty (ProductSlicePoint P (fun k ↦ a k + h k)) :=
      productSlicePoint_nonempty P (fun k ↦ a k + h k) (fun k ↦ by
        calc
          a k + h k ≤ r k + ((P.fiber k).card - r k) :=
            Nat.add_le_add (ha k) (hh k)
          _ = (P.fiber k).card := Nat.add_sub_of_le (hr k))
    letI : Nonempty (ProductSlicePoint P (fun k ↦ b k + h k)) :=
      productSlicePoint_nonempty P (fun k ↦ b k + h k) (fun k ↦ by
        calc
          b k + h k ≤ r k + ((P.fiber k).card - r k) :=
            Nat.add_le_add (hb k) (hh k)
          _ = (P.fiber k).card := Nat.add_sub_of_le (hr k))
    FiniteUniformCoupling
      (ProductSlicePoint P (fun k ↦ a k + h k))
      (ProductSlicePoint P (fun k ↦ b k + h k)) := by
  have hleft : ∀ k, a k + h k ≤ (P.fiber k).card := fun k ↦ by
    calc
      a k + h k ≤ r k + ((P.fiber k).card - r k) :=
        Nat.add_le_add (ha k) (hh k)
      _ = (P.fiber k).card := Nat.add_sub_of_le (hr k)
  have hright : ∀ k, b k + h k ≤ (P.fiber k).card := fun k ↦ by
    calc
      b k + h k ≤ r k + ((P.fiber k).card - r k) :=
        Nat.add_le_add (hb k) (hh k)
      _ = (P.fiber k).card := Nat.add_sub_of_le (hr k)
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  letI : Nonempty (ProductSlicePoint P (fun k ↦ a k + h k)) :=
    productSlicePoint_nonempty P (fun k ↦ a k + h k) hleft
  letI : Nonempty (ProductSlicePoint P (fun k ↦ b k + h k)) :=
    productSlicePoint_nonempty P (fun k ↦ b k + h k) hright
  exact FiniteUniformCoupling.ofMaps
    (productTwoStageSliceLeft P r a b h)
    (productTwoStageSliceRight P r a b h)
    (complexExpectation_productTwoStageSliceLeft P r a b h hr ha hb hh)
    (complexExpectation_productTwoStageSliceRight P r a b h hr ha hb hh)

/-- An explicit coupling of two arbitrary products of Boolean slices: use
one common independent bucket-permutation sample and decode the two prefix
lengths from it.  Both marginals are exactly uniform. -/
noncomputable def productSliceSharedPermutationCoupling
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell ell' : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (hell' : ∀ k, ell' k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k)) :
    letI : Nonempty (ProductSlicePoint P ell) :=
      productSlicePoint_nonempty P ell hell
    letI : Nonempty (ProductSlicePoint P ell') :=
      productSlicePoint_nonempty P ell' hell'
    FiniteUniformCoupling (ProductSlicePoint P ell)
      (ProductSlicePoint P ell') := by
  letI : Nonempty (ProductSlicePoint P ell) :=
    productSlicePoint_nonempty P ell hell
  letI : Nonempty (ProductSlicePoint P ell') :=
    productSlicePoint_nonempty P ell' hell'
  exact FiniteUniformCoupling.ofMaps
      (productSlicePermutationDecode P ell hell e)
      (productSlicePermutationDecode P ell' hell' e)
      (complexExpectation_productSlicePermutationDecode P ell hell e)
      (complexExpectation_productSlicePermutationDecode P ell' hell' e)

end TwoStageSliceCoupling

end BooleanSlices
end Erdos88

namespace Erdos88
namespace BooleanSlices

section Influence

variable {n : ℕ}

/-- Influence of coordinate `t` for the multilinear polynomial obtained from
`f₀ + f·x + xᵀFx` after deleting the diagonal of `F`.  The coefficient of
`x_t x_j` is `F t j + F j t` under the ordered-double-sum convention. -/
def degreeTwoInfluence (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (t : Fin n) : ℝ :=
  f t ^ 2 + ∑ j, (F t j + F j t) ^ 2

lemma degreeTwoInfluence_nonneg (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (t : Fin n) : 0 ≤ degreeTwoInfluence f F t := by
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- Coefficient bound used in the degree-two specialization of the MOO
invariance principle (KSSS Lemma 11.6). -/
lemma degreeTwoInfluence_le (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A) (t : Fin n) :
    degreeTwoInfluence f F t ≤ B ^ 2 + 4 * n * A ^ 2 := by
  have hf_sq : f t ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (f t)) hB).2 (hf t)
  have hentry : ∀ j, (F t j + F j t) ^ 2 ≤ 4 * A ^ 2 := by
    intro j
    have habs : |F t j + F j t| ≤ 2 * A := by
      calc
        |F t j + F j t| ≤ |F t j| + |F j t| := abs_add_le _ _
        _ ≤ A + A := add_le_add (hF t j) (hF j t)
        _ = 2 * A := by ring
    simpa only [sq_abs, show (2 * A) ^ 2 = 4 * A ^ 2 by ring] using
      (sq_le_sq₀ (abs_nonneg (F t j + F j t)) (by positivity)).2 habs
  calc
    degreeTwoInfluence f F t
        ≤ B ^ 2 + ∑ _j : Fin n, 4 * A ^ 2 :=
          add_le_add hf_sq (Finset.sum_le_sum fun j _ ↦ hentry j)
    _ = B ^ 2 + 4 * n * A ^ 2 := by simp; ring

/-- Sum-of-squared-influences bound fed to KSSS Theorem 11.5. -/
lemma sum_degreeTwoInfluence_sq_le (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A) :
    (∑ t, degreeTwoInfluence f F t ^ 2) ≤
      n * (B ^ 2 + 4 * n * A ^ 2) ^ 2 := by
  have hM : 0 ≤ B ^ 2 + 4 * n * A ^ 2 := by positivity
  calc
    (∑ t, degreeTwoInfluence f F t ^ 2) ≤
        ∑ _t : Fin n, (B ^ 2 + 4 * n * A ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro t _
      nlinarith [degreeTwoInfluence_nonneg f F t,
        degreeTwoInfluence_le f F A B hA hB hf hF t]
    _ = n * (B ^ 2 + 4 * n * A ^ 2) ^ 2 := by simp

/-- The explicit coefficient-growth estimate used in KSSS Lemma 11.6.
The numerical constant `25` is harmless (the paper uses `≲`), while the
exponent `3 + 12δ` is exact. -/
lemma sum_degreeTwoInfluence_sq_le_ksss (δ : ℝ) (hn : 1 ≤ n) (hδ : 0 ≤ δ)
    (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1) :
    (∑ t, degreeTwoInfluence f F t ^ 2) ≤ 25 * scale n (3 + 12 * δ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := hnR.trans' zero_le_one
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  let M : ℝ := scale n (1 + 6 * δ)
  have hBsq : scale n (1 / 2 + 3 * δ) ^ 2 = M := by
    dsimp [M, scale]
    rw [← Real.rpow_mul_natCast hn0]
    congr 1
    ring
  have hnM : (n : ℝ) ≤ M := by
    rw [← Real.rpow_one n]
    exact Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have hM0 : 0 ≤ M := by
    dsimp only [M, scale]
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hscale : (n : ℝ) * M ^ 2 = scale n (3 + 12 * δ) := by
    dsimp only [M, scale]
    calc
      (n : ℝ) * ((n : ℝ) ^ (1 + 6 * δ)) ^ 2 =
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((1 + 6 * δ) * 2) := by
        rw [Real.rpow_one, pow_two, ← Real.rpow_add hnpos]
        congr 1
        ring
      _ = (n : ℝ) ^ (1 + (1 + 6 * δ) * 2) :=
        (Real.rpow_add hnpos _ _).symm
      _ = (n : ℝ) ^ (3 + 12 * δ) := by
        congr 1
        ring
  have hraw := sum_degreeTwoInfluence_sq_le f F 1
    (scale n (1 / 2 + 3 * δ)) (by norm_num)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hf hF
  rw [hBsq] at hraw
  have hsum : M + 4 * (n : ℝ) ≤ 5 * M := by
    nlinarith [hnM]
  calc
    (∑ t, degreeTwoInfluence f F t ^ 2)
        ≤ n * (M + 4 * n) ^ 2 := by simpa using hraw
    _ ≤ n * (5 * M) ^ 2 := by
      have hsquare : (M + 4 * (n : ℝ)) ^ 2 ≤ (5 * M) ^ 2 :=
        (sq_le_sq₀ (add_nonneg hM0 (mul_nonneg (by norm_num) hn0))
          (mul_nonneg (by norm_num) hM0)).2 hsum
      exact mul_le_mul_of_nonneg_left
        hsquare hn0
    _ = 25 * ((n : ℝ) * M ^ 2) := by ring
    _ = 25 * scale n (3 + 12 * δ) := by rw [hscale]

end Influence

section InvarianceBridge

open Invariance

variable {n : ℕ}

/-- Scalar multiplication of every coefficient.  Applying the invariance
principle to this array and the unscaled tests `cos` and `sin` makes the
fourth-derivative cost appear as the exact factor `|τ|⁴`. -/
def scaleQuadraticCoeffs (τ : ℝ) (q : Invariance.QuadraticCoeffs n) :
    Invariance.QuadraticCoeffs n where
  constant := τ * q.constant
  linear i := τ * q.linear i
  pair i j := τ * q.pair i j

lemma scaleQuadraticCoeffs_symPair (τ : ℝ)
    (q : Invariance.QuadraticCoeffs n) (i j : Fin n) :
    (scaleQuadraticCoeffs τ q).symPair i j = τ * q.symPair i j := by
  by_cases hij : i < j
  · simp [scaleQuadraticCoeffs, Invariance.QuadraticCoeffs.symPair, hij]
  · by_cases hji : j < i
    · simp [scaleQuadraticCoeffs, Invariance.QuadraticCoeffs.symPair, hij, hji]
    · simp [scaleQuadraticCoeffs, Invariance.QuadraticCoeffs.symPair, hij, hji]

lemma scaleQuadraticCoeffs_eval (τ : ℝ)
    (q : Invariance.QuadraticCoeffs n) (x : Fin n → ℝ) :
    (scaleQuadraticCoeffs τ q).eval x = τ * q.eval x := by
  rw [Invariance.QuadraticCoeffs.eval, Invariance.QuadraticCoeffs.eval]
  change τ * q.constant + ∑ i, (τ * q.linear i) * x i +
      (1 / 2 : ℝ) * ∑ i, ∑ j,
        (scaleQuadraticCoeffs τ q).symPair i j * x i * x j = _
  simp_rw [scaleQuadraticCoeffs_symPair]
  have hlinear : (∑ i, (τ * q.linear i) * x i) =
      τ * ∑ i, q.linear i * x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hquad : (∑ i, ∑ j, (τ * q.symPair i j) * x i * x j) =
      τ * ∑ i, ∑ j, q.symPair i j * x i * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hlinear, hquad]
  ring

lemma scaleQuadraticCoeffs_influence (τ : ℝ)
    (q : Invariance.QuadraticCoeffs n) (i : Fin n) :
    (scaleQuadraticCoeffs τ q).influence i = τ ^ 2 * q.influence i := by
  rw [Invariance.QuadraticCoeffs.influence, Invariance.QuadraticCoeffs.influence]
  change (τ * q.linear i) ^ 2 +
      ∑ j, (scaleQuadraticCoeffs τ q).symPair i j ^ 2 = _
  simp_rw [scaleQuadraticCoeffs_symPair, mul_pow]
  rw [← Finset.mul_sum]
  ring

lemma scaleQuadraticCoeffs_sum_influence_sq (τ : ℝ)
    (q : Invariance.QuadraticCoeffs n) :
    (∑ i, (scaleQuadraticCoeffs τ q).influence i ^ 2) =
      τ ^ 4 * ∑ i, q.influence i ^ 2 := by
  simp_rw [scaleQuadraticCoeffs_influence, mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma isBoundedC4Test_cos : Invariance.IsBoundedC4Test Real.cos 1 where
  contDiff := Real.contDiff_cos
  bounded := ⟨1, Real.abs_cos_le_one⟩
  fourth_nonneg := by norm_num
  fourth_bound := Real.abs_iteratedDeriv_cos_le_one 4

lemma isBoundedC4Test_sin : Invariance.IsBoundedC4Test Real.sin 1 where
  contDiff := Real.contDiff_sin
  bounded := ⟨1, Real.abs_sin_le_one⟩
  fourth_nonneg := by norm_num
  fourth_bound := Real.abs_iteratedDeriv_sin_le_one 4

/-- Multilinearization of the ordered matrix convention `xᵀFx`: diagonal
coefficients move into the constant, while the coefficient of `xᵢxⱼ`,
`i < j`, is `Fᵢⱼ + Fⱼᵢ`. -/
def toQuadraticCoeffs (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) : Invariance.QuadraticCoeffs n where
  constant := f₀ + trace F
  linear := f
  pair i j := F i j + F j i

lemma sum_row_order_split (a : Fin n → Fin n → ℝ) (i : Fin n) :
    (∑ j, a i j) = a i i +
      (∑ j ∈ Finset.univ.filter (i < ·), a i j) +
      ∑ j ∈ Finset.univ.filter (· < i), a i j := by
  calc
    (∑ j, a i j) = ∑ j, ((if j = i then a i j else 0) +
        (if i < j then a i j else 0) + if j < i then a i j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rcases lt_trichotomy j i with h | h | h
      · simp [h, h.ne, not_lt_of_ge h.le]
      · subst j
        simp
      · simp [h, h.ne', not_lt_of_ge h.le]
    _ = a i i +
        (∑ j ∈ Finset.univ.filter (i < ·), a i j) +
          ∑ j ∈ Finset.univ.filter (· < i), a i j := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp_rw [Finset.sum_filter]
      simp

lemma sum_lower_eq_sum_upper_transpose (a : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.filter (· < i), a i j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), a j i := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Every ordered double sum is its diagonal plus one copy of each unordered
pair, with the two ordered coefficients added. -/
lemma sum_ordered_eq_trace_add_upper (a : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, a i j) =
      (∑ i, a i i) +
        ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), (a i j + a j i) := by
  simp_rw [sum_row_order_split]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_lower_eq_sum_upper_transpose]
  simp_rw [Finset.sum_add_distrib]
  ring

lemma toQuadraticCoeffs_eval (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    (toQuadraticCoeffs f₀ f F).eval x =
      f₀ + trace F + linearPart f x +
        ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
          (F i j + F j i) * x i * x j := by
  let a : Fin n → Fin n → ℝ := fun i j ↦
    (toQuadraticCoeffs f₀ f F).symPair i j * x i * x j
  have hdouble : (∑ i, ∑ j, a i j) =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        (F i j + F j i) * x i * x j := by
    rw [sum_ordered_eq_trace_add_upper a]
    have hdiag : (∑ i, a i i) = 0 := by
      simp [a, Invariance.QuadraticCoeffs.symPair]
    rw [hdiag, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i < j := (Finset.mem_filter.mp hj).2
    have hji : ¬j < i := not_lt_of_ge hij.le
    simp only [a, toQuadraticCoeffs,
      Invariance.QuadraticCoeffs.symPair, hij, hji, if_true, if_false]
    ring
  rw [Invariance.QuadraticCoeffs.eval]
  simp only [toQuadraticCoeffs]
  change f₀ + trace F + ∑ i, f i * x i +
      (1 / 2 : ℝ) * (∑ i, ∑ j, a i j) = _
  rw [hdouble]
  simp only [linearPart]
  ring

/-- On a sign vector, multilinearization does not change the value. -/
lemma toQuadraticCoeffs_eval_of_sq_eq_one (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : ∀ i, x i ^ 2 = 1) :
    (toQuadraticCoeffs f₀ f F).eval x = quadraticPolynomial f₀ f F x := by
  rw [toQuadraticCoeffs_eval]
  have hdiag : (∑ i, x i * F i i * x i) = trace F := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      x i * F i i * x i = F i i * x i ^ 2 := by ring
      _ = F i i := by rw [hx i]; ring
  have hquad : quadraticPart F x = trace F +
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        (F i j + F j i) * x i * x j := by
    rw [quadraticPart, sum_ordered_eq_trace_add_upper
      (fun i j ↦ x i * F i j * x j), hdiag]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [quadraticPolynomial, hquad]
  ring

@[simp] lemma toQuadraticCoeffs_eval_signOfSet (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (S : Finset (Fin n)) :
    (toQuadraticCoeffs f₀ f F).eval (signOfSet S) = sliceQuadratic f₀ f F S := by
  exact toQuadraticCoeffs_eval_of_sq_eq_one f₀ f F _ (signOfSet_sq S)

/-- The abstract MOO influence agrees with the ordered-matrix coefficient
formula, except that the harmless diagonal summand is omitted. -/
lemma toQuadraticCoeffs_influence (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (t : Fin n) :
    (toQuadraticCoeffs 0 f F).influence t =
      f t ^ 2 + ∑ j ∈ Finset.univ.erase t, (F t j + F j t) ^ 2 := by
  rw [Invariance.QuadraticCoeffs.influence]
  change f t ^ 2 + ∑ j, (toQuadraticCoeffs 0 f F).symPair t j ^ 2 = _
  have hsplit : (Finset.univ.erase t : Finset (Fin n)) =
      Finset.univ.filter (· < t) ∪ Finset.univ.filter (t < ·) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_filter]
    simpa only [and_true] using
      (ne_iff_lt_or_gt : j ≠ t ↔ j < t ∨ t < j)
  have hdisj : Disjoint (Finset.univ.filter (fun j ↦ j < t))
      (Finset.univ.filter (fun j ↦ t < j)) := by
    rw [Finset.disjoint_left]
    intro j hjlt hjgt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjlt hjgt
    omega
  have hleft :
      (∑ j ∈ Finset.univ.filter (fun j ↦ j < t),
          (toQuadraticCoeffs 0 f F).symPair t j ^ 2) =
        ∑ j ∈ Finset.univ.filter (fun j ↦ j < t),
          (F t j + F j t) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjt : j < t := (Finset.mem_filter.mp hj).2
    have hntj : ¬t < j := not_lt_of_ge hjt.le
    simp [toQuadraticCoeffs, Invariance.QuadraticCoeffs.symPair, hjt, hntj,
      add_comm]
  have hright :
      (∑ j ∈ Finset.univ.filter (fun j ↦ t < j),
          (toQuadraticCoeffs 0 f F).symPair t j ^ 2) =
        ∑ j ∈ Finset.univ.filter (fun j ↦ t < j),
          (F t j + F j t) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have htj : t < j := (Finset.mem_filter.mp hj).2
    have hnjt : ¬j < t := not_lt_of_ge htj.le
    simp [toQuadraticCoeffs, Invariance.QuadraticCoeffs.symPair, htj, hnjt]
  have hall :
      (∑ j, (toQuadraticCoeffs 0 f F).symPair t j ^ 2) =
        ∑ j ∈ Finset.univ.erase t,
          (toQuadraticCoeffs 0 f F).symPair t j ^ 2 := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun j ↦ (toQuadraticCoeffs 0 f F).symPair t j ^ 2)
      (Finset.mem_univ t)]
    simp
  rw [hall, hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj,
    hleft, hright]

lemma toQuadraticCoeffs_influence_le (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A) (t : Fin n) :
    (toQuadraticCoeffs 0 f F).influence t ≤ B ^ 2 + 4 * n * A ^ 2 := by
  have hf_sq : f t ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (f t)) hB).2 (hf t)
  have hentry : ∀ j, (F t j + F j t) ^ 2 ≤ 4 * A ^ 2 := by
    intro j
    have habs : |F t j + F j t| ≤ 2 * A := by
      calc
        |F t j + F j t| ≤ |F t j| + |F j t| := abs_add_le _ _
        _ ≤ A + A := add_le_add (hF t j) (hF j t)
        _ = 2 * A := by ring
    simpa only [sq_abs, show (2 * A) ^ 2 = 4 * A ^ 2 by ring] using
      (sq_le_sq₀ (abs_nonneg (F t j + F j t)) (by positivity)).2 habs
  rw [toQuadraticCoeffs_influence]
  calc
    f t ^ 2 + ∑ j ∈ Finset.univ.erase t, (F t j + F j t) ^ 2 ≤
        B ^ 2 + ∑ _j ∈ Finset.univ.erase t, 4 * A ^ 2 := by
      exact add_le_add hf_sq (Finset.sum_le_sum fun j _ ↦ hentry j)
    _ ≤ B ^ 2 + 4 * n * A ^ 2 := by
      have hc : (Finset.univ.erase t).card ≤ n := by simp
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcReal : ((Finset.univ.erase t).card : ℝ) ≤ n := by
        exact_mod_cast hc
      have hmul : ((Finset.univ.erase t).card : ℝ) * (4 * A ^ 2) ≤
          (n : ℝ) * (4 * A ^ 2) :=
        mul_le_mul_of_nonneg_right hcReal (by positivity)
      nlinarith

lemma sum_toQuadraticCoeffs_influence_sq_le (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A) :
    (∑ t, (toQuadraticCoeffs 0 f F).influence t ^ 2) ≤
      n * (B ^ 2 + 4 * n * A ^ 2) ^ 2 := by
  calc
    (∑ t, (toQuadraticCoeffs 0 f F).influence t ^ 2) ≤
        ∑ _t : Fin n, (B ^ 2 + 4 * n * A ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro t _
      have h0 := Invariance.QuadraticCoeffs.influence_nonneg
        (toQuadraticCoeffs 0 f F) t
      have hle := toQuadraticCoeffs_influence_le f F A B hA hB hf hF t
      have hM : 0 ≤ B ^ 2 + 4 * n * A ^ 2 := by positivity
      exact (sq_le_sq₀ h0 hM).2 hle
    _ = n * (B ^ 2 + 4 * n * A ^ 2) ^ 2 := by simp

/-- Explicit `n^(3+12δ)` MOO influence bound in KSSS Lemma 11.6. -/
lemma sum_toQuadraticCoeffs_influence_sq_le_rpow
    (δ : ℝ) (hδ : 0 ≤ δ) (hn : 1 ≤ n)
    (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1) :
    (∑ t, (toQuadraticCoeffs 0 f F).influence t ^ 2) ≤
      25 * scale n (3 + 12 * δ) := by
  let x : ℝ := n
  let p : ℝ := scale n (1 + 6 * δ)
  have hx1 : 1 ≤ x := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hxp : 0 < x := zero_lt_one.trans_le hx1
  have hscale_sq : scale n (1 / 2 + 3 * δ) ^ 2 = p := by
    dsimp only [p, scale]
    calc
      Real.rpow (n : ℝ) (1 / 2 + 3 * δ) ^ 2 =
          Real.rpow (n : ℝ) (1 / 2 + 3 * δ) *
            Real.rpow (n : ℝ) (1 / 2 + 3 * δ) := by ring
      _ = Real.rpow (n : ℝ) ((1 / 2 + 3 * δ) + (1 / 2 + 3 * δ)) :=
        (Real.rpow_add hxp _ _).symm
      _ = Real.rpow (n : ℝ) (1 + 6 * δ) := by
        congr 1
        ring
  have hxp_ge : x ≤ p := by
    change (n : ℝ) ≤ Real.rpow (n : ℝ) (1 + 6 * δ)
    calc
      (n : ℝ) = Real.rpow (n : ℝ) 1 :=
        (Real.rpow_one (n : ℝ)).symm
      _ ≤ Real.rpow (n : ℝ) (1 + 6 * δ) :=
        Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
          (show (1 : ℝ) ≤ 1 + 6 * δ by linarith)
  have hmul : x * p ^ 2 = scale n (3 + 12 * δ) := by
    dsimp only [x, p, scale]
    have hpow : Real.rpow (n : ℝ) (1 + 6 * δ) ^ 2 =
        Real.rpow (n : ℝ) ((1 + 6 * δ) * 2) := by
      calc
        Real.rpow (n : ℝ) (1 + 6 * δ) ^ 2 =
            Real.rpow (n : ℝ) (1 + 6 * δ) *
              Real.rpow (n : ℝ) (1 + 6 * δ) := by ring
        _ = Real.rpow (n : ℝ) ((1 + 6 * δ) + (1 + 6 * δ)) :=
          (Real.rpow_add hxp _ _).symm
        _ = Real.rpow (n : ℝ) ((1 + 6 * δ) * 2) := by
          congr 1
          ring
    calc
      (n : ℝ) * Real.rpow (n : ℝ) (1 + 6 * δ) ^ 2 =
          (n : ℝ) * Real.rpow (n : ℝ) ((1 + 6 * δ) * 2) := by
        rw [hpow]
      _ = Real.rpow (n : ℝ) 1 *
            Real.rpow (n : ℝ) ((1 + 6 * δ) * 2) := by
        exact congrArg
          (fun z : ℝ ↦ z * Real.rpow (n : ℝ) ((1 + 6 * δ) * 2))
          (Real.rpow_one (n : ℝ)).symm
      _ = Real.rpow (n : ℝ) (1 + (1 + 6 * δ) * 2) :=
        (Real.rpow_add hxp _ _).symm
      _ = Real.rpow (n : ℝ) (3 + 12 * δ) := by
        congr 1
        ring
  have hraw := sum_toQuadraticCoeffs_influence_sq_le
    f F 1 (scale n (1 / 2 + 3 * δ)) (by norm_num)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _) hf hF
  have hsum : p + 4 * x ≤ 5 * p := by
    nlinarith [hxp_ge]
  have hp0 : 0 ≤ p := by
    dsimp only [p, scale]
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc
    (∑ t, (toQuadraticCoeffs 0 f F).influence t ^ 2) ≤
        x * (scale n (1 / 2 + 3 * δ) ^ 2 + 4 * x * 1 ^ 2) ^ 2 := by
      simpa [x] using hraw
    _ = x * (p + 4 * x) ^ 2 := by rw [hscale_sq]; ring
    _ ≤ x * (5 * p) ^ 2 := by
      have hsquare : (p + 4 * x) ^ 2 ≤ (5 * p) ^ 2 :=
        (sq_le_sq₀ (add_nonneg hp0 (mul_nonneg (by norm_num) hx0))
          (mul_nonneg (by norm_num) hp0)).2 hsum
      exact mul_le_mul_of_nonneg_left
        hsquare hx0
    _ = 25 * scale n (3 + 12 * δ) := by rw [← hmul]; ring

end InvarianceBridge

end BooleanSlices
end Erdos88

namespace Erdos88
namespace BooleanSlices

section FiniteMoments

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {n : ℕ}

noncomputable def uniformExpectation (X : Ω → ℝ) : ℝ := 𝔼 ω, X ω
noncomputable def uniformVariance (X : Ω → ℝ) : ℝ :=
  uniformExpectation fun ω ↦ (X ω - uniformExpectation X) ^ 2

lemma uniformExpectation_const (c : ℝ) :
    uniformExpectation (fun _ : Ω ↦ c) = c := by simp [uniformExpectation]

lemma uniformExpectation_add (X Y : Ω → ℝ) :
    uniformExpectation (fun ω ↦ X ω + Y ω) =
      uniformExpectation X + uniformExpectation Y := by
  simp [uniformExpectation, Finset.expect_add_distrib]

lemma uniformExpectation_sum {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) :
    uniformExpectation (fun ω ↦ ∑ i, X i ω) =
      ∑ i, uniformExpectation (X i) := by
  simp only [uniformExpectation]
  exact Finset.expect_sum_comm Finset.univ Finset.univ (fun ω i ↦ X i ω)

lemma uniformExpectation_const_mul (c : ℝ) (X : Ω → ℝ) :
    uniformExpectation (fun ω ↦ c * X ω) = c * uniformExpectation X := by
  simp [uniformExpectation, Finset.mul_expect]

lemma uniformExpectation_mul_const (X : Ω → ℝ) (c : ℝ) :
    uniformExpectation (fun ω ↦ X ω * c) = uniformExpectation X * c := by
  simp [uniformExpectation, Finset.expect_mul]

lemma uniformExpectation_sub (X Y : Ω → ℝ) :
    uniformExpectation (fun ω ↦ X ω - Y ω) =
      uniformExpectation X - uniformExpectation Y := by
  simp [uniformExpectation, Finset.expect_sub_distrib]

lemma uniformExpectation_congr {X Y : Ω → ℝ} (h : ∀ ω, X ω = Y ω) :
    uniformExpectation X = uniformExpectation Y := by
  apply congrArg uniformExpectation
  funext ω
  exact h ω

lemma uniformExpectation_centered (X : Ω → ℝ) :
    uniformExpectation (fun ω ↦ X ω - uniformExpectation X) = 0 := by
  rw [uniformExpectation_sub, uniformExpectation_const]
  ring

lemma uniformVariance_nonneg (X : Ω → ℝ) : 0 ≤ uniformVariance X := by
  exact Finset.expect_nonneg (fun _ _ ↦ sq_nonneg _)

/-- The elementary identity `Var X = E[X²] - E[X]²` for a finite
uniform probability space. -/
lemma uniformVariance_eq_second_sub_sq (X : Ω → ℝ) :
    uniformVariance X =
      uniformExpectation (fun ω ↦ X ω ^ 2) - uniformExpectation X ^ 2 := by
  rw [uniformVariance]
  calc
    uniformExpectation (fun ω ↦ (X ω - uniformExpectation X) ^ 2) =
        uniformExpectation (fun ω ↦
          X ω ^ 2 - (2 * uniformExpectation X) * X ω +
            uniformExpectation X ^ 2) := by
      apply uniformExpectation_congr
      intro ω
      ring
    _ = uniformExpectation (fun ω ↦ X ω ^ 2) - uniformExpectation X ^ 2 := by
      rw [uniformExpectation_add, uniformExpectation_sub,
        uniformExpectation_const_mul, uniformExpectation_const]
      ring

lemma uniformVariance_le_second (X : Ω → ℝ) :
    uniformVariance X ≤ uniformExpectation (fun ω ↦ X ω ^ 2) := by
  rw [uniformVariance_eq_second_sub_sq]
  exact sub_le_self _ (sq_nonneg _)

/-- Expanding `X = Y + (X-Y)` expresses the variance difference as a
variance plus a covariance.  This form is convenient because the second
factor of the covariance is the actual coupled difference, rather than its
centered version. -/
lemma uniformVariance_sub_eq (X Y : Ω → ℝ) :
    uniformVariance X - uniformVariance Y =
      uniformVariance (fun ω ↦ X ω - Y ω) +
        2 * uniformExpectation (fun ω ↦
          (Y ω - uniformExpectation Y) * (X ω - Y ω)) := by
  let D : Ω → ℝ := fun ω ↦ X ω - Y ω
  have hmean : uniformExpectation X =
      uniformExpectation Y + uniformExpectation D := by
    rw [show X = fun ω ↦ Y ω + D ω by
      funext ω; dsimp only [D]; ring, uniformExpectation_add]
  have hsecond : uniformExpectation (fun ω ↦ X ω ^ 2) =
      uniformExpectation (fun ω ↦ Y ω ^ 2) +
        2 * uniformExpectation (fun ω ↦ Y ω * D ω) +
          uniformExpectation (fun ω ↦ D ω ^ 2) := by
    calc
      uniformExpectation (fun ω ↦ X ω ^ 2) =
          uniformExpectation (fun ω ↦
            Y ω ^ 2 + 2 * (Y ω * D ω) + D ω ^ 2) := by
        apply uniformExpectation_congr
        intro ω
        dsimp only [D]
        ring
      _ = uniformExpectation (fun ω ↦ Y ω ^ 2) +
          2 * uniformExpectation (fun ω ↦ Y ω * D ω) +
            uniformExpectation (fun ω ↦ D ω ^ 2) := by
        rw [uniformExpectation_add, uniformExpectation_add,
          uniformExpectation_const_mul]
  have hcov : uniformExpectation (fun ω ↦
      (Y ω - uniformExpectation Y) * D ω) =
      uniformExpectation (fun ω ↦ Y ω * D ω) -
        uniformExpectation Y * uniformExpectation D := by
    calc
      uniformExpectation (fun ω ↦
          (Y ω - uniformExpectation Y) * D ω) =
          uniformExpectation (fun ω ↦
            Y ω * D ω - uniformExpectation Y * D ω) := by
        apply uniformExpectation_congr
        intro ω
        ring
      _ = uniformExpectation (fun ω ↦ Y ω * D ω) -
          uniformExpectation Y * uniformExpectation D := by
        rw [uniformExpectation_sub, uniformExpectation_const_mul]
  change uniformVariance X - uniformVariance Y =
    uniformVariance D + 2 * uniformExpectation (fun ω ↦
      (Y ω - uniformExpectation Y) * D ω)
  rw [uniformVariance_eq_second_sub_sq, uniformVariance_eq_second_sub_sq,
    uniformVariance_eq_second_sub_sq, hmean, hsecond, hcov]
  ring

/-- Finite `L²` comparison for variances.  It is the quantitative bridge
from the second-moment coupling bound to the variance error in KSSS
Lemma 11.1. -/
lemma abs_uniformVariance_sub_le (X Y : Ω → ℝ) :
    |uniformVariance X - uniformVariance Y| ≤
      uniformExpectation (fun ω ↦ (X ω - Y ω) ^ 2) +
        2 * √(uniformVariance Y *
          uniformExpectation (fun ω ↦ (X ω - Y ω) ^ 2)) := by
  let D : Ω → ℝ := fun ω ↦ X ω - Y ω
  let C : ℝ := uniformExpectation (fun ω ↦
    (Y ω - uniformExpectation Y) * D ω)
  have hcs : C ^ 2 ≤ uniformVariance Y * uniformExpectation (fun ω ↦ D ω ^ 2) := by
    simpa only [C, D, uniformVariance, uniformExpectation] using
      (Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset Ω)
        (fun ω ↦ Y ω - uniformExpectation Y) D)
  have habsC : |C| ≤ √(uniformVariance Y *
      uniformExpectation (fun ω ↦ D ω ^ 2)) :=
    Real.abs_le_sqrt hcs
  have hvarD0 : 0 ≤ uniformVariance D := uniformVariance_nonneg D
  have hvarD : uniformVariance D ≤
      uniformExpectation (fun ω ↦ D ω ^ 2) := uniformVariance_le_second D
  rw [uniformVariance_sub_eq]
  change |uniformVariance D + 2 * C| ≤ _
  calc
    |uniformVariance D + 2 * C| ≤
        uniformVariance D + 2 * |C| := by
      calc
        |uniformVariance D + 2 * C| ≤
            |uniformVariance D| + |2 * C| := abs_add_le _ _
        _ = uniformVariance D + 2 * |C| := by
          rw [abs_of_nonneg hvarD0, abs_mul, abs_of_nonneg (by norm_num)]
    _ ≤ uniformExpectation (fun ω ↦ D ω ^ 2) +
        2 * √(uniformVariance Y *
          uniformExpectation (fun ω ↦ D ω ^ 2)) := by
      gcongr

end FiniteMoments

end BooleanSlices
end Erdos88

namespace Erdos88
namespace BooleanSlices

section FiniteMoments

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {n : ℕ}

section RademacherCube

/-- The degree-one and unordered degree-two Walsh monomials occurring in a
multilinear quadratic polynomial. -/
abbrev DegreeTwoMonomialIndex (n : ℕ) :=
  Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2}

def degreeTwoMonomialSupport : DegreeTwoMonomialIndex n → Finset (Fin n)
  | Sum.inl i => {i}
  | Sum.inr p => {p.1.1, p.1.2}

lemma degreeTwoMonomialSupport_injective :
    Function.Injective (degreeTwoMonomialSupport (n := n)) := by
  intro p q hpq
  cases p with
  | inl i =>
      cases q with
      | inl j =>
          simp only [degreeTwoMonomialSupport, Finset.singleton_inj] at hpq
          subst j
          rfl
      | inr q =>
          have hc := congrArg Finset.card hpq
          have hqne : q.1.1 ≠ q.1.2 := ne_of_lt q.2
          simp [degreeTwoMonomialSupport, hqne] at hc
  | inr p =>
      cases q with
      | inl j =>
          have hc := congrArg Finset.card hpq
          have hpne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
          simp [degreeTwoMonomialSupport, hpne] at hc
      | inr q =>
          change ({p.1.1, p.1.2} : Finset (Fin n)) =
            ({q.1.1, q.1.2} : Finset (Fin n)) at hpq
          refine congrArg Sum.inr ?_
          apply Subtype.ext
          apply Prod.ext
          · have hp_mem : p.1.1 ∈ ({q.1.1, q.1.2} : Finset (Fin n)) := by
              rw [← hpq]
              simp [degreeTwoMonomialSupport]
            simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
            rcases hp_mem with hfirst | hsecond
            · exact hfirst
            · have hp2_mem : p.1.2 ∈ ({q.1.1, q.1.2} : Finset (Fin n)) := by
                rw [← hpq]
                simp [degreeTwoMonomialSupport]
              simp only [Finset.mem_insert, Finset.mem_singleton] at hp2_mem
              rcases hp2_mem with h21 | h22
              · exfalso
                have : q.1.2 < q.1.1 := by simpa [hsecond, h21] using p.2
                exact (not_lt_of_ge q.2.le) this
              · exact False.elim ((ne_of_lt p.2) (hsecond.trans h22.symm))
          · have hp2_mem : p.1.2 ∈ ({q.1.1, q.1.2} : Finset (Fin n)) := by
              rw [← hpq]
              simp [degreeTwoMonomialSupport]
            simp only [Finset.mem_insert, Finset.mem_singleton] at hp2_mem
            rcases hp2_mem with hfirst | hsecond
            · have hp1_mem : p.1.1 ∈ ({q.1.1, q.1.2} : Finset (Fin n)) := by
                rw [← hpq]
                simp [degreeTwoMonomialSupport]
              simp only [Finset.mem_insert, Finset.mem_singleton] at hp1_mem
              rcases hp1_mem with h11 | h12
              · exact False.elim ((ne_of_lt p.2) (h11.trans hfirst.symm))
              · exfalso
                have : q.1.2 < q.1.1 := by simpa [h12, hfirst] using p.2
                exact (not_lt_of_ge q.2.le) this
            · exact hsecond

def degreeTwoMonomialCoeff (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) :
    DegreeTwoMonomialIndex n → ℝ
  | Sum.inl i => f i
  | Sum.inr p => F p.1.1 p.1.2 + F p.1.2 p.1.1

lemma sum_upperPair (H : Fin n → Fin n → ℝ) :
    (∑ p : {p : Fin n × Fin n // p.1 < p.2}, H p.1.1 p.1.2) =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), H i j := by
  classical
  let s := (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p ↦ p.1 < p.2)
  have hs : (∑ p ∈ s, H p.1 p.2) =
      ∑ p : {p : Fin n × Fin n // p.1 < p.2}, H p.1.1 p.1.2 := by
    apply Finset.sum_subtype
    intro p
    simp [s]
  rw [← hs]
  simp only [s, Finset.sum_filter, Fintype.sum_prod_type]

lemma degreeTwoWalshSum_eq (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (W : Finset (Fin n)) :
    (∑ p, degreeTwoMonomialCoeff f F p *
      Probability.walsh (degreeTwoMonomialSupport p) W) =
      linearPart f (signOfSet W) +
        ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
          (F i j + F j i) * signOfSet W i * signOfSet W j := by
  classical
  have hsingle (i : Fin n) :
      degreeTwoMonomialCoeff f F (Sum.inl i) *
          Probability.walsh (degreeTwoMonomialSupport (Sum.inl i)) W =
        f i * signOfSet W i := by
    simp [degreeTwoMonomialCoeff, degreeTwoMonomialSupport,
      Probability.walsh, Probability.sign, signOfSet]
  have hpair (p : {p : Fin n × Fin n // p.1 < p.2}) :
      degreeTwoMonomialCoeff f F (Sum.inr p) *
          Probability.walsh (degreeTwoMonomialSupport (Sum.inr p)) W =
        (F p.1.1 p.1.2 + F p.1.2 p.1.1) *
          signOfSet W p.1.1 * signOfSet W p.1.2 := by
    have hpne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
    simp [degreeTwoMonomialCoeff, degreeTwoMonomialSupport,
      Probability.walsh, Probability.sign, signOfSet, hpne]
  rw [Fintype.sum_sum_type]
  simp_rw [hsingle, hpair]
  rw [linearPart]
  congr 1
  simpa only [] using sum_upperPair
    (H := fun i j ↦ (F i j + F j i) * signOfSet W i * signOfSet W j)

lemma bernoulliWeight_half (W : Finset (Fin n)) :
    Probability.bernoulliWeight (1 / 2 : ℝ) W = (1 / 2 : ℝ) ^ n := by
  rw [Probability.bernoulliWeight, Erdos202.ParkPham.bernoulliMass]
  have hcard : W.card ≤ n := by
    calc
      W.card ≤ Fintype.card (Fin n) := Finset.card_le_univ W
      _ = n := Fintype.card_fin n
  have hcardUniv : W.card ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card (by simp)
  rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
  rw [← pow_add]
  congr 1
  calc
    W.card + ((Finset.univ : Finset (Fin n)).card - W.card) =
        (Finset.univ : Finset (Fin n)).card := Nat.add_sub_of_le hcardUniv
    _ = n := by simp

/-- The Bernoulli model at density `1/2` is exactly the uniform model on
all sign sets. -/
lemma uniformExpectation_finset_eq_probability_half
    (X : Finset (Fin n) → ℝ) :
    uniformExpectation X = Probability.expectation (1 / 2 : ℝ) X := by
  rw [uniformExpectation, Fintype.expect_eq_sum_div_card]
  unfold Probability.expectation
  simp_rw [bernoulliWeight_half]
  rw [← Finset.mul_sum]
  simp only [Fintype.card_finset, Fintype.card_fin, one_div, inv_pow]
  rw [div_eq_mul_inv, mul_comm]
  norm_num [Nat.cast_pow]

lemma sum_probability_walsh_eq_zero {T : Finset (Fin n)} (hT : T.Nonempty) :
    ∑ W : Finset (Fin n), Probability.walsh T W = 0 := by
  classical
  rw [Probability.sum_univ_eq_sum_powerset]
  calc
    (∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
        Probability.walsh T W) =
        ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
          ∏ v ∈ (Finset.univ : Finset (Fin n)),
            if v ∈ W then (1 : ℝ) else if v ∈ T then -1 else 1 := by
      apply Finset.sum_congr rfl
      intro W hW
      rw [Probability.walsh]
      symm
      calc
        (∏ v ∈ (Finset.univ : Finset (Fin n)),
            if v ∈ W then (1 : ℝ) else if v ∈ T then -1 else 1) =
            ∏ v ∈ T,
              if v ∈ W then (1 : ℝ) else if v ∈ T then -1 else 1 := by
          symm
          apply Finset.prod_subset (by simp)
          intro v _ hvT
          simp [hvT]
        _ = ∏ v ∈ T, Probability.sign v W := by
          apply Finset.prod_congr rfl
          intro v hvT
          simp [Probability.sign, hvT]
    _ = ∏ v ∈ (Finset.univ : Finset (Fin n)),
          ((1 : ℝ) + if v ∈ T then -1 else 1) := by
      exact Probability.sum_prod_ite_mem (X := (Finset.univ : Finset (Fin n)))
        (a := fun _ ↦ (1 : ℝ)) (b := fun v ↦ if v ∈ T then -1 else 1)
    _ = 0 := by
      obtain ⟨v, hv⟩ := hT
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [hv]

lemma uniformExpectation_probability_walsh (T : Finset (Fin n)) :
    uniformExpectation (Probability.walsh T) = if T = ∅ then 1 else 0 := by
  classical
  by_cases hT : T = ∅
  · subst T
    simp [Probability.walsh, uniformExpectation]
  · rw [if_neg hT, uniformExpectation, Fintype.expect_eq_sum_div_card,
      sum_probability_walsh_eq_zero (Finset.nonempty_iff_ne_empty.mpr hT), zero_div]

lemma probability_walsh_mul (T U W : Finset (Fin n)) :
    Probability.walsh T W * Probability.walsh U W =
      Probability.walsh (T ∆ U) W := by
  classical
  simp only [Probability.walsh]
  rw [← Finset.prod_inter_mul_prod_sdiff T U,
    ← Finset.prod_inter_mul_prod_sdiff U T]
  rw [Finset.inter_comm U T]
  have hcommon :
      (∏ x ∈ T ∩ U, Probability.sign x W) *
          ∏ x ∈ T ∩ U, Probability.sign x W = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro x _
    by_cases hx : x ∈ W <;> simp [Probability.sign, hx]
  have hdisjoint : Disjoint (T \ U) (U \ T) := by
    exact Finset.disjoint_left.mpr (by simp +contextual)
  rw [Finset.symmDiff_def, Finset.prod_union hdisjoint]
  calc
    ((∏ x ∈ T ∩ U, Probability.sign x W) *
          ∏ x ∈ T \ U, Probability.sign x W) *
        ((∏ x ∈ T ∩ U, Probability.sign x W) *
          ∏ x ∈ U \ T, Probability.sign x W) =
        ((∏ x ∈ T ∩ U, Probability.sign x W) *
          ∏ x ∈ T ∩ U, Probability.sign x W) *
        ((∏ x ∈ T \ U, Probability.sign x W) *
          ∏ x ∈ U \ T, Probability.sign x W) := by ring
    _ = (∏ x ∈ T \ U, Probability.sign x W) *
          ∏ x ∈ U \ T, Probability.sign x W := by rw [hcommon, one_mul]

/-- Walsh characters are an orthonormal family in the finite uniform cube. -/
lemma uniformExpectation_probability_walsh_mul (T U : Finset (Fin n)) :
    uniformExpectation (fun W ↦ Probability.walsh T W * Probability.walsh U W) =
      if T = U then 1 else 0 := by
  simp_rw [probability_walsh_mul]
  rw [uniformExpectation_probability_walsh]
  simp

lemma uniformExpectation_sq_walsh_sum {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (T : I → Finset (Fin n)) (hT : Function.Injective T) :
    uniformExpectation (fun W : Finset (Fin n) ↦
      (∑ i, a i * Probability.walsh (T i) W) ^ 2) = ∑ i, a i ^ 2 := by
  have hpoint : (fun W : Finset (Fin n) ↦
      (∑ i, a i * Probability.walsh (T i) W) ^ 2) =
      fun W ↦ ∑ i, ∑ j,
        (a i * a j) *
          (Probability.walsh (T i) W * Probability.walsh (T j) W) := by
    funext W
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hpoint, uniformExpectation_sum]
  simp_rw [uniformExpectation_sum, uniformExpectation_const_mul,
    uniformExpectation_probability_walsh_mul]
  classical
  simp [hT.eq_iff, pow_two]

lemma uniformExpectation_signOfSet (i : Fin n) :
    uniformExpectation (fun W : Finset (Fin n) ↦ signOfSet W i) = 0 := by
  have hpoint : (fun W : Finset (Fin n) ↦ signOfSet W i) =
      Probability.walsh ({i} : Finset (Fin n)) := by
    funext W
    simp [Probability.walsh, Probability.sign, signOfSet]
  rw [hpoint, uniformExpectation_probability_walsh]
  simp

lemma uniformExpectation_signOfSet_mul {i j : Fin n} (hij : i ≠ j) :
    uniformExpectation (fun W : Finset (Fin n) ↦
      signOfSet W i * signOfSet W j) = 0 := by
  have hpoint : (fun W : Finset (Fin n) ↦
      signOfSet W i * signOfSet W j) =
      Probability.walsh ({i, j} : Finset (Fin n)) := by
    funext W
    simp [Probability.walsh, Probability.sign, signOfSet, hij]
  rw [hpoint, uniformExpectation_probability_walsh]
  simp [hij]

lemma uniformExpectation_signOfSet_mul_apply (i j : Fin n) :
    uniformExpectation (fun W : Finset (Fin n) ↦
      signOfSet W i * signOfSet W j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [if_pos, ← pow_two, signOfSet_sq]
    exact uniformExpectation_const 1
  · rw [if_neg hij, uniformExpectation_signOfSet_mul hij]

/-- Exact mean of the independent-Rademacher quadratic. -/
theorem rademacher_sliceQuadratic_mean (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) :
    uniformExpectation (sliceQuadratic f₀ f F) = f₀ + trace F := by
  change uniformExpectation (fun W : Finset (Fin n) ↦
      f₀ + linearPart f (signOfSet W) +
        quadraticPart F (signOfSet W)) = _
  rw [uniformExpectation_add, uniformExpectation_add,
    uniformExpectation_const]
  have hlinear :
      uniformExpectation (fun W : Finset (Fin n) ↦
        linearPart f (signOfSet W)) = 0 := by
    simp only [linearPart]
    rw [uniformExpectation_sum]
    simp_rw [uniformExpectation_const_mul, uniformExpectation_signOfSet]
    simp
  have hquadratic :
      uniformExpectation (fun W : Finset (Fin n) ↦
        quadraticPart F (signOfSet W)) = trace F := by
    simp only [quadraticPart]
    rw [uniformExpectation_sum]
    simp_rw [uniformExpectation_sum]
    simp_rw [show ∀ (W : Finset (Fin n)) (i j : Fin n),
        signOfSet W i * F i j * signOfSet W j =
          F i j * (signOfSet W i * signOfSet W j) by intros; ring]
    simp_rw [uniformExpectation_const_mul,
      uniformExpectation_signOfSet_mul_apply]
    classical
    simp [trace]
  rw [hlinear, hquadratic]
  ring

lemma sliceQuadratic_centered_eq_degreeTwoWalshSum
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (W : Finset (Fin n)) :
    sliceQuadratic f₀ f F W - (f₀ + trace F) =
      ∑ p, degreeTwoMonomialCoeff f F p *
        Probability.walsh (degreeTwoMonomialSupport p) W := by
  rw [← toQuadraticCoeffs_eval_signOfSet, toQuadraticCoeffs_eval,
    degreeTwoWalshSum_eq]
  ring

/-- Exact independent-Rademacher variance in upper-triangular coefficient
coordinates. -/
theorem rademacher_sliceQuadratic_variance (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) :
    uniformVariance (sliceQuadratic f₀ f F) =
      vectorSqNorm f +
        ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), (F i j + F j i) ^ 2 := by
  rw [uniformVariance, rademacher_sliceQuadratic_mean]
  simp_rw [sliceQuadratic_centered_eq_degreeTwoWalshSum]
  rw [uniformExpectation_sq_walsh_sum _ _ degreeTwoMonomialSupport_injective]
  rw [Fintype.sum_sum_type]
  simp only [degreeTwoMonomialCoeff]
  rw [vectorSqNorm]
  congr 1
  simpa only [] using sum_upperPair
    (H := fun i j ↦ (F i j + F j i) ^ 2)

lemma symmetric_upper_pair_sq (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j ∈ Finset.univ.filter (i < ·), (F i j + F j i) ^ 2) =
      2 * frobeniusSq F - 2 * ∑ i, F i i ^ 2 := by
  let U : ℝ := ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), F i j ^ 2
  let D : ℝ := ∑ i, F i i ^ 2
  have hordered : frobeniusSq F = D + 2 * U := by
    rw [frobeniusSq, sum_ordered_eq_trace_add_upper]
    dsimp only [D, U]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hF i j]
    ring
  have hupper :
      (∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        (F i j + F j i) ^ 2) = 4 * U := by
    dsimp only [U]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hF i j]
    ring
  rw [hupper]
  dsimp only [D] at hordered ⊢
  linarith

/-- The Rademacher variance differs from the Gaussian variance only by the
diagonal correction `2 ∑ᵢ Fᵢᵢ²`. -/
theorem rademacher_sliceQuadratic_variance_symmetric
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) :
    uniformVariance (sliceQuadratic f₀ f F) =
      2 * frobeniusSq F + vectorSqNorm f - 2 * ∑ i, F i i ^ 2 := by
  rw [rademacher_sliceQuadratic_variance, symmetric_upper_pair_sq F hF]
  ring

lemma abs_rademacherVariance_sub_gaussianVariance_le
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hFsymm : ∀ i j, F i j = F j i) (hF : ∀ i j, |F i j| ≤ 1) :
    |uniformVariance (sliceQuadratic f₀ f F) -
        (2 * frobeniusSq F + vectorSqNorm f)| ≤ 2 * n := by
  rw [rademacher_sliceQuadratic_variance_symmetric f₀ f F hFsymm]
  have hdiag : (∑ i, F i i ^ 2) ≤ n := by
    calc
      (∑ i, F i i ^ 2) ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs, one_pow] using
          (sq_le_sq₀ (abs_nonneg (F i i)) (by norm_num)).2 (hF i i)
      _ = n := by simp
  have hdiag0 : 0 ≤ ∑ i, F i i ^ 2 := by positivity
  rw [show 2 * frobeniusSq F + vectorSqNorm f - 2 * ∑ i, F i i ^ 2 -
      (2 * frobeniusSq F + vectorSqNorm f) = -2 * ∑ i, F i i ^ 2 by ring]
  rw [abs_mul, abs_of_nonneg hdiag0]
  norm_num
  linarith

end RademacherCube

/-- The joint moments used by the Gaussian mean and variance computation. -/
structure HasStandardGaussianMoments (z : Ω → Fin n → ℝ) : Prop where
  first : ∀ i, uniformExpectation (fun ω ↦ z ω i) = 0
  second : ∀ i j, uniformExpectation (fun ω ↦ z ω i * z ω j) =
    if i = j then 1 else 0
  third : ∀ i j k, uniformExpectation (fun ω ↦ z ω i * z ω j * z ω k) = 0
  fourth : ∀ i j k l,
    uniformExpectation (fun ω ↦ z ω i * z ω j * z ω k * z ω l) =
      (if i = j ∧ k = l then 1 else 0) +
      (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0)

lemma gaussian_linear_mean (z : Ω → Fin n → ℝ) (hz : HasStandardGaussianMoments z)
    (f : Fin n → ℝ) :
    uniformExpectation (fun ω ↦ linearPart f (z ω)) = 0 := by
  simp only [linearPart]
  rw [uniformExpectation_sum]
  simp_rw [uniformExpectation_const_mul, hz.first]
  simp

lemma gaussian_quadratic_mean (z : Ω → Fin n → ℝ)
    (hz : HasStandardGaussianMoments z) (F : Fin n → Fin n → ℝ) :
    uniformExpectation (fun ω ↦ quadraticPart F (z ω)) = trace F := by
  simp only [quadraticPart]
  rw [uniformExpectation_sum]
  simp_rw [uniformExpectation_sum]
  simp_rw [show ∀ (ω : Ω) (i j : Fin n),
      z ω i * F i j * z ω j = F i j * (z ω i * z ω j) by intros; ring]
  simp_rw [uniformExpectation_const_mul, hz.second]
  simp [trace]

/-- Exact expectation identity from KSSS Lemma 11.1 for its Gaussian analog. -/
theorem gaussian_quadraticPolynomial_mean (z : Ω → Fin n → ℝ)
    (hz : HasStandardGaussianMoments z) (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) :
    uniformExpectation (fun ω ↦ quadraticPolynomial f₀ f F (z ω)) =
      f₀ + trace F := by
  simp only [quadraticPolynomial]
  rw [uniformExpectation_add, uniformExpectation_add, uniformExpectation_const,
    gaussian_linear_mean z hz f, gaussian_quadratic_mean z hz F]
  ring

lemma gaussian_linear_sq_mean (z : Ω → Fin n → ℝ)
    (hz : HasStandardGaussianMoments z) (f : Fin n → ℝ) :
    uniformExpectation (fun ω ↦ linearPart f (z ω) ^ 2) = vectorSqNorm f := by
  have hpoint : ∀ ω, linearPart f (z ω) ^ 2 =
      ∑ i, ∑ j, (f j * f i) * (z ω j * z ω i) := by
    intro ω
    simp only [linearPart, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hpoint]
  rw [uniformExpectation_sum]
  simp_rw [uniformExpectation_sum]
  simp_rw [uniformExpectation_const_mul, hz.second]
  classical
  simp [vectorSqNorm, pow_two]

lemma gaussian_linear_mul_centeredQuadratic_mean (z : Ω → Fin n → ℝ)
    (hz : HasStandardGaussianMoments z) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) :
    uniformExpectation (fun ω ↦
      linearPart f (z ω) * (quadraticPart F (z ω) - trace F)) = 0 := by
  have hpoint : ∀ ω,
      linearPart f (z ω) * (quadraticPart F (z ω) - trace F) =
        (∑ i, ∑ j, ∑ k,
          (f i * F j k) * (z ω i * z ω j * z ω k)) -
        ∑ i, (trace F * f i) * z ω i := by
    intro ω
    simp only [linearPart, quadraticPart, mul_sub, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  simp_rw [hpoint]
  rw [uniformExpectation_sub]
  simp_rw [uniformExpectation_sum, uniformExpectation_const_mul, hz.third, hz.first]
  simp

lemma gaussian_quadratic_sq_mean (z : Ω → Fin n → ℝ)
    (hz : HasStandardGaussianMoments z) (F : Fin n → Fin n → ℝ) :
    uniformExpectation (fun ω ↦ quadraticPart F (z ω) ^ 2) =
      trace F ^ 2 + frobeniusSq F + ∑ i, ∑ j, F i j * F j i := by
  have hpoint : ∀ ω, quadraticPart F (z ω) ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (F k l * F i j) * (z ω k * z ω l * z ω i * z ω j) := by
    intro ω
    simp only [quadraticPart, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hpoint]
  rw [uniformExpectation_sum]
  simp_rw [uniformExpectation_sum]
  simp_rw [uniformExpectation_const_mul, hz.fourth]
  classical
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  simp [ite_and, trace, frobeniusSq, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma gaussian_centeredQuadratic_sq_mean (z : Ω → Fin n → ℝ)
    (hz : HasStandardGaussianMoments z) (F : Fin n → Fin n → ℝ) :
    uniformExpectation (fun ω ↦
      (quadraticPart F (z ω) - trace F) ^ 2) =
      frobeniusSq F + ∑ i, ∑ j, F i j * F j i := by
  have hpoint : ∀ ω,
      (quadraticPart F (z ω) - trace F) ^ 2 =
        quadraticPart F (z ω) ^ 2 +
          ((-2 * trace F) * quadraticPart F (z ω) + trace F ^ 2) := by
    intro ω
    ring
  simp_rw [hpoint]
  rw [uniformExpectation_add, uniformExpectation_add,
    gaussian_quadratic_sq_mean z hz F,
    uniformExpectation_const_mul, gaussian_quadratic_mean z hz F,
    uniformExpectation_const]
  ring

lemma symmetric_cross_frobenius (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j * F j i) = frobeniusSq F := by
  simp_rw [← hF]
  simp [frobeniusSq, pow_two]

/-- Exact variance identity from KSSS Lemma 11.1 for its Gaussian analog. -/
theorem gaussian_quadraticPolynomial_variance (z : Ω → Fin n → ℝ)
    (hz : HasStandardGaussianMoments z) (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (hF : ∀ i j, F i j = F j i) :
    uniformVariance (fun ω ↦ quadraticPolynomial f₀ f F (z ω)) =
      2 * frobeniusSq F + vectorSqNorm f := by
  rw [uniformVariance, gaussian_quadraticPolynomial_mean z hz f₀ f F]
  have hpoint : ∀ ω,
      quadraticPolynomial f₀ f F (z ω) - (f₀ + trace F) =
        linearPart f (z ω) + (quadraticPart F (z ω) - trace F) := by
    intro ω
    simp [quadraticPolynomial]
    ring
  simp_rw [hpoint, add_sq]
  rw [uniformExpectation_add, uniformExpectation_add,
    gaussian_linear_sq_mean z hz f,
    gaussian_centeredQuadratic_sq_mean z hz F,
    symmetric_cross_frobenius F hF]
  rw [show uniformExpectation (fun ω ↦
      2 * linearPart f (z ω) * (quadraticPart F (z ω) - trace F)) = 0 by
    simp_rw [show ∀ ω, 2 * linearPart f (z ω) *
        (quadraticPart F (z ω) - trace F) =
        2 * (linearPart f (z ω) * (quadraticPart F (z ω) - trace F)) by intro; ring]
    rw [uniformExpectation_const_mul,
      gaussian_linear_mul_centeredQuadratic_mean z hz f F]
    ring]
  ring

end FiniteMoments

end BooleanSlices
end Erdos88

namespace Erdos88
namespace BooleanSlices

section CouplingTransfer

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

variable {A B : Type*} [Fintype A] [Nonempty A]
  [Fintype B] [Nonempty B]

/-- Probability of an event in the explicit finite coupling. -/
noncomputable def FiniteUniformCoupling.probability (C : FiniteUniformCoupling A B)
    (p : Fin C.size → Prop) [DecidablePred p] : ℝ :=
  ((Finset.univ.filter p).card : ℝ) / C.size

lemma FiniteUniformCoupling.probability_nonneg (C : FiniteUniformCoupling A B)
    (p : Fin C.size → Prop) [DecidablePred p] : 0 ≤ C.probability p := by
  exact div_nonneg (by positivity) (by positivity)

lemma FiniteUniformCoupling.probability_le_one (C : FiniteUniformCoupling A B)
    (p : Fin C.size → Prop) [DecidablePred p] : C.probability p ≤ 1 := by
  rw [probability]
  apply (div_le_one (by exact_mod_cast C.size_pos)).mpr
  exact_mod_cast (by simpa using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin C.size))) p))

/-- The source-exact conclusion type of the two slice couplings: both
marginals are uniform and the displayed event has the required mass. -/
def FiniteUniformCoupling.IsClose (C : FiniteUniformCoupling A B)
    (X : A → ℝ) (Y : B → ℝ)
    (r q : ℝ) : Prop :=
  C.probability (fun ω ↦ |X (C.left ω) - Y (C.right ω)| ≤ r) ≥ 1 - q

/-- A finite uniform coupling.  Equality of every complex-valued test
expectation is a convenient, exact formulation of the two uniform marginals. -/
def IsUniformCoupling {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (left : Ω → A) (right : Ω → B) : Prop :=
  (∀ g : A → ℂ, (𝔼 ω, g (left ω)) = 𝔼 a, g a) ∧
  (∀ g : B → ℂ, (𝔼 ω, g (right ω)) = 𝔼 b, g b)

lemma FiniteUniformCoupling.isUniformCoupling {A B : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) :
    letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
    IsUniformCoupling C.left C.right := by
  exact ⟨C.left_uniform, C.right_uniform⟩

lemma FiniteUniformCoupling.left_uniform_real {A B : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (g : A → ℝ) :
    (𝔼 ω, g (C.left ω)) = 𝔼 a, g a := by
  have h := congrArg Complex.re (C.left_uniform fun a ↦ (g a : ℂ))
  simpa using h

lemma FiniteUniformCoupling.right_uniform_real {A B : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (g : B → ℝ) :
    (𝔼 ω, g (C.right ω)) = 𝔼 b, g b := by
  have h := congrArg Complex.re (C.right_uniform fun b ↦ (g b : ℂ))
  simpa using h

lemma FiniteUniformCoupling.left_uniform_variance {A B : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (g : A → ℝ) :
    letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
    uniformVariance (fun ω ↦ g (C.left ω)) = uniformVariance g := by
  letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
  rw [uniformVariance, uniformVariance]
  have hmean : (𝔼 ω, g (C.left ω)) = 𝔼 a, g a :=
    C.left_uniform_real g
  calc
    (𝔼 ω, (g (C.left ω) - 𝔼 ω, g (C.left ω)) ^ 2) =
        𝔼 ω, (g (C.left ω) - 𝔼 a, g a) ^ 2 := by
      congr 1
      funext ω
      rw [hmean]
    _ = 𝔼 a, (g a - 𝔼 a, g a) ^ 2 :=
      C.left_uniform_real fun a ↦ (g a - uniformExpectation g) ^ 2

lemma FiniteUniformCoupling.right_uniform_variance {A B : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (g : B → ℝ) :
    letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
    uniformVariance (fun ω ↦ g (C.right ω)) = uniformVariance g := by
  letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
  rw [uniformVariance, uniformVariance]
  have hmean : (𝔼 ω, g (C.right ω)) = 𝔼 b, g b :=
    C.right_uniform_real g
  calc
    (𝔼 ω, (g (C.right ω) - 𝔼 ω, g (C.right ω)) ^ 2) =
        𝔼 ω, (g (C.right ω) - 𝔼 b, g b) ^ 2 := by
      congr 1
      funext ω
      rw [hmean]
    _ = 𝔼 b, (g b - 𝔼 b, g b) ^ 2 :=
      C.right_uniform_real fun b ↦ (g b - uniformExpectation g) ^ 2

lemma FiniteUniformCoupling.bad_probability_le_of_isClose
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    (r q : ℝ) (hclose : C.IsClose X Y r q) :
    C.probability (fun ω ↦ r < |X (C.left ω) - Y (C.right ω)|) ≤ q := by
  classical
  let good : Fin C.size → Prop :=
    fun ω ↦ |X (C.left ω) - Y (C.right ω)| ≤ r
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin C.size))) good
  have hcard' :
      ((Finset.univ.filter fun ω ↦ r <
          |X (C.left ω) - Y (C.right ω)|).card : ℝ) +
        ((Finset.univ.filter good).card : ℝ) = C.size := by
    exact_mod_cast (by simpa [good, not_le, add_comm] using hcard)
  have hsize : (0 : ℝ) < C.size := by exact_mod_cast C.size_pos
  change 1 - q ≤
    ((Finset.univ.filter good).card : ℝ) / C.size at hclose
  rw [le_div_iff₀ hsize] at hclose
  rw [FiniteUniformCoupling.probability, div_le_iff₀ hsize]
  nlinarith

lemma FiniteUniformCoupling.expectation_abs_difference_le_of_isClose
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    (r q D : ℝ) (hr : 0 ≤ r) (hD0 : 0 ≤ D)
    (hclose : C.IsClose X Y r q)
    (hD : ∀ ω, |X (C.left ω) - Y (C.right ω)| ≤ D) :
    letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
    uniformExpectation (fun ω ↦ |X (C.left ω) - Y (C.right ω)|) ≤
      r + D * q := by
  letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
  have hbad := C.bad_probability_le_of_isClose X Y r q hclose
  calc
    uniformExpectation (fun ω ↦ |X (C.left ω) - Y (C.right ω)|) ≤
        uniformExpectation (fun ω ↦
          r + if r < |X (C.left ω) - Y (C.right ω)| then D else 0) := by
      apply Finset.expect_le_expect
      intro ω _
      by_cases hω : r < |X (C.left ω) - Y (C.right ω)|
      · simp only [hω, if_true]
        exact (hD ω).trans (by linarith)
      · simp only [hω, if_false, add_zero]
        exact le_of_not_gt hω
    _ = r + D * C.probability
        (fun ω ↦ r < |X (C.left ω) - Y (C.right ω)|) := by
      rw [uniformExpectation, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
      have hsum :
          (∑ ω : Fin C.size,
              (r + if r < |X (C.left ω) - Y (C.right ω)| then D else 0)) =
            (C.size : ℝ) * r +
              ((Finset.univ.filter fun ω ↦
                r < |X (C.left ω) - Y (C.right ω)|).card : ℝ) * D := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite, mul_comm]
      rw [hsum, FiniteUniformCoupling.probability]
      field_simp [Nat.ne_of_gt C.size_pos] <;> ring
    _ ≤ r + D * q := by
      gcongr

/-- Mean transfer from a high-probability coupling.  `D` is a deterministic
bound for the coupled difference; unlike a first-moment hypothesis, it is
available directly for the quadratic polynomials in Section 11. -/
lemma FiniteUniformCoupling.abs_expectation_sub_le_of_isClose
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    (r q D : ℝ) (hr : 0 ≤ r) (hD0 : 0 ≤ D)
    (hclose : C.IsClose X Y r q)
    (hD : ∀ ω, |X (C.left ω) - Y (C.right ω)| ≤ D) :
    |uniformExpectation X - uniformExpectation Y| ≤ r + D * q := by
  letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
  have hbad := C.bad_probability_le_of_isClose X Y r q hclose
  have hmarginal :
      uniformExpectation X - uniformExpectation Y =
        uniformExpectation (fun ω ↦ X (C.left ω) - Y (C.right ω)) := by
    rw [uniformExpectation_sub]
    change (𝔼 a, X a) - (𝔼 b, Y b) =
      (𝔼 ω, X (C.left ω)) - 𝔼 ω, Y (C.right ω)
    rw [C.left_uniform_real X, C.right_uniform_real Y]
  rw [hmarginal]
  calc
    |uniformExpectation (fun ω ↦ X (C.left ω) - Y (C.right ω))| ≤
        uniformExpectation (fun ω ↦ |X (C.left ω) - Y (C.right ω)|) := by
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ uniformExpectation (fun ω ↦
        r + if r < |X (C.left ω) - Y (C.right ω)| then D else 0) := by
      apply Finset.expect_le_expect
      intro ω _
      by_cases hω : r < |X (C.left ω) - Y (C.right ω)|
      · simp only [hω, if_true]
        exact (hD ω).trans (by linarith)
      · simp only [hω, if_false, add_zero]
        exact le_of_not_gt hω
    _ = r + D * C.probability
        (fun ω ↦ r < |X (C.left ω) - Y (C.right ω)|) := by
      rw [uniformExpectation, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
      have hsum :
          (∑ ω : Fin C.size,
              (r + if r < |X (C.left ω) - Y (C.right ω)| then D else 0)) =
            (C.size : ℝ) * r +
              ((Finset.univ.filter fun ω ↦
                r < |X (C.left ω) - Y (C.right ω)|).card : ℝ) * D := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite, mul_comm]
      rw [hsum, FiniteUniformCoupling.probability]
      field_simp [Nat.ne_of_gt C.size_pos] <;> ring
    _ ≤ r + D * q := by
      gcongr

/-- Second-moment transfer for the same coupling.  This is the quantitative
input to the variance comparison in KSSS Lemma 11.1. -/
lemma FiniteUniformCoupling.expectation_sq_difference_le_of_isClose
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    (r q D : ℝ) (hr : 0 ≤ r) (hD0 : 0 ≤ D)
    (hclose : C.IsClose X Y r q)
    (hD : ∀ ω, |X (C.left ω) - Y (C.right ω)| ≤ D) :
    uniformExpectation (fun ω ↦
      (X (C.left ω) - Y (C.right ω)) ^ 2) ≤ r ^ 2 + D ^ 2 * q := by
  letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
  have hbad := C.bad_probability_le_of_isClose X Y r q hclose
  calc
    uniformExpectation (fun ω ↦
        (X (C.left ω) - Y (C.right ω)) ^ 2) ≤
      uniformExpectation (fun ω ↦
        r ^ 2 + if r < |X (C.left ω) - Y (C.right ω)| then D ^ 2 else 0) := by
      apply Finset.expect_le_expect
      intro ω _
      by_cases hω : r < |X (C.left ω) - Y (C.right ω)|
      · simp only [hω, if_true]
        have hsquare : (X (C.left ω) - Y (C.right ω)) ^ 2 ≤ D ^ 2 := by
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg _) hD0).2 (hD ω)
        linarith [sq_nonneg r]
      · simp only [hω, if_false, add_zero]
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hr).2 (le_of_not_gt hω)
    _ = r ^ 2 + D ^ 2 * C.probability
        (fun ω ↦ r < |X (C.left ω) - Y (C.right ω)|) := by
      rw [uniformExpectation, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
      have hsum :
          (∑ ω : Fin C.size,
              (r ^ 2 + if r < |X (C.left ω) - Y (C.right ω)|
                then D ^ 2 else 0)) =
            (C.size : ℝ) * r ^ 2 +
              ((Finset.univ.filter fun ω ↦
                r < |X (C.left ω) - Y (C.right ω)|).card : ℝ) * D ^ 2 := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite, mul_comm]
      rw [hsum, FiniteUniformCoupling.probability]
      field_simp [Nat.ne_of_gt C.size_pos] <;> ring
    _ ≤ r ^ 2 + D ^ 2 * q := by
      gcongr

end CouplingTransfer

end BooleanSlices
end Erdos88

namespace Erdos88
namespace BooleanSlices

section CouplingTransfer

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Characteristic function on a finite uniform probability space. -/
noncomputable def finiteCharacteristic (X : Ω → ℝ) (τ : ℝ) : ℂ :=
  𝔼 ω, Complex.exp (Complex.I * (τ * X ω : ℝ))

lemma finiteCharacteristic_comp_left_eq {A B : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    {left : Ω → A} {right : Ω → B} (h : IsUniformCoupling left right)
    (X : A → ℝ) (τ : ℝ) :
    finiteCharacteristic (X ∘ left) τ = finiteCharacteristic X τ := by
  exact h.1 fun a ↦ Complex.exp (Complex.I * (τ * X a : ℝ))

lemma finiteCharacteristic_comp_right_eq {A B : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    {left : Ω → A} {right : Ω → B} (h : IsUniformCoupling left right)
    (Y : B → ℝ) (τ : ℝ) :
    finiteCharacteristic (Y ∘ right) τ = finiteCharacteristic Y τ := by
  exact h.2 fun b ↦ Complex.exp (Complex.I * (τ * Y b : ℝ))

/-- The fraction of outcomes in a finite uniform model on which `p` holds. -/
noncomputable def eventFraction (p : Ω → Prop) [DecidablePred p] : ℝ :=
  ((Finset.univ.filter p).card : ℝ) / Fintype.card Ω

lemma eventFraction_nonneg (p : Ω → Prop) [DecidablePred p] :
    0 ≤ eventFraction p := by
  exact div_nonneg (by positivity) (by positivity)

lemma eventFraction_le_one (p : Ω → Prop) [DecidablePred p] :
    eventFraction p ≤ 1 := by
  rw [eventFraction]
  apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
  exact_mod_cast Finset.card_filter_le (s := (Finset.univ : Finset Ω)) p

/-- The complex exponential is one-Lipschitz along the imaginary axis. -/
lemma norm_exp_I_mul_sub_exp_I_mul_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) -
        Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have hid :
      Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
        Complex.exp (Complex.I * (b : ℂ)) *
          (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hid, norm_mul, Complex.norm_exp]
  have hre : (Complex.I * (b : ℂ)).re = 0 := by
    rw [Complex.mul_re]
    simp
  rw [hre, Real.exp_zero, one_mul]
  simpa [mul_comm, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

lemma norm_exp_I_mul_sub_exp_I_mul_le_two (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) -
        Complex.exp (Complex.I * (b : ℂ))‖ ≤ 2 := by
  calc
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖
        ≤ ‖Complex.exp (Complex.I * (a : ℂ))‖ +
          ‖Complex.exp (Complex.I * (b : ℂ))‖ := norm_sub_le _ _
    _ = 2 := by
      norm_num [Complex.norm_exp, Complex.mul_re]

/-- The norm of a finite uniform complex average is at most the uniform
average of the pointwise norms. -/
lemma norm_expect_le_expect_norm (Z : Ω → ℂ) :
    ‖𝔼 ω, Z ω‖ ≤ 𝔼 ω, ‖Z ω‖ := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card,
    norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)

/-- Coupling transfer for characteristic functions before a tail estimate is
inserted.  This is the exact analytic step used after Lemmas 11.2 and 11.3. -/
lemma norm_finiteCharacteristic_sub_le (X Y : Ω → ℝ) (τ : ℝ) :
    ‖finiteCharacteristic X τ - finiteCharacteristic Y τ‖ ≤
      𝔼 ω, |τ| * |X ω - Y ω| := by
  rw [finiteCharacteristic, finiteCharacteristic,
    ← Finset.expect_sub_distrib]
  let D : Ω → ℂ := fun ω ↦
    Complex.exp (Complex.I * (τ * X ω : ℝ)) -
      Complex.exp (Complex.I * (τ * Y ω : ℝ))
  calc
    ‖𝔼 ω, D ω‖ ≤ 𝔼 ω, ‖D ω‖ := norm_expect_le_expect_norm D
    _ ≤ 𝔼 ω, |τ| * |X ω - Y ω| := by
      apply Finset.expect_le_expect
      intro ω _
      change ‖Complex.exp (Complex.I * (τ * X ω : ℝ)) -
        Complex.exp (Complex.I * (τ * Y ω : ℝ))‖ ≤ _
      calc
        ‖Complex.exp (Complex.I * (τ * X ω : ℝ)) -
            Complex.exp (Complex.I * (τ * Y ω : ℝ))‖
            ≤ |τ * X ω - τ * Y ω| :=
              norm_exp_I_mul_sub_exp_I_mul_le _ _
        _ = |τ| * |X ω - Y ω| := by rw [← mul_sub, abs_mul]

/-- If a coupling is within `r` except on a fraction `q` of its outcomes,
the characteristic functions differ by at most `|τ| r + 2q`. -/
lemma norm_finiteCharacteristic_sub_le_of_event
    (X Y : Ω → ℝ) (τ r : ℝ) (hr : 0 ≤ r) :
    ‖finiteCharacteristic X τ - finiteCharacteristic Y τ‖ ≤
      |τ| * r + 2 * eventFraction (fun ω ↦ r < |X ω - Y ω|) := by
  classical
  rw [finiteCharacteristic, finiteCharacteristic,
    ← Finset.expect_sub_distrib]
  let D : Ω → ℂ := fun ω ↦
    Complex.exp (Complex.I * (τ * X ω : ℝ)) -
      Complex.exp (Complex.I * (τ * Y ω : ℝ))
  calc
    ‖𝔼 ω, D ω‖ ≤ 𝔼 ω, ‖D ω‖ := norm_expect_le_expect_norm D
    _ ≤ 𝔼 ω, (|τ| * r + if r < |X ω - Y ω| then 2 else 0) := by
      apply Finset.expect_le_expect
      intro ω _
      change ‖Complex.exp (Complex.I * (τ * X ω : ℝ)) -
        Complex.exp (Complex.I * (τ * Y ω : ℝ))‖ ≤ _
      by_cases hbad : r < |X ω - Y ω|
      · simp only [hbad, if_true]
        exact (norm_exp_I_mul_sub_exp_I_mul_le_two _ _).trans
          (by nlinarith [mul_nonneg (abs_nonneg τ) hr])
      · simp only [hbad, if_false, add_zero]
        exact (norm_exp_I_mul_sub_exp_I_mul_le _ _).trans_eq
          (by rw [← mul_sub, abs_mul]) |>.trans
            (mul_le_mul_of_nonneg_left (le_of_not_gt hbad) (abs_nonneg τ))
    _ = |τ| * r + 2 * eventFraction (fun ω ↦ r < |X ω - Y ω|) := by
      rw [Fintype.expect_eq_sum_div_card]
      have hsum :
          (∑ ω : Ω, (|τ| * r + if r < |X ω - Y ω| then 2 else 0)) =
            (Fintype.card Ω : ℝ) * (|τ| * r) +
              ((Finset.univ.filter fun ω ↦ r < |X ω - Y ω|).card : ℝ) * 2 := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite, mul_comm]
      rw [hsum, eventFraction]
      field_simp

/-- Characteristic-function transfer in the public finite-coupling API.
This is the exact deterministic implication used after KSSS Lemmas 11.2
and 11.3. -/
lemma FiniteUniformCoupling.norm_characteristic_sub_le_of_isClose
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    (r q τ : ℝ) (hr : 0 ≤ r) (hclose : C.IsClose X Y r q) :
    ‖finiteCharacteristic X τ - finiteCharacteristic Y τ‖ ≤ |τ| * r + 2 * q := by
  letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
  have hcoupling : IsUniformCoupling C.left C.right := C.isUniformCoupling
  rw [← finiteCharacteristic_comp_left_eq hcoupling X τ,
    ← finiteCharacteristic_comp_right_eq hcoupling Y τ]
  have htransfer := norm_finiteCharacteristic_sub_le_of_event
    (X := X ∘ C.left) (Y := Y ∘ C.right) τ r hr
  have hbad := C.bad_probability_le_of_isClose X Y r q hclose
  have hevent : eventFraction (fun ω : Fin C.size ↦
      r < |(X ∘ C.left) ω - (Y ∘ C.right) ω|) =
      C.probability (fun ω ↦ r < |X (C.left ω) - Y (C.right ω)|) := by
    simp [eventFraction, FiniteUniformCoupling.probability, Function.comp_def]
  rw [hevent] at htransfer
  linarith

/-- Range-sensitive characteristic transfer.  Unlike the bounded integrand
estimate above, this form keeps a factor `|τ|` on the exceptional
probability and is therefore the form used at very small frequencies in
KSSS Lemma 11.1. -/
lemma FiniteUniformCoupling.norm_characteristic_sub_le_of_isClose_range
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    (r q D τ : ℝ) (hr : 0 ≤ r) (hD0 : 0 ≤ D)
    (hclose : C.IsClose X Y r q)
    (hD : ∀ ω, |X (C.left ω) - Y (C.right ω)| ≤ D) :
    ‖finiteCharacteristic X τ - finiteCharacteristic Y τ‖ ≤
      |τ| * (r + D * q) := by
  letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
  have hcoupling : IsUniformCoupling C.left C.right := C.isUniformCoupling
  rw [← finiteCharacteristic_comp_left_eq hcoupling X τ,
    ← finiteCharacteristic_comp_right_eq hcoupling Y τ]
  have hchar := norm_finiteCharacteristic_sub_le
    (X := X ∘ C.left) (Y := Y ∘ C.right) τ
  calc
    ‖finiteCharacteristic (X ∘ C.left) τ -
        finiteCharacteristic (Y ∘ C.right) τ‖ ≤
        uniformExpectation (fun ω ↦
          |τ| * |X (C.left ω) - Y (C.right ω)|) := by
      simpa only [uniformExpectation, Function.comp_apply] using hchar
    _ = |τ| * uniformExpectation (fun ω ↦
        |X (C.left ω) - Y (C.right ω)|) := by
      rw [uniformExpectation_const_mul]
    _ ≤ |τ| * (r + D * q) := by
      exact mul_le_mul_of_nonneg_left
        (C.expectation_abs_difference_le_of_isClose X Y r q D hr hD0 hclose hD)
        (abs_nonneg τ)

section QuadraticCouplingConsequences

variable {n m : ℕ}

/-- The deterministic range used on the exceptional event in the KSSS
slice couplings. -/
noncomputable def ksssQuadraticDifferenceBound (n : ℕ) (δ : ℝ) : ℝ :=
  2 * n * scale n (1 / 2 + 3 * δ) + 2 * n ^ 2

lemma ksssQuadraticDifferenceBound_nonneg (n : ℕ) (δ : ℝ) :
    0 ≤ ksssQuadraticDifferenceBound n δ := by
  unfold ksssQuadraticDifferenceBound
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
      (scale_nonneg n _))
    (mul_nonneg (by norm_num) (sq_nonneg (n : ℝ)))

/-- Exact mean consequence of a slice-to-Rademacher coupling. -/
lemma productSlice_mean_error_of_coupling
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    [Nonempty (ProductSlicePoint P ell)]
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (δ r q : ℝ)
    (hr : 0 ≤ r)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteUniformCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose (productSliceQuadratic P ell f₀ f F)
      (sliceQuadratic f₀ f F) r q) :
    |uniformExpectation (productSliceQuadratic P ell f₀ f F) -
        (f₀ + trace F)| ≤
      r + ksssQuadraticDifferenceBound n δ * q := by
  have hD : ∀ ω,
      |productSliceQuadratic P ell f₀ f F (C.left ω) -
        sliceQuadratic f₀ f F (C.right ω)| ≤
          ksssQuadraticDifferenceBound n δ := by
    intro ω
    simpa only [productSliceQuadratic, ksssQuadraticDifferenceBound,
      mul_one] using
      (abs_sliceQuadratic_sub_le f₀ f F 1
        (scale n (1 / 2 + 3 * δ)) (by norm_num)
        (scale_nonneg n _) hf hF (C.left ω).1 (C.right ω))
  calc
    |uniformExpectation (productSliceQuadratic P ell f₀ f F) -
        (f₀ + trace F)| =
        |uniformExpectation (productSliceQuadratic P ell f₀ f F) -
          uniformExpectation (sliceQuadratic f₀ f F)| := by
      rw [rademacher_sliceQuadratic_mean]
    _ ≤ r + ksssQuadraticDifferenceBound n δ * q :=
      C.abs_expectation_sub_le_of_isClose _ _ r q
        (ksssQuadraticDifferenceBound n δ) hr
        (ksssQuadraticDifferenceBound_nonneg n δ) hclose hD

lemma productSlice_mean_error_ksss_of_coupling
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    [Nonempty (ProductSlicePoint P ell)]
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (δ q : ℝ)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteUniformCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose (productSliceQuadratic P ell f₀ f F)
      (sliceQuadratic f₀ f F) (scale n (3 / 4 + 4 * δ)) q)
    (hexception : ksssQuadraticDifferenceBound n δ * q ≤
      scale n (3 / 4 + 4 * δ)) :
    |uniformExpectation (productSliceQuadratic P ell f₀ f F) -
        (f₀ + trace F)| ≤ 2 * scale n (3 / 4 + 4 * δ) := by
  have h := productSlice_mean_error_of_coupling P ell f₀ f F δ
    (scale n (3 / 4 + 4 * δ)) q (scale_nonneg _ _) hf hF C hclose
  linarith

/-- Exact variance consequence of a slice-to-Rademacher coupling.  The last
`2n` is precisely the diagonal correction between Rademacher and Gaussian
quadratics. -/
lemma productSlice_variance_error_of_coupling
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    [Nonempty (ProductSlicePoint P ell)]
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (δ r q : ℝ)
    (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hFsymm : ∀ i j, F i j = F j i)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteUniformCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose (productSliceQuadratic P ell f₀ f F)
      (sliceQuadratic f₀ f F) r q) :
    |uniformVariance (productSliceQuadratic P ell f₀ f F) -
        (2 * frobeniusSq F + vectorSqNorm f)| ≤
      (r ^ 2 + ksssQuadraticDifferenceBound n δ ^ 2 * q) +
        2 * √((2 * frobeniusSq F + vectorSqNorm f) *
          (r ^ 2 + ksssQuadraticDifferenceBound n δ ^ 2 * q)) + 2 * n := by
  letI : Nonempty (Fin C.size) := Fin.pos_iff_nonempty.mp C.size_pos
  let X : ProductSlicePoint P ell → ℝ := productSliceQuadratic P ell f₀ f F
  let Y : Finset (Fin n) → ℝ := sliceQuadratic f₀ f F
  let D : ℝ := ksssQuadraticDifferenceBound n δ
  let E₂ : ℝ := r ^ 2 + D ^ 2 * q
  have hD0 : 0 ≤ D := ksssQuadraticDifferenceBound_nonneg n δ
  have hE₂0 : 0 ≤ E₂ := by dsimp only [E₂]; positivity
  have hD : ∀ ω, |X (C.left ω) - Y (C.right ω)| ≤ D := by
    intro ω
    dsimp only [X, Y, D]
    simpa only [productSliceQuadratic, ksssQuadraticDifferenceBound,
      mul_one] using
      (abs_sliceQuadratic_sub_le f₀ f F 1
        (scale n (1 / 2 + 3 * δ)) (by norm_num)
        (scale_nonneg n _) hf hF (C.left ω).1 (C.right ω))
  have hsecond : uniformExpectation (fun ω ↦
      (X (C.left ω) - Y (C.right ω)) ^ 2) ≤ E₂ := by
    exact C.expectation_sq_difference_le_of_isClose X Y r q D hr hD0
      hclose hD
  have hYvar0 : 0 ≤ uniformVariance Y := uniformVariance_nonneg Y
  have htarget0 : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f := by
    unfold frobeniusSq vectorSqNorm
    positivity
  have hYtarget : uniformVariance Y ≤
      2 * frobeniusSq F + vectorSqNorm f := by
    rw [show Y = sliceQuadratic f₀ f F by rfl,
      rademacher_sliceQuadratic_variance_symmetric f₀ f F hFsymm]
    have hdiag : 0 ≤ ∑ i, F i i ^ 2 := by positivity
    linarith
  have hsame := abs_uniformVariance_sub_le
    (fun ω ↦ X (C.left ω)) (fun ω ↦ Y (C.right ω))
  have hsecond0 : 0 ≤ uniformExpectation (fun ω ↦
      (X (C.left ω) - Y (C.right ω)) ^ 2) := by
    rw [uniformExpectation, Fintype.expect_eq_sum_div_card]
    positivity
  have hsqrt :
      √(uniformVariance (fun ω ↦ Y (C.right ω)) *
          uniformExpectation (fun ω ↦
            (X (C.left ω) - Y (C.right ω)) ^ 2)) ≤
        √((2 * frobeniusSq F + vectorSqNorm f) * E₂) := by
    apply Real.sqrt_le_sqrt
    rw [C.right_uniform_variance Y]
    exact mul_le_mul hYtarget hsecond hsecond0 htarget0
  have hXY : |uniformVariance X - uniformVariance Y| ≤
      E₂ + 2 * √((2 * frobeniusSq F + vectorSqNorm f) * E₂) := by
    rw [← C.left_uniform_variance X, ← C.right_uniform_variance Y]
    exact hsame.trans (add_le_add hsecond (mul_le_mul_of_nonneg_left hsqrt (by norm_num)))
  have hdiag := abs_rademacherVariance_sub_gaussianVariance_le
    f₀ f F hFsymm hF
  change |uniformVariance X - (2 * frobeniusSq F + vectorSqNorm f)| ≤ _
  calc
    |uniformVariance X - (2 * frobeniusSq F + vectorSqNorm f)| ≤
        |uniformVariance X - uniformVariance Y| +
          |uniformVariance Y - (2 * frobeniusSq F + vectorSqNorm f)| := by
      rw [show uniformVariance X - (2 * frobeniusSq F + vectorSqNorm f) =
        (uniformVariance X - uniformVariance Y) +
          (uniformVariance Y - (2 * frobeniusSq F + vectorSqNorm f)) by ring]
      exact abs_add_le _ _
    _ ≤ E₂ + 2 * √((2 * frobeniusSq F + vectorSqNorm f) * E₂) +
        2 * n := by
      gcongr

/-- Exponent arithmetic for the variance part of KSSS Lemma 11.1.  Once
the coupling's exceptional contribution is at most one further copy of the
main squared error, the exact source exponent is `7/4 + 7δ`. -/
lemma productSlice_variance_error_ksss_of_coupling
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    [Nonempty (ProductSlicePoint P ell)]
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (δ q : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 4) (hn : 1 ≤ n) (hq : 0 ≤ q)
    (hFsymm : ∀ i j, F i j = F j i)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteUniformCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose (productSliceQuadratic P ell f₀ f F)
      (sliceQuadratic f₀ f F) (scale n (3 / 4 + 4 * δ)) q)
    (hexception : ksssQuadraticDifferenceBound n δ ^ 2 * q ≤
      scale n (3 / 4 + 4 * δ) ^ 2) :
    |uniformVariance (productSliceQuadratic P ell f₀ f F) -
        (2 * frobeniusSq F + vectorSqNorm f)| ≤
      10 * scale n (7 / 4 + 7 * δ) := by
  let r : ℝ := scale n (3 / 4 + 4 * δ)
  let E₂ : ℝ := r ^ 2 + ksssQuadraticDifferenceBound n δ ^ 2 * q
  let T : ℝ := scale n (2 + 6 * δ)
  let S : ℝ := scale n (7 / 4 + 7 * δ)
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hr0 : 0 ≤ r := scale_nonneg _ _
  have hE₂0 : 0 ≤ E₂ := by
    dsimp only [E₂]
    exact add_nonneg (sq_nonneg r)
      (mul_nonneg (sq_nonneg _) hq)
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    exact scale_nonneg n _
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    exact scale_nonneg n _
  have hE₂ : E₂ ≤ 2 * r ^ 2 := by
    dsimp only [E₂]
    linarith
  have htarget : 2 * frobeniusSq F + vectorSqNorm f ≤ 3 * T := by
    exact gaussianVarianceTarget_le_ksss δ hδ0 hn f F hf hF
  have hrSq : r ^ 2 = scale n (3 / 2 + 8 * δ) := by
    dsimp only [r]
    rw [scale_sq (Nat.zero_le n)]
    congr 1
    ring
  have hrSq_le_S : r ^ 2 ≤ S := by
    rw [hrSq]
    apply scale_mono_exponent hn
    linarith
  have hE₂S : E₂ ≤ 2 * S := hE₂.trans (by gcongr)
  have hTS : T * r ^ 2 = S ^ 2 := by
    rw [hrSq]
    calc
      T * scale n (3 / 2 + 8 * δ) =
          scale n ((2 + 6 * δ) + (3 / 2 + 8 * δ)) := by
        exact scale_mul hnpos _ _
      _ = scale n ((7 / 4 + 7 * δ) * 2) := by congr 1 <;> ring
      _ = S ^ 2 := by
        symm
        exact scale_sq (Nat.zero_le n) _
  have hproduct :
      (2 * frobeniusSq F + vectorSqNorm f) * E₂ ≤ 6 * S ^ 2 := by
    calc
      (2 * frobeniusSq F + vectorSqNorm f) * E₂ ≤
          (3 * T) * (2 * r ^ 2) := by
        exact mul_le_mul htarget hE₂ hE₂0
          (mul_nonneg (by norm_num) hT0)
      _ = 6 * S ^ 2 := by rw [← hTS]; ring
  have hsqrt :
      √((2 * frobeniusSq F + vectorSqNorm f) * E₂) ≤ 3 * S := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact mul_nonneg (by norm_num) hS0
    · calc
        (2 * frobeniusSq F + vectorSqNorm f) * E₂ ≤ 6 * S ^ 2 := hproduct
        _ ≤ (3 * S) ^ 2 := by nlinarith [sq_nonneg S]
  have hnS : (n : ℝ) ≤ S := by
    change (n : ℝ) ≤ Real.rpow (n : ℝ) (7 / 4 + 7 * δ)
    calc
      (n : ℝ) = Real.rpow (n : ℝ) 1 :=
        (Real.rpow_one (n : ℝ)).symm
      _ ≤ Real.rpow (n : ℝ) (7 / 4 + 7 * δ) :=
        Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
          (by linarith)
  have hbase := productSlice_variance_error_of_coupling P ell f₀ f F δ r q
    hr0 hq hFsymm hf hF C hclose
  change |uniformVariance (productSliceQuadratic P ell f₀ f F) -
      (2 * frobeniusSq F + vectorSqNorm f)| ≤ 10 * S
  exact hbase.trans (by
    change E₂ + 2 * √((2 * frobeniusSq F + vectorSqNorm f) * E₂) +
      2 * n ≤ 10 * S
    linarith)

end QuadraticCouplingConsequences

end CouplingTransfer

end BooleanSlices
end Erdos88
