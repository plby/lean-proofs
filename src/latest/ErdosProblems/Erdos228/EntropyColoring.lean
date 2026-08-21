/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Powerset
import Mathlib.InformationTheory.Hamming

/-!
# Finite counting tools for partial colouring

A profile map with few values has a large fibre.  If every near-neighbourhood
is smaller than that fibre, the fibre contains two far-apart points.  This is
the deterministic pigeonhole step in entropy proofs of partial-colouring
lemmas.
-/

open scoped BigOperators

namespace Erdos228.EntropyColoring

open Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A finite profile map has a same-profile pair outside a prescribed
neighbourhood as soon as `card β * k < card α` and every neighbourhood has
cardinality at most `k`. -/
theorem exists_sameProfile_not_mem_near
    (profile : α → β) (near : α → Finset α) (k : ℕ)
    (hnear : ∀ x, (near x).card ≤ k)
    (hcard : Fintype.card β * k < Fintype.card α) :
    ∃ x y, profile x = profile y ∧ y ∉ near x := by
  classical
  obtain ⟨b, hb⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := profile) hcard
  let fiber : Finset α := Finset.univ.filter fun x ↦ profile x = b
  have hfiber : k < fiber.card := by simpa [fiber] using hb
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le k) hfiber)
  have houtside : ∃ y ∈ fiber, y ∉ near x := by
    by_contra! h
    have hsub : fiber ⊆ near x := fun y hy ↦ h y hy
    exact (Nat.not_lt_of_ge ((Finset.card_le_card hsub).trans (hnear x))) hfiber
  obtain ⟨y, hy, hyfar⟩ := houtside
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact ⟨x, y, hx.trans hy.symm, hyfar⟩

/-- Finset version of `exists_sameProfile_not_mem_near`.  Unlike the type-level
version, the profile codomain need not be finite; only the image on `s` is
counted. -/
theorem Finset.exists_sameProfile_not_mem_near
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (profile : α → β) (near : α → Finset α) (k : ℕ)
    (hnear : ∀ x ∈ s, (near x).card ≤ k)
    (hcard : (s.image profile).card * k < s.card) :
    ∃ x ∈ s, ∃ y ∈ s, profile x = profile y ∧ y ∉ near x := by
  obtain ⟨b, hbimage, hb⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := s) (t := s.image profile) (f := profile)
      (fun x hx ↦ Finset.mem_image.mpr ⟨x, hx, rfl⟩) hcard
  let fiber : Finset α := s.filter fun x ↦ profile x = b
  have hfiber : k < fiber.card := by simpa [fiber] using hb
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le k) hfiber)
  have hx' : x ∈ s ∧ profile x = b := by simpa [fiber] using hx
  have houtside : ∃ y ∈ fiber, y ∉ near x := by
    by_contra! h
    have hsub : fiber ⊆ near x := fun y hy ↦ h y hy
    exact (Nat.not_lt_of_ge
      ((Finset.card_le_card hsub).trans (hnear x hx'.1))) hfiber
  obtain ⟨y, hy, hyfar⟩ := houtside
  have hy' : y ∈ s ∧ profile y = b := by simpa [fiber] using hy
  exact ⟨x, hx'.1, y, hy'.1, hx'.2.trans hy'.2.symm, hyfar⟩

section BooleanCube

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Coordinates on which two Boolean cube points differ. -/
def diffSet (x y : I → Bool) : Finset I :=
  Finset.univ.filter fun i ↦ x i ≠ y i

/-- Flip exactly the coordinates in `s`. -/
def flipOn (x : I → Bool) (s : Finset I) : I → Bool :=
  fun i ↦ if i ∈ s then !x i else x i

@[simp] theorem card_diffSet (x y : I → Bool) :
    (diffSet x y).card = hammingDist x y := by
  rfl

@[simp] theorem diffSet_flipOn (x : I → Bool) (s : Finset I) :
    diffSet x (flipOn x s) = s := by
  ext i
  simp [diffSet, flipOn]

@[simp] theorem flipOn_diffSet (x y : I → Bool) :
    flipOn x (diffSet x y) = y := by
  funext i
  by_cases h : x i = y i
  · simp [flipOn, diffSet, h]
  · have hnot : (!x i) = y i := Bool.not_eq_iff.mpr h
    simp [flipOn, diffSet, h, hnot]

theorem diffSet_right_injective (x : I → Bool) :
    Function.Injective (diffSet x) := by
  intro y z h
  rw [← flipOn_diffSet x y, ← flipOn_diffSet x z, h]

/-- The Hamming sphere of radius `k` around a Boolean cube point. -/
def hammingSphere (x : I → Bool) (k : ℕ) : Finset (I → Bool) :=
  Finset.univ.filter fun y ↦ hammingDist x y = k

/-- Exact cardinality of a Boolean Hamming sphere.  Mathlib has Hamming
distance and fixed-cardinality powersets, but does not currently connect
their cardinalities. -/
theorem card_hammingSphere (x : I → Bool) (k : ℕ) :
    (hammingSphere x k).card = Nat.choose (Fintype.card I) k := by
  calc
    (hammingSphere x k).card =
        ((Finset.univ : Finset I).powersetCard k).card := by
      apply Finset.card_bij (fun y _ ↦ diffSet x y)
      · intro y hy
        have hy' : hammingDist x y = k := by
          simpa [hammingSphere] using hy
        exact Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, by simpa using hy'⟩
      · intro y₁ _ y₂ _ h
        exact diffSet_right_injective x h
      · intro s hs
        refine ⟨flipOn x s, ?_, ?_⟩
        · have hscard : s.card = k := (Finset.mem_powersetCard.mp hs).2
          simp [hammingSphere, ← card_diffSet, hscard]
        · exact diffSet_flipOn x s
    _ = Nat.choose (Fintype.card I) k := by simp

/-- The strict Hamming ball of radius `r`. -/
def hammingBall (x : I → Bool) (r : ℕ) : Finset (I → Bool) :=
  Finset.univ.filter fun y ↦ hammingDist x y < r

/-- A strict Boolean Hamming ball has at most the usual binomial-tail
cardinality.  (In fact equality holds; the upper bound is the form needed by
the pigeonhole step.) -/
theorem card_hammingBall_le (x : I → Bool) (r : ℕ) :
    (hammingBall x r).card ≤
      ∑ k ∈ Finset.range r, Nat.choose (Fintype.card I) k := by
  let pieces : Finset (Finset I) :=
    (Finset.range r).biUnion fun k ↦
      (Finset.univ : Finset I).powersetCard k
  have himage :
      (hammingBall x r).image (diffSet x) ⊆ pieces := by
    intro s hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hs
    have hyr : hammingDist x y < r := by
      simpa [hammingBall] using hy
    apply Finset.mem_biUnion.mpr
    refine ⟨hammingDist x y, Finset.mem_range.mpr hyr, ?_⟩
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, by simp⟩
  calc
    (hammingBall x r).card =
        ((hammingBall x r).image (diffSet x)).card := by
      symm
      exact Finset.card_image_of_injective _ (diffSet_right_injective x)
    _ ≤ pieces.card := Finset.card_le_card himage
    _ ≤ ∑ k ∈ Finset.range r,
        ((Finset.univ : Finset I).powersetCard k).card := by
      exact Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.range r, Nat.choose (Fintype.card I) k := by simp

/-- Finite entropy/pigeonhole core for the Boolean cube: if the number of
profiles times a Hamming-ball bound is smaller than the cube, then one profile
class contains two points at Hamming distance at least `r`. -/
theorem exists_sameProfile_hammingDist_ge
    {β : Type*} [Fintype β] (profile : (I → Bool) → β) (r : ℕ)
    (hcard :
      Fintype.card β *
          (∑ k ∈ Finset.range r, Nat.choose (Fintype.card I) k) <
        2 ^ Fintype.card I) :
    ∃ x y, profile x = profile y ∧ r ≤ hammingDist x y := by
  let near : (I → Bool) → Finset (I → Bool) := fun x ↦ hammingBall x r
  have hcube : Fintype.card (I → Bool) = 2 ^ Fintype.card I := by
    simp
  obtain ⟨x, y, hprofile, hfar⟩ :=
    exists_sameProfile_not_mem_near profile near
      (∑ k ∈ Finset.range r, Nat.choose (Fintype.card I) k)
      (fun x ↦ card_hammingBall_le x r) (by simpa [hcube] using hcard)
  refine ⟨x, y, hprofile, ?_⟩
  simpa [near, hammingBall] using hfar

/-- Image-cardinality version of the Boolean-cube pigeonhole lemma.  This is
the form used by rounded profiles, whose codomain is typically `J → ℤ` and
hence not a finite type. -/
theorem exists_sameProfile_hammingDist_ge_of_image
    {β : Type*} [DecidableEq β] (profile : (I → Bool) → β) (r : ℕ)
    (hcard :
      ((Finset.univ : Finset (I → Bool)).image profile).card *
          (∑ k ∈ Finset.range r, Nat.choose (Fintype.card I) k) <
        2 ^ Fintype.card I) :
    ∃ x y, profile x = profile y ∧ r ≤ hammingDist x y := by
  let near : (I → Bool) → Finset (I → Bool) := fun x ↦ hammingBall x r
  have hcube : (Finset.univ : Finset (I → Bool)).card =
      2 ^ Fintype.card I := by simp
  obtain ⟨x, _, y, _, hprofile, hfar⟩ :=
    Finset.exists_sameProfile_not_mem_near
      (Finset.univ : Finset (I → Bool)) profile near
      (∑ k ∈ Finset.range r, Nat.choose (Fintype.card I) k)
      (fun x _ ↦ card_hammingBall_le x r) (by simpa [hcube] using hcard)
  refine ⟨x, y, hprofile, ?_⟩
  simpa [near, hammingBall] using hfar

/-- Same-profile Hamming separation inside an arbitrary large set of cube
points.  This is the convenient endpoint for a typical-set entropy argument. -/
theorem Finset.exists_sameProfile_hammingDist_ge
    {β : Type*} [DecidableEq β] (s : Finset (I → Bool))
    (profile : (I → Bool) → β) (r : ℕ)
    (hcard :
      (s.image profile).card *
          (∑ k ∈ Finset.range r, Nat.choose (Fintype.card I) k) <
        s.card) :
    ∃ x ∈ s, ∃ y ∈ s,
      profile x = profile y ∧ r ≤ hammingDist x y := by
  let near : (I → Bool) → Finset (I → Bool) := fun x ↦ hammingBall x r
  obtain ⟨x, hx, y, hy, hprofile, hfar⟩ :=
    Finset.exists_sameProfile_not_mem_near s profile near
      (∑ k ∈ Finset.range r, Nat.choose (Fintype.card I) k)
      (fun x _ ↦ card_hammingBall_le x r) hcard
  refine ⟨x, hx, y, hy, hprofile, ?_⟩
  simpa [near, hammingBall] using hfar

/-! ## Rounded linear-form profiles -/

/-- The usual embedding of a Boolean value as a sign. -/
def boolSign : Bool → ℝ
  | false => -1
  | true => 1

@[simp] theorem boolSign_false : boolSign false = -1 := rfl

@[simp] theorem boolSign_true : boolSign true = 1 := rfl

/-- Half the difference of two Boolean sign vectors. -/
noncomputable def partialSign (x y : I → Bool) : I → ℝ :=
  fun i ↦ (boolSign (x i) - boolSign (y i)) / 2

/-- The nonzero support of `partialSign`. -/
noncomputable def partialSupport (x y : I → Bool) : Finset I :=
  Finset.univ.filter fun i ↦ partialSign x y i ≠ 0

theorem partialSupport_eq_diffSet (x y : I → Bool) :
    partialSupport x y = diffSet x y := by
  ext i
  cases hx : x i <;> cases hy : y i <;>
    simp [partialSupport, partialSign, diffSet, hx, hy] <;> norm_num

theorem partialSign_mem (x y : I → Bool) (i : I) :
    partialSign x y i = 0 ∨
      partialSign x y i = 1 ∨ partialSign x y i = -1 := by
  cases hx : x i <;> cases hy : y i <;>
    simp [partialSign, hx, hy] <;> norm_num

theorem abs_partialSign_le_one (x y : I → Bool) (i : I) :
    |partialSign x y i| ≤ 1 := by
  obtain h | h | h := partialSign_mem x y i <;> rw [h] <;> norm_num

/-- For a partial sign vector, nonzero coordinates are exactly coordinates
which have absolute value one. -/
theorem partialSupport_eq_filter_abs_eq_one (x y : I → Bool) :
    partialSupport x y =
      Finset.univ.filter fun i ↦ |partialSign x y i| = 1 := by
  ext i
  obtain h | h | h := partialSign_mem x y i <;>
    simp [partialSupport, h]

@[simp] theorem card_partialSupport (x y : I → Bool) :
    (partialSupport x y).card = hammingDist x y := by
  rw [partialSupport_eq_diffSet, card_diffSet]

/-- A linear form evaluated at a Boolean sign vector. -/
def rademacherDot (x : I → Bool) (v : I → ℝ) : ℝ :=
  ∑ i, boolSign (x i) * v i

/-- The same linear form evaluated at the partial sign vector. -/
noncomputable def partialDot (x y : I → Bool) (v : I → ℝ) : ℝ :=
  ∑ i, partialSign x y i * v i

theorem partialDot_eq (x y : I → Bool) (v : I → ℝ) :
    partialDot x y v = (rademacherDot x v - rademacherDot y v) / 2 := by
  rw [partialDot, rademacherDot, rademacherDot,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [partialSign]
  ring

/-- Bucket a real number into half-open intervals of length `2 * width`, with
the central bucket centred at zero. -/
noncomputable def roundedBucket (width value : ℝ) : ℤ :=
  ⌊value / (2 * width) + 1 / 2⌋

theorem roundedBucket_eq_zero_of_abs_lt
    {width value : ℝ} (hwidth : 0 < width) (hvalue : |value| < width) :
    roundedBucket width value = 0 := by
  have hden : 0 < 2 * width := mul_pos (by norm_num) hwidth
  have hwne : width ≠ 0 := ne_of_gt hwidth
  have hleft : (-width) / (2 * width) = (-1 / 2 : ℝ) := by
    field_simp
  have hright : width / (2 * width) = (1 / 2 : ℝ) := by
    field_simp
  have hlower := (div_lt_div_iff_of_pos_right hden).mpr (abs_lt.mp hvalue).1
  have hupper := (div_lt_div_iff_of_pos_right hden).mpr (abs_lt.mp hvalue).2
  rw [hleft] at hlower
  rw [hright] at hupper
  rw [roundedBucket, Int.floor_eq_zero_iff]
  constructor <;> linarith

theorem width_le_abs_of_roundedBucket_ne_zero
    {width value : ℝ} (hwidth : 0 < width)
    (hzero : roundedBucket width value ≠ 0) :
    width ≤ |value| := by
  contrapose! hzero
  exact roundedBucket_eq_zero_of_abs_lt hwidth hzero

/-- Equal positive-width buckets contain values less than `2 * width` apart. -/
theorem abs_sub_lt_two_mul_of_roundedBucket_eq
    {width a b : ℝ} (hwidth : 0 < width)
    (h : roundedBucket width a = roundedBucket width b) :
    |a - b| < 2 * width := by
  change ⌊a / (2 * width) + 1 / 2⌋ =
    ⌊b / (2 * width) + 1 / 2⌋ at h
  have hfloor : |a / (2 * width) - b / (2 * width)| < 1 :=
    by simpa only [add_sub_add_right_eq_sub] using
      (Int.abs_sub_lt_one_of_floor_eq_floor h)
  have hscaled : |(a - b) / (2 * width)| < 1 := by
    simpa only [sub_div] using hfloor
  have hden : 0 < 2 * width := mul_pos (by norm_num) hwidth
  rw [abs_div, abs_of_pos hden] at hscaled
  exact (div_lt_one hden).mp hscaled

/-- Coordinatewise rounded profile of all the prescribed linear forms. -/
noncomputable def roundedLinearProfile
    {J : Type*} (v : J → I → ℝ) (width : J → ℝ) (x : I → Bool) : J → ℤ :=
  fun j ↦ roundedBucket (width j) (rademacherDot x (v j))

/-- A collision of rounded profiles gives all the desired strict discrepancy
bounds for the associated partial sign vector. -/
theorem abs_partialDot_lt_of_roundedLinearProfile_eq
    {J : Type*} (v : J → I → ℝ) (width : J → ℝ)
    (hwidth : ∀ j, 0 < width j) {x y : I → Bool}
    (hprofile : roundedLinearProfile v width x =
      roundedLinearProfile v width y) (j : J) :
    |partialDot x y (v j)| < width j := by
  have hbucket :
      roundedBucket (width j) (rademacherDot x (v j)) =
        roundedBucket (width j) (rademacherDot y (v j)) :=
    congrFun hprofile j
  have hdiff :=
    abs_sub_lt_two_mul_of_roundedBucket_eq (hwidth j) hbucket
  rw [partialDot_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by
    simpa only [mul_comm] using hdiff)

/-- Deterministic rounded-profile partial colouring.  The remaining analytic
task in an entropy proof is exactly the displayed image-cardinality bound. -/
theorem exists_partialSign_of_roundedProfile_image_bound
    {J : Type*} [Fintype J] (v : J → I → ℝ) (width : J → ℝ)
    (hwidth : ∀ j, 0 < width j) (r : ℕ)
    (hcard :
      ((Finset.univ : Finset (I → Bool)).image
          (roundedLinearProfile v width)).card *
          (∑ k ∈ Finset.range r, Nat.choose (Fintype.card I) k) <
        2 ^ Fintype.card I) :
    ∃ x y : I → Bool,
      r ≤ (partialSupport x y).card ∧
        ∀ j, |partialDot x y (v j)| < width j := by
  obtain ⟨x, y, hprofile, hdist⟩ :=
    exists_sameProfile_hammingDist_ge_of_image
      (roundedLinearProfile v width) r hcard
  refine ⟨x, y, ?_, fun j ↦ ?_⟩
  · simpa only [card_partialSupport] using hdist
  · exact abs_partialDot_lt_of_roundedLinearProfile_eq
      v width hwidth hprofile j

/-- Typical-set version of the deterministic rounded-profile partial
colouring lemma. -/
theorem Finset.exists_partialSign_of_roundedProfile_image_bound
    {J : Type*} [Fintype J] (s : Finset (I → Bool))
    (v : J → I → ℝ) (width : J → ℝ)
    (hwidth : ∀ j, 0 < width j) (r : ℕ)
    (hcard :
      (s.image (roundedLinearProfile v width)).card *
          (∑ k ∈ Finset.range r, Nat.choose (Fintype.card I) k) <
        s.card) :
    ∃ x ∈ s, ∃ y ∈ s,
      r ≤ (partialSupport x y).card ∧
        ∀ j, |partialDot x y (v j)| < width j := by
  obtain ⟨x, hx, y, hy, hprofile, hdist⟩ :=
    Finset.exists_sameProfile_hammingDist_ge
      s (roundedLinearProfile v width) r hcard
  refine ⟨x, hx, y, hy, ?_, fun j ↦ ?_⟩
  · simpa only [card_partialSupport] using hdist
  · exact abs_partialDot_lt_of_roundedLinearProfile_eq
      v width hwidth hprofile j

end BooleanCube

end Erdos228.EntropyColoring
