/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.IntegerBoxCount
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Bilu's badly-approximable systems

This file formalizes Definition 6.7 and the measure-theoretic core of
Lemma 6.8 in Yuri Bilu, *Structure of sets with small sumset*, Astérisque
258 (1999), pp. 77--108.

Bilu writes `‖z‖_B > C`, where `B` is a symmetric convex body.  For the
measure argument only the corresponding sublevel set matters, so we express
the strict inequality without choosing a gauge: `z ∉ C • B`.  For a convex
body containing the origin this is precisely the source definition (with
the usual harmless convention on the boundary).
-/

open scoped BigOperators ENNReal Pointwise
open MeasureTheory Set

namespace Erdos186.CFP.Bilu.BadlyApproximable

/-- Coordinatewise formulation of the strict sup-norm bound `‖x‖∞ < X`.
This avoids making an arbitrary norm choice on integer coordinate vectors. -/
def CoordBound {d : ℕ} (X : ℝ) (x : Fin d → ℤ) : Prop :=
  ∀ i, |(x i : ℝ)| < X

/-- The real vector represented by an integer coordinate vector. -/
def integerPoint {d : ℕ} (x : Fin d → ℤ) : Fin d → ℝ :=
  fun i ↦ (x i : ℝ)

/-- The linear combination of a system of real vectors with integer
coefficients. -/
def integerCombination {n r : ℕ} (a : Fin r → Fin n → ℝ)
    (y : Fin r → ℤ) : Fin n → ℝ :=
  ∑ i, (y i : ℝ) • a i

/-- Bilu's Definition 6.7.  A system `a₁, …, aᵣ` is `(B,X,C)`-badly
approximable if every nontrivial integer combination with coefficient sup
norm below `X` stays outside every translate `x + C • B` with
`‖x‖∞ < X`. -/
def IsBadlyApproximable {n r : ℕ} (B : Set (Fin n → ℝ))
    (X C : ℝ) (a : Fin r → Fin n → ℝ) : Prop :=
  ∀ (x : Fin n → ℤ) (y : Fin r → ℤ),
    CoordBound X x →
    (∃ i, y i ≠ 0) →
    CoordBound X y →
    integerCombination a y - integerPoint x ∉ C • B

/-- Restriction of an infinite sequence to its first `r` entries, phrased
using Definition 6.7.  This presentation makes Bilu's induction literal. -/
def IsBadlyApproximableUpTo {n : ℕ} (B : Set (Fin n → ℝ))
    (X C : ℝ) (r : ℕ) (a : ℕ → Fin n → ℝ) : Prop :=
  IsBadlyApproximable B X C (fun i : Fin r ↦ a i)

/-- The bad affine slice belonging to fixed earlier contribution `v`,
nonzero integer coefficient `q`, and integer point `x`. -/
def badAffineSlice {n : ℕ} (B : Set (Fin n → ℝ)) (C : ℝ)
    (v : Fin n → ℝ) (q : ℤ) (x : Fin n → ℤ) : Set (Fin n → ℝ) :=
  {z | v + (q : ℝ) • z - integerPoint x ∈ C • B}

/-- Exact volume of one affine obstruction.  This is the change-of-variables
calculation in the proof of Bilu's Lemma 6.8. -/
theorem volume_badAffineSlice {n : ℕ} (B : Set (Fin n → ℝ)) (C : ℝ)
    (v : Fin n → ℝ) (q : ℤ) (x : Fin n → ℤ) (hq : q ≠ 0) :
    volume (badAffineSlice B C v q x) =
      ENNReal.ofReal (abs (((q : ℝ) ^ n))⁻¹) *
        (ENNReal.ofReal (abs (C ^ n)) * volume B) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  let T : Set (Fin n → ℝ) :=
    (fun w ↦ (v - integerPoint x) + w) ⁻¹' (C • B)
  have hset : badAffineSlice B C v q x = ((q : ℝ) • ·) ⁻¹' T := by
    ext z
    simp only [badAffineSlice, mem_ofPred_eq, T, mem_preimage]
    rw [show v + (q : ℝ) • z - integerPoint x =
        (v - integerPoint x) + (q : ℝ) • z by module]
  rw [hset, volume.addHaar_preimage_smul hqR]
  have hT : volume T = volume (C • B) := by
    simpa [T] using
      (measure_preimage_add volume (v - integerPoint x) (C • B))
  rw [hT, volume.addHaar_smul]
  simp only [Module.finrank_fin_fun ℝ]

/-- An integer coefficient has absolute value at least one, so a bad affine
slice has volume at most the volume of `C • B`. -/
theorem volume_badAffineSlice_le {n : ℕ} (B : Set (Fin n → ℝ))
    {C : ℝ} (hC : 0 ≤ C) (v : Fin n → ℝ) (q : ℤ)
    (x : Fin n → ℤ) (hq : q ≠ 0) :
    volume (badAffineSlice B C v q x) ≤
      ENNReal.ofReal (C ^ n) * volume B := by
  rw [volume_badAffineSlice B C v q x hq]
  rw [abs_of_nonneg (pow_nonneg hC n)]
  have hqabs : (1 : ℝ) ≤ |(q : ℝ)| := by
    exact_mod_cast Int.one_le_abs hq
  have hpow : (1 : ℝ) ≤ |(q : ℝ) ^ n| := by
    rw [abs_pow]
    exact one_le_pow₀ hqabs
  have hinv : |((q : ℝ) ^ n)|⁻¹ ≤ 1 :=
    (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hpow)).2 hpow
  have hfac : ENNReal.ofReal |((q : ℝ) ^ n)⁻¹| ≤ 1 := by
    rw [abs_inv]
    exact ENNReal.ofReal_le_one.mpr hinv
  calc
    ENNReal.ofReal |((q : ℝ) ^ n)⁻¹| *
          (ENNReal.ofReal (C ^ n) * volume B)
        ≤ 1 * (ENNReal.ofReal (C ^ n) * volume B) :=
      mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = ENNReal.ofReal (C ^ n) * volume B := one_mul _

/-- Affine obstructions are measurable whenever the convex body is
measurable and the dilation parameter is nonzero. -/
theorem measurableSet_badAffineSlice {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : MeasurableSet B) {C : ℝ} (hC : C ≠ 0)
    (v : Fin n → ℝ) (q : ℤ) (x : Fin n → ℤ) :
    MeasurableSet (badAffineSlice B C v q x) := by
  have hCB : MeasurableSet (C • B) := by
    rw [← image_smul]
    exact (Homeomorph.smul (isUnit_iff_ne_zero.mpr hC).unit).toMeasurableEquiv
      |>.measurableSet_image.mpr hB
  exact hCB.preimage
    (((continuous_const.add (continuous_const_smul (q : ℝ))).sub continuous_const).measurable)

/-- Contribution of the first `k` coefficients when adjoining one new
vector at the last coordinate. -/
def previousContribution {n k : ℕ} (a : ℕ → Fin n → ℝ)
    (y : Fin (k + 1) → ℤ) : Fin n → ℝ :=
  ∑ i : Fin k, (y i.castSucc : ℝ) • a i

/-- Splitting the last term of the integer combination after an update. -/
theorem integerCombination_update_eq {n k : ℕ} (a : ℕ → Fin n → ℝ)
    (z : Fin n → ℝ) (y : Fin (k + 1) → ℤ) :
    integerCombination
        (fun i : Fin (k + 1) ↦ Function.update a k z i) y =
      previousContribution a y + (y (Fin.last k) : ℝ) • z := by
  rw [integerCombination, previousContribution, Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    change (y i.castSucc : ℝ) • Function.update a k z i.val =
      (y i.castSucc : ℝ) • a i.val
    rw [Function.update_of_ne (Nat.ne_of_lt i.isLt)]
  · change (y (Fin.last k) : ℝ) • Function.update a k z k =
      (y (Fin.last k) : ℝ) • z
    rw [Function.update_self]

/-- The finite union of all affine obstructions associated to prescribed
finite boxes of integer points and coefficient vectors. -/
def extensionBadUnion {n k : ℕ} (B : Set (Fin n → ℝ)) (C : ℝ)
    (a : ℕ → Fin n → ℝ) (SX : Finset (Fin n → ℤ))
    (SY : Finset (Fin (k + 1) → ℤ)) : Set (Fin n → ℝ) :=
  ⋃ x ∈ (SX : Set (Fin n → ℤ)), ⋃ y ∈ (SY : Set (Fin (k + 1) → ℤ)),
    badAffineSlice B C (previousContribution a y) (y (Fin.last k)) x

/-- The finite obstruction union is measurable. -/
theorem measurableSet_extensionBadUnion {n k : ℕ} {B : Set (Fin n → ℝ)}
    (hB : MeasurableSet B) {C : ℝ} (hC : C ≠ 0)
    (a : ℕ → Fin n → ℝ) (SX : Finset (Fin n → ℤ))
    (SY : Finset (Fin (k + 1) → ℤ)) :
    MeasurableSet (extensionBadUnion B C a SX SY) := by
  apply SX.measurableSet_biUnion
  intro x hx
  apply SY.measurableSet_biUnion
  intro y hy
  exact measurableSet_badAffineSlice hB hC _ _ _

/-- Union bound for Bilu's finite family of affine obstructions.  The
right side is deliberately left as a finite sum; substituting the elementary
cardinality estimates for the two integer boxes gives the displayed constant
in Lemma 6.8. -/
theorem volume_extensionBadUnion_le {n k : ℕ} (B : Set (Fin n → ℝ))
    {C : ℝ} (hC : 0 ≤ C) (a : ℕ → Fin n → ℝ)
    (SX : Finset (Fin n → ℤ)) (SY : Finset (Fin (k + 1) → ℤ))
    (hSY : ∀ y ∈ SY, y (Fin.last k) ≠ 0) :
    volume (extensionBadUnion B C a SX SY) ≤
      ∑ _x ∈ SX, ∑ _y ∈ SY, ENNReal.ofReal (C ^ n) * volume B := by
  calc
    volume (extensionBadUnion B C a SX SY)
        ≤ ∑ x ∈ SX, volume (⋃ y ∈ (SY : Set (Fin (k + 1) → ℤ)),
            badAffineSlice B C (previousContribution a y) (y (Fin.last k)) x) := by
      unfold extensionBadUnion
      let U := fun x : Fin n → ℤ ↦
        ⋃ y ∈ (SY : Set (Fin (k + 1) → ℤ)),
          badAffineSlice B C (previousContribution a y) (y (Fin.last k)) x
      rw [show (⋃ x ∈ (SX : Set (Fin n → ℤ)), U x) = ⋃ x ∈ SX, U x by
        ext z
        simp]
      exact measure_biUnion_finset_le SX U
    _ ≤ ∑ x ∈ SX, ∑ y ∈ SY,
          volume (badAffineSlice B C (previousContribution a y)
            (y (Fin.last k)) x) := by
      gcongr with x hx
      exact measure_biUnion_finset_le SY fun y ↦
        badAffineSlice B C (previousContribution a y) (y (Fin.last k)) x
    _ ≤ ∑ _x ∈ SX, ∑ _y ∈ SY, ENNReal.ofReal (C ^ n) * volume B := by
      gcongr with x hx y hy
      exact volume_badAffineSlice_le B hC _ _ _ (hSY y hy)

/-- Avoiding the explicit finite obstruction union upgrades a good prefix
to a good prefix with one more vector. -/
theorem good_extension_of_notMem_extensionBadUnion {n k : ℕ}
    (B : Set (Fin n → ℝ)) (X C : ℝ) (a : ℕ → Fin n → ℝ)
    (SX : Finset (Fin n → ℤ)) (SY : Finset (Fin (k + 1) → ℤ))
    (hSX : ∀ x, CoordBound X x → x ∈ SX)
    (hSY : ∀ y, CoordBound X y → y (Fin.last k) ≠ 0 → y ∈ SY)
    (ha : IsBadlyApproximableUpTo B X C k a)
    {z : Fin n → ℝ} (hz : z ∉ extensionBadUnion B C a SX SY) :
    IsBadlyApproximableUpTo B X C (k + 1) (Function.update a k z) := by
  intro x y hx hyny hy
  have hcomb := integerCombination_update_eq a z y
  by_cases hlast : y (Fin.last k) = 0
  · let yt : Fin k → ℤ := fun i ↦ y i.castSucc
    have hynyt : ∃ i, yt i ≠ 0 := by
      by_contra h
      push Not at h
      have hyzero : y = 0 := by
        funext j
        refine Fin.lastCases hlast (fun i ↦ ?_) j
        exact h i
      obtain ⟨i, hi⟩ := hyny
      exact hi (congrFun hyzero i)
    have hytbound : CoordBound X yt := fun i ↦ hy i.castSucc
    have hprev := ha x yt hx hynyt hytbound
    rw [hcomb, hlast, Int.cast_zero, zero_smul, add_zero]
    exact hprev
  · intro hbad
    apply hz
    simp only [extensionBadUnion, mem_iUnion]
    refine ⟨x, ⟨hSX x hx, ⟨y, ⟨hSY y hy hlast, ?_⟩⟩⟩⟩
    change previousContribution a y + (y (Fin.last k) : ℝ) • z - integerPoint x ∈ C • B
    rwa [← hcomb]

/-- With boxes containing exactly the admissible integer vectors, the
finite obstruction union is exactly the set of bad extensions. -/
theorem extensionBadUnion_eq_badExtensions {n k : ℕ}
    (B : Set (Fin n → ℝ)) (X C : ℝ) (a : ℕ → Fin n → ℝ)
    (SX : Finset (Fin n → ℤ)) (SY : Finset (Fin (k + 1) → ℤ))
    (hSXcover : ∀ x, CoordBound X x → x ∈ SX)
    (hSXvalid : ∀ x ∈ SX, CoordBound X x)
    (hSYcover : ∀ y, CoordBound X y → y (Fin.last k) ≠ 0 → y ∈ SY)
    (hSYvalid : ∀ y ∈ SY, CoordBound X y ∧ y (Fin.last k) ≠ 0)
    (ha : IsBadlyApproximableUpTo B X C k a) :
    extensionBadUnion B C a SX SY =
      {z | ¬ IsBadlyApproximableUpTo B X C (k + 1)
        (Function.update a k z)} := by
  ext z
  constructor
  · intro hz hgood
    simp only [extensionBadUnion, mem_iUnion] at hz
    obtain ⟨x, hxS, y, hyS, hslice⟩ := hz
    have hx := hSXvalid x hxS
    have hyv := hSYvalid y hyS
    have hnonzero : ∃ i, y i ≠ 0 := ⟨Fin.last k, hyv.2⟩
    have hout := hgood x y hx hnonzero hyv.1
    apply hout
    rw [integerCombination_update_eq]
    exact hslice
  · intro hbad
    by_contra hz
    exact hbad (good_extension_of_notMem_extensionBadUnion B X C a SX SY
      hSXcover hSYcover ha hz)

/-- A positive-measure set cannot be contained in a strictly smaller
measurable obstruction.  This elementary form is the selection step used
at every stage of Bilu's induction in Lemma 6.8. -/
theorem exists_mem_notMem_of_measure_lt {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {M Z : Set α} (_hM : MeasurableSet M)
    (_hZ : MeasurableSet Z) (hlt : μ Z < μ M) :
    ∃ a, a ∈ M ∧ a ∉ Z := by
  by_contra h
  push Not at h
  have hsub : M ⊆ Z := fun a ha ↦ h a ha
  exact (not_lt_of_ge (measure_mono hsub)) hlt

/-- Finite union bound in the exact strict form needed by Lemma 6.8. -/
theorem exists_avoiding_iUnion_finset {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} (S : Finset ι) (M : Set α) (Z : ι → Set α)
    (hM : MeasurableSet M) (hZ : ∀ i ∈ S, MeasurableSet (Z i))
    (hlt : ∑ i ∈ S, μ (Z i) < μ M) :
    ∃ a, a ∈ M ∧ ∀ i ∈ S, a ∉ Z i := by
  let U : Set α := ⋃ i ∈ (S : Set ι), Z i
  have hU : MeasurableSet U := by
    exact S.measurableSet_biUnion hZ
  have hμU : μ U ≤ ∑ i ∈ S, μ (Z i) := by
    simpa [U] using measure_biUnion_finset_le S Z
  obtain ⟨a, haM, haU⟩ :=
    exists_mem_notMem_of_measure_lt hM hU (lt_of_le_of_lt hμU hlt)
  refine ⟨a, haM, ?_⟩
  intro i hi hai
  exact haU (by
    simp only [U, mem_iUnion]
    exact ⟨i, ⟨hi, hai⟩⟩)

/-- The induction/measure engine of Bilu's Lemma 6.8.  Once the affine
slice calculation and finite union count show that the bad extensions have
smaller volume than `M k`, this theorem chooses all vectors successively.

Unlike a bare choice principle, every hypothesis here is a measurable fact:
the obstruction at stage `k` must be measurable and strictly smaller than
the candidate set. -/
theorem lemma6_8_induction {n r : ℕ} (B : Set (Fin n → ℝ))
    (X C : ℝ) (M : ℕ → Set (Fin n → ℝ))
    (hM : ∀ k < r, MeasurableSet (M k))
    (hstep : ∀ (k : ℕ), k < r → ∀ a : ℕ → Fin n → ℝ,
      IsBadlyApproximableUpTo B X C k a →
      (∀ i < k, a i ∈ M i) →
      MeasurableSet {z | ¬ IsBadlyApproximableUpTo B X C (k + 1)
        (Function.update a k z)} ∧
      volume {z | ¬ IsBadlyApproximableUpTo B X C (k + 1)
        (Function.update a k z)} < volume (M k)) :
    ∃ a : ℕ → Fin n → ℝ,
      (∀ i < r, a i ∈ M i) ∧ IsBadlyApproximableUpTo B X C r a := by
  have H : ∀ k ≤ r, ∃ a : ℕ → Fin n → ℝ,
      (∀ i < k, a i ∈ M i) ∧ IsBadlyApproximableUpTo B X C k a := by
    intro k hk
    induction k with
    | zero =>
        refine ⟨0, ?_, ?_⟩
        · simp
        · intro x y _ hy _
          exact (hy.choose.elim0)
    | succ k ih =>
        obtain ⟨a, haM, haGood⟩ := ih (Nat.le_of_succ_le hk)
        have hklt : k < r := lt_of_lt_of_le (Nat.lt_succ_self k) hk
        let Z : Set (Fin n → ℝ) :=
          {z | ¬ IsBadlyApproximableUpTo B X C (k + 1)
            (Function.update a k z)}
        have hs := hstep k hklt a haGood haM
        obtain ⟨z, hzM, hzZ⟩ :=
          exists_mem_notMem_of_measure_lt (hM k hklt) hs.1 hs.2
        refine ⟨Function.update a k z, ?_, ?_⟩
        · intro i hi
          by_cases hik : i = k
          · subst i
            simpa using hzM
          · rw [Function.update_of_ne hik]
            exact haM i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hik)
        · exact not_not.mp hzZ
  exact H r le_rfl

/-! ## Bilu's finite integer boxes -/

open Erdos186.CFP.Bilu.IntegerBoxCount

/-- The integer points satisfying the first bound in Definition 6.7. -/
noncomputable def admissibleIntegerPoints (n : ℕ) (X : ℝ) : Finset (Fin n → ℤ) :=
  by
    classical
    exact (centeredIntBox n (Nat.ceil X - 1)).filter (CoordBound X)

/-- At the `k`th extension step, only coefficient vectors whose last
coefficient is nonzero have to be excluded; the others are already ruled
out by the good-prefix hypothesis. -/
noncomputable def admissibleLastCoefficients (k : ℕ) (X : ℝ) :
    Finset (Fin (k + 1) → ℤ) :=
  by
    classical
    exact (centeredIntBox (k + 1) (Nat.ceil X - 1)).filter
      (fun y ↦ CoordBound X y ∧ y (Fin.last k) ≠ 0)

theorem mem_admissibleIntegerPoints {n : ℕ} {X : ℝ} (hX : 0 < X)
    (x : Fin n → ℤ) (hx : CoordBound X x) :
    x ∈ admissibleIntegerPoints n X := by
  classical
  simp only [admissibleIntegerPoints, Finset.mem_filter]
  exact ⟨mem_centeredIntBox_ceil_sub_one hX x hx, hx⟩

theorem mem_admissibleLastCoefficients {k : ℕ} {X : ℝ} (hX : 0 < X)
    (y : Fin (k + 1) → ℤ) (hy : CoordBound X y)
    (hlast : y (Fin.last k) ≠ 0) :
    y ∈ admissibleLastCoefficients k X := by
  classical
  simp only [admissibleLastCoefficients, Finset.mem_filter]
  exact ⟨mem_centeredIntBox_ceil_sub_one hX y hy, hy, hlast⟩

/-- Lemma 6.8 with the finite obstruction count displayed exactly as the
finite sum to which Bilu applies the elementary box-cardinality bound.  No
analytic or selection hypothesis remains hidden in this statement. -/
theorem lemma6_8_finiteBoxes {n r : ℕ} (B : Set (Fin n → ℝ))
    (X C : ℝ) (M : ℕ → Set (Fin n → ℝ))
    (hB : MeasurableSet B) (hX : 0 < X) (hC : 0 < C)
    (hM : ∀ k < r, MeasurableSet (M k))
    (hvolume : ∀ k < r,
      (∑ _x ∈ admissibleIntegerPoints n X,
        ∑ _y ∈ admissibleLastCoefficients k X,
          ENNReal.ofReal (C ^ n) * volume B) < volume (M k)) :
    ∃ a : ℕ → Fin n → ℝ,
      (∀ i < r, a i ∈ M i) ∧ IsBadlyApproximableUpTo B X C r a := by
  classical
  apply lemma6_8_induction B X C M hM
  intro k hk a ha haM
  let SX := admissibleIntegerPoints n X
  let SY := admissibleLastCoefficients k X
  have hSXcover : ∀ x, CoordBound X x → x ∈ SX :=
    fun x hx ↦ mem_admissibleIntegerPoints hX x hx
  have hSXvalid : ∀ x ∈ SX, CoordBound X x := by
    intro x hx
    have hx' := hx
    simp only [SX, admissibleIntegerPoints, Finset.mem_filter] at hx'
    exact hx'.2
  have hSYcover : ∀ y, CoordBound X y → y (Fin.last k) ≠ 0 → y ∈ SY :=
    fun y hy hlast ↦ mem_admissibleLastCoefficients hX y hy hlast
  have hSYvalid : ∀ y ∈ SY, CoordBound X y ∧ y (Fin.last k) ≠ 0 := by
    intro y hy
    have hy' := hy
    simp only [SY, admissibleLastCoefficients, Finset.mem_filter] at hy'
    exact hy'.2
  have heq := extensionBadUnion_eq_badExtensions B X C a SX SY
    hSXcover hSXvalid hSYcover hSYvalid ha
  constructor
  · rw [← heq]
    exact measurableSet_extensionBadUnion hB hC.ne' a SX SY
  · rw [← heq]
    exact (volume_extensionBadUnion_le B hC.le a SX SY
      (fun y hy ↦ (hSYvalid y hy).2)).trans_lt (hvolume k hk)

/-- Quantitative form of Lemma 6.8 after inserting the elementary count
`#[-X,X]^d ≤ (3X)^d`.  This is the exact estimate used before Bilu rounds
it up to the dimension-uniform displayed constant. -/
theorem lemma6_8_counted {n r : ℕ} (B : Set (Fin n → ℝ))
    (X C : ℝ) (M : ℕ → Set (Fin n → ℝ))
    (hB : MeasurableSet B) (hX : 1 ≤ X) (hC : 0 < C)
    (hM : ∀ k < r, MeasurableSet (M k))
    (hvolume : ∀ k < r,
      ENNReal.ofReal ((3 * X) ^ n * (3 * X) ^ (k + 1) * C ^ n) * volume B <
        volume (M k)) :
    ∃ a : ℕ → Fin n → ℝ,
      (∀ i < r, a i ∈ M i) ∧ IsBadlyApproximableUpTo B X C r a := by
  apply lemma6_8_finiteBoxes B X C M hB (zero_lt_one.trans_le hX) hC hM
  intro k hk
  have hxcardR : ((admissibleIntegerPoints n X).card : ℝ) ≤ (3 * X) ^ n := by
    calc
      ((admissibleIntegerPoints n X).card : ℝ) ≤
          ((centeredIntBox n (Nat.ceil X - 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (by
          intro x hx
          have hx' := hx
          simp only [admissibleIntegerPoints, Finset.mem_filter] at hx'
          exact hx'.1)
      _ ≤ (3 * X) ^ n := card_centeredIntBox_ceil_sub_one_le hX
  have hycardR : ((admissibleLastCoefficients k X).card : ℝ) ≤
      (3 * X) ^ (k + 1) := by
    calc
      ((admissibleLastCoefficients k X).card : ℝ) ≤
          ((centeredIntBox (k + 1) (Nat.ceil X - 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (by
          intro y hy
          have hy' := hy
          simp only [admissibleLastCoefficients, Finset.mem_filter] at hy'
          exact hy'.1)
      _ ≤ (3 * X) ^ (k + 1) :=
        card_centeredIntBox_ceil_sub_one_le hX
  have hxcardE : ((admissibleIntegerPoints n X).card : ℝ≥0∞) ≤
      ENNReal.ofReal ((3 * X) ^ n) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hxcardR
  have hycardE : ((admissibleLastCoefficients k X).card : ℝ≥0∞) ≤
      ENNReal.ofReal ((3 * X) ^ (k + 1)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hycardR
  calc
    (∑ _x ∈ admissibleIntegerPoints n X,
        ∑ _y ∈ admissibleLastCoefficients k X,
          ENNReal.ofReal (C ^ n) * volume B) =
        ((admissibleIntegerPoints n X).card : ℝ≥0∞) *
          ((admissibleLastCoefficients k X).card : ℝ≥0∞) *
            (ENNReal.ofReal (C ^ n) * volume B) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ENNReal.ofReal ((3 * X) ^ n) *
          ENNReal.ofReal ((3 * X) ^ (k + 1)) *
            (ENNReal.ofReal (C ^ n) * volume B) := by
      gcongr
    _ = ENNReal.ofReal ((3 * X) ^ n * (3 * X) ^ (k + 1) * C ^ n) *
          volume B := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (3 * X) ^ n),
        ← mul_assoc,
        ← ENNReal.ofReal_mul
          (by positivity : 0 ≤ (3 * X) ^ n * (3 * X) ^ (k + 1))]
    _ < volume (M k) := hvolume k hk

/-- Uniform-in-the-stage version of `lemma6_8_counted`.  This is the
convenient interface used in Propositions 8.2 and 8.3. -/
theorem lemma6_8_uniform {n r : ℕ} (B : Set (Fin n → ℝ))
    (X C : ℝ) (M : ℕ → Set (Fin n → ℝ))
    (hB : MeasurableSet B) (hX : 1 ≤ X) (hC : 0 < C)
    (hM : ∀ k < r, MeasurableSet (M k))
    (hvolume : ∀ k < r,
      ENNReal.ofReal ((3 * X) ^ n * (3 * X) ^ r * C ^ n) * volume B <
        volume (M k)) :
    ∃ a : ℕ → Fin n → ℝ,
      (∀ i < r, a i ∈ M i) ∧ IsBadlyApproximableUpTo B X C r a := by
  apply lemma6_8_counted B X C M hB hX hC hM
  intro k hk
  have hbase : (1 : ℝ) ≤ 3 * X := by nlinarith
  have hpow : (3 * X) ^ (k + 1) ≤ (3 * X) ^ r :=
    pow_le_pow_right₀ hbase (Nat.succ_le_iff.mpr hk)
  have hreal : (3 * X) ^ n * (3 * X) ^ (k + 1) * C ^ n ≤
      (3 * X) ^ n * (3 * X) ^ r * C ^ n := by
    gcongr
  have henn :
      ENNReal.ofReal ((3 * X) ^ n * (3 * X) ^ (k + 1) * C ^ n) ≤
        ENNReal.ofReal ((3 * X) ^ n * (3 * X) ^ r * C ^ n) :=
    ENNReal.ofReal_le_ofReal hreal
  exact (mul_le_mul_of_nonneg_right henn (by positivity)).trans_lt (hvolume k hk)

/-- **Bilu, Lemma 6.8.**  This is the source's rounded constant
`6^n 3^r X^(n+r) C^n Vol(B)`.  The proof is an immediate consequence of
the sharper uniform count above. -/
theorem lemma6_8 {n r : ℕ} (B : Set (Fin n → ℝ))
    (X C : ℝ) (M : ℕ → Set (Fin n → ℝ))
    (hB : MeasurableSet B) (hX : 1 ≤ X) (hC : 0 < C)
    (hM : ∀ k < r, MeasurableSet (M k))
    (hvolume : ∀ k < r,
      ENNReal.ofReal ((6 : ℝ) ^ n * 3 ^ r * X ^ (n + r) * C ^ n) * volume B <
        volume (M k)) :
    ∃ a : ℕ → Fin n → ℝ,
      (∀ i < r, a i ∈ M i) ∧ IsBadlyApproximableUpTo B X C r a := by
  apply lemma6_8_uniform B X C M hB hX hC hM
  intro k hk
  have htwo : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  let A : ℝ := (3 : ℝ) ^ n * X ^ n * (3 : ℝ) ^ r * X ^ r * C ^ n
  have hA : 0 ≤ A := by positivity
  have hreal : (3 * X) ^ n * (3 * X) ^ r * C ^ n ≤
      (6 : ℝ) ^ n * 3 ^ r * X ^ (n + r) * C ^ n := by
    calc
      (3 * X) ^ n * (3 * X) ^ r * C ^ n = A := by
        simp only [A, mul_pow]
        ring
      _ ≤ 2 ^ n * A := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right htwo hA
      _ = (6 : ℝ) ^ n * 3 ^ r * X ^ (n + r) * C ^ n := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num, mul_pow, pow_add]
        simp only [A]
        ring
  have henn := ENNReal.ofReal_le_ofReal hreal
  exact (mul_le_mul_of_nonneg_right henn (by positivity)).trans_lt (hvolume k hk)

/-- Finite-indexed presentation of Bilu's Lemma 6.8. -/
theorem lemma6_8_fin {n r : ℕ} (B : Set (Fin n → ℝ))
    (X C : ℝ) (M : ℕ → Set (Fin n → ℝ))
    (hB : MeasurableSet B) (hX : 1 ≤ X) (hC : 0 < C)
    (hM : ∀ k < r, MeasurableSet (M k))
    (hvolume : ∀ k < r,
      ENNReal.ofReal ((6 : ℝ) ^ n * 3 ^ r * X ^ (n + r) * C ^ n) * volume B <
        volume (M k)) :
    ∃ a : Fin r → Fin n → ℝ,
      (∀ i : Fin r, a i ∈ M i) ∧ IsBadlyApproximable B X C a := by
  obtain ⟨a, haM, ha⟩ := lemma6_8 B X C M hB hX hC hM hvolume
  exact ⟨fun i ↦ a i, fun i ↦ haM i i.isLt, ha⟩

end Erdos186.CFP.Bilu.BadlyApproximable

#print axioms Erdos186.CFP.Bilu.BadlyApproximable.exists_avoiding_iUnion_finset
#print axioms Erdos186.CFP.Bilu.BadlyApproximable.lemma6_8_induction
#print axioms Erdos186.CFP.Bilu.BadlyApproximable.lemma6_8_counted
#print axioms Erdos186.CFP.Bilu.BadlyApproximable.lemma6_8
#print axioms Erdos186.CFP.Bilu.BadlyApproximable.lemma6_8_fin
