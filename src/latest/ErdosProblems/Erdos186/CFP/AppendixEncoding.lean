/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Main
import ErdosProblems.Erdos186.CFP.NoCarryEmbedding

/-!
# Translation-invariant homogenized encoding for the CFP Appendix

An arbitrary integer box can be far from the origin, so an encoding based
on absolute coordinate radius does not have an endpoint controlled by the
box cardinality.  We first subtract the lower corner and adjoin a leading
cardinality coordinate.  The inverse affine translation becomes an honest
additive homomorphism on this homogenized lattice.

The mixed-radix base is then the canonical witness-independent Appendix
base from `NoCarryEmbedding`.  This file proves positivity, cardinality
preservation, and the exact equality between the one-dimensional integer
input and the Horner image to which the checked witness lift applies.
-/

namespace Erdos186.CFP.AppendixEncoding

open scoped BigOperators
open NoCarryEmbedding

noncomputable section

/-- Normalize a box point and adjoin a leading homogeneous coordinate. -/
def boxHomogenize {d : ℕ} (B : IntegerBox d) (x : LatticePoint d) :
    LatticePoint (d + 1) :=
  Fin.cases 1 (fun i ↦ x i - B.lower i)

@[simp]
theorem boxHomogenize_zero {d : ℕ} (B : IntegerBox d)
    (x : LatticePoint d) :
    boxHomogenize B x 0 = 1 :=
  rfl

@[simp]
theorem boxHomogenize_succ {d : ℕ} (B : IntegerBox d)
    (x : LatticePoint d) (i : Fin d) :
    boxHomogenize B x i.succ = x i - B.lower i := by
  simp [boxHomogenize]

/-- Undo normalization.  The leading coordinate makes translation by the
lower corner linear. -/
def boxDehomogenizeHom {d : ℕ} (B : IntegerBox d) :
    LatticePoint (d + 1) →+ LatticePoint d where
  toFun y := fun i ↦ y i.succ + y 0 * B.lower i
  map_zero' := by
    ext i
    simp
  map_add' x y := by
    ext i
    simp only [Pi.add_apply]
    ring

@[simp]
theorem boxDehomogenizeHom_boxHomogenize {d : ℕ}
    (B : IntegerBox d) (x : LatticePoint d) :
    boxDehomogenizeHom B (boxHomogenize B x) = x := by
  ext i
  simp [boxDehomogenizeHom]

theorem boxHomogenize_injective {d : ℕ} (B : IntegerBox d) :
    Function.Injective (boxHomogenize B) := by
  intro x y hxy
  simpa only [boxDehomogenizeHom_boxHomogenize] using
    congrArg (boxDehomogenizeHom B) hxy

/-- The normalized homogeneous image of a finite set in a box. -/
def homogenizedBoxSet {d : ℕ} (B : IntegerBox d)
    (A : Finset (LatticePoint d)) : Finset (LatticePoint (d + 1)) :=
  A.image (boxHomogenize B)

@[simp]
theorem card_homogenizedBoxSet {d : ℕ} (B : IntegerBox d)
    (A : Finset (LatticePoint d)) :
    (homogenizedBoxSet B A).card = A.card := by
  exact Finset.card_image_of_injective A (boxHomogenize_injective B)

theorem boxDehomogenizeHom_image_homogenizedBoxSet {d : ℕ}
    (B : IntegerBox d) (A : Finset (LatticePoint d)) :
    (homogenizedBoxSet B A).image (boxDehomogenizeHom B) = A := by
  ext x
  simp only [homogenizedBoxSet, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨boxHomogenize B x, ⟨x, hx, rfl⟩,
      boxDehomogenizeHom_boxHomogenize B x⟩

/-- Every normalized digit is nonnegative for a point of the box. -/
theorem boxHomogenize_nonneg_of_mem {d : ℕ} {B : IntegerBox d}
    {x : LatticePoint d} (hx : x ∈ B.carrier) (i : Fin (d + 1)) :
    0 ≤ boxHomogenize B x i := by
  refine Fin.cases (by simp) (fun j ↦ ?_) i
  rw [boxHomogenize_succ]
  exact sub_nonneg.mpr (IntegerBox.mem_carrier_iff.mp hx j).1

/-- Every side length is positive once the box contains a point. -/
theorem box_sideLength_pos_of_mem {d : ℕ} {B : IntegerBox d}
    {x : LatticePoint d} (hx : x ∈ B.carrier) (i : Fin d) :
    0 < (B.upper i + 1 - B.lower i).toNat := by
  have hi := IntegerBox.mem_carrier_iff.mp hx i
  have hpos : 0 < B.upper i + 1 - B.lower i := by omega
  have hcast :
      (((B.upper i + 1 - B.lower i).toNat : ℕ) : ℤ) =
        B.upper i + 1 - B.lower i :=
    Int.toNat_of_nonneg hpos.le
  rw [← hcast] at hpos
  exact_mod_cast hpos

/-- In a nonempty product box, each individual side length is at most the
box cardinality. -/
theorem box_sideLength_le_card_of_mem {d : ℕ} {B : IntegerBox d}
    {x : LatticePoint d} (hx : x ∈ B.carrier) (i : Fin d) :
    (B.upper i + 1 - B.lower i).toNat ≤ B.carrier.card := by
  rw [IntegerBox.card_carrier]
  apply Finset.single_le_prod'
    (f := fun j : Fin d ↦ (B.upper j + 1 - B.lower j).toNat)
    (s := Finset.univ)
  · intro j _hj
    exact box_sideLength_pos_of_mem hx j
  · exact Finset.mem_univ i

/-- A normalized coordinate is bounded by its side length. -/
theorem natAbs_boxHomogenize_succ_le_sideLength {d : ℕ}
    {B : IntegerBox d} {x : LatticePoint d} (hx : x ∈ B.carrier)
    (i : Fin d) :
    (boxHomogenize B x i.succ).natAbs ≤
      (B.upper i + 1 - B.lower i).toNat := by
  rw [boxHomogenize_succ]
  have hi := IntegerBox.mem_carrier_iff.mp hx i
  have hnonneg : 0 ≤ x i - B.lower i := by omega
  have hwidthNonneg : 0 ≤ B.upper i + 1 - B.lower i := by omega
  have hcast :
      (((B.upper i + 1 - B.lower i).toNat : ℕ) : ℤ) =
        B.upper i + 1 - B.lower i := by
    exact Int.toNat_of_nonneg hwidthNonneg
  have hlt : x i - B.lower i <
      (((B.upper i + 1 - B.lower i).toNat : ℕ) : ℤ) := by
    rw [hcast]
    omega
  have hltNat : (x i - B.lower i).natAbs <
      (B.upper i + 1 - B.lower i).toNat := by
    rw [← Int.natAbs_of_nonneg hnonneg] at hlt
    exact_mod_cast hlt
  exact hltNat.le

/-- Translation-invariant radius bound: after normalization and
homogenization, every coordinate is bounded by the cardinality of the
ambient box, regardless of where that box is located. -/
theorem coordinateRadius_homogenizedBoxSet_le_card {d : ℕ}
    {B : IntegerBox d} {A : Finset (LatticePoint d)}
    (hAB : A ⊆ B.carrier) :
    coordinateRadius (homogenizedBoxSet B A) ≤ B.carrier.card := by
  unfold coordinateRadius
  apply Finset.sup_le
  intro y hy
  obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp hy
  apply Finset.sup_le
  intro i _hi
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [boxHomogenize_zero, Int.natAbs_one]
    exact Finset.card_pos.mpr ⟨x, hAB hxA⟩
  · exact (natAbs_boxHomogenize_succ_le_sideLength (hAB hxA) j).trans
      (box_sideLength_le_card_of_mem (hAB hxA) j)

/-- The canonical no-carry base chosen before the one-dimensional witness
is returned. -/
def appendixEncodingBase {d : ℕ} (D s : ℕ) (B : IntegerBox d)
    (A : Finset (LatticePoint d)) : ℕ :=
  appendixHornerBase D s (homogenizedBoxSet B A)

/-- Positive one-dimensional integer encoding of a normalized box point. -/
def appendixEncode {d : ℕ} (D s : ℕ) (B : IntegerBox d)
    (A : Finset (LatticePoint d)) (x : LatticePoint d) : ℤ :=
  hornerEncode (d + 1) (appendixEncodingBase D s B A)
    (boxHomogenize B x)

/-- The integer input to the one-dimensional CFP theorem. -/
def appendixEncodedIntegers {d : ℕ} (D s : ℕ) (B : IntegerBox d)
    (A : Finset (LatticePoint d)) : Finset ℤ :=
  A.image (appendixEncode D s B A)

theorem appendixEncode_pos_of_mem {d D s : ℕ}
    {B : IntegerBox d} {A : Finset (LatticePoint d)}
    {x : LatticePoint d} (hxA : x ∈ A) (hAB : A ⊆ B.carrier) :
    0 < appendixEncode D s B A x := by
  rw [appendixEncode, hornerEncode_succ, boxHomogenize_zero]
  have htail :
      0 ≤ hornerEncode d (appendixEncodingBase D s B A)
        (fun i ↦ boxHomogenize B x i.succ) :=
    hornerEncode_nonneg_of_nonneg _
      (fun i ↦ boxHomogenize_nonneg_of_mem (hAB hxA) i.succ)
  positivity

/-- A coarse geometric-series upper bound for Horner evaluation of
nonnegative digits.  Its deliberately simple polynomial shape is convenient
for the outer exponent bookkeeping in the higher-dimensional corollary. -/
theorem hornerEncode_le_radius_mul_pow :
    ∀ {m b R : ℕ} (x : LatticePoint m),
      (∀ i, 0 ≤ x i) → (∀ i, x i ≤ (R : ℤ)) →
      hornerEncode m b x ≤ (R * (b + 1) ^ m : ℕ) := by
  intro m
  induction m with
  | zero =>
      intro b R x _hnonneg _hupper
      simp
  | succ m ih =>
      intro b R x hnonneg hupper
      rw [hornerEncode_succ]
      have htail := ih (b := b) (R := R) (fun i ↦ x i.succ)
        (fun i ↦ hnonneg i.succ) (fun i ↦ hupper i.succ)
      have hRgrow : (R : ℤ) ≤ (R * (b + 1) ^ m : ℕ) := by
        exact_mod_cast Nat.le_mul_of_pos_right R
          (pow_pos (by omega : 0 < b + 1) m)
      calc
        x 0 + (b : ℤ) * hornerEncode m b (fun i ↦ x i.succ) ≤
            (R : ℤ) + (b : ℤ) * (R * (b + 1) ^ m : ℕ) := by
          exact add_le_add (hupper 0)
            (mul_le_mul_of_nonneg_left htail (Int.natCast_nonneg b))
        _ ≤ (R * (b + 1) ^ m : ℕ) +
            (b : ℤ) * (R * (b + 1) ^ m : ℕ) := by
          simpa only [add_comm] using
            add_le_add_left hRgrow
              ((b : ℤ) * (R * (b + 1) ^ m : ℕ))
        _ = (R * (b + 1) ^ (m + 1) : ℕ) := by
          push_cast
          rw [pow_succ]
          ring

/-- Explicit endpoint of the encoded one-dimensional interval. -/
def appendixEncodedEndpoint {d : ℕ} (D s : ℕ) (B : IntegerBox d)
    (A : Finset (LatticePoint d)) : ℕ :=
  A.sup fun x ↦ (appendixEncode D s B A x).toNat

/-- The endpoint is polynomial in the coordinate radius of the normalized
homogeneous set and the already explicit Appendix base. -/
theorem appendixEncodedEndpoint_le {d D s : ℕ}
    (B : IntegerBox d) (A : Finset (LatticePoint d))
    (hAB : A ⊆ B.carrier) :
    appendixEncodedEndpoint D s B A ≤
      coordinateRadius (homogenizedBoxSet B A) *
        (appendixEncodingBase D s B A + 1) ^ (d + 1) := by
  apply Finset.sup_le
  intro x hx
  let H := homogenizedBoxSet B A
  let y := boxHomogenize B x
  let R := coordinateRadius H
  have hyH : y ∈ H := by
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hynonneg : ∀ i, 0 ≤ y i :=
    fun i ↦ boxHomogenize_nonneg_of_mem (hAB hx) i
  have hyupper : ∀ i, y i ≤ (R : ℤ) := by
    intro i
    have habs := natAbs_le_coordinateRadius hyH i
    have hcast : ((y i).natAbs : ℤ) ≤ (R : ℤ) := by
      exact_mod_cast habs
    simpa only [Int.natAbs_of_nonneg (hynonneg i)] using hcast
  have henc := hornerEncode_le_radius_mul_pow
    (b := appendixEncodingBase D s B A) (R := R) y hynonneg hyupper
  have hencnonneg :
      0 ≤ appendixEncode D s B A x :=
    (appendixEncode_pos_of_mem hx hAB).le
  rw [Int.toNat_le]
  simpa only [appendixEncode, y, R, H] using henc

/-- The witness-independent lift radius as a polynomial in an externally
supplied coordinate-radius bound. -/
def uniformRadiusBound (D s ambient R : ℕ) : ℕ :=
  let L := 2 * s * R
  let rho := D * (2 * (s * R) + 1) ^ ambient
  let T := s * rho * L
  max (s * R) (max (3 * rho * L) (T + 3 * (s * rho) * L))

theorem uniformHornerLiftWindowRadius_eq_uniformRadiusBound
    {ambient : ℕ} (D s : ℕ) (A : Finset (LatticePoint ambient)) :
    uniformHornerLiftWindowRadius D s A =
      uniformRadiusBound D s ambient (coordinateRadius A) :=
  rfl

theorem uniformRadiusBound_mono {D s ambient R N : ℕ} (hRN : R ≤ N) :
    uniformRadiusBound D s ambient R ≤
      uniformRadiusBound D s ambient N := by
  simp only [uniformRadiusBound]
  gcongr

/-- A fully translation-invariant natural-number endpoint bound.  Its
parameters are only the fixed ambient dimension/rank bound, the reserve
scale, and the box cardinality. -/
def appendixEndpointPolynomialBound
    (D s ambient boxCard : ℕ) : ℕ :=
  boxCard *
    (2 * uniformRadiusBound D s (ambient + 1) boxCard + 2) ^
      (ambient + 1)

theorem appendixEncodedEndpoint_le_polynomialBound {d D s : ℕ}
    {B : IntegerBox d} {A : Finset (LatticePoint d)}
    (hAB : A ⊆ B.carrier) :
    appendixEncodedEndpoint D s B A ≤
      appendixEndpointPolynomialBound D s d B.carrier.card := by
  let H := homogenizedBoxSet B A
  let R := coordinateRadius H
  let N := B.carrier.card
  have hRN : R ≤ N := by
    simpa only [R, N, H] using
      coordinateRadius_homogenizedBoxSet_le_card hAB
  have hU := uniformRadiusBound_mono
    (D := D) (s := s) (ambient := d + 1) hRN
  have hU' :
      uniformRadiusBound D s (d + 1)
          (coordinateRadius (homogenizedBoxSet B A)) ≤
        uniformRadiusBound D s (d + 1) N := by
    simpa only [R, H] using hU
  have hbase : appendixEncodingBase D s B A + 1 ≤
      2 * uniformRadiusBound D s (d + 1) N + 2 := by
    dsimp only [appendixEncodingBase, appendixHornerBase]
    rw [uniformHornerLiftWindowRadius_eq_uniformRadiusBound]
    omega
  calc
    appendixEncodedEndpoint D s B A ≤
        R * (appendixEncodingBase D s B A + 1) ^ (d + 1) := by
      simpa only [R, H] using appendixEncodedEndpoint_le B A hAB
    _ ≤ N *
        (2 * uniformRadiusBound D s (d + 1) N + 2) ^ (d + 1) := by
      exact Nat.mul_le_mul hRN (Nat.pow_le_pow_left hbase (d + 1))
    _ = appendixEndpointPolynomialBound D s d B.carrier.card := by
      rfl

theorem appendixEncode_mem_Icc {d D s : ℕ}
    {B : IntegerBox d} {A : Finset (LatticePoint d)}
    (hAB : A ⊆ B.carrier) {x : LatticePoint d} (hx : x ∈ A) :
    appendixEncode D s B A x ∈
      Finset.Icc (1 : ℤ) (appendixEncodedEndpoint D s B A : ℤ) := by
  rw [Finset.mem_Icc]
  constructor
  · exact appendixEncode_pos_of_mem hx hAB
  · have hnonneg : 0 ≤ appendixEncode D s B A x :=
      (appendixEncode_pos_of_mem hx hAB).le
    have hsup : (appendixEncode D s B A x).toNat ≤
        appendixEncodedEndpoint D s B A :=
      Finset.le_sup (s := A)
        (f := fun y ↦ (appendixEncode D s B A y).toNat) hx
    rw [← Int.toNat_of_nonneg hnonneg]
    exact_mod_cast hsup

theorem appendixEncodedIntegers_subset_Icc {d D s : ℕ}
    {B : IntegerBox d} {A : Finset (LatticePoint d)}
    (hAB : A ⊆ B.carrier) :
    appendixEncodedIntegers D s B A ⊆
      Finset.Icc (1 : ℤ) (appendixEncodedEndpoint D s B A : ℤ) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  exact appendixEncode_mem_Icc hAB hx

/-- The target used by `IntegerTheorem15` is definitionally the integer
point version of the Horner image used by the canonical Appendix lift. -/
theorem integerPoints_appendixEncodedIntegers {d D s : ℕ}
    (B : IntegerBox d) (A : Finset (LatticePoint d)) :
    integerPoints (appendixEncodedIntegers D s B A) =
      (homogenizedBoxSet B A).image
        (hornerLatticeHom (d + 1) (appendixEncodingBase D s B A)) := by
  classical
  ext y
  simp only [integerPoints, appendixEncodedIntegers, homogenizedBoxSet,
    Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨boxHomogenize B x, ⟨x, hx, rfl⟩, by
      ext i
      simp [integerPoint, appendixEncode]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨appendixEncode D s B A x, ⟨x, hx, rfl⟩, by
      ext i
      simp [integerPoint, appendixEncode]⟩

/-- The canonical Appendix base is injective on the normalized homogeneous
source set as soon as the reserve scale is positive. -/
theorem horner_injectiveOn_homogenizedBoxSet {d D s : ℕ}
    (B : IntegerBox d) (A : Finset (LatticePoint d)) (hs : 0 < s) :
    Set.InjOn
      (hornerLatticeHom (d + 1) (appendixEncodingBase D s B A))
      (homogenizedBoxSet B A) := by
  let H := homogenizedBoxSet B A
  let M := coordinateRadius H
  let U := uniformHornerLiftWindowRadius D s H
  have hMU : M ≤ U := by
    calc
      M = 1 * M := by simp
      _ ≤ s * M := Nat.mul_le_mul_right M hs
      _ ≤ U := by
        simp only [U, uniformHornerLiftWindowRadius]
        exact Nat.le_max_left _ _
  have hwidth : 2 * M < appendixEncodingBase D s B A := by
    exact (Nat.mul_le_mul_left 2 hMU).trans_lt (by
      simpa only [appendixEncodingBase, H, U] using
        appendixHornerBase_width D s H)
  exact (hornerLatticeHom_injOn_coordinateWindow (by omega) hwidth).mono
    (subset_coordinateWindow H (Nat.le_refl M))

@[simp]
theorem card_appendixEncodedIntegers {d D s : ℕ}
    (B : IntegerBox d) (A : Finset (LatticePoint d)) (hs : 0 < s) :
    (appendixEncodedIntegers D s B A).card = A.card := by
  have hinjective : Set.InjOn (appendixEncode D s B A) A := by
    intro x hx y hy hxy
    apply boxHomogenize_injective B
    apply horner_injectiveOn_homogenizedBoxSet B A hs
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    · ext i
      simpa [appendixEncode] using hxy
  exact Finset.card_image_iff.mpr hinjective

/-- Apply the checked quantitative Appendix lift to a one-dimensional
witness for the positive encoded set.  The result is the full fixed-scale
witness on the translation-invariant homogenized source.  The only
remaining step toward the original box is the genuine projected
properization/dimension-reduction step. -/
noncomputable def liftFixedScaleWitness_to_homogenizedBoxSet
    {d D s k loss scaleNum scaleDen : ℕ}
    (B : IntegerBox d) (A : Finset (LatticePoint d))
    (W : FixedScaleWitness
      (integerPoints (appendixEncodedIntegers D s B A))
        s D k loss scaleNum scaleDen) :
    FixedScaleWitness (homogenizedBoxSet B A)
      s D k loss scaleNum scaleDen := by
  let H := homogenizedBoxSet B A
  let b := appendixEncodingBase D s B A
  have htarget :
      integerPoints (appendixEncodedIntegers D s B A) =
        H.image (hornerLatticeHom (d + 1) b) := by
    simpa only [H, b] using integerPoints_appendixEncodedIntegers
      (D := D) (s := s) B A
  let W' : FixedScaleWitness
      (H.image (hornerLatticeHom (d + 1) b))
        s D k loss scaleNum scaleDen := htarget ▸ W
  have hb : b = appendixHornerBase D s H := by
    rfl
  subst b
  exact liftFixedScaleWitness_appendixHornerBase W'

end

end Erdos186.CFP.AppendixEncoding
