/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP
import ErdosProblems.Erdos186.CFP.Bilu.MahlerBasis

/-!
# The finite interface to the discrete John theorem

Pham--Zakharov use the discrete John theorem only through a finite,
rank-sensitive consequence: the lattice points of a symmetric convex body
are contained in a proper symmetric GAP whose size is within a bounded
factor of the number of lattice points in the body.  This file develops the
entirely discrete part of that consequence.

The genuinely geometric existence theorem is represented by `Certificate`.
Constructing such a certificate for every symmetric convex body is the
(non-elementary) discrete John theorem; the certificate lemmas below show,
with no geometric assumptions left implicit, exactly how its two inclusions
imply the cardinality and dilation bounds used later.  For the particular
cardinality estimate needed here, the residue-fiber argument below supplies
an elementary substitute that does not require geometric existence.
-/

namespace Erdos186

open scoped BigOperators

namespace DiscreteJohn

variable {d r : ℕ}

/-- The integral linear combination map associated to a tuple of lattice
vectors. -/
def integerCombination (steps : Fin r → LatticePoint d) (z : Fin r → ℤ) :
    LatticePoint d :=
  fun j ↦ ∑ i, z i * steps i j

/-- The steps are independent over the integers.  This is the exact
injectivity property needed for a proper symmetric GAP. -/
def IntegerIndependent (steps : Fin r → LatticePoint d) : Prop :=
  Function.Injective (integerCombination steps)

/-- The symmetric progression
`{∑ i, z i * steps i | -radii i ≤ z i ≤ radii i}` represented in the
one-sided `GAP` interface. -/
def symmetricGAP (steps : Fin r → LatticePoint d) (radii : Fin r → ℕ) : GAP d r where
  offset := fun j ↦ -∑ i, (radii i : ℤ) * steps i j
  steps := steps
  widths := fun i ↦ 2 * radii i + 1
  width_pos := fun _ ↦ Nat.zero_lt_succ _

@[simp]
theorem symmetricGAP_offset (steps : Fin r → LatticePoint d) (radii : Fin r → ℕ) :
    (symmetricGAP steps radii).offset =
      fun j ↦ -∑ i, (radii i : ℤ) * steps i j := rfl

@[simp]
theorem symmetricGAP_steps (steps : Fin r → LatticePoint d) (radii : Fin r → ℕ) :
    (symmetricGAP steps radii).steps = steps := rfl

@[simp]
theorem symmetricGAP_widths (steps : Fin r → LatticePoint d) (radii : Fin r → ℕ)
    (i : Fin r) :
    (symmetricGAP steps radii).widths i = 2 * radii i + 1 := rfl

/-- The displayed one-sided coordinates evaluate to the expected centered
integer coefficients. -/
theorem symmetricGAP_coordPoint (steps : Fin r → LatticePoint d)
    (radii : Fin r → ℕ) (n : (symmetricGAP steps radii).Coord) :
    (symmetricGAP steps radii).coordPoint n =
      integerCombination steps (fun i ↦ (n i : ℤ) - (radii i : ℤ)) := by
  funext j
  simp [symmetricGAP, GAP.coordPoint, integerCombination, sub_mul,
    Finset.sum_sub_distrib]
  abel

/-- Integer independence makes every centered box presentation proper. -/
theorem symmetricGAP_proper {steps : Fin r → LatticePoint d}
    (hsteps : IntegerIndependent steps) (radii : Fin r → ℕ) :
    (symmetricGAP steps radii).Proper := by
  intro n m hnm
  rw [symmetricGAP_coordPoint, symmetricGAP_coordPoint] at hnm
  have hz := hsteps hnm
  funext i
  have hi := congrFun hz i
  apply Fin.ext
  have hi' : (n i : ℤ) = (m i : ℤ) := sub_left_inj.mp hi
  exact Int.ofNat_inj.mp hi'

@[simp]
theorem symmetricGAP_volume (steps : Fin r → LatticePoint d) (radii : Fin r → ℕ) :
    (symmetricGAP steps radii).volume = ∏ i, (2 * radii i + 1) := rfl

/-! ## A residue-fiber substitute for the geometric theorem

For the cardinality estimate in Pham--Zakharov one can bypass discrete John.
The following construction partitions the coefficient box of `tP` by its
coordinates modulo `t`.  Width-one coordinates are assigned modulus one;
this keeps them from introducing a spurious factor of `t`.
-/

/-- The modulus used in one coefficient: `t` for an active coordinate and
one for a width-one coordinate. -/
def residueModulus (P : GAP d r) (t : ℕ) (i : Fin r) : ℕ :=
  if P.widths i = 1 then 1 else t

theorem residueModulus_pos (P : GAP d r) {t : ℕ} (ht : 0 < t) (i : Fin r) :
    0 < residueModulus P t i := by
  simp only [residueModulus]
  split <;> omega

/-- The tuple of coordinate residues, with the width-one coordinates
collapsed to a singleton. -/
abbrev ResidueCoord (P : GAP d r) (t : ℕ) :=
  (i : Fin r) → Fin (residueModulus P t i)

/-- The residue tuple of a point in the coefficient box of `tP`. -/
def residue (P : GAP d r) {t : ℕ} (ht : 0 < t) (n : (P.dilate t).Coord) :
    ResidueCoord P t :=
  fun i ↦ ⟨(n i : ℕ) % residueModulus P t i,
    Nat.mod_lt _ (residueModulus_pos P ht i)⟩

/-- Dividing the non-residue part of a coefficient of `tP` gives a valid
coefficient of `P`. -/
def quotientCoord (P : GAP d r) {t : ℕ} (ht : 0 < t) (n : (P.dilate t).Coord) :
    P.Coord :=
  fun i ↦ if hi : P.widths i = 1 then
      ⟨0, P.width_pos i⟩
    else
      ⟨(n i : ℕ) / t, by
        apply (Nat.div_lt_iff_lt_mul ht).2
        calc
          (n i : ℕ) < t * (P.widths i - 1) + 1 := (n i).isLt
          _ ≤ t * (P.widths i - 1) + t := Nat.add_le_add_left ht _
          _ = t * ((P.widths i - 1) + 1) := by simp [Nat.mul_add]
          _ = t * P.widths i :=
            congrArg (t * ·) (Nat.sub_add_cancel (P.width_pos i))
          _ = P.widths i * t := Nat.mul_comm _ _⟩

/-- The coefficient tuple in `tP` obtained by retaining only the residues.
It lies in the dilated coefficient box, including in width-one coordinates. -/
def residueRepresentative (P : GAP d r) {t : ℕ} (ht : 0 < t)
    (n : (P.dilate t).Coord) : (P.dilate t).Coord :=
  fun i ↦ ⟨(n i : ℕ) % residueModulus P t i, by
    by_cases hi : P.widths i = 1
    · change (n i : ℕ) % residueModulus P t i <
        t * (P.widths i - 1) + 1
      rw [residueModulus, if_pos hi, hi, Nat.mod_one]
      omega
    · have hone : 1 ≤ P.widths i := P.width_pos i
      have hwi : 2 ≤ P.widths i :=
        Nat.succ_le_iff.mpr (lt_of_le_of_ne hone (Ne.symm hi))
      have hmod : (n i : ℕ) % t < t := Nat.mod_lt _ ht
      have ht_le : t ≤ t * (P.widths i - 1) :=
        Nat.le_mul_of_pos_right t (by omega)
      simp only [residueModulus, hi, if_false, GAP.dilate_widths]
      exact hmod.trans_le (ht_le.trans (Nat.le_add_right _ _))⟩

/-- Splitting a coefficient into quotient and residue, in integer form. -/
theorem coeff_sub_residueRepresentative (P : GAP d r) {t : ℕ} (ht : 0 < t)
    (n : (P.dilate t).Coord) (i : Fin r) :
    (n i : ℤ) - (residueRepresentative P ht n i : ℤ) =
      (t : ℤ) * (quotientCoord P ht n i : ℤ) := by
  by_cases hi : P.widths i = 1
  · have hn := (n i).isLt
    simp [GAP.dilate_widths, hi] at hn
    have hn0 : (n i : ℕ) = 0 := by omega
    simp [residueRepresentative, quotientCoord, hi, hn0]
  · have hdiv := Nat.mod_add_div (n i : ℕ) t
    have hrep : (residueRepresentative P ht n i : ℕ) = (n i : ℕ) % t := by
      simp [residueRepresentative, residueModulus, hi]
    have hquot : (quotientCoord P ht n i : ℕ) = (n i : ℕ) / t := by
      simp [quotientCoord, hi]
    have hdivZ : (((n i : ℕ) % t : ℕ) : ℤ) +
        (t : ℤ) * (((n i : ℕ) / t : ℕ) : ℤ) = (n i : ℤ) := by
      exact_mod_cast hdiv
    rw [show (residueRepresentative P ht n i : ℤ) =
        (((n i : ℕ) % t : ℕ) : ℤ) by exact_mod_cast hrep,
      show (quotientCoord P ht n i : ℤ) =
        (((n i : ℕ) / t : ℕ) : ℤ) by exact_mod_cast hquot]
    linarith

/-- The integral quotient point attached to a coefficient tuple of `tP`.
It is the difference between that point and its residue representative,
divided by `t`; the offset therefore disappears. -/
def quotientPoint (P : GAP d r) {t : ℕ} (ht : 0 < t) (n : (P.dilate t).Coord) :
    LatticePoint d :=
  integerCombination P.steps (fun i ↦ ((quotientCoord P ht n i : ℕ) : ℤ))

/-- The difference between a point of `tP` and its residue representative is
exactly `t` times its quotient point. -/
theorem coordPoint_sub_residueRepresentative (P : GAP d r) {t : ℕ} (ht : 0 < t)
    (n : (P.dilate t).Coord) :
    (fun j ↦ (P.dilate t).coordPoint n j -
      (P.dilate t).coordPoint (residueRepresentative P ht n) j) =
        fun j ↦ (t : ℤ) * quotientPoint P ht n j := by
  funext j
  simp only [GAP.coordPoint, quotientPoint, integerCombination]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sub_mul, coeff_sub_residueRepresentative P ht n i]
  rw [mul_assoc, GAP.dilate_steps]

/-- A convenient bridge from containment of a translate of `tP` to the
quotient-point hypothesis of the residue-fiber bound.  The premise `hdivide`
is where the ambient box calculation is supplied: whenever two points of
`S` differ by `t*q`, it places `q` in the finite difference container `D`. -/
theorem quotientPoint_mem_of_translate_containment (P : GAP d r) {t : ℕ}
    (ht : 0 < t) (shift : LatticePoint d) (S D : Finset (LatticePoint d))
    (hcontain : ∀ n : (P.dilate t).Coord,
      (fun j ↦ shift j + (P.dilate t).coordPoint n j) ∈ S)
    (hdivide : ∀ q : LatticePoint d,
      (∃ x ∈ S, ∃ y ∈ S, ∀ j, x j - y j = (t : ℤ) * q j) → q ∈ D) :
    ∀ n : (P.dilate t).Coord, quotientPoint P ht n ∈ D := by
  intro n
  apply hdivide
  refine ⟨fun j ↦ shift j + (P.dilate t).coordPoint n j, hcontain n,
    fun j ↦ shift j + (P.dilate t).coordPoint (residueRepresentative P ht n) j,
    hcontain (residueRepresentative P ht n), ?_⟩
  intro j
  have hj := congrFun (coordPoint_sub_residueRepresentative P ht n) j
  dsimp only at hj ⊢
  linarith

/-- Residue together with quotient point. -/
def residueCode (P : GAP d r) {t : ℕ} (ht : 0 < t) (n : (P.dilate t).Coord) :
    ResidueCoord P t × LatticePoint d :=
  (residue P ht n, quotientPoint P ht n)

/-- Properness of `P` makes the residue/quotient-point code injective. -/
theorem residueCode_injective (P : GAP d r) (hP : P.Proper) {t : ℕ} (ht : 0 < t) :
    Function.Injective (residueCode P ht) := by
  intro n m hnm
  have hres : residue P ht n = residue P ht m := congrArg Prod.fst hnm
  have hpoint : quotientPoint P ht n = quotientPoint P ht m := congrArg Prod.snd hnm
  have hquot : quotientCoord P ht n = quotientCoord P ht m := by
    apply hP
    funext j
    exact congrArg (fun z ↦ P.offset j + z) (congrFun hpoint j)
  funext i
  apply Fin.ext
  by_cases hi : P.widths i = 1
  · have hn := (n i).isLt
    have hm := (m i).isLt
    simp [GAP.dilate_widths, hi] at hn hm
    omega
  · have hrem := congrArg (fun z ↦ (z i : ℕ)) hres
    have hdiv := congrArg (fun z ↦ (z i : ℕ)) hquot
    have hrem' : (n i : ℕ) % t = (m i : ℕ) % t := by
      simpa only [residue, residueModulus, hi, ↓reduceIte] using hrem
    have hdiv' : (n i : ℕ) / t = (m i : ℕ) / t := by
      simpa only [quotientCoord, hi, ↓reduceDIte] using hdiv
    calc
      (n i : ℕ) = (n i : ℕ) % t + t * ((n i : ℕ) / t) :=
        (Nat.mod_add_div _ _).symm
      _ = (m i : ℕ) % t + t * ((m i : ℕ) / t) := by rw [hrem', hdiv']
      _ = (m i : ℕ) := Nat.mod_add_div _ _

/-- If all quotient points lie in `D`, the coefficient box of `tP` has at
most `(∏ i, residueModulus P t i) * |D|` elements. -/
theorem volume_dilate_le_residue_mul_card (P : GAP d r) (hP : P.Proper)
    {t : ℕ} (ht : 0 < t) (D : Finset (LatticePoint d))
    (hD : ∀ n : (P.dilate t).Coord, quotientPoint P ht n ∈ D) :
    (P.dilate t).volume ≤ (∏ i, residueModulus P t i) * D.card := by
  let source : Finset (P.dilate t).Coord := Finset.univ
  let target : Finset (ResidueCoord P t × LatticePoint d) := Finset.univ.product D
  have hmap : Set.MapsTo (residueCode P ht) source target := by
    intro n hn
    change residueCode P ht n ∈ target
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hD n⟩
  have hinj : (source : Set (P.dilate t).Coord).InjOn (residueCode P ht) :=
    (residueCode_injective P hP ht).injOn
  have hcard := Finset.card_le_card_of_injOn (residueCode P ht) hmap hinj
  calc
    (P.dilate t).volume = source.card := by
      change (∏ i, (t * (P.widths i - 1) + 1)) =
        Fintype.card ((i : Fin r) → Fin (t * (P.widths i - 1) + 1))
      rw [Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro i hi
      exact (Fintype.card_fin _).symm
    _ ≤ target.card := hcard
    _ = (∏ i, residueModulus P t i) * D.card := by simp [target]

/-- One coordinate of `P`, multiplied by its residue modulus, is at most
twice the corresponding coordinate of `tP`. -/
lemma residueModulus_mul_width_le (P : GAP d r) {t : ℕ} (_ht : 0 < t) (i : Fin r) :
    residueModulus P t i * P.widths i ≤ 2 * (P.dilate t).widths i := by
  by_cases hi : P.widths i = 1
  · simp [residueModulus, hi]
  · have hone : 1 ≤ P.widths i := P.width_pos i
    have hwi : 2 ≤ P.widths i :=
      Nat.succ_le_iff.mpr (lt_of_le_of_ne hone (Ne.symm hi))
    simp only [residueModulus, hi, if_false, GAP.dilate_widths]
    calc
      t * P.widths i = t * ((P.widths i - 1) + 1) :=
        congrArg (t * ·) (Nat.sub_add_cancel (P.width_pos i)).symm
      _ = t * (P.widths i - 1) + t := by simp [Nat.mul_add]
      _ ≤ 2 * (t * (P.widths i - 1) + 1) := by
        have hmul : t ≤ t * (P.widths i - 1) := by
          exact Nat.le_mul_of_pos_right t (by omega)
        omega

/-- **Residue-fiber bound.**  If all integral quotient points coming from
the dilated coefficient box lie in `D`, then the original proper GAP has
volume at most `2^r |D|`.  This is the cancellation step that replaces the
discrete John theorem in the no-dimension-increase estimate. -/
theorem volume_le_pow_two_mul_card_of_quotient_subset (P : GAP d r)
    (hP : P.Proper) {t : ℕ} (ht : 0 < t) (D : Finset (LatticePoint d))
    (hD : ∀ n : (P.dilate t).Coord, quotientPoint P ht n ∈ D) :
    P.volume ≤ 2 ^ r * D.card := by
  let M : ℕ := ∏ i, residueModulus P t i
  have hMpos : 0 < M := by
    exact Finset.prod_pos fun i _ ↦ residueModulus_pos P ht i
  have hcompare : M * P.volume ≤ 2 ^ r * (P.dilate t).volume := by
    change M * (∏ i, P.widths i) ≤
      2 ^ r * ∏ i, (P.dilate t).widths i
    dsimp [M]
    calc
      (∏ i, residueModulus P t i) * ∏ i, P.widths i =
          ∏ i, (residueModulus P t i * P.widths i) :=
        Finset.prod_mul_distrib.symm
      _ ≤ ∏ i, (2 * (P.dilate t).widths i) :=
        Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
          (fun i _ ↦ residueModulus_mul_width_le P ht i)
      _ = (∏ _i : Fin r, 2) * ∏ i, (P.dilate t).widths i :=
        Finset.prod_mul_distrib
      _ = 2 ^ r * ∏ i, (P.dilate t).widths i := by simp
  have hdilate : (P.dilate t).volume ≤ M * D.card := by
    simpa [M] using volume_dilate_le_residue_mul_card P hP ht D hD
  have hcancel : M * P.volume ≤ M * (2 ^ r * D.card) := by
    calc
      M * P.volume ≤ 2 ^ r * (P.dilate t).volume := hcompare
      _ ≤ 2 ^ r * (M * D.card) := Nat.mul_le_mul_left _ hdilate
      _ = M * (2 ^ r * D.card) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hcancel hMpos

/-- The residue-fiber bound with the usual translate-containment premise
exposed directly. -/
theorem volume_le_pow_two_mul_card_of_translate_containment (P : GAP d r)
    (hP : P.Proper) {t : ℕ} (ht : 0 < t) (shift : LatticePoint d)
    (S D : Finset (LatticePoint d))
    (hcontain : ∀ n : (P.dilate t).Coord,
      (fun j ↦ shift j + (P.dilate t).coordPoint n j) ∈ S)
    (hdivide : ∀ q : LatticePoint d,
      (∃ x ∈ S, ∃ y ∈ S, ∀ j, x j - y j = (t : ℤ) * q j) → q ∈ D) :
    P.volume ≤ 2 ^ r * D.card :=
  volume_le_pow_two_mul_card_of_quotient_subset P hP ht D
    (quotientPoint_mem_of_translate_containment P ht shift S D hcontain hdivide)

/-- Cardinal form of the residue-fiber bound. -/
theorem card_carrier_le_pow_two_mul_card_of_translate_containment (P : GAP d r)
    (hP : P.Proper) {t : ℕ} (ht : 0 < t) (shift : LatticePoint d)
    (S D : Finset (LatticePoint d))
    (hcontain : ∀ n : (P.dilate t).Coord,
      (fun j ↦ shift j + (P.dilate t).coordPoint n j) ∈ S)
    (hdivide : ∀ q : LatticePoint d,
      (∃ x ∈ S, ∃ y ∈ S, ∀ j, x j - y j = (t : ℤ) * q j) → q ∈ D) :
    P.carrier.card ≤ 2 ^ r * D.card := by
  rw [GAP.card_carrier_eq_volume P hP]
  exact volume_le_pow_two_mul_card_of_translate_containment
    P hP ht shift S D hcontain hdivide

/-- Shrink all radii by an integral factor. -/
def shrinkRadii (factor : ℕ) (radii : Fin r → ℕ) : Fin r → ℕ :=
  fun i ↦ radii i / factor

/-- A finite certificate for the conclusion of the discrete John theorem.

The outer symmetric GAP covers `points`; the GAP obtained by dividing every
radius by `factor` lies inside `points`.  The geometric theorem supplies
certificates with `factor` bounded solely in terms of the rank. -/
structure Certificate (points : Finset (LatticePoint d)) (r factor : ℕ) where
  steps : Fin r → LatticePoint d
  radii : Fin r → ℕ
  factor_pos : 0 < factor
  independent : IntegerIndependent steps
  inner_subset :
    (symmetricGAP steps (shrinkRadii factor radii)).carrier ⊆ points
  subset_outer : points ⊆ (symmetricGAP steps radii).carrier

namespace Certificate

variable {points : Finset (LatticePoint d)} {factor : ℕ}

/-- The inner progression in a discrete John certificate. -/
def inner (C : Certificate points r factor) : GAP d r :=
  symmetricGAP C.steps (shrinkRadii factor C.radii)

/-- The outer progression in a discrete John certificate. -/
def outer (C : Certificate points r factor) : GAP d r :=
  symmetricGAP C.steps C.radii

theorem inner_proper (C : Certificate points r factor) : C.inner.Proper :=
  symmetricGAP_proper C.independent _

theorem outer_proper (C : Certificate points r factor) : C.outer.Proper :=
  symmetricGAP_proper C.independent _

theorem inner_carrier_subset (C : Certificate points r factor) :
    C.inner.carrier ⊆ points := C.inner_subset

theorem subset_outer_carrier (C : Certificate points r factor) :
    points ⊆ C.outer.carrier := C.subset_outer

/-- The elementary one-coordinate comparison between an outer radius and
the radius divided by the certificate factor. -/
lemma width_le_factor_mul_width (C : Certificate points r factor) (i : Fin r) :
    2 * C.radii i + 1 ≤
      (2 * factor + 1) * (2 * (C.radii i / factor) + 1) := by
  have hmod := Nat.mod_lt (C.radii i) C.factor_pos
  have hdiv := Nat.mod_add_div (C.radii i) factor
  have hn : C.radii i ≤ factor * (C.radii i / factor + 1) := by
    calc
      C.radii i = C.radii i % factor + factor * (C.radii i / factor) := hdiv.symm
      _ ≤ factor + factor * (C.radii i / factor) :=
        Nat.add_le_add_right hmod.le _
      _ = factor * (C.radii i / factor + 1) := by
        simp [Nat.mul_add, Nat.add_comm]
  calc
    2 * C.radii i + 1 ≤
        2 * (factor * (C.radii i / factor + 1)) + 1 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hn) 1
    _ ≤ (2 * factor + 1) * (2 * (C.radii i / factor) + 1) := by
      calc
        2 * (factor * (C.radii i / factor + 1)) + 1 =
            2 * factor * (C.radii i / factor) + 2 * factor + 1 := by ring
        _ ≤ 4 * factor * (C.radii i / factor) + 2 * factor +
              2 * (C.radii i / factor) + 1 := by
          have hprod : 2 * factor * (C.radii i / factor) ≤
              4 * factor * (C.radii i / factor) := by
            gcongr
            omega
          omega
        _ = (2 * factor + 1) * (2 * (C.radii i / factor) + 1) := by ring

/-- Comparing coordinatewise and multiplying gives the volume loss in the
discrete John sandwich. -/
theorem outer_volume_le (C : Certificate points r factor) :
    C.outer.volume ≤ (2 * factor + 1) ^ r * C.inner.volume := by
  rw [outer, inner, symmetricGAP_volume, symmetricGAP_volume]
  calc
    (∏ i, (2 * C.radii i + 1)) ≤
        ∏ i, ((2 * factor + 1) * (2 * (C.radii i / factor) + 1)) :=
      Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun i _ ↦ C.width_le_factor_mul_width i)
    _ = (∏ _i : Fin r, (2 * factor + 1)) *
          ∏ i, (2 * (C.radii i / factor) + 1) := Finset.prod_mul_distrib
    _ = (2 * factor + 1) ^ r *
          ∏ i, (2 * shrinkRadii factor C.radii i + 1) := by
      simp [shrinkRadii]

/-- The outer covering progression has cardinality at most a rank-dependent
factor times the number of lattice points being covered. -/
theorem card_outer_le (C : Certificate points r factor) :
    C.outer.carrier.card ≤ (2 * factor + 1) ^ r * points.card := by
  rw [GAP.card_carrier_eq_volume C.outer C.outer_proper]
  calc
    C.outer.volume ≤ (2 * factor + 1) ^ r * C.inner.volume := C.outer_volume_le
    _ = (2 * factor + 1) ^ r * C.inner.carrier.card := by
      rw [GAP.card_carrier_eq_volume C.inner C.inner_proper]
    _ ≤ (2 * factor + 1) ^ r * points.card :=
      Nat.mul_le_mul_left _ (Finset.card_le_card C.inner_carrier_subset)

/-- Rank-sensitive polynomial growth of all dilates of the outer covering
progression.  This is the precise cardinal estimate used in the
Pham--Zakharov no-dimension-increase argument. -/
theorem card_dilate_outer_le (C : Certificate points r factor) (k : ℕ) :
    (C.outer.dilate k).carrier.card ≤
      (k + 1) ^ r * (2 * factor + 1) ^ r * points.card := by
  calc
    (C.outer.dilate k).carrier.card ≤ (C.outer.dilate k).volume :=
      GAP.card_carrier_le_volume _
    _ ≤ (k + 1) ^ r * C.outer.volume := GAP.volume_dilate_le _ _
    _ = (k + 1) ^ r * C.outer.carrier.card := by
      rw [GAP.card_carrier_eq_volume C.outer C.outer_proper]
    _ ≤ (k + 1) ^ r * ((2 * factor + 1) ^ r * points.card) :=
      Nat.mul_le_mul_left _ C.card_outer_le
    _ = (k + 1) ^ r * (2 * factor + 1) ^ r * points.card := by
      simp [Nat.mul_assoc]

end Certificate

/-! ## Unimodular coordinates and the source-shaped existence boundary -/

open Erdos186.CFP.Bilu.Mahler
open Module

noncomputable section

/-- Integral coordinates in an integral basis.  Since `b` is a basis over
`ℤ`, this is a unimodular change of lattice coordinates. -/
def basisCoordinates
    (b : Basis (Fin d) ℤ (LatticePoint d)) (x : LatticePoint d) :
    LatticePoint d :=
  fun i ↦ b.repr x i

/-- Synthesis from integral basis coordinates. -/
def basisSynthesis
    (b : Basis (Fin d) ℤ (LatticePoint d)) (z : LatticePoint d) :
    LatticePoint d :=
  b.equivFun.symm z

@[simp]
theorem basisCoordinates_basisSynthesis
    (b : Basis (Fin d) ℤ (LatticePoint d)) (z : LatticePoint d) :
    basisCoordinates b (basisSynthesis b z) = z := by
  funext i
  exact congrFun (b.equivFun.apply_symm_apply z) i

@[simp]
theorem basisSynthesis_basisCoordinates
    (b : Basis (Fin d) ℤ (LatticePoint d)) (x : LatticePoint d) :
    basisSynthesis b (basisCoordinates b x) = x := by
  change b.equivFun.symm (fun i ↦ b.repr x i) = x
  rw [← b.equivFun_apply]
  exact b.equivFun.symm_apply_apply x

theorem basisCoordinates_injective
    (b : Basis (Fin d) ℤ (LatticePoint d)) :
    Function.Injective (basisCoordinates b) := by
  intro x y hxy
  have := congrArg (basisSynthesis b) hxy
  simpa using this

theorem basisCoordinates_surjective
    (b : Basis (Fin d) ℤ (LatticePoint d)) :
    Function.Surjective (basisCoordinates b) := by
  intro z
  exact ⟨basisSynthesis b z, basisCoordinates_basisSynthesis b z⟩

@[simp]
theorem basisCoordinates_zero
    (b : Basis (Fin d) ℤ (LatticePoint d)) :
    basisCoordinates b 0 = 0 := by
  funext i
  change (b.repr 0) i = 0
  rw [map_zero]
  rfl

@[simp]
theorem basisCoordinates_add
    (b : Basis (Fin d) ℤ (LatticePoint d)) (x y : LatticePoint d) :
    basisCoordinates b (x + y) = basisCoordinates b x + basisCoordinates b y := by
  funext i
  change (b.repr (x + y)) i = (b.repr x) i + (b.repr y) i
  rw [map_add]
  rfl

@[simp]
theorem basisCoordinates_sub
    (b : Basis (Fin d) ℤ (LatticePoint d)) (x y : LatticePoint d) :
    basisCoordinates b (x - y) = basisCoordinates b x - basisCoordinates b y := by
  funext i
  change (b.repr (x - y)) i = (b.repr x) i - (b.repr y) i
  rw [map_sub]
  rfl

/-- Image of a finite lattice set under a unimodular coordinate map. -/
def coordinateImage
    (b : Basis (Fin d) ℤ (LatticePoint d))
    (S : Finset (LatticePoint d)) : Finset (LatticePoint d) :=
  S.image (basisCoordinates b)

@[simp]
theorem card_coordinateImage
    (b : Basis (Fin d) ℤ (LatticePoint d))
    (S : Finset (LatticePoint d)) :
    (coordinateImage b S).card = S.card := by
  exact Finset.card_image_of_injective S (basisCoordinates_injective b)

/-- The finite difference set `S - T`. -/
def differenceFinset (S T : Finset (LatticePoint d)) :
    Finset (LatticePoint d) :=
  S.image₂ (fun x y ↦ x - y) T

@[simp]
theorem mem_differenceFinset {S T : Finset (LatticePoint d)}
    {z : LatticePoint d} :
    z ∈ differenceFinset S T ↔ ∃ x ∈ S, ∃ y ∈ T, x - y = z := by
  simp [differenceFinset]

/-- A unimodular coordinate change commutes exactly with finite difference
bodies. -/
theorem coordinateImage_differenceFinset
    (b : Basis (Fin d) ℤ (LatticePoint d))
    (S T : Finset (LatticePoint d)) :
    coordinateImage b (differenceFinset S T) =
      differenceFinset (coordinateImage b S) (coordinateImage b T) := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_differenceFinset.mp hw
    subst w
    subst z
    exact mem_differenceFinset.mpr
      ⟨basisCoordinates b x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        basisCoordinates b y, Finset.mem_image.mpr ⟨y, hy, rfl⟩,
        (basisCoordinates_sub b x y).symm⟩
  · intro hz
    obtain ⟨x', hx', y', hy', hxy'⟩ := mem_differenceFinset.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy'
    rw [← basisCoordinates_sub] at hxy'
    apply Finset.mem_image.mpr
    exact ⟨x - y, mem_differenceFinset.mpr ⟨x, hx, y, hy, rfl⟩, hxy'⟩

@[simp]
theorem card_coordinateImage_differenceFinset
    (b : Basis (Fin d) ℤ (LatticePoint d))
    (S T : Finset (LatticePoint d)) :
    (differenceFinset (coordinateImage b S) (coordinateImage b T)).card =
      (differenceFinset S T).card := by
  rw [← coordinateImage_differenceFinset]
  exact card_coordinateImage b (differenceFinset S T)

/-- The centered integer coordinate box with half-widths `radii`. -/
def centeredCoordinateBox (radii : Fin r → ℕ) :
    Finset (LatticePoint r) :=
  Fintype.piFinset fun i ↦ Finset.Icc (-(radii i : ℤ)) (radii i : ℤ)

@[simp]
theorem mem_centeredCoordinateBox {radii : Fin r → ℕ}
    {z : LatticePoint r} :
    z ∈ centeredCoordinateBox radii ↔
      ∀ i, -(radii i : ℤ) ≤ z i ∧ z i ≤ (radii i : ℤ) := by
  simp [centeredCoordinateBox]

@[simp]
theorem card_centeredCoordinateBox (radii : Fin r → ℕ) :
    (centeredCoordinateBox radii).card = ∏ i, (2 * radii i + 1) := by
  simp only [centeredCoordinateBox, Fintype.card_piFinset,
    Int.card_Icc]
  apply Finset.prod_congr rfl
  intro i _hi
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg (by omega)]
  push_cast
  ring

/-- Evaluating an integral basis combination and embedding it in real
coordinates commutes with the finite sum. -/
theorem integralEmbed_integerCombination
    (steps : Fin r → LatticePoint d) (z : Fin r → ℤ) :
    integralEmbed (integerCombination steps z) =
      ∑ i, (z i : ℝ) • integralEmbed (steps i) := by
  funext j
  simp [integralEmbed, integerCombination]

/-- Synthesis in an integral basis is the `integerCombination` used by the
GAP interface. -/
theorem basisSynthesis_eq_integerCombination
    (b : Basis (Fin d) ℤ (LatticePoint d)) (z : LatticePoint d) :
    basisSynthesis b z = integerCombination (fun i ↦ b i) z := by
  rw [basisSynthesis, Basis.equivFun_symm_apply]
  funext j
  simp [integerCombination]

/-- An integral basis is independent in the exact sense required by a
proper symmetric GAP. -/
theorem integerIndependent_basis
    (b : Basis (Fin d) ℤ (LatticePoint d)) :
    IntegerIndependent (fun i ↦ b i) := by
  intro z w hzw
  rw [← basisSynthesis_eq_integerCombination b z,
    ← basisSynthesis_eq_integerCombination b w] at hzw
  exact b.equivFun.symm.injective hzw

/-- Membership in a symmetric GAP generated by an integral basis is exactly
the corresponding coordinatewise centered-box condition. -/
theorem mem_symmetricGAP_basis_iff
    (b : Basis (Fin d) ℤ (LatticePoint d)) (radii : Fin d → ℕ)
    (x : LatticePoint d) :
    x ∈ (symmetricGAP (fun i ↦ b i) radii).carrier ↔
      ∀ i, -(radii i : ℤ) ≤ basisCoordinates b x i ∧
        basisCoordinates b x i ≤ (radii i : ℤ) := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := GAP.mem_carrier_iff.mp hx
    have hcoord : basisCoordinates b x =
        fun i ↦ (n i : ℤ) - (radii i : ℤ) := by
      rw [← hn, symmetricGAP_coordPoint,
        ← basisSynthesis_eq_integerCombination]
      exact basisCoordinates_basisSynthesis _ _
    intro i
    have hi := congrFun hcoord i
    have hnlt := (n i).isLt
    change (n i : ℕ) < 2 * radii i + 1 at hnlt
    change -(radii i : ℤ) ≤ basisCoordinates b x i ∧
      basisCoordinates b x i ≤ (radii i : ℤ)
    rw [hi]
    constructor <;> omega
  · intro hx
    let n : (symmetricGAP (fun i ↦ b i) radii).Coord := fun i ↦
      ⟨(basisCoordinates b x i + (radii i : ℤ)).toNat, by
        have hi := hx i
        have hnonneg : 0 ≤ basisCoordinates b x i + (radii i : ℤ) := by
          omega
        have hcast := Int.toNat_of_nonneg hnonneg
        change (basisCoordinates b x i + (radii i : ℤ)).toNat <
          2 * radii i + 1
        omega⟩
    apply GAP.mem_carrier_iff.mpr
    refine ⟨n, ?_⟩
    rw [symmetricGAP_coordPoint, ← basisSynthesis_eq_integerCombination]
    have hn : (fun i ↦ (n i : ℤ) - (radii i : ℤ)) =
        basisCoordinates b x := by
      funext i
      have hi := hx i
      have hnonneg : 0 ≤ basisCoordinates b x i + (radii i : ℤ) := by
        omega
      change (((basisCoordinates b x i + (radii i : ℤ)).toNat : ℕ) : ℤ) -
          (radii i : ℤ) = basisCoordinates b x i
      rw [Int.toNat_of_nonneg hnonneg]
      ring
    rw [hn, basisSynthesis_basisCoordinates]

/-- Topological data for a closed symmetric convex body in coordinate real
space.  The neighbourhood condition is the source's nonempty-interior
hypothesis centered at zero; boundedness makes its gauge definite. -/
structure SymmetricConvexBody (K : Set (Fin d → ℝ)) : Prop where
  balanced : Balanced ℝ K
  convex : Convex ℝ K
  nhds_zero : K ∈ nhds 0
  bounded : Bornology.IsVonNBounded ℝ K
  isClosed : IsClosed K

namespace SymmetricConvexBody

/-- The Minkowski functional of a symmetric convex body. -/
noncomputable def seminorm {K : Set (Fin d → ℝ)}
    (hK : SymmetricConvexBody K) : Seminorm ℝ (Fin d → ℝ) :=
  gaugeSeminorm hK.balanced hK.convex (absorbent_nhds_zero hK.nhds_zero)

theorem seminorm_definite {K : Set (Fin d → ℝ)}
    (hK : SymmetricConvexBody K) : IsDefinite hK.seminorm :=
  isDefinite_gaugeSeminorm hK.balanced hK.convex
    (absorbent_nhds_zero hK.nhds_zero) hK.bounded

/-- Closed-body membership is exactly the closed unit ball of the gauge. -/
theorem seminorm_le_one_iff_mem {K : Set (Fin d → ℝ)}
    (hK : SymmetricConvexBody K) (x : Fin d → ℝ) :
    hK.seminorm x ≤ 1 ↔ x ∈ K := by
  change gauge K x ≤ 1 ↔ x ∈ K
  rw [gauge_le_one_iff_mem_closure hK.convex hK.nhds_zero,
    hK.isClosed.closure_eq]

end SymmetricConvexBody

/-- The exact, source-shaped discrete-John existence proposition.  It says
that in each ambient dimension there is a uniform factor bound, and returns
the actual rank `e ≤ d`; it is intentionally a proposition, not an assumed
inhabitant. -/
def DiscreteJohnStatement : Prop :=
  ∀ d : ℕ, ∃ factorBound : ℕ,
    ∀ (K : Set (Fin d → ℝ)) (hK : SymmetricConvexBody K)
      (points : Finset (LatticePoint d)),
      (∀ z, z ∈ points ↔ integralEmbed z ∈ K) →
        ∃ (e factor : ℕ), e ≤ d ∧ factor ≤ factorBound ∧
          Nonempty (Certificate points e factor)

/-- The precise extra successive-minimum information needed after a Mahler
basis has been chosen.  `outer_coordinate_bound` is the covering half of
the geometry-of-numbers argument, while `inner_budget` is the packing half.
Keeping both fields explicit prevents `MahlerBasisStatement` from being
silently strengthened. -/
structure FullRankMinimaData
    (p : Seminorm ℝ (Fin d → ℝ))
    (b : Basis (Fin d) ℤ (LatticePoint d)) where
  factor : ℕ
  radii : Fin d → ℕ
  factor_pos : 0 < factor
  mahler : IsMahlerBasis p b
  outer_coordinate_bound :
    ∀ z : LatticePoint d, p (integralEmbed z) ≤ 1 →
      ∀ i, |b.repr z i| ≤ (radii i : ℤ)
  inner_budget :
    (∑ i, ((radii i / factor : ℕ) : ℝ) *
      p (integralEmbed (b i))) ≤ 1

/-- Construct the full-rank finite certificate from the exact
Mahler/successive-minimum data. -/
noncomputable def certificateOfFullRankMinimaData
    (p : Seminorm ℝ (Fin d → ℝ))
    (b : Basis (Fin d) ℤ (LatticePoint d))
    (D : FullRankMinimaData p b)
    (points : Finset (LatticePoint d))
    (hpoints : ∀ z, z ∈ points ↔ p (integralEmbed z) ≤ 1) :
    Certificate points d D.factor where
  steps := fun i ↦ b i
  radii := D.radii
  factor_pos := D.factor_pos
  independent := integerIndependent_basis b
  inner_subset := by
    intro z hz
    rw [hpoints]
    rw [mem_symmetricGAP_basis_iff] at hz
    let c : Fin d → ℤ := basisCoordinates b z
    have hc (i : Fin d) : |c i| ≤ (D.radii i / D.factor : ℕ) := by
      exact abs_le.mpr (hz i)
    have hcReal (i : Fin d) : |(c i : ℝ)| ≤
        ((D.radii i / D.factor : ℕ) : ℝ) := by
      let q : ℕ := D.radii i / D.factor
      have hc' : |c i| ≤ (q : ℤ) := hc i
      have hcast : ((|c i| : ℤ) : ℝ) ≤ ((q : ℤ) : ℝ) :=
        (Int.cast_le).2 hc'
      change |(c i : ℝ)| ≤ (q : ℝ)
      simpa only [Int.cast_abs, Int.cast_natCast] using hcast
    have hzSynth : integralEmbed z =
        ∑ i, (c i : ℝ) • integralEmbed (b i) := by
      rw [← integralEmbed_integerCombination]
      change integralEmbed z =
        integralEmbed (integerCombination (fun i ↦ b i) c)
      congr 1
      rw [← basisSynthesis_eq_integerCombination,
        basisSynthesis_basisCoordinates]
    rw [hzSynth]
    refine (Erdos186.CFP.Bilu.Mahler.seminorm_sum_le p
      (fun i ↦ (c i : ℝ)) (fun i ↦ integralEmbed (b i))).trans ?_
    exact (Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_right (hcReal i)
        (apply_nonneg p (integralEmbed (b i)))).trans D.inner_budget
  subset_outer := by
    intro z hz
    rw [mem_symmetricGAP_basis_iff]
    intro i
    exact abs_le.mp (D.outer_coordinate_bound z ((hpoints z).mp hz) i)

/-- Body form of `certificateOfFullRankMinimaData`. -/
noncomputable def certificateOfFullRankMinimaDataBody
    {K : Set (Fin d → ℝ)} (hK : SymmetricConvexBody K)
    (b : Basis (Fin d) ℤ (LatticePoint d))
    (D : FullRankMinimaData hK.seminorm b)
    (points : Finset (LatticePoint d))
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K) :
    Certificate points d D.factor :=
  certificateOfFullRankMinimaData hK.seminorm b D points fun z ↦ by
    rw [hpoints, hK.seminorm_le_one_iff_mem]

/-- The remaining successive-minimum box statement, separated from
Mahler's basis theorem. -/
def FullRankMinimaStatement : Prop :=
  ∀ (d : ℕ) (p : Seminorm ℝ (Fin d → ℝ)), IsDefinite p →
    ∀ b : Basis (Fin d) ℤ (LatticePoint d), IsMahlerBasis p b →
      Nonempty (FullRankMinimaData p b)

/-- Mahler basis existence plus the explicit successive-minimum box input
constructs a full-rank certificate for every exact lattice section. -/
theorem exists_fullRank_certificate_of_mahlerBasisStatement
    (hMahler : MahlerBasisStatement) (hMinima : FullRankMinimaStatement)
    {K : Set (Fin d → ℝ)} (hK : SymmetricConvexBody K)
    (points : Finset (LatticePoint d))
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K) :
    ∃ factor : ℕ, Nonempty (Certificate points d factor) := by
  obtain ⟨b, hb⟩ := hMahler d hK.seminorm hK.seminorm_definite
  obtain ⟨D⟩ := hMinima d hK.seminorm hK.seminorm_definite b hb
  exact ⟨D.factor,
    ⟨certificateOfFullRankMinimaDataBody hK b D points hpoints⟩⟩

end

end DiscreteJohn

end Erdos186
