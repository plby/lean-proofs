/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Centering

/-!
# Real and rational dilations of centered GAP presentations

For a homogeneous GAP written with integer coefficient intervals
`lower i ≤ z i ≤ upper i`, Conlon--Fox--Pham define the real dilation
`qP` by requiring the still-integral coefficient `z i` to satisfy

`q * lower i ≤ z i ≤ q * upper i`.

Thus its finite integer-coordinate interval has endpoints
`ceil (q * lower i)` and `floor (q * upper i)`.  This file packages that
definition for the asymmetric `CenteredCertificate` of `CFP/Centering.lean`
and proves the exact bridge to the repository's natural-number `GAP.dilate`.
-/

namespace Erdos186.CFP

open scoped BigOperators Pointwise

noncomputable section

namespace CenteredCertificate

variable {d r : ℕ} {P : GAP d r}

/-- The first integral coefficient allowed by the real dilation `qP`. -/
def realLower (hP : CenteredCertificate P) (q : ℝ) (i : Fin r) : ℤ :=
  ⌈q * (hP.lower i : ℝ)⌉

/-- The last integral coefficient allowed by the real dilation `qP`. -/
def realUpper (hP : CenteredCertificate P) (q : ℝ) (i : Fin r) : ℤ :=
  ⌊q * (hP.upper i : ℝ)⌋

/-- The CFP real-scaled box predicate.  Its coordinates remain integral. -/
def InRealBox (hP : CenteredCertificate P) (q : ℝ)
    (z : Fin r → ℤ) : Prop :=
  ∀ i, q * (hP.lower i : ℝ) ≤ (z i : ℝ) ∧
    (z i : ℝ) ≤ q * (hP.upper i : ℝ)

/-- A finite coordinate tuple for `qP`, using the equivalent ceiling and
floor bounds. -/
abbrev RealCoord (hP : CenteredCertificate P) (q : ℝ) :=
  (i : Fin r) → {z : ℤ // z ∈ Finset.Icc (hP.realLower q i) (hP.realUpper q i)}

/-- Evaluation of a finite real-dilation coordinate tuple. -/
def realCoordPoint (hP : CenteredCertificate P) (q : ℝ)
    (z : hP.RealCoord q) : LatticePoint d :=
  hP.relativePoint fun i ↦ z i

/-- CFP's real dilation `qP`, represented as a finite carrier. -/
def realDilateCarrier (hP : CenteredCertificate P) (q : ℝ) :
    Finset (LatticePoint d) :=
  Finset.univ.image (hP.realCoordPoint q)

/-- Properness of the displayed real dilation: the linear evaluation is
injective on its integral coefficient box.  Formulating this as `Set.InjOn`
makes it convenient to compare different scale parameters. -/
def RealDilateProper (hP : CenteredCertificate P) (q : ℝ) : Prop :=
  Set.InjOn hP.relativePoint {z | hP.InRealBox q z}

theorem mem_realCoord_iff (hP : CenteredCertificate P) (q : ℝ)
    (z : Fin r → ℤ) :
    (∀ i, z i ∈ Finset.Icc (hP.realLower q i) (hP.realUpper q i)) ↔
      hP.InRealBox q z := by
  constructor
  · intro hz i
    have hi := hz i
    simp only [Finset.mem_Icc, realLower, realUpper] at hi
    exact ⟨(Int.ceil_le.mp hi.1), (Int.le_floor.mp hi.2)⟩
  · intro hz i
    have hi := hz i
    simp only [Finset.mem_Icc, realLower, realUpper]
    exact ⟨Int.ceil_le.mpr hi.1, Int.le_floor.mpr hi.2⟩

/-- Exact membership characterization of the finite real dilation. -/
theorem mem_realDilateCarrier_iff (hP : CenteredCertificate P) (q : ℝ)
    {x : LatticePoint d} :
    x ∈ hP.realDilateCarrier q ↔
      ∃ z : Fin r → ℤ, hP.InRealBox q z ∧ hP.relativePoint z = x := by
  classical
  constructor
  · intro hx
    simp only [realDilateCarrier, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨fun i ↦ z i, ?_, rfl⟩
    exact hP.mem_realCoord_iff q (fun i ↦ z i) |>.mp (fun i ↦ (z i).property)
  · rintro ⟨z, hz, rfl⟩
    let z' : hP.RealCoord q := fun i ↦
      ⟨z i, (hP.mem_realCoord_iff q z).mpr hz i⟩
    exact Finset.mem_image.mpr ⟨z', Finset.mem_univ _, rfl⟩

/-- `RealDilateProper` is precisely injectivity of the finite ceiling/floor
coordinate presentation used to define `realDilateCarrier`. -/
theorem realDilateProper_iff_injective_realCoordPoint
    (hP : CenteredCertificate P) (q : ℝ) :
    hP.RealDilateProper q ↔ Function.Injective (hP.realCoordPoint q) := by
  constructor
  · intro hproper z z' hzz'
    have hz : hP.InRealBox q (fun i ↦ z i) :=
      (hP.mem_realCoord_iff q (fun i ↦ z i)).mp (fun i ↦ (z i).property)
    have hz' : hP.InRealBox q (fun i ↦ z' i) :=
      (hP.mem_realCoord_iff q (fun i ↦ z' i)).mp (fun i ↦ (z' i).property)
    have hcoeff := hproper hz hz' hzz'
    funext i
    exact Subtype.ext (congrFun hcoeff i)
  · intro hinj z hz z' hz' hzz'
    let c : hP.RealCoord q := fun i ↦
      ⟨z i, (hP.mem_realCoord_iff q z).mpr hz i⟩
    let c' : hP.RealCoord q := fun i ↦
      ⟨z' i, (hP.mem_realCoord_iff q z').mpr hz' i⟩
    have hcc' : c = c' := hinj hzz'
    funext i
    exact congrArg (fun w ↦ (w i : ℤ)) hcc'

theorem zero_mem_realDilateCarrier (hP : CenteredCertificate P)
    {q : ℝ} (hq : 0 ≤ q) :
    0 ∈ hP.realDilateCarrier q := by
  apply (hP.mem_realDilateCarrier_iff q).mpr
  refine ⟨0, ?_, ?_⟩
  · intro i
    have hlo : (hP.lower i : ℝ) ≤ 0 := by exact_mod_cast hP.lower_nonpos i
    have hup : 0 ≤ (hP.upper i : ℝ) := by exact_mod_cast hP.upper_nonneg i
    constructor <;> simp only [Pi.zero_apply, Int.cast_zero]
    · exact mul_nonpos_of_nonneg_of_nonpos hq hlo
    · exact mul_nonneg hq hup
  · funext j
    simp [relativePoint]

/-- Enlarging a nonnegative scale enlarges the real dilation. -/
theorem realDilateCarrier_mono (hP : CenteredCertificate P)
    {q q' : ℝ} (_hq : 0 ≤ q) (hqq' : q ≤ q') :
    hP.realDilateCarrier q ⊆ hP.realDilateCarrier q' := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := (hP.mem_realDilateCarrier_iff q).mp hx
  apply (hP.mem_realDilateCarrier_iff q').mpr
  refine ⟨z, ?_, rfl⟩
  intro i
  have hlo : (hP.lower i : ℝ) ≤ 0 := by exact_mod_cast hP.lower_nonpos i
  have hup : 0 ≤ (hP.upper i : ℝ) := by exact_mod_cast hP.upper_nonneg i
  exact ⟨(mul_le_mul_of_nonpos_right hqq' hlo).trans (hz i).1,
    (hz i).2.trans (mul_le_mul_of_nonneg_right hqq' hup)⟩

/-- An integer-scaled centered box is contained in every larger real-scaled
box. -/
theorem integerBox_subset_realBox (hP : CenteredCertificate P)
    {k : ℕ} {q : ℝ} (_hq : 0 ≤ q) (hkq : (k : ℝ) ≤ q)
    {z : Fin r → ℤ}
    (hz : ∀ i, (k : ℤ) * hP.lower i ≤ z i ∧
      z i ≤ (k : ℤ) * hP.upper i) :
    hP.InRealBox q z := by
  intro i
  have hlo : (hP.lower i : ℝ) ≤ 0 := by exact_mod_cast hP.lower_nonpos i
  have hup : 0 ≤ (hP.upper i : ℝ) := by exact_mod_cast hP.upper_nonneg i
  have hzlo : (k : ℝ) * (hP.lower i : ℝ) ≤ (z i : ℝ) := by
    exact_mod_cast (hz i).1
  have hzup : (z i : ℝ) ≤ (k : ℝ) * (hP.upper i : ℝ) := by
    exact_mod_cast (hz i).2
  exact ⟨(mul_le_mul_of_nonpos_right hkq hlo).trans hzlo,
    hzup.trans (mul_le_mul_of_nonneg_right hkq hup)⟩

/-- The carrier of the integral dilation `kP` is contained in the CFP real
dilation `qP` whenever `0 ≤ k ≤ q`. -/
theorem dilate_carrier_subset_realDilateCarrier (hP : CenteredCertificate P)
    {k : ℕ} {q : ℝ} (hq : 0 ≤ q) (hkq : (k : ℝ) ≤ q) :
    (P.dilate k).carrier ⊆ hP.realDilateCarrier q := by
  intro x hx
  obtain ⟨z, hz, hx⟩ := (hP.mem_dilate_carrier_iff_exists_inBox k).mp hx
  exact (hP.mem_realDilateCarrier_iff q).mpr
    ⟨z, hP.integerBox_subset_realBox hq hkq hz, hx⟩

/-- At a natural-number scale, the real-dilation definition agrees exactly
with both `GAP.dilate` and the `k`-fold pointwise sumset. -/
theorem realDilateCarrier_natCast (hP : CenteredCertificate P) (k : ℕ) :
    hP.realDilateCarrier (k : ℝ) = (P.dilate k).carrier := by
  ext x
  rw [hP.mem_realDilateCarrier_iff, hP.mem_dilate_carrier_iff_exists_inBox]
  constructor
  · rintro ⟨z, hz, hx⟩
    refine ⟨z, ?_, hx⟩
    intro i
    constructor
    · exact_mod_cast (hz i).1
    · exact_mod_cast (hz i).2
  · rintro ⟨z, hz, hx⟩
    refine ⟨z, ?_, hx⟩
    intro i
    constructor
    · exact_mod_cast (hz i).1
    · exact_mod_cast (hz i).2

theorem realDilateCarrier_natCast_eq_nsmul (hP : CenteredCertificate P)
    (k : ℕ) :
    hP.realDilateCarrier (k : ℝ) = k • P.carrier := by
  rw [hP.realDilateCarrier_natCast, dilate_carrier_eq_nsmul_carrier]

/-- Properness of a real dilation descends to every smaller integral
dilation. -/
theorem dilate_proper_of_realDilateProper (hP : CenteredCertificate P)
    {k : ℕ} {q : ℝ} (hproper : hP.RealDilateProper q)
    (hq : 0 ≤ q) (hkq : (k : ℝ) ≤ q) :
    (P.dilate k).Proper := by
  intro n m hnm
  have hnBounds := (hP.dilate k).relativeCoeff_mem_box n
  have hmBounds := (hP.dilate k).relativeCoeff_mem_box m
  simp only [InBox, dilate_lower, dilate_upper] at hnBounds hmBounds
  have hnReal := hP.integerBox_subset_realBox hq hkq hnBounds
  have hmReal := hP.integerBox_subset_realBox hq hkq hmBounds
  have heval :
      hP.relativePoint ((hP.dilate k).relativeCoeff n) =
        hP.relativePoint ((hP.dilate k).relativeCoeff m) := by
    rw [← hP.dilate_relativePoint k, ← hP.dilate_relativePoint k,
      ← (hP.dilate k).coordPoint_eq_relativePoint,
      ← (hP.dilate k).coordPoint_eq_relativePoint]
    exact hnm
  have hcoeff := hproper hnReal hmReal heval
  funext i
  have hi := congrFun hcoeff i
  simp only [relativeCoeff] at hi
  exact Fin.ext (Int.ofNat_inj.mp (sub_left_injective hi))

/-! ## Floor and rational specializations -/

/-- The largest natural scale below a nonnegative real scale embeds in that
real dilation. -/
theorem dilate_natFloor_subset_realDilateCarrier (hP : CenteredCertificate P)
    {q : ℝ} (hq : 0 ≤ q) :
    (P.dilate ⌊q⌋₊).carrier ⊆ hP.realDilateCarrier q := by
  apply hP.dilate_carrier_subset_realDilateCarrier hq
  exact_mod_cast Nat.floor_le hq

theorem dilate_natFloor_proper_of_realDilateProper
    (hP : CenteredCertificate P) {q : ℝ}
    (hproper : hP.RealDilateProper q) (hq : 0 ≤ q) :
    (P.dilate ⌊q⌋₊).Proper := by
  apply hP.dilate_proper_of_realDilateProper hproper hq
  exact_mod_cast Nat.floor_le hq

/-- Rational version of the integer-to-real inclusion bridge. -/
theorem dilate_carrier_subset_rationalDilateCarrier
    (hP : CenteredCertificate P) {k : ℕ} {q : ℚ}
    (hq : 0 ≤ q) (hkq : (k : ℚ) ≤ q) :
    (P.dilate k).carrier ⊆ hP.realDilateCarrier (q : ℝ) := by
  apply hP.dilate_carrier_subset_realDilateCarrier
  · exact_mod_cast hq
  · exact_mod_cast hkq

/-- Rational version of properness descent. -/
theorem dilate_proper_of_rationalDilateProper
    (hP : CenteredCertificate P) {k : ℕ} {q : ℚ}
    (hproper : hP.RealDilateProper (q : ℝ))
    (hq : 0 ≤ q) (hkq : (k : ℚ) ≤ q) :
    (P.dilate k).Proper := by
  apply hP.dilate_proper_of_realDilateProper hproper
  · exact_mod_cast hq
  · exact_mod_cast hkq

end CenteredCertificate
end
end Erdos186.CFP
