/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# Centering a GAP at the origin

This file formalizes Claim 2.6 of Conlon--Fox--Pham: a generalized
arithmetic progression which contains zero admits a presentation whose
coefficient interval in every direction crosses zero.

There is a small terminological point.  `GAP.Centered` in
`CFP/SymmetricGAP.lean` describes a *symmetric* box, with bounds `-ρ` and
`ρ`.  CFP's Claim 2.6 only asserts that the (possibly asymmetric) bounds
cross zero.  `CenteredCertificate` below is the latter notion.

The repository's `GAP` structure stores the one-sided bounds
`0 ≤ n i < widths i`.  If `center` is a coordinate tuple displaying zero,
then subtracting `center i` from the `i`-th coefficient gives the integer
bounds

`-(center i) ≤ z i ≤ widths i - 1 - center i`.

We retain the one-sided `GAP` as the underlying finite presentation and
package the shifted integer box as a certificate.  We also construct the
literally re-presented `GAP` whose offset is the negative combination of the
chosen center coordinates and prove that it is equal to the original GAP.
Consequently carrier, steps, widths, volume, properness, and every integral
dilation are preserved.
-/

namespace Erdos186.CFP

open scoped BigOperators Pointwise

variable {d r : ℕ}

/-! ## Integral GAP dilations are multifold sumsets -/

/-- A natural number at most `k * L` is a sum of `k` natural numbers, each
at most `L`. -/
private theorem exists_bounded_fin_sum (k L t : ℕ) (ht : t ≤ k * L) :
    ∃ f : Fin k → Fin (L + 1), ∑ q, (f q : ℕ) = t := by
  induction k generalizing t with
  | zero =>
      have ht0 : t = 0 := by simpa using ht
      subst t
      exact ⟨Fin.elim0, by simp⟩
  | succ k ih =>
      by_cases hsmall : t ≤ L
      · let f : Fin (k + 1) → Fin (L + 1) :=
          Fin.cons ⟨t, Nat.lt_succ_of_le hsmall⟩ (fun _ ↦ 0)
        refine ⟨f, ?_⟩
        simp [f, Fin.sum_univ_succ]
      · have hL : L ≤ t := le_of_lt (Nat.lt_of_not_ge hsmall)
        have hrest : t - L ≤ k * L := by
          rw [Nat.succ_mul] at ht
          omega
        obtain ⟨g, hg⟩ := ih (t - L) hrest
        let f : Fin (k + 1) → Fin (L + 1) :=
          Fin.cons ⟨L, Nat.lt_succ_self L⟩ g
        refine ⟨f, ?_⟩
        rw [Fin.sum_univ_succ]
        simp only [f, Fin.cons_zero, Fin.cons_succ]
        rw [hg]
        omega

/-- A coordinate in the `k`-dilated interval is a sum of `k` coordinates
in the original interval. -/
private theorem exists_coord_decomposition (k w t : ℕ) (hw : 0 < w)
    (ht : t < k * (w - 1) + 1) :
    ∃ f : Fin k → Fin w, ∑ q, (f q : ℕ) = t := by
  have ht' : t ≤ k * (w - 1) := by omega
  obtain ⟨g, hg⟩ := exists_bounded_fin_sum k (w - 1) t ht'
  have hwidth : w - 1 + 1 = w := by omega
  let f : Fin k → Fin w :=
    fun q ↦ ⟨g q, by simpa [hwidth] using (g q).isLt⟩
  refine ⟨f, ?_⟩
  simpa [f] using hg

/-- The carrier of the repository's natural-number dilation is exactly the
`k`-fold pointwise sumset of the original carrier.  In particular, although
`GAP.dilate` is defined from a presentation, its carrier for integral `k`
depends only on the original carrier as a finite set. -/
theorem dilate_carrier_eq_nsmul_carrier (P : GAP d r) (k : ℕ) :
    (P.dilate k).carrier = k • P.carrier := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := GAP.mem_carrier_iff.mp hx
    have hdecomp (i : Fin r) :
        ∃ f : Fin k → Fin (P.widths i), ∑ q, (f q : ℕ) = (n i : ℕ) :=
      exists_coord_decomposition k (P.widths i) (n i) (P.width_pos i) (n i).isLt
    choose coeff hcoeff using hdecomp
    let coords : Fin k → P.Coord := fun q i ↦ coeff i q
    let points : Fin k → {y // y ∈ P.carrier} := fun q ↦
      ⟨P.coordPoint (coords q), P.coordPoint_mem_carrier (coords q)⟩
    rw [Finset.mem_nsmul]
    refine ⟨points, ?_⟩
    rw [List.sum_ofFn, ← hn]
    ext j
    simp only [points, coords, GAP.coordPoint, GAP.dilate_offset, GAP.dilate_steps,
      Finset.sum_apply]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]
    congr 1
    exact_mod_cast hcoeff i
  · intro hx
    rw [Finset.mem_nsmul] at hx
    obtain ⟨points, hpoints⟩ := hx
    have hexists (q : Fin k) : ∃ n : P.Coord, P.coordPoint n = points q :=
      GAP.mem_carrier_iff.mp (points q).property
    choose repr hrepr using hexists
    let total : Fin r → ℕ := fun i ↦ ∑ q, (repr q i : ℕ)
    have total_lt (i : Fin r) : total i < k * (P.widths i - 1) + 1 := by
      have hterm (q : Fin k) : (repr q i : ℕ) ≤ P.widths i - 1 := by
        have := (repr q i).isLt
        omega
      calc
        total i ≤ ∑ _q : Fin k, (P.widths i - 1) := by
          exact Finset.sum_le_sum fun q _ ↦ hterm q
        _ = k * (P.widths i - 1) := by simp
        _ < k * (P.widths i - 1) + 1 := Nat.lt_succ_self _
    let n : (P.dilate k).Coord := fun i ↦ ⟨total i, total_lt i⟩
    refine GAP.mem_carrier_iff.mpr ⟨n, ?_⟩
    rw [← hpoints, List.sum_ofFn]
    ext j
    have hrepr' (q : Fin k) :
        (points q : LatticePoint d) = P.coordPoint (repr q) := (hrepr q).symm
    simp_rw [hrepr']
    simp only [GAP.coordPoint, GAP.dilate_offset, GAP.dilate_steps, n, total,
      Finset.sum_apply]
    push_cast
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]

/-- Consequently, two GAP presentations of the same finite carrier have the
same carrier after every integral dilation. -/
theorem dilate_carrier_eq_of_carrier_eq {P Q : GAP d r}
    (hcarrier : P.carrier = Q.carrier) (k : ℕ) :
    (P.dilate k).carrier = (Q.dilate k).carrier := by
  rw [dilate_carrier_eq_nsmul_carrier, dilate_carrier_eq_nsmul_carrier,
    hcarrier]

/-- A witness that a GAP is centered in the sense of CFP Claim 2.6: a
displayed coordinate tuple evaluates to the origin.  Its shifted coefficient
bounds are defined below and are allowed to be asymmetric. -/
structure CenteredCertificate (P : GAP d r) where
  center : P.Coord
  coordPoint_center : P.coordPoint center = 0

namespace CenteredCertificate

variable {P : GAP d r}

/-- The lower endpoint after translating the chosen coordinate tuple to
zero. -/
def lower (hP : CenteredCertificate P) (i : Fin r) : ℤ :=
  -(hP.center i : ℤ)

/-- The upper endpoint after translating the chosen coordinate tuple to
zero. -/
def upper (hP : CenteredCertificate P) (i : Fin r) : ℤ :=
  (P.widths i : ℤ) - 1 - (hP.center i : ℤ)

/-- The coefficient of a one-sided coordinate after shifting the coordinate
which displays zero to the origin. -/
def relativeCoeff (hP : CenteredCertificate P) (n : P.Coord) (i : Fin r) : ℤ :=
  (n i : ℤ) - (hP.center i : ℤ)

/-- Evaluation using the integer coefficients of the centered
presentation. -/
def relativePoint (_hP : CenteredCertificate P) (z : Fin r → ℤ) :
    LatticePoint d :=
  fun j ↦ ∑ i, z i * P.steps i j

/-- Membership in the shifted integer coefficient box. -/
def InBox (hP : CenteredCertificate P) (z : Fin r → ℤ) : Prop :=
  ∀ i, hP.lower i ≤ z i ∧ z i ≤ hP.upper i

/-- The original offset is the negative of the linear combination specified
by the coordinate tuple which displays zero. -/
theorem offset_eq (hP : CenteredCertificate P) :
    P.offset = fun j ↦ -∑ i, (hP.center i : ℤ) * P.steps i j := by
  funext j
  have hj := congrFun hP.coordPoint_center j
  simp only [GAP.coordPoint, Pi.zero_apply] at hj
  exact (eq_neg_iff_add_eq_zero).2 hj

theorem lower_nonpos (hP : CenteredCertificate P) (i : Fin r) :
    hP.lower i ≤ 0 := by
  simp [lower]

theorem upper_nonneg (hP : CenteredCertificate P) (i : Fin r) :
    0 ≤ hP.upper i := by
  have hi := (hP.center i).isLt
  simp only [upper]
  omega

/-- Every shifted coefficient interval crosses zero. -/
theorem lower_le_zero_le_upper (hP : CenteredCertificate P) (i : Fin r) :
    hP.lower i ≤ 0 ∧ 0 ≤ hP.upper i :=
  ⟨hP.lower_nonpos i, hP.upper_nonneg i⟩

/-- Shifting the interval does not change its number of integer points. -/
theorem upper_sub_lower_add_one (hP : CenteredCertificate P) (i : Fin r) :
    hP.upper i - hP.lower i + 1 = (P.widths i : ℤ) := by
  simp only [upper, lower]
  ring

theorem relativeCoeff_mem_box (hP : CenteredCertificate P) (n : P.Coord) :
    hP.InBox (hP.relativeCoeff n) := by
  intro i
  have hn := (n i).isLt
  constructor <;> simp only [lower, upper, relativeCoeff] <;> omega

@[simp]
theorem relativeCoeff_center (hP : CenteredCertificate P) :
    hP.relativeCoeff hP.center = 0 := by
  funext i
  simp [relativeCoeff]

/-- Evaluation in the original one-sided coordinates is evaluation in the
shifted integer coordinates. -/
theorem coordPoint_eq_relativePoint (hP : CenteredCertificate P) (n : P.Coord) :
    P.coordPoint n = hP.relativePoint (hP.relativeCoeff n) := by
  funext j
  rw [GAP.coordPoint, hP.offset_eq]
  simp only [relativePoint, relativeCoeff]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  abel

/-- Turn any integer tuple in the shifted box back into a one-sided GAP
coordinate. -/
def coordOfInBox (hP : CenteredCertificate P) (z : Fin r → ℤ)
    (hz : hP.InBox z) : P.Coord :=
  fun i ↦ ⟨(z i + (hP.center i : ℤ)).toNat, by
    have hlo : 0 ≤ z i + (hP.center i : ℤ) := by
      have := (hz i).1
      simp only [lower] at this
      omega
    have hhi : z i + (hP.center i : ℤ) < (P.widths i : ℤ) := by
      have := (hz i).2
      simp only [upper] at this
      omega
    exact (Int.toNat_lt hlo).2 hhi⟩

@[simp]
theorem relativeCoeff_coordOfInBox (hP : CenteredCertificate P)
    (z : Fin r → ℤ) (hz : hP.InBox z) :
    hP.relativeCoeff (hP.coordOfInBox z hz) = z := by
  funext i
  have hlo : 0 ≤ z i + (hP.center i : ℤ) := by
    have := (hz i).1
    simp only [lower] at this
    omega
  simp only [relativeCoeff, coordOfInBox]
  rw [Int.toNat_of_nonneg hlo]
  ring

/-- Exact carrier description by the shifted integer box.  This is the
set-theoretic content of CFP Claim 2.6. -/
theorem mem_carrier_iff_exists_inBox (hP : CenteredCertificate P)
    {x : LatticePoint d} :
    x ∈ P.carrier ↔
      ∃ z : Fin r → ℤ, hP.InBox z ∧ hP.relativePoint z = x := by
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hx
    exact ⟨hP.relativeCoeff n, hP.relativeCoeff_mem_box n,
      (hP.coordPoint_eq_relativePoint n).symm⟩
  · rintro ⟨z, hz, rfl⟩
    let n := hP.coordOfInBox z hz
    refine GAP.mem_carrier_iff.mpr ⟨n, ?_⟩
    rw [hP.coordPoint_eq_relativePoint, show hP.relativeCoeff n = z by
      exact hP.relativeCoeff_coordOfInBox z hz]

/-- Every integer tuple in the shifted box evaluates to a point of the
carrier.  The converse for a *specified* tuple is intentionally not stated:
even a proper finite presentation can have collisions with coefficients
outside its displayed box. -/
theorem relativePoint_mem_carrier (hP : CenteredCertificate P)
    {z : Fin r → ℤ} (hz : hP.InBox z) :
    hP.relativePoint z ∈ P.carrier :=
  hP.mem_carrier_iff_exists_inBox.mpr ⟨z, hz, rfl⟩

/-- Under properness, the centered coefficient box is an exact, injective
parameterization. -/
theorem relativePoint_injective_on (hP : CenteredCertificate P)
    (hproper : P.Proper) :
    Set.InjOn hP.relativePoint {z | hP.InBox z} := by
  intro z hz z' hz' heq
  let n := hP.coordOfInBox z hz
  let n' := hP.coordOfInBox z' hz'
  have hn : P.coordPoint n = hP.relativePoint z := by
    rw [hP.coordPoint_eq_relativePoint]
    exact congrArg hP.relativePoint (hP.relativeCoeff_coordOfInBox z hz)
  have hn' : P.coordPoint n' = hP.relativePoint z' := by
    rw [hP.coordPoint_eq_relativePoint]
    exact congrArg hP.relativePoint (hP.relativeCoeff_coordOfInBox z' hz')
  have hnn' : n = n' := hproper (hn.trans (heq.trans hn'.symm))
  calc
    z = hP.relativeCoeff n := (hP.relativeCoeff_coordOfInBox z hz).symm
    _ = hP.relativeCoeff n' := congrArg hP.relativeCoeff hnn'
    _ = z' := hP.relativeCoeff_coordOfInBox z' hz'

/-! ## A literal GAP re-presentation -/

/-- The one-sided GAP whose offset is written as the negative linear
combination supplied by a centered certificate. -/
def recentered (hP : CenteredCertificate P) : GAP d r where
  offset := fun j ↦ -∑ i, (hP.center i : ℤ) * P.steps i j
  steps := P.steps
  widths := P.widths
  width_pos := P.width_pos

@[simp]
theorem recentered_offset (hP : CenteredCertificate P) :
    hP.recentered.offset =
      fun j ↦ -∑ i, (hP.center i : ℤ) * P.steps i j := rfl

@[simp]
theorem recentered_steps (hP : CenteredCertificate P) :
    hP.recentered.steps = P.steps := rfl

@[simp]
theorem recentered_widths (hP : CenteredCertificate P) :
    hP.recentered.widths = P.widths := rfl

/-- The literal re-presentation is equal to the original one-sided GAP,
because its displayed offset equality was forced by the zero witness. -/
theorem recentered_eq (hP : CenteredCertificate P) : hP.recentered = P := by
  rw [GAP.mk.injEq]
  exact ⟨hP.offset_eq.symm, rfl, rfl⟩

@[simp]
theorem recentered_carrier (hP : CenteredCertificate P) :
    hP.recentered.carrier = P.carrier := by
  rw [hP.recentered_eq]

@[simp]
theorem recentered_volume (hP : CenteredCertificate P) :
    hP.recentered.volume = P.volume := by
  rw [hP.recentered_eq]

@[simp]
theorem recentered_proper_iff (hP : CenteredCertificate P) :
    hP.recentered.Proper ↔ P.Proper := by
  rw [hP.recentered_eq]

/-- Integral dilation is unaffected by the centered re-presentation. -/
@[simp]
theorem recentered_dilate (hP : CenteredCertificate P) (k : ℕ) :
    hP.recentered.dilate k = P.dilate k := by
  rw [hP.recentered_eq]

/-- In particular, every integral dilation has exactly the same carrier.
This is the representation-invariance used for integer multifold sumsets. -/
@[simp]
theorem recentered_dilate_carrier (hP : CenteredCertificate P) (k : ℕ) :
    (hP.recentered.dilate k).carrier = (P.dilate k).carrier := by
  rw [hP.recentered_dilate]

/-! ## Integral dilations in centered coordinates -/

/-- The chosen center coordinate scales to a coordinate of the integral
dilation. -/
def dilateCenter (hP : CenteredCertificate P) (k : ℕ) :
    (P.dilate k).Coord :=
  fun i ↦ ⟨k * (hP.center i : ℕ), by
    have hi := (hP.center i).isLt
    simp only [GAP.dilate_widths]
    exact Nat.lt_succ_of_le (Nat.mul_le_mul_left k (by omega))⟩

theorem coordPoint_dilateCenter (hP : CenteredCertificate P) (k : ℕ) :
    (P.dilate k).coordPoint (hP.dilateCenter k) = 0 := by
  funext j
  simp only [GAP.coordPoint, GAP.dilate_offset, GAP.dilate_steps, dilateCenter,
    Pi.zero_apply]
  rw [hP.offset_eq]
  push_cast
  rw [mul_neg, Finset.mul_sum]
  simp_rw [mul_assoc]
  abel

/-- Every natural dilation inherits a centered certificate. -/
def dilate (hP : CenteredCertificate P) (k : ℕ) :
    CenteredCertificate (P.dilate k) where
  center := hP.dilateCenter k
  coordPoint_center := hP.coordPoint_dilateCenter k

@[simp]
theorem dilate_center_apply (hP : CenteredCertificate P) (k : ℕ) (i : Fin r) :
    ((hP.dilate k).center i : ℕ) = k * (hP.center i : ℕ) := rfl

/-- The lower endpoint of a centered interval scales exactly under an
integral dilation. -/
theorem dilate_lower (hP : CenteredCertificate P) (k : ℕ) (i : Fin r) :
    (hP.dilate k).lower i = (k : ℤ) * hP.lower i := by
  simp only [lower, dilate_center_apply]
  push_cast
  ring

/-- The upper endpoint of a centered interval scales exactly under an
integral dilation. -/
theorem dilate_upper (hP : CenteredCertificate P) (k : ℕ) (i : Fin r) :
    (hP.dilate k).upper i = (k : ℤ) * hP.upper i := by
  have hw : 1 ≤ P.widths i := P.width_pos i
  simp only [upper, GAP.dilate_widths, dilate_center_apply]
  push_cast [Nat.cast_sub hw]
  ring

@[simp]
theorem dilate_relativePoint (hP : CenteredCertificate P) (k : ℕ)
    (z : Fin r → ℤ) :
    (hP.dilate k).relativePoint z = hP.relativePoint z := rfl

/-- Exact centered-box formula for every integral dilation.  Thus the
integer dilation has bounds `k * lower` and `k * upper`, just as the CFP
definition of integer `kQ`; together with `recentered_dilate_carrier`, this
records representation invariance. -/
theorem mem_dilate_carrier_iff_exists_inBox (hP : CenteredCertificate P)
    (k : ℕ) {x : LatticePoint d} :
    x ∈ (P.dilate k).carrier ↔
      ∃ z : Fin r → ℤ,
        (∀ i, (k : ℤ) * hP.lower i ≤ z i ∧
          z i ≤ (k : ℤ) * hP.upper i) ∧
        hP.relativePoint z = x := by
  simpa only [InBox, dilate_lower, dilate_upper, dilate_relativePoint] using
    (hP.dilate k).mem_carrier_iff_exists_inBox (x := x)

end CenteredCertificate

/-! ## Existence: CFP Claim 2.6 -/

/-- A point of the carrier equal to zero supplies the centered
certificate. -/
theorem exists_centeredCertificate_of_zero_mem {P : GAP d r}
    (hzero : 0 ∈ P.carrier) : Nonempty (CenteredCertificate P) := by
  obtain ⟨center, hcenter⟩ := GAP.mem_carrier_iff.mp hzero
  exact ⟨⟨center, hcenter⟩⟩

/-- A centered certificate displays zero, so zero belongs to the carrier. -/
theorem zero_mem_carrier_of_centeredCertificate {P : GAP d r}
    (hP : CenteredCertificate P) : 0 ∈ P.carrier := by
  exact GAP.mem_carrier_iff.mpr ⟨hP.center, hP.coordPoint_center⟩

/-- CFP Claim 2.6, as an exact equivalence for the repository's finite GAP
representation. -/
theorem claim_2_6 {P : GAP d r} :
    0 ∈ P.carrier ↔ Nonempty (CenteredCertificate P) := by
  constructor
  · exact exists_centeredCertificate_of_zero_mem
  · rintro ⟨hP⟩
    exact zero_mem_carrier_of_centeredCertificate hP

/-- Constructive existential packaging of Claim 2.6, exposing the literal
re-presented GAP and all invariants normally used downstream. -/
theorem exists_recentered_gap_of_zero_mem {P : GAP d r}
    (hzero : 0 ∈ P.carrier) :
    ∃ (hP : CenteredCertificate P) (C : GAP d r),
      C = hP.recentered ∧
      C.carrier = P.carrier ∧
      C.steps = P.steps ∧
      C.widths = P.widths ∧
      C.volume = P.volume ∧
      (C.Proper ↔ P.Proper) ∧
      C.offset = (fun j ↦ -∑ i, (hP.center i : ℤ) * P.steps i j) ∧
      ∀ k : ℕ, (C.dilate k).carrier = (P.dilate k).carrier := by
  obtain ⟨hP⟩ := exists_centeredCertificate_of_zero_mem hzero
  refine ⟨hP, hP.recentered, rfl, hP.recentered_carrier,
    hP.recentered_steps, hP.recentered_widths, hP.recentered_volume,
    hP.recentered_proper_iff, hP.recentered_offset, ?_⟩
  exact hP.recentered_dilate_carrier

end Erdos186.CFP
