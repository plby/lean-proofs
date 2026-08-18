/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Witness
import ErdosProblems.Erdos186.PZ.Intersection.Main
import ErdosProblems.Erdos186.PZ.Intersection.ResidualAbsorption

/-!
# Absorbing zonotope-rounding errors in a symmetric GAP

This file supplies the coefficient-box calculation between zonotope rounding
and Pham--Zakharov equation (15).  A point of an `m`-dilate plus a point of an
`n`-dilate lies in the `(m+n)`-dilate.  For a symmetric GAP, zero lies in
every dilate, so this inclusion can be padded to any larger dilation.

Consequently, if the coordinate error box from `Zonotope.zonotope_rounding`
is contained in a `margin`-dilate, then adding those errors to a translate of
the `structuredDilation`-dilate stays in the covered `coveredDilation`-dilate
whenever `structuredDilation + margin ≤ coveredDilation`.  The final theorem
combines this fact with the actual CFP coverage field and equation (15).
-/

namespace Erdos186

open scoped BigOperators

noncomputable section

set_option autoImplicit false

namespace GAP

/-- Addition of displayed dilation envelopes.  This is an exact
coefficient-box calculation and requires neither properness nor symmetry. -/
theorem add_mem_dilate_add {d r m n : ℕ} (P : GAP d r)
    {x y : LatticePoint d} (hx : x ∈ (P.dilate m).carrier)
    (hy : y ∈ (P.dilate n).carrier) :
    x + y ∈ (P.dilate (m + n)).carrier := by
  rw [mem_carrier_iff] at hx hy ⊢
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  let c : (P.dilate (m + n)).Coord := fun i ↦
    ⟨(a i : ℕ) + (b i : ℕ), by
      have ha : (a i : ℕ) ≤ m * (P.widths i - 1) := by
        have hai := (a i).isLt
        simp only [dilate_widths] at hai
        omega
      have hb : (b i : ℕ) ≤ n * (P.widths i - 1) := by
        have hbi := (b i).isLt
        simp only [dilate_widths] at hbi
        omega
      change (a i : ℕ) + (b i : ℕ) <
        (m + n) * (P.widths i - 1) + 1
      calc
        (a i : ℕ) + (b i : ℕ)
            ≤ m * (P.widths i - 1) + n * (P.widths i - 1) :=
          Nat.add_le_add ha hb
        _ = (m + n) * (P.widths i - 1) := by rw [Nat.add_mul]
        _ < (m + n) * (P.widths i - 1) + 1 := Nat.lt_succ_self _⟩
  refine ⟨c, ?_⟩
  funext j
  simp only [coordPoint, dilate_offset, Pi.add_apply, c]
  push_cast
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simp only [dilate_steps]
  ring

/-- Carriers of dilates of a symmetric GAP are monotone in the dilation
parameter.  Symmetry is used to pad the smaller sum by zero points. -/
theorem dilate_carrier_mono_of_symmetric {d r m n : ℕ} (P : GAP d r)
    (hP : P.Symmetric) (hmn : m ≤ n) :
    (P.dilate m).carrier ⊆ (P.dilate n).carrier := by
  intro x hx
  have hzero : (0 : LatticePoint d) ∈ (P.dilate (n - m)).carrier :=
    (hP.dilate (n - m)).zero_mem_carrier
  have hadd := P.add_mem_dilate_add hx hzero
  have hmn' : m + (n - m) = n := Nat.add_sub_of_le hmn
  simpa only [add_zero, hmn'] using hadd

end GAP

namespace PZ.Intersection

/-- A translated structured dilate absorbs every error in a margin dilate,
provided the sum of the two dilation parameters fits in the covered scale. -/
theorem add_mem_translate_dilate_of_margin {d r structuredDilation margin
    coveredDilation : ℕ} (P : GAP d r) (hP : P.Symmetric)
    (translatePoint : LatticePoint d)
    (hscale : structuredDilation + margin ≤ coveredDilation)
    {p e : LatticePoint d}
    (hp : p ∈ CFP.translate translatePoint
      (P.dilate structuredDilation).carrier)
    (he : e ∈ (P.dilate margin).carrier) :
    p + e ∈ CFP.translate translatePoint
      (P.dilate coveredDilation).carrier := by
  obtain ⟨q, hq, rfl⟩ := CFP.mem_translate_iff.mp hp
  have hqe : q + e ∈ (P.dilate (structuredDilation + margin)).carrier :=
    P.add_mem_dilate_add hq he
  have hqe' : q + e ∈ (P.dilate coveredDilation).carrier :=
    P.dilate_carrier_mono_of_symmetric hP hscale hqe
  exact CFP.mem_translate_iff.mpr ⟨q + e, hqe', by simp [add_assoc]⟩

/-- Coordinate-error-box form of
`add_mem_translate_dilate_of_margin`.  This theorem is the concrete
replacement for the former free `habsorb` input. -/
theorem translate_dilate_absorbs_errorBox {d r structuredDilation margin
    coveredDilation : ℕ} (P : GAP d r) (hP : P.Symmetric)
    (translatePoint : LatticePoint d) (radius : ℝ)
    (hscale : structuredDilation + margin ≤ coveredDilation)
    (herrorBox : ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤ radius) →
        e ∈ (P.dilate margin).carrier) :
    ∀ p ∈ CFP.translate translatePoint
        (P.dilate structuredDilation).carrier,
      ∀ e : LatticePoint d, (∀ i, |(e i : ℝ)| ≤ radius) →
        p + e ∈ CFP.translate translatePoint
          (P.dilate coveredDilation).carrier := by
  intro p hp e he
  exact add_mem_translate_dilate_of_margin P hP translatePoint hscale hp
    (herrorBox e he)

/-- Zonotope rounding followed by the symmetric-GAP margin calculation.
There is no residual-absorption hypothesis: the only geometric input is the
literal inclusion of the rounding error box in the selected margin dilate. -/
theorem roundingErrorsAbsorbedBy_cfpTranslate_add_of_margin
    {d r structuredDilation margin coveredDilation : ℕ}
    (target core : Finset (LatticePoint d)) (width : ℝ)
    (P : GAP d r) (hP : P.Symmetric)
    (translatePoint : LatticePoint d)
    (hwidth : 0 ≤ width)
    (hcore : ∀ x ∈ core, ∀ i, |(x i : ℝ)| ≤ width)
    (htarget : ∀ z ∈ target,
      ∃ p ∈ CFP.translate translatePoint
          (P.dilate structuredDilation).carrier,
        ∃ x : LatticePoint d,
          Zonotope.IsZonotopePoint core (fun i ↦ (x i : ℝ)) ∧
            z = p + x)
    (hscale : structuredDilation + margin ≤ coveredDilation)
    (herrorBox : ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * core.card : ℕ) : ℝ)) * width) →
      e ∈ (P.dilate margin).carrier) :
    RoundingErrorsAbsorbedBy target core
      (CFP.translate translatePoint
        (P.dilate coveredDilation).carrier) := by
  apply roundingErrorsAbsorbedBy_cfpTranslate_add target core
    (CFP.translate translatePoint (P.dilate structuredDilation).carrier)
    width P translatePoint hwidth hcore htarget
  exact translate_dilate_absorbs_errorBox P hP translatePoint
    (Real.sqrt (((d * core.card : ℕ) : ℝ)) * width) hscale herrorBox

/-- The complete finite Equation-(15) bridge for an enhanced CFP witness.
The witness supplies symmetry and the selected proper-dilate coverage;
zonotope rounding and the margin calculation supply the residual inclusion.
-/
theorem equation15_subsetSums_of_zonotope_margin
    {d s D k loss structuredDilation margin : ℕ}
    {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    (target core : Finset (LatticePoint d)) (width : ℝ)
    (hcoreA : core ⊆ A)
    (hdisjoint : Disjoint W.reserved core)
    (hwidth : 0 ≤ width)
    (hcore : ∀ x ∈ core, ∀ i, |(x i : ℝ)| ≤ width)
    (htarget : ∀ z ∈ target,
      ∃ p ∈ CFP.translate W.translatePoint
          (W.progression.dilate structuredDilation).carrier,
        ∃ x : LatticePoint d,
          Zonotope.IsZonotopePoint core (fun i ↦ (x i : ℝ)) ∧
            z = p + x)
    (hscale : structuredDilation + margin ≤ k)
    (herrorBox : ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * core.card : ℕ) : ℝ)) * width) →
      e ∈ (W.progression.dilate margin).carrier) :
    target ⊆ GAP.subsetSums A := by
  have hround : RoundingErrorsAbsorbedBy target core
      (CFP.translate W.translatePoint
        (W.progression.dilate k).carrier) :=
    roundingErrorsAbsorbedBy_cfpTranslate_add_of_margin target core width
      W.progression W.progression_symmetric W.translatePoint hwidth hcore
      htarget hscale herrorBox
  exact equation15_subsetSums_of_cfpWitness W.basic hcoreA hdisjoint hround

namespace IntersectionSideInput

variable {d : ℕ} {pool : Finset (LatticePoint d)}
    {a : LatticePoint d} {orientation : Orientation}

/-- Direct source-geometry adapter for one intersection side.  Unlike
`lemma13ResidualAbsorption_of_zonotope_add`, this has no free absorption
hypothesis: the structured part is a smaller dilate of the actual enhanced
CFP progression, and the rounding error box is placed in an explicit margin
dilate. -/
theorem lemma13ResidualAbsorption_of_zonotope_margin
    (I : IntersectionSideInput pool a orientation)
    (structuredDilation margin : ℕ) (width : ℝ)
    (hwidth : 0 ≤ width)
    (hcore : ∀ x ∈ I.roundingCore, ∀ i, |(x i : ℝ)| ≤ width)
    (htarget : ∀ z ∈ I.target,
      ∃ p ∈ CFP.translate I.witness.translatePoint
          (I.witness.progression.dilate structuredDilation).carrier,
        ∃ x : LatticePoint d,
          Zonotope.IsZonotopePoint I.roundingCore
            (fun i ↦ (x i : ℝ)) ∧ z = p + x)
    (hscale : structuredDilation + margin ≤ I.dilation)
    (herrorBox : ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * I.roundingCore.card : ℕ) : ℝ)) * width) →
      e ∈ (I.witness.progression.dilate margin).carrier) :
    I.Lemma13ResidualAbsorption := by
  exact roundingErrorsAbsorbedBy_cfpTranslate_add_of_margin
    I.target I.roundingCore width I.witness.progression
    I.witness.progression_symmetric I.witness.translatePoint hwidth hcore
    htarget hscale herrorBox

end IntersectionSideInput

namespace Theorem4PostCFPData

variable {d : ℕ} {A : Finset (LatticePoint d)}

/-- Assemble the post-CFP intersection data with Lemma 13 discharged by the
concrete symmetric-GAP margin calculation on both sides.  Unlike
`ofSourceLemmas`, this constructor has no abstract residual-absorption input.
-/
def ofZonotopeMarginSourceLemmas {R : ℕ} {a : LatticePoint d}
    {A₁ A₂ : Finset (LatticePoint d)} {center : Fin d → ℝ}
    (hd : 0 < d) (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisjoint : Disjoint A₁ A₂)
    (I₁ : IntersectionSideInput A₁ a .forward)
    (I₂ : IntersectionSideInput A₂ a .reverse)
    (structuredDilation₁ margin₁ : ℕ) (width₁ : ℝ)
    (hwidth₁ : 0 ≤ width₁)
    (hcore₁ : ∀ x ∈ I₁.roundingCore, ∀ i, |(x i : ℝ)| ≤ width₁)
    (htarget₁ : ∀ z ∈ I₁.target,
      ∃ p ∈ CFP.translate I₁.witness.translatePoint
          (I₁.witness.progression.dilate structuredDilation₁).carrier,
        ∃ x : LatticePoint d,
          Zonotope.IsZonotopePoint I₁.roundingCore
            (fun i ↦ (x i : ℝ)) ∧ z = p + x)
    (hscale₁ : structuredDilation₁ + margin₁ ≤ I₁.dilation)
    (herrorBox₁ : ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * I₁.roundingCore.card : ℕ) : ℝ)) * width₁) →
      e ∈ (I₁.witness.progression.dilate margin₁).carrier)
    (structuredDilation₂ margin₂ : ℕ) (width₂ : ℝ)
    (hwidth₂ : 0 ≤ width₂)
    (hcore₂ : ∀ x ∈ I₂.roundingCore, ∀ i, |(x i : ℝ)| ≤ width₂)
    (htarget₂ : ∀ z ∈ I₂.target,
      ∃ p ∈ CFP.translate I₂.witness.translatePoint
          (I₂.witness.progression.dilate structuredDilation₂).carrier,
        ∃ x : LatticePoint d,
          Zonotope.IsZonotopePoint I₂.roundingCore
            (fun i ↦ (x i : ℝ)) ∧ z = p + x)
    (hscale₂ : structuredDilation₂ + margin₂ ≤ I₂.dilation)
    (herrorBox₂ : ∀ e : LatticePoint d,
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * I₂.roundingCore.card : ℕ) : ℝ)) * width₂) →
      e ∈ (I₂.witness.progression.dilate margin₂).carrier)
    (hthick₁ : I₁.Lemma14TargetThickness center (3 * R + 2))
    (hthick₂ : I₂.Lemma14TargetThickness center (3 * R + 2))
    (hcovolume : FullRankLatticeCovolumeConclusion I₁ I₂ R) :
    Theorem4PostCFPData A := by
  apply ofSourceLemmas hd ha hA₁ hA₂ hdisjoint I₁ I₂
  · exact I₁.lemma13ResidualAbsorption_of_zonotope_margin
      structuredDilation₁ margin₁ width₁ hwidth₁ hcore₁ htarget₁ hscale₁
      herrorBox₁
  · exact I₂.lemma13ResidualAbsorption_of_zonotope_margin
      structuredDilation₂ margin₂ width₂ hwidth₂ hcore₂ htarget₂ hscale₂
      herrorBox₂
  · exact hthick₁
  · exact hthick₂
  · exact hcovolume

end Theorem4PostCFPData

end PZ.Intersection

end

end Erdos186
