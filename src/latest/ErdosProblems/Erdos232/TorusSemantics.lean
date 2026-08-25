/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.TorusFourier
import ErdosProblems.Erdos232.CertificateExpectations
import ErdosProblems.Erdos232.CongruenceCertificates
import ErdosProblems.Erdos232.Spectral
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Set
open scoped ComplexConjugate ENNReal

namespace Erdos232

noncomputable section

local instance torusSemanticsMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusSemanticsIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusSemanticsIsProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The certificate's two-point rows -/

/-- The first endpoint of the unit row and the 26 two-point rows of the certificate. -/
def pairLeft (j : Fin 27) : Fin 23 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 5
  | 8 => 5
  | 9 => 6
  | 10 => 6
  | 11 => 6
  | 12 => 6
  | 13 => 6
  | 14 => 7
  | 15 => 7
  | 16 => 8
  | 17 => 8
  | 18 => 8
  | 19 => 10
  | 20 => 10
  | 21 => 11
  | 22 => 13
  | 23 => 13
  | 24 => 14
  | 25 => 20
  | _ => 20

/-- The second endpoint of the unit row and the 26 two-point rows of the certificate. -/
def pairRight (j : Fin 27) : Fin 23 :=
  match j.val with
  | 0 => 1
  | 1 => 9
  | 2 => 16
  | 3 => 22
  | 4 => 11
  | 5 => 14
  | 6 => 21
  | 7 => 7
  | 8 => 14
  | 9 => 8
  | 10 => 11
  | 11 => 14
  | 12 => 20
  | 13 => 22
  | 14 => 21
  | 15 => 22
  | 16 => 12
  | 17 => 21
  | 18 => 22
  | 19 => 21
  | 20 => 22
  | 21 => 18
  | 22 => 21
  | 23 => 22
  | 24 => 15
  | 25 => 21
  | _ => 22

theorem pairLeft_ne_pairRight (j : Fin 27) : pairLeft j ≠ pairRight j := by
  fin_cases j <;> decide

theorem pair_configurationDistanceLabel (j : Fin 27) :
    configurationDistanceLabel (pairLeft j) (pairRight j) = j := by
  fin_cases j <;> rfl

/-- Natural-number mask selecting precisely the two endpoints of row `j`. -/
def pairMask (j : Fin 27) : Nat :=
  2 ^ (pairLeft j).val ||| 2 ^ (pairRight j).val

theorem pairMask_values (j : Fin 27) : pairMask j =
    ![3, 513, 65537, 4194305, 2052, 16388, 2097160, 160, 16416,
      320, 2112, 16448, 1048640, 4194368, 2097280, 4194432, 4352,
      2097408, 4194560, 2098176, 4195328, 264192, 2105344, 4202496,
      49152, 3145728, 5242880] j := by
  fin_cases j <;> decide

theorem maskEvent_pairMask {Ω : Type*} (X : Ω → Assignment) (j : Fin 27) :
    maskEvent X (pairMask j) =
      {ω | X ω (pairLeft j) = true ∧ X ω (pairRight j) = true} := by
  ext ω
  simp only [maskEvent, mem_setOf_eq]
  constructor
  · intro h
    constructor
    · apply h (pairLeft j)
      simp [pairMask, Nat.testBit_or, Nat.testBit_two_pow]
    · apply h (pairRight j)
      simp [pairMask, Nat.testBit_or, Nat.testBit_two_pow]
  · rintro ⟨hleft, hright⟩ k hk
    simp only [pairMask, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq] at hk
    rcases hk with hk | hk
    · have hkl : k = pairLeft j := Fin.ext hk.symm
      simpa [hkl] using hleft
    · have hkr : k = pairRight j := Fin.ext hk.symm
      simpa [hkr] using hright

/-! ## Every sampled atom is independent -/

theorem normSq_orientedConfigurationPoint_sub
    (reflected : Bool) (i j : Fin 23) (hij : i ≠ j) :
    Complex.normSq
        (orientedConfigurationPoint reflected i - orientedConfigurationPoint reflected j) =
      dualSquaredDistance (configurationDistanceLabel i j) := by
  cases reflected
  · simpa [orientedConfigurationPoint] using configuration_normSq i j hij
  · simp only [orientedConfigurationPoint, Bool.true_eq, if_true]
    rw [← map_sub, Complex.normSq_conj]
    exact configuration_normSq i j hij

theorem sampleAssignment_not_both_of_label_zero
    {S : Set SquareTorus} {L : ℝ} (hfree : TorusUnitDistanceFree L S)
    (reflected : Bool) (ω : TorusSample) (i j : Fin 23) (hij : i ≠ j)
    (hlabel : configurationDistanceLabel i j = 0) :
    ¬(sampleAssignment S L reflected ω i = true ∧
      sampleAssignment S L reflected ω j = true) := by
  rintro ⟨hi, hj⟩
  have hiS : samplePoint L reflected ω i ∈ S := by
    simpa [sampleAssignment] using hi
  have hjS : samplePoint L reflected ω j ∈ S := by
    simpa [sampleAssignment] using hj
  apply hfree (samplePoint L reflected ω j)
      (rotateComplex ω.1
        (orientedConfigurationPoint reflected i - orientedConfigurationPoint reflected j))
  · rw [normSq_rotateComplex,
      normSq_orientedConfigurationPoint_sub reflected i j hij, hlabel]
    rfl
  · refine ⟨hjS, ?_⟩
    convert hiS using 1
    unfold samplePoint
    rw [rotateComplex_sub, torusVector_sub]
    abel

private theorem assignmentAtom_bit
    (v : Assignment) (i : Nat) (hi : i < 23) :
    (BitVec.ofNat 23 (assignmentAtom v).val).getLsbD i = v ⟨i, hi⟩ := by
  rw [BitVec.getLsbD_ofNat]
  simp only [hi, decide_true, Bool.true_and, assignmentAtom, Fin.val_ofBits]
  exact Nat.testBit_ofBits_lt v i hi

/-- The Boolean atom obtained at every sample contains none of the 47 unit-distance edges. -/
theorem sampleAssignment_independent
    {S : Set SquareTorus} {L : ℝ} (hfree : TorusUnitDistanceFree L S)
    (reflected : Bool) (ω : TorusSample) :
    independentMaskBV
      (BitVec.ofNat 23 (assignmentAtom (sampleAssignment S L reflected ω)).val) = true := by
  let v := sampleAssignment S L reflected ω
  let b := BitVec.ofNat 23 (assignmentAtom v).val
  have hedge (i j : Nat) (hi : i < 23) (hj : j < 23) (hij : i ≠ j)
      (hlabel : configurationDistanceLabel ⟨i, hi⟩ ⟨j, hj⟩ = 0) :
      (!(b.getLsbD i && b.getLsbD j)) = true := by
    have hnot := sampleAssignment_not_both_of_label_zero hfree reflected ω
      ⟨i, hi⟩ ⟨j, hj⟩ (by exact Fin.ne_of_val_ne hij) hlabel
    have hbi : b.getLsbD i = v ⟨i, hi⟩ := assignmentAtom_bit v i hi
    have hbj : b.getLsbD j = v ⟨j, hj⟩ := assignmentAtom_bit v j hj
    rw [hbi, hbj]
    cases hv_i : v ⟨i, hi⟩
    · rfl
    · cases hv_j : v ⟨j, hj⟩
      · rfl
      · exact (hnot ⟨hv_i, hv_j⟩).elim
  change independentMaskBV b = true
  simp only [independentMaskBV,
    hedge 0 1 (by omega) (by omega) (by omega) rfl,
    hedge 0 2 (by omega) (by omega) (by omega) rfl,
    hedge 0 4 (by omega) (by omega) (by omega) rfl,
    hedge 0 5 (by omega) (by omega) (by omega) rfl,
    hedge 0 8 (by omega) (by omega) (by omega) rfl,
    hedge 1 2 (by omega) (by omega) (by omega) rfl,
    hedge 1 3 (by omega) (by omega) (by omega) rfl,
    hedge 1 11 (by omega) (by omega) (by omega) rfl,
    hedge 1 18 (by omega) (by omega) (by omega) rfl,
    hedge 1 19 (by omega) (by omega) (by omega) rfl,
    hedge 2 3 (by omega) (by omega) (by omega) rfl,
    hedge 3 6 (by omega) (by omega) (by omega) rfl,
    hedge 3 7 (by omega) (by omega) (by omega) rfl,
    hedge 3 10 (by omega) (by omega) (by omega) rfl,
    hedge 4 5 (by omega) (by omega) (by omega) rfl,
    hedge 4 6 (by omega) (by omega) (by omega) rfl,
    hedge 4 7 (by omega) (by omega) (by omega) rfl,
    hedge 4 9 (by omega) (by omega) (by omega) rfl,
    hedge 4 12 (by omega) (by omega) (by omega) rfl,
    hedge 4 17 (by omega) (by omega) (by omega) rfl,
    hedge 5 6 (by omega) (by omega) (by omega) rfl,
    hedge 5 10 (by omega) (by omega) (by omega) rfl,
    hedge 5 15 (by omega) (by omega) (by omega) rfl,
    hedge 6 18 (by omega) (by omega) (by omega) rfl,
    hedge 7 8 (by omega) (by omega) (by omega) rfl,
    hedge 7 9 (by omega) (by omega) (by omega) rfl,
    hedge 7 10 (by omega) (by omega) (by omega) rfl,
    hedge 7 13 (by omega) (by omega) (by omega) rfl,
    hedge 8 10 (by omega) (by omega) (by omega) rfl,
    hedge 9 11 (by omega) (by omega) (by omega) rfl,
    hedge 9 12 (by omega) (by omega) (by omega) rfl,
    hedge 9 14 (by omega) (by omega) (by omega) rfl,
    hedge 9 15 (by omega) (by omega) (by omega) rfl,
    hedge 9 16 (by omega) (by omega) (by omega) rfl,
    hedge 10 15 (by omega) (by omega) (by omega) rfl,
    hedge 10 20 (by omega) (by omega) (by omega) rfl,
    hedge 11 13 (by omega) (by omega) (by omega) rfl,
    hedge 11 14 (by omega) (by omega) (by omega) rfl,
    hedge 11 16 (by omega) (by omega) (by omega) rfl,
    hedge 11 17 (by omega) (by omega) (by omega) rfl,
    hedge 12 21 (by omega) (by omega) (by omega) rfl,
    hedge 13 17 (by omega) (by omega) (by omega) rfl,
    hedge 16 20 (by omega) (by omega) (by omega) rfl,
    hedge 16 21 (by omega) (by omega) (by omega) rfl,
    hedge 16 22 (by omega) (by omega) (by omega) rfl,
    hedge 18 19 (by omega) (by omega) (by omega) rfl,
    hedge 21 22 (by omega) (by omega) (by omega) rfl,
    Bool.true_and]

theorem atomMass_sampleAssignment_support
    {S : Set SquareTorus} {L : ℝ} (hfree : TorusUnitDistanceFree L S)
    (reflected : Bool) (s : AtomIndex)
    (hs : atomMass volume (sampleAssignment S L reflected) s ≠ 0) :
    independentMaskBV (BitVec.ofNat 23 s.val) = true := by
  by_contra hind
  have hempty :
      ((assignmentAtom ∘ sampleAssignment S L reflected) ⁻¹' ({s} : Set AtomIndex)) = ∅ := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hω
    have hpoint := sampleAssignment_independent hfree reflected ω
    rw [show assignmentAtom (sampleAssignment S L reflected ω) = s by
      simpa [Function.comp_apply] using hω] at hpoint
    exact hind hpoint
  apply hs
  simp [atomMass, hempty]

theorem torusAtomMass_support
    {S : Set SquareTorus} {L : ℝ} (hfree : TorusUnitDistanceFree L S)
    (s : AtomIndex) (hs : torusAtomMass S L s ≠ 0) :
    independentMaskBV (BitVec.ofNat 23 s.val) = true := by
  by_contra hind
  have hfalse : atomMass volume (sampleAssignment S L false) s = 0 := by
    by_contra hne
    exact hind (atomMass_sampleAssignment_support hfree false s hne)
  have htrue : atomMass volume (sampleAssignment S L true) s = 0 := by
    by_contra hne
    exact hind (atomMass_sampleAssignment_support hfree true s hne)
  apply hs
  simp [torusAtomMass, hfalse, htrue]

/-! ## Radial correlations are the two-point marginals -/

/-- The product-space event used to average a displacement over all angles and translations. -/
def radialPairSampleEvent (S : Set SquareTorus) (L : ℝ) (z : ℂ) : Set TorusSample :=
  {ω | ω.2 ∈ S ∧ ω.2 + torusVector L (rotateComplex ω.1 z) ∈ S}

theorem measurable_radialPairSampleEvent
    {S : Set SquareTorus} (hS : MeasurableSet S) (L : ℝ) (z : ℂ) :
    MeasurableSet (radialPairSampleEvent S L z) := by
  exact hS.preimage measurable_snd |>.inter <|
    hS.preimage (measurable_snd.add
      (measurable_torusVector L |>.comp <| by
        unfold rotateComplex
        fun_prop))

/-- Fubini identifies product Haar measure of the sampled pair event with the radial
correlation. -/
theorem volumeReal_radialPairSampleEvent
    {S : Set SquareTorus} (hS : MeasurableSet S) (L : ℝ) (z : ℂ) :
    volume.real (radialPairSampleEvent S L z) = torusRadialCorrelation S L z := by
  let E := radialPairSampleEvent S L z
  have hE : MeasurableSet E := measurable_radialPairSampleEvent hS L z
  have hint : Integrable (E.indicator fun _ ↦ (1 : ℝ)) volume :=
    (integrable_const (1 : ℝ)).indicator hE
  calc
    volume.real E = ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x ∂volume :=
      (integral_indicator_one hE).symm
    _ = ∫ theta, ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) (theta, x) ∂volume ∂volume :=
      MeasureTheory.integral_prod _ hint
    _ = torusRadialCorrelation S L z := by
      unfold torusRadialCorrelation
      apply integral_congr_ae
      filter_upwards [] with theta
      have hfun :
          (fun x : SquareTorus ↦ E.indicator (fun _ ↦ (1 : ℝ)) (theta, x)) =
            (torusPairEvent S (torusVector L (rotateComplex theta z))).indicator
              (fun _ ↦ (1 : ℝ)) := by
        funext x
        by_cases hx : x ∈ S <;>
          by_cases hxz : x + torusVector L (rotateComplex theta z) ∈ S <;>
          simp [E, radialPairSampleEvent, torusPairEvent, hx, hxz]
      rw [hfun]
      convert
        (integral_indicator_one (μ := (volume : Measure SquareTorus))
          (measurable_torusPairEvent hS _)) using 1
      apply integral_congr_ae
      filter_upwards [] with x
      rfl

/-- The physical displacement represented by row `j`, in either orientation component. -/
def configurationDisplacement (reflected : Bool) (j : Fin 27) : ℂ :=
  orientedConfigurationPoint reflected (pairRight j) -
    orientedConfigurationPoint reflected (pairLeft j)

private theorem pair_configurationDistanceLabel_reverse (j : Fin 27) :
    configurationDistanceLabel (pairRight j) (pairLeft j) = j := by
  fin_cases j <;> rfl

theorem norm_configurationDisplacement (reflected : Bool) (j : Fin 27) :
    ‖configurationDisplacement reflected j‖ = dualDistance j := by
  rw [configurationDisplacement, Complex.norm_def, dualDistance,
    normSq_orientedConfigurationPoint_sub reflected (pairRight j) (pairLeft j)
      (pairLeft_ne_pairRight j).symm,
    pair_configurationDistanceLabel_reverse]

private theorem samplePoint_rigid_zero_neg_left
    (L : ℝ) (reflected : Bool) (j : Fin 27) (ω : TorusSample) :
    samplePoint L reflected
        (rigidSampleMap L 0
          (-orientedConfigurationPoint reflected (pairLeft j)) ω)
        (pairLeft j) = ω.2 := by
  unfold samplePoint rigidSampleMap
  simp only [Prod.fst, Prod.snd, add_zero, rotateComplex_neg, torusVector_neg]
  abel

private theorem samplePoint_rigid_zero_neg_right
    (L : ℝ) (reflected : Bool) (j : Fin 27) (ω : TorusSample) :
    samplePoint L reflected
        (rigidSampleMap L 0
          (-orientedConfigurationPoint reflected (pairLeft j)) ω)
        (pairRight j) =
      ω.2 + torusVector L (rotateComplex ω.1 (configurationDisplacement reflected j)) := by
  unfold samplePoint rigidSampleMap configurationDisplacement
  simp only [Prod.fst, Prod.snd, add_zero, rotateComplex_neg, torusVector_neg,
    rotateComplex_sub, torusVector_sub]
  abel

theorem radialPairSampleEvent_eq_preimage_maskEvent
    (S : Set SquareTorus) (L : ℝ) (reflected : Bool) (j : Fin 27) :
    radialPairSampleEvent S L (configurationDisplacement reflected j) =
      rigidSampleMap L 0 (-orientedConfigurationPoint reflected (pairLeft j)) ⁻¹'
        maskEvent (sampleAssignment S L reflected) (pairMask j) := by
  ext ω
  rw [maskEvent_pairMask]
  simp only [radialPairSampleEvent, mem_setOf_eq, mem_preimage, sampleAssignment,
    decide_eq_true_eq, samplePoint_rigid_zero_neg_left,
    samplePoint_rigid_zero_neg_right]

theorem volumeReal_maskEvent_pairMask
    {S : Set SquareTorus} (hS : MeasurableSet S) (L : ℝ)
    (reflected : Bool) (j : Fin 27) :
    volume.real (maskEvent (sampleAssignment S L reflected) (pairMask j)) =
      torusRadialCorrelation S L (configurationDisplacement reflected j) := by
  have hmask := measurable_maskEvent (measurable_sampleAssignment hS L reflected) (pairMask j)
  have hmeasure :
      volume.real (maskEvent (sampleAssignment S L reflected) (pairMask j)) =
        volume.real (radialPairSampleEvent S L (configurationDisplacement reflected j)) := by
    rw [radialPairSampleEvent_eq_preimage_maskEvent]
    exact congrArg ENNReal.toReal
      ((measurePreserving_rigidSampleMap L 0
        (-orientedConfigurationPoint reflected (pairLeft j))).measure_preimage
          hmask.nullMeasurableSet) |>.symm
  rw [hmeasure, volumeReal_radialPairSampleEvent hS]

theorem torusRadialCorrelation_eq_of_norm_eq
    {S : Set SquareTorus} (hS : MeasurableSet S) {L : ℝ} (hL : 0 < L)
    {z w : ℂ} (hzw : ‖z‖ = ‖w‖) :
    torusRadialCorrelation S L z = torusRadialCorrelation S L w := by
  exact (hasSum_torusFourierMass_mul_besselJ0 hS hL z).unique <| by
    simpa only [hzw] using hasSum_torusFourierMass_mul_besselJ0 hS hL w

/-- The 27 correlations used in both halves of the dual certificate. -/
def torusCertificateCorrelation (S : Set SquareTorus) (L : ℝ) (j : Fin 27) : ℝ :=
  torusRadialCorrelation S L (configurationDisplacement false j)

theorem pairMask_lt_two_pow (j : Fin 27) : pairMask j < 2 ^ 23 := by
  rw [pairMask_values]
  fin_cases j <;> norm_num

/-- Every two-point marginal of the radialized atom distribution is the corresponding radial
correlation. -/
theorem maskMass_torusAtomMass_pair
    {S : Set SquareTorus} (hS : MeasurableSet S) {L : ℝ} (hL : 0 < L)
    (j : Fin 27) :
    maskMass (torusAtomMass S L) (pairMask j) = torusCertificateCorrelation S L j := by
  rw [maskMass_torusAtomMass hS L (pairMask j) (pairMask_lt_two_pow j),
    volumeReal_maskEvent_pairMask hS L false j,
    volumeReal_maskEvent_pairMask hS L true j]
  have hreflect :
      torusRadialCorrelation S L (configurationDisplacement true j) =
        torusRadialCorrelation S L (configurationDisplacement false j) :=
    torusRadialCorrelation_eq_of_norm_eq hS hL <| by
      rw [norm_configurationDisplacement, norm_configurationDisplacement]
  rw [hreflect]
  simp [torusCertificateCorrelation]

/-! ## The remaining semantic rows and the torus bound -/

theorem maskEvent_one {Ω : Type*} (X : Ω → Assignment) :
    maskEvent X 1 = {ω | X ω 0 = true} := by
  ext ω
  simp only [maskEvent, mem_setOf_eq]
  constructor
  · intro h
    exact h 0 Nat.testBit_one_zero
  · intro h i hi
    have hi0 : i.val = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hi
    have hieq : i = 0 := Fin.ext hi0
    simpa [hieq] using h

theorem samplePoint_zero (S : Set SquareTorus) (L : ℝ) (reflected : Bool)
    (ω : TorusSample) : samplePoint L reflected ω 0 = ω.2 := by
  have hzero : orientedConfigurationPoint reflected 0 = 0 := by
    have hc : configurationPoint (0 : Fin 23) = 0 := by
      rw [show configurationPoint (0 : Fin 23) = ({ re := 0, im := 0 } : ℂ) by rfl]
      apply Complex.ext <;> rfl
    cases reflected <;> simp [orientedConfigurationPoint, hc]
  unfold samplePoint
  rw [hzero, rotateComplex_zero, torusVector_zero, add_zero]

theorem maskEvent_sampleAssignment_one
    (S : Set SquareTorus) (L : ℝ) (reflected : Bool) :
    maskEvent (sampleAssignment S L reflected) 1 =
      (Set.univ : Set UnitAddCircle) ×ˢ S := by
  rw [maskEvent_one]
  apply Set.ext
  intro ω
  change (sampleAssignment S L reflected ω 0 = true) ↔
    ω.1 ∈ (Set.univ : Set UnitAddCircle) ∧ ω.2 ∈ S
  simp only [sampleAssignment, decide_eq_true_eq, mem_univ, true_and]
  rw [samplePoint_zero S L reflected ω]

/-- The distinguished-vertex marginal equals Haar density of the torus set. -/
theorem maskMass_torusAtomMass_one
    {S : Set SquareTorus} (hS : MeasurableSet S) (L : ℝ) :
    maskMass (torusAtomMass S L) 1 = volume.real S := by
  rw [maskMass_torusAtomMass hS L 1 (by norm_num),
    maskEvent_sampleAssignment_one, maskEvent_sampleAssignment_one]
  change ((((volume : Measure UnitAddCircle).prod (volume : Measure SquareTorus)).real
      ((Set.univ : Set UnitAddCircle) ×ˢ S) +
    ((volume : Measure UnitAddCircle).prod (volume : Measure SquareTorus)).real
      ((Set.univ : Set UnitAddCircle) ×ˢ S)) / 2) = volume.real S
  simp

theorem torusCertificateCorrelation_eq_tsum
    {S : Set SquareTorus} (hS : MeasurableSet S) {L : ℝ} (hL : 0 < L)
    (j : Fin 27) :
    torusCertificateCorrelation S L j =
      ∑' n : Fin 2 → ℤ, torusFourierMass S n *
        besselJ0 (torusFrequency L n * dualDistance j) := by
  unfold torusCertificateCorrelation
  simpa only [norm_configurationDisplacement] using
    (hasSum_torusFourierMass_mul_besselJ0 hS hL
      (configurationDisplacement false j)).tsum_eq.symm

/-- The unit-distance row vanishes for an admissible torus set. -/
theorem torusCertificateCorrelation_zero
    {S : Set SquareTorus} {L : ℝ} (hfree : TorusUnitDistanceFree L S) :
    torusCertificateCorrelation S L 0 = 0 := by
  have hempty (theta : UnitAddCircle) :
      torusPairEvent S
        (torusVector L (rotateComplex theta (configurationDisplacement false 0))) = ∅ := by
    ext x
    simp only [torusPairEvent, mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact hfree x (rotateComplex theta (configurationDisplacement false 0)) <| by
      rw [normSq_rotateComplex, configurationDisplacement,
        normSq_orientedConfigurationPoint_sub false (pairRight 0) (pairLeft 0)
          (pairLeft_ne_pairRight 0).symm,
        pair_configurationDistanceLabel_reverse]
      rfl
  unfold torusCertificateCorrelation torusRadialCorrelation
  simp_rw [hempty]
  simp

theorem torusAtomMass_pair_rows
    {S : Set SquareTorus} (hS : MeasurableSet S) {L : ℝ} (hL : 0 < L) :
    maskMass (torusAtomMass S L) 513 = torusCertificateCorrelation S L 1 ∧
    maskMass (torusAtomMass S L) 65537 = torusCertificateCorrelation S L 2 ∧
    maskMass (torusAtomMass S L) 4194305 = torusCertificateCorrelation S L 3 ∧
    maskMass (torusAtomMass S L) 2052 = torusCertificateCorrelation S L 4 ∧
    maskMass (torusAtomMass S L) 16388 = torusCertificateCorrelation S L 5 ∧
    maskMass (torusAtomMass S L) 2097160 = torusCertificateCorrelation S L 6 ∧
    maskMass (torusAtomMass S L) 160 = torusCertificateCorrelation S L 7 ∧
    maskMass (torusAtomMass S L) 16416 = torusCertificateCorrelation S L 8 ∧
    maskMass (torusAtomMass S L) 320 = torusCertificateCorrelation S L 9 ∧
    maskMass (torusAtomMass S L) 2112 = torusCertificateCorrelation S L 10 ∧
    maskMass (torusAtomMass S L) 16448 = torusCertificateCorrelation S L 11 ∧
    maskMass (torusAtomMass S L) 1048640 = torusCertificateCorrelation S L 12 ∧
    maskMass (torusAtomMass S L) 4194368 = torusCertificateCorrelation S L 13 ∧
    maskMass (torusAtomMass S L) 2097280 = torusCertificateCorrelation S L 14 ∧
    maskMass (torusAtomMass S L) 4194432 = torusCertificateCorrelation S L 15 ∧
    maskMass (torusAtomMass S L) 4352 = torusCertificateCorrelation S L 16 ∧
    maskMass (torusAtomMass S L) 2097408 = torusCertificateCorrelation S L 17 ∧
    maskMass (torusAtomMass S L) 4194560 = torusCertificateCorrelation S L 18 ∧
    maskMass (torusAtomMass S L) 2098176 = torusCertificateCorrelation S L 19 ∧
    maskMass (torusAtomMass S L) 4195328 = torusCertificateCorrelation S L 20 ∧
    maskMass (torusAtomMass S L) 264192 = torusCertificateCorrelation S L 21 ∧
    maskMass (torusAtomMass S L) 2105344 = torusCertificateCorrelation S L 22 ∧
    maskMass (torusAtomMass S L) 4202496 = torusCertificateCorrelation S L 23 ∧
    maskMass (torusAtomMass S L) 49152 = torusCertificateCorrelation S L 24 ∧
    maskMass (torusAtomMass S L) 3145728 = torusCertificateCorrelation S L 25 ∧
    maskMass (torusAtomMass S L) 5242880 = torusCertificateCorrelation S L 26 := by
  have hrow (j : Fin 27) := maskMass_torusAtomMass_pair hS hL j
  have row (j : Fin 27) (m : Nat) (hm : pairMask j = m) :
      maskMass (torusAtomMass S L) m = torusCertificateCorrelation S L j := by
    simpa only [hm] using hrow j
  exact ⟨row 1 513 (by decide), row 2 65537 (by decide),
    row 3 4194305 (by decide), row 4 2052 (by decide),
    row 5 16388 (by decide), row 6 2097160 (by decide),
    row 7 160 (by decide), row 8 16416 (by decide),
    row 9 320 (by decide), row 10 2112 (by decide),
    row 11 16448 (by decide), row 12 1048640 (by decide),
    row 13 4194368 (by decide), row 14 2097280 (by decide),
    row 15 4194432 (by decide), row 16 4352 (by decide),
    row 17 2097408 (by decide), row 18 4194560 (by decide),
    row 19 2098176 (by decide), row 20 4195328 (by decide),
    row 21 264192 (by decide), row 22 2105344 (by decide),
    row 23 4202496 (by decide), row 24 49152 (by decide),
    row 25 3145728 (by decide), row 26 5242880 (by decide)⟩

theorem torusAtomMass_congruence_rows
    {S : Set SquareTorus} (hS : MeasurableSet S) (L : ℝ) :
    ∀ i : Fin 24, ∀ c ∈ atomCongruenceWeights i,
      maskMass (torusAtomMass S L) c.1 = maskMass (torusAtomMass S L) c.2.1 := by
  intro i c hc
  have hb := certificateMasks_bounded i c hc
  exact maskMass_torusAtomMass_eq_of_congruent hS L hb.1 hb.2
    (certificateMasks_congruent i c hc)

/-- Exact ACMVZ bound for a measurable unit-distance-free subset of a square torus. -/
theorem torus_density_le_dualTarget
    {S : Set SquareTorus} (hS : MeasurableSet S) {L : ℝ} (hL : 0 < L)
    (hfree : TorusUnitDistanceFree L S) :
    volume.real S ≤ (246993028 / 1000000000 : ℝ) := by
  let a : AtomIndex → ℝ := torusAtomMass S L
  let correlation : Fin 27 → ℝ := torusCertificateCorrelation S L
  have hfinite : (1062576034 / 1000000000 : ℝ) * volume.real S +
      pairSpectralValue correlation ≤ (246993028 / 1000000000 : ℝ) := by
    apply semanticFiniteCertificate_bound a (volume.real S) correlation
    · exact torusAtomMass_nonnegative S L
    · exact torusAtomMass_support hfree
    · exact torusAtomMass_total hS L
    · exact maskMass_torusAtomMass_one hS L
    · exact torusAtomMass_pair_rows hS hL
    · exact torusAtomMass_congruence_rows hS L
  have hspectral : volume.real S ≤ (1062576034 / 1000000000 : ℝ) * volume.real S +
      pairSpectralValue correlation := by
    have hspectral' : volume.real S ≤ (dualConstant : ℝ) * volume.real S +
        pairSpectralValue correlation := by
      apply spectralCertificate_bound (torusFourierMass S) (torusFrequency L)
        (volume.real S) correlation
      · exact summable_torusFourierMass hS
      · exact torusFourierMass_nonnegative S
      · exact (hasSum_torusFourierMass hS).tsum_eq
      · exact torusCertificateCorrelation_eq_tsum hS hL
      · exact torusCertificateCorrelation_zero hfree
      · intro n
        exact dual_spectral_nonnegative (torusFrequency L n)
          (torusFrequency_nonnegative hL n)
    norm_num [dualConstant] at hspectral' ⊢
    exact hspectral'
  exact hspectral.trans hfinite

end

end Erdos232
