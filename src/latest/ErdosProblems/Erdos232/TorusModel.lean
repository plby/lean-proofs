/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.AtomDistribution
import ErdosProblems.Erdos232.MaskCongruence
import Mathlib.Analysis.Fourier.AddCircleMulti

open MeasureTheory Set
open scoped ComplexConjugate ENNReal

namespace Erdos232

noncomputable section

local instance torusModelMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusModelIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusModelIsProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev SquareTorus := UnitAddTorus (Fin 2)
abbrev TorusSample := UnitAddCircle × SquareTorus

/-- Embed a physical complex displacement, divided by the square period, in the unit torus. -/
noncomputable def torusVector (L : ℝ) (z : ℂ) : SquareTorus := fun i ↦
  match i.val with
  | 0 => (z.re / L : UnitAddCircle)
  | _ => (z.im / L : UnitAddCircle)

theorem torusVector_zero (L : ℝ) : torusVector L 0 = 0 := by
  ext i
  fin_cases i <;> simp [torusVector]

theorem torusVector_add (L : ℝ) (z w : ℂ) :
    torusVector L (z + w) = torusVector L z + torusVector L w := by
  ext i
  fin_cases i <;> simp [torusVector, add_div]

theorem torusVector_sub (L : ℝ) (z w : ℂ) :
    torusVector L (z - w) = torusVector L z - torusVector L w := by
  ext i
  fin_cases i <;> simp [torusVector, sub_div]

theorem torusVector_neg (L : ℝ) (z : ℂ) :
    torusVector L (-z) = -torusVector L z := by
  simpa only [zero_sub, torusVector_zero] using torusVector_sub L 0 z

theorem measurable_torusVector (L : ℝ) : Measurable (torusVector L) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · exact AddCircle.measurable_mk'.comp (Complex.measurable_re.div_const L)
  · exact AddCircle.measurable_mk'.comp (Complex.measurable_im.div_const L)

/-- Multiplication by the unit-circle character is the physical rotation used in the radial
average. -/
noncomputable def rotateComplex (θ : UnitAddCircle) (z : ℂ) : ℂ :=
  fourier 1 θ * z

@[simp] theorem rotateComplex_zero (θ : UnitAddCircle) : rotateComplex θ 0 = 0 := by
  simp [rotateComplex]

theorem rotateComplex_add (θ : UnitAddCircle) (z w : ℂ) :
    rotateComplex θ (z + w) = rotateComplex θ z + rotateComplex θ w := by
  simp [rotateComplex, mul_add]

theorem rotateComplex_sub (θ : UnitAddCircle) (z w : ℂ) :
    rotateComplex θ (z - w) = rotateComplex θ z - rotateComplex θ w := by
  simp [rotateComplex, mul_sub]

theorem rotateComplex_neg (θ : UnitAddCircle) (z : ℂ) :
    rotateComplex θ (-z) = -rotateComplex θ z := by
  simpa only [zero_sub, rotateComplex_zero] using rotateComplex_sub θ 0 z

theorem measurable_rotateComplex_const (z : ℂ) :
    Measurable fun θ : UnitAddCircle ↦ rotateComplex θ z := by
  unfold rotateComplex
  fun_prop

theorem normSq_rotateComplex (θ : UnitAddCircle) (z : ℂ) :
    Complex.normSq (rotateComplex θ z) = Complex.normSq z := by
  rw [rotateComplex, Complex.normSq_mul]
  have hunit : Complex.normSq (fourier 1 θ) = 1 := by
    rw [fourier_one]
    exact Circle.normSq_coe _
  rw [hunit, one_mul]

/-- A torus set is admissible when it never contains a point and any of its physical
unit-displacement translates. -/
def TorusUnitDistanceFree (L : ℝ) (S : Set SquareTorus) : Prop :=
  ∀ x z, Complex.normSq z = 1 → ¬ (x ∈ S ∧ x + torusVector L z ∈ S)

noncomputable def orientedConfigurationPoint (reflected : Bool) (i : Fin 23) : ℂ :=
  if reflected then conj (configurationPoint i) else configurationPoint i

noncomputable def samplePoint (L : ℝ) (reflected : Bool)
    (ω : TorusSample) (i : Fin 23) : SquareTorus :=
  ω.2 + torusVector L (rotateComplex ω.1 (orientedConfigurationPoint reflected i))

theorem measurable_samplePoint (L : ℝ) (reflected : Bool) (i : Fin 23) :
    Measurable fun ω : TorusSample ↦ samplePoint L reflected ω i := by
  exact measurable_snd.add <| (measurable_torusVector L).comp <|
    (measurable_rotateComplex_const (orientedConfigurationPoint reflected i)).comp measurable_fst

noncomputable def sampleAssignment (S : Set SquareTorus) (L : ℝ) (reflected : Bool)
    (ω : TorusSample) : Assignment := fun i ↦
  @decide (samplePoint L reflected ω i ∈ S) (Classical.propDecidable _)

theorem measurable_sampleAssignment {S : Set SquareTorus} (hS : MeasurableSet S)
    (L : ℝ) (reflected : Bool) : Measurable (sampleAssignment S L reflected) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_to_countable'
  intro b
  cases b
  · have hpre := hS.preimage (measurable_samplePoint L reflected i)
    convert hpre.compl using 1
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, sampleAssignment,
      decide_eq_false_iff_not]
  · have hpre := hS.preimage (measurable_samplePoint L reflected i)
    convert hpre using 1
    ext ω
    simp only [mem_preimage, mem_singleton_iff, sampleAssignment, decide_eq_true_eq]

/-- The exact atom distribution is the average of the directly rotated and reflected-rotated
configuration distributions. -/
noncomputable def torusAtomMass (S : Set SquareTorus) (L : ℝ) (s : AtomIndex) : ℝ :=
  (atomMass volume (sampleAssignment S L false) s +
    atomMass volume (sampleAssignment S L true) s) / 2

theorem torusAtomMass_nonnegative (S : Set SquareTorus) (L : ℝ) (s : AtomIndex) :
    0 ≤ torusAtomMass S L s := by
  exact div_nonneg (add_nonneg (atomMass_nonnegative _ _ _) (atomMass_nonnegative _ _ _))
    (by norm_num)

theorem torusAtomMass_total {S : Set SquareTorus} (hS : MeasurableSet S) (L : ℝ) :
    ∑ s, torusAtomMass S L s = 1 := by
  calc
    ∑ s, torusAtomMass S L s =
        ((∑ s, atomMass volume (sampleAssignment S L false) s) +
          ∑ s, atomMass volume (sampleAssignment S L true) s) / 2 := by
      unfold torusAtomMass
      calc
        ∑ s, (atomMass volume (sampleAssignment S L false) s +
            atomMass volume (sampleAssignment S L true) s) / 2 =
            (∑ s, (atomMass volume (sampleAssignment S L false) s +
              atomMass volume (sampleAssignment S L true) s)) / 2 :=
          (Finset.sum_div Finset.univ
            (fun s ↦ atomMass volume (sampleAssignment S L false) s +
              atomMass volume (sampleAssignment S L true) s) 2).symm
        _ = _ := by rw [Finset.sum_add_distrib]
    _ = (1 + 1) / 2 := by
      rw [atomMass_total volume _ (measurable_sampleAssignment hS L false),
        atomMass_total volume _ (measurable_sampleAssignment hS L true)]
    _ = 1 := by norm_num

theorem maskMass_torusAtomMass {S : Set SquareTorus} (hS : MeasurableSet S)
    (L : ℝ) (m : Nat) (hm : m < 2 ^ 23) :
    maskMass (torusAtomMass S L) m =
      (volume.real (maskEvent (sampleAssignment S L false) m) +
        volume.real (maskEvent (sampleAssignment S L true) m)) / 2 := by
  simp only [maskMass, torusAtomMass]
  have hsplit (r : Bool) :
      (∑ s, if natMaskSubset m s.val then atomMass volume (sampleAssignment S L r) s / 2 else 0) =
        maskMass (atomMass volume (sampleAssignment S L r)) m / 2 := by
    rw [maskMass, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    split <;> simp_all
  rw [show (∑ s, if natMaskSubset m s.val then
        (atomMass volume (sampleAssignment S L false) s +
          atomMass volume (sampleAssignment S L true) s) / 2 else 0) =
      (∑ s, if natMaskSubset m s.val then
          atomMass volume (sampleAssignment S L false) s / 2 else 0) +
        (∑ s, if natMaskSubset m s.val then
          atomMass volume (sampleAssignment S L true) s / 2 else 0) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      split <;> ring]
  rw [hsplit false, hsplit true,
    maskMass_atomMass volume _ (measurable_sampleAssignment hS L false) m hm,
    maskMass_atomMass volume _ (measurable_sampleAssignment hS L true) m hm]
  ring

/-! ## Haar invariance and the semantic congruence rows -/

/-- The skew translation of the sampling space induced by a rotation phase and a physical
translation. -/
noncomputable def rigidSampleMap (L : ℝ) (φ : UnitAddCircle) (c : ℂ) :
    TorusSample → TorusSample := fun ω ↦
  (ω.1 + φ, ω.2 + torusVector L (rotateComplex ω.1 c))

theorem measurable_rigidSampleMap (L : ℝ) (φ : UnitAddCircle) (c : ℂ) :
    Measurable (rigidSampleMap L φ c) := by
  unfold rigidSampleMap
  apply Measurable.prodMk
  · exact measurable_fst.add measurable_const
  · exact measurable_snd.add <| (measurable_torusVector L).comp <|
      (measurable_rotateComplex_const c).comp measurable_fst

/-- `rigidSampleMap` preserves the product of normalized Haar measures. -/
theorem measurePreserving_rigidSampleMap (L : ℝ) (φ : UnitAddCircle) (c : ℂ) :
    MeasurePreserving (rigidSampleMap L φ c) volume volume := by
  change MeasurePreserving (fun ω : UnitAddCircle × SquareTorus ↦
      (ω.1 + φ, ω.2 + torusVector L (rotateComplex ω.1 c)))
    ((volume : Measure UnitAddCircle).prod (volume : Measure SquareTorus))
    ((volume : Measure UnitAddCircle).prod (volume : Measure SquareTorus))
  refine (measurePreserving_add_right (volume : Measure UnitAddCircle) φ).skew_product
    (g := fun θ x ↦ x + torusVector L (rotateComplex θ c)) ?_ ?_
  · exact measurable_snd.add <| (measurable_torusVector L).comp <|
      (measurable_rotateComplex_const c).comp measurable_fst
  · filter_upwards [] with θ
    exact (measurePreserving_add_right (volume : Measure SquareTorus)
      (torusVector L (rotateComplex θ c))).map_eq

private theorem fourier_one_add (θ φ : UnitAddCircle) :
    fourier 1 (θ + φ) = fourier 1 θ * fourier 1 φ := by
  simp only [fourier_apply, one_zsmul, AddCircle.toCircle_add, Circle.coe_mul]

/-- A rigid motion of configuration points is absorbed by a Haar-preserving change of the
rotation and translation sampling parameters. -/
theorem samplePoint_eq_rigidSampleMap
    (Sref Tref : Bool) (L : ℝ) (φ : UnitAddCircle) (u c : ℂ)
    (i j : Fin 23) (hφ : fourier 1 φ = u)
    (hpoint : orientedConfigurationPoint Tref j =
      u * orientedConfigurationPoint Sref i + c) (ω : TorusSample) :
    samplePoint L Tref ω j = samplePoint L Sref (rigidSampleMap L φ c ω) i := by
  have hrot : rotateComplex ω.1 (u * orientedConfigurationPoint Sref i) =
      rotateComplex (ω.1 + φ) (orientedConfigurationPoint Sref i) := by
    simp only [rotateComplex, fourier_one_add, hφ]
    ring
  calc
    samplePoint L Tref ω j =
        ω.2 + torusVector L
          (rotateComplex ω.1 (u * orientedConfigurationPoint Sref i + c)) := by
            rw [samplePoint, hpoint]
    _ = ω.2 + torusVector L (rotateComplex ω.1
          (u * orientedConfigurationPoint Sref i)) +
          torusVector L (rotateComplex ω.1 c) := by
            rw [rotateComplex_add, torusVector_add]
            abel
    _ = (ω.2 + torusVector L (rotateComplex ω.1 c)) +
          torusVector L (rotateComplex (ω.1 + φ)
            (orientedConfigurationPoint Sref i)) := by
            rw [hrot]
            abel
    _ = samplePoint L Sref (rigidSampleMap L φ c ω) i := rfl

private theorem selectedVertices_mem_iff (m : Nat) (i : Fin 23) :
    i ∈ selectedVertices m ↔ m.testBit i := by
  simp [selectedVertices]

/-- A pointwise rigid correspondence identifies the associated positive-mask events by the
Haar-preserving sampling change of variables. -/
theorem maskEvent_eq_preimage_rigidSampleMap
    {S : Set SquareTorus} (L : ℝ) (Sref Tref : Bool)
    {m n : Nat} (e : (↥(selectedVertices m)) ≃ (↥(selectedVertices n)))
    (φ : UnitAddCircle) (u c : ℂ) (hφ : fourier 1 φ = u)
    (hpoint : ∀ i, orientedConfigurationPoint Tref (e i).1 =
      u * orientedConfigurationPoint Sref i.1 + c) :
    maskEvent (sampleAssignment S L Tref) n =
      rigidSampleMap L φ c ⁻¹' maskEvent (sampleAssignment S L Sref) m := by
  ext ω
  simp only [maskEvent, mem_setOf_eq, mem_preimage, sampleAssignment,
    decide_eq_true_eq]
  constructor
  · intro h i hi
    have him : i ∈ selectedVertices m := (selectedVertices_mem_iff m i).2 hi
    let ii : ↥(selectedVertices m) := ⟨i, him⟩
    have hei : (e ii).1 ∈ selectedVertices n := (e ii).2
    have htarget := h (e ii).1 ((selectedVertices_mem_iff n (e ii).1).1 hei)
    rw [samplePoint_eq_rigidSampleMap Sref Tref L φ u c i (e ii).1 hφ
      (by simpa [ii] using hpoint ii) ω] at htarget
    exact htarget
  · intro h j hj
    have hjn : j ∈ selectedVertices n := (selectedVertices_mem_iff n j).2 hj
    let jj : ↥(selectedVertices n) := ⟨j, hjn⟩
    let ii : ↥(selectedVertices m) := e.symm jj
    have hii : ii.1 ∈ selectedVertices m := ii.2
    have hsource := h ii.1 ((selectedVertices_mem_iff m ii.1).1 hii)
    have heq : (e ii).1 = j := by
      exact congrArg Subtype.val (e.apply_symm_apply jj)
    rw [← heq]
    rw [samplePoint_eq_rigidSampleMap Sref Tref L φ u c ii.1 (e ii).1 hφ
      (hpoint ii) ω]
    exact hsource

/-- The two orientation components of the radialized atom distribution make every certified
direct or reflected finite congruence an exact equality of mask marginals. -/
theorem maskMass_torusAtomMass_eq_of_congruent
    {S : Set SquareTorus} (hS : MeasurableSet S) (L : ℝ)
    {m n : Nat} (hm : m < 2 ^ 23) (hn : n < 2 ^ 23)
    (hcong : MaskCongruent m n) :
    maskMass (torusAtomMass S L) m = maskMass (torusAtomMass S L) n := by
  classical
  obtain ⟨e, reflected, u, c, hu, hrigid⟩ := hcong.exists_rigid
  have hunorm : ‖u‖ = 1 := by
    have hnonneg : 0 ≤ ‖u‖ := norm_nonneg u
    rw [Complex.normSq_eq_norm_sq] at hu
    nlinarith
  let ucircle : Circle := ⟨u, by simpa [Submonoid.unitSphere] using hunorm⟩
  let φ : UnitAddCircle := (AddCircle.homeomorphCircle one_ne_zero).symm ucircle
  have hφ : fourier 1 φ = u := by
    rw [fourier_one]
    have hs : (AddCircle.homeomorphCircle one_ne_zero) φ = ucircle := by
      exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply ucircle
    rw [AddCircle.homeomorphCircle_apply] at hs
    simpa [ucircle] using congrArg ((↑) : Circle → ℂ) hs
  have hφneg : fourier 1 (-φ) = conj u := by
    rw [fourier_one, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]
    simpa only [← fourier_one] using congrArg conj hφ
  have hfalse : volume.real (maskEvent (sampleAssignment S L false) n) =
      volume.real (maskEvent (sampleAssignment S L reflected) m) := by
    rw [maskEvent_eq_preimage_rigidSampleMap L reflected false e φ u c hφ
      (by simpa [orientedConfigurationPoint] using hrigid)]
    exact congrArg ENNReal.toReal <|
      (measurePreserving_rigidSampleMap L φ c).measure_preimage
        (measurable_maskEvent (measurable_sampleAssignment hS L reflected) m).nullMeasurableSet
  have hrigidConj : ∀ i, orientedConfigurationPoint true (e i).1 =
      conj u * orientedConfigurationPoint (!reflected) i.1 + conj c := by
    intro i
    have hi := congrArg conj (hrigid i)
    cases reflected <;>
      simpa [orientedConfigurationPoint, map_add, map_mul] using hi
  have htrue : volume.real (maskEvent (sampleAssignment S L true) n) =
      volume.real (maskEvent (sampleAssignment S L (!reflected)) m) := by
    rw [maskEvent_eq_preimage_rigidSampleMap L (!reflected) true e (-φ) (conj u)
      (conj c) hφneg hrigidConj]
    exact congrArg ENNReal.toReal <|
      (measurePreserving_rigidSampleMap L (-φ) (conj c)).measure_preimage
        (measurable_maskEvent
          (measurable_sampleAssignment hS L (!reflected)) m).nullMeasurableSet
  rw [maskMass_torusAtomMass hS L m hm, maskMass_torusAtomMass hS L n hn,
    hfalse, htrue]
  cases reflected <;> simp <;> ring

end

end Erdos232
