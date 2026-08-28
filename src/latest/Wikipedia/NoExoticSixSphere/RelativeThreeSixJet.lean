import Wikipedia.NoExoticSixSphere.GenericThreeSixRestriction
import Wikipedia.NoExoticSixSphere.DoublePointRelativePerturbation
import Wikipedia.NoExoticSixSphere.SpatialDerivativeFamily
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Endpoint-relative genericity of actual spatial derivatives

The sigmoid covers the open time interval. Dividing the spatial derivative
by the positive cutoff in these parameters gives a globally smooth operator
family. Almost every constant translation is regular; the scaled-pullback
comparison transfers this to the derivative of the actual cutoff perturbation.
No claim is made about singularities of unchanged exterior-time maps.
-/

noncomputable section

open Set Function Module
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.RelativeDoublePointPerturbation

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem fderiv_perturb (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f))
    (A : V →L[ℝ] W) (t : ℝ) (x : V) :
    fderiv ℝ (perturb f A t) x = fderiv ℝ (f t) x + cutoff t • A := by
  have h : ContDiff ℝ ∞ (f t) := hf.comp (contDiff_const.prodMk contDiff_id)
  exact ((h.differentiable (by simp) x).hasFDerivAt.add
    (A.hasFDerivAt.const_smul (cutoff t))).fderiv

def interiorTime (q : ℝ × V) : ℝ × V := (Real.sigmoid q.1, q.2)

def inverseCutoff (q : ℝ × V) : ℝ := (cutoff (Real.sigmoid q.1))⁻¹

omit [FiniteDimensional ℝ V] in
theorem contDiff_interiorTime : ContDiff ℝ ∞ (interiorTime (V := V)) :=
  ((contDiff_sigmoid.of_le le_top).comp contDiff_fst).prodMk contDiff_snd

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem inverseCutoff_ne_zero (q : ℝ × V) : inverseCutoff q ≠ 0 :=
  inv_ne_zero ((cutoff_pos ⟨Real.sigmoid_pos q.1, Real.sigmoid_lt_one q.1⟩).ne')

omit [FiniteDimensional ℝ V] in
theorem contDiff_inverseCutoff : ContDiff ℝ ∞ (inverseCutoff (V := V)) :=
  (contDiff_cutoff.comp ((contDiff_sigmoid.of_le le_top).comp contDiff_fst)).inv
    (fun q ↦ (cutoff_pos ⟨Real.sigmoid_pos q.1, Real.sigmoid_lt_one q.1⟩).ne')

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem interiorTime_covers (q : ℝ × V) (hq : q.1 ∈ Ioo (0 : ℝ) 1) :
    ∃ p, interiorTime p = q := by
  obtain ⟨t, ht⟩ := Real.range_sigmoid.symm ▸ hq
  exact ⟨(t, q.2), Prod.ext ht rfl⟩

def normalizedSpatialFamily (f : ℝ → V → W) (q : ℝ × V) : V →L[ℝ] W :=
  inverseCutoff q • fderiv ℝ (f (interiorTime q).1) (interiorTime q).2

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem contDiff_normalizedSpatialFamily (f : ℝ → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f)) : ContDiff ℝ ∞ (normalizedSpatialFamily f) :=
  contDiff_inverseCutoff.smul
    ((DiskHomotopy.contDiff_spatial_fderiv f hf).comp contDiff_interiorTime)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem normalizedSpatialFamily_add (f : ℝ → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f)) (A : V →L[ℝ] W) (q : ℝ × V) :
    normalizedSpatialFamily f q + A =
      inverseCutoff q • fderiv ℝ (perturb f A (interiorTime q).1) (interiorTime q).2 := by
  rw [fderiv_perturb f hf, smul_add]
  simp only [normalizedSpatialFamily, inverseCutoff, interiorTime,
    inv_smul_smul₀ (cutoff_pos ⟨Real.sigmoid_pos q.1, Real.sigmoid_lt_one q.1⟩).ne']

theorem ae_regular_jets [MeasurableSpace (V →L[ℝ] W)] [BorelSpace (V →L[ℝ] W)]
    (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f))
    (hv : finrank ℝ V = 3) (hw : finrank ℝ W = 6) :
    ∀ᵐ A ∂μ, OperatorRank.RegularThreeSixOn
      (fun q : ℝ × V ↦ fderiv ℝ (perturb f A q.1) q.2)
      {q | q.1 ∈ Ioo (0 : ℝ) 1} := by
  have hd : finrank ℝ (ℝ × V) = 4 := by
    simp only [finrank_prod, finrank_self, hv]
  apply (OperatorRank.ae_regular_three_six μ (normalizedSpatialFamily f)
    (contDiff_normalizedSpatialFamily f hf) hd hv hw).mono
  intro A hA
  have hreg : OperatorRank.RegularThreeSix
      (fun q ↦ inverseCutoff q •
        fderiv ℝ (perturb f A (interiorTime q).1) (interiorTime q).2) := by
    simpa only [← normalizedSpatialFamily_add f hf A] using hA
  exact OperatorRank.regularOn_of_scaled_pullback
    (fun q : ℝ × V ↦ fderiv ℝ (perturb f A q.1) q.2)
    (DiskHomotopy.contDiff_spatial_fderiv _ (contDiff_perturb f hf A))
    interiorTime contDiff_interiorTime inverseCutoff contDiff_inverseCutoff
    inverseCutoff_ne_zero {q | q.1 ∈ Ioo (0 : ℝ) 1} interiorTime_covers hd hreg

end NoExoticSixSphere.RelativeDoublePointPerturbation
