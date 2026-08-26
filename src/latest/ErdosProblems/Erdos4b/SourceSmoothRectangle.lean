/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceSmoothInterval
import ErdosProblems.Erdos4b.SourceTensorPairSum

/-!
# Smoothing finite rectangular tensor families

Arbitrary real coefficients are allowed in each coordinate factor. No
support endpoint is enlarged, and all variational energies converge.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology ContDiff

def sourceRectangleFactors {ι J : Type*}
    (a b c : J → ι → ℝ) (j : J) (i : ι) (t : ℝ) : ℝ :=
  c j i * sourceIntervalIndicator (a j i) (b j i) t

def sourceSmoothRectangleFactors {ι J : Type*}
    (a b c : J → ι → ℝ) (n : ℕ) (j : J) (i : ι) (t : ℝ) : ℝ :=
  c j i * sourceSmoothInterval (a j i) (b j i) n t

theorem sourceSmoothRectangleFactors_smooth {ι J : Type*}
    (a b c : J → ι → ℝ) (n : ℕ) (j : J) (i : ι) :
    ContDiff ℝ ∞ (sourceSmoothRectangleFactors a b c n j i) :=
  contDiff_const.mul (sourceSmoothInterval_smooth (a j i) (b j i) n)

theorem sourceSmoothRectangleFactors_upper {ι J : Type*}
    (a b c : J → ι → ℝ) (n : ℕ) (j : J) (i : ι) {t : ℝ} (ht : b j i ≤ t) :
    sourceSmoothRectangleFactors a b c n j i t = 0 := by
  unfold sourceSmoothRectangleFactors
  rw [sourceSmoothInterval_eq_zero_of_ge n ht, mul_zero]

theorem sourceRectangleFactors_pair_integrable {ι J : Type*}
    (a b c : J → ι → ℝ) (j k : J) (i : ι) :
    IntegrableOn (fun t ↦ sourceRectangleFactors a b c j i t *
      sourceRectangleFactors a b c k i t) (Set.Ioi 0) := by
  have hh := ((sourceIntervalIndicator_pair_integrable (a j i) (b j i) (a k i) (b k i)).const_mul
    (c j i * c k i)).integrableOn (s := Set.Ioi 0)
  convert hh using 1
  ext t
  unfold sourceRectangleFactors
  ring

theorem sourceSmoothRectangleFactors_pair_integrable {ι J : Type*}
    (a b c : J → ι → ℝ) (n : ℕ) (j k : J) (i : ι) :
    IntegrableOn (fun t ↦ sourceSmoothRectangleFactors a b c n j i t *
      sourceSmoothRectangleFactors a b c n k i t) (Set.Ioi 0) := by
  have hh := ((sourceSmoothInterval_pair_integrable (a j i) (b j i) (a k i) (b k i) n).const_mul
    (c j i * c k i)).integrableOn (s := Set.Ioi 0)
  convert hh using 1
  ext t
  unfold sourceSmoothRectangleFactors
  ring

theorem tendsto_integral_sourceSmoothRectangleFactors {ι J : Type*}
    (a b c : J → ι → ℝ) (j : J) (i : ι) :
    Tendsto (fun n ↦ ∫ t : ℝ in Set.Ioi 0, sourceSmoothRectangleFactors a b c n j i t) atTop
      (𝓝 (∫ t : ℝ in Set.Ioi 0, sourceRectangleFactors a b c j i t)) := by
  simp only [sourceSmoothRectangleFactors, sourceRectangleFactors, integral_const_mul]
  exact (tendsto_integral_sourceSmoothInterval (a j i) (b j i)).const_mul (c j i)

theorem tendsto_integral_sourceSmoothRectangleFactors_pair {ι J : Type*}
    (a b c : J → ι → ℝ) (j k : J) (i : ι) :
    Tendsto (fun n ↦ ∫ t : ℝ in Set.Ioi 0, sourceSmoothRectangleFactors a b c n j i t *
      sourceSmoothRectangleFactors a b c n k i t) atTop
      (𝓝 (∫ t : ℝ in Set.Ioi 0,
        sourceRectangleFactors a b c j i t * sourceRectangleFactors a b c k i t)) := by
  have hid (u v : ℝ) : (c j i * u) * (c k i * v) = (c j i * c k i) * (u * v) := by ring
  simp only [sourceSmoothRectangleFactors, sourceRectangleFactors, hid, integral_const_mul]
  exact (tendsto_integral_sourceSmoothInterval_pair (a j i) (b j i) (a k i) (b k i)).const_mul
    (c j i * c k i)

theorem tendsto_sourceSmoothRectangleEnergy {ι J : Type*} [Fintype ι]
    (S : Finset J) (a b c : J → ι → ℝ) :
    Tendsto (fun n ↦ sourceTensorEnergy S (sourceSmoothRectangleFactors a b c n)) atTop
      (𝓝 (sourceTensorEnergy S (sourceRectangleFactors a b c))) :=
  tendsto_sourceTensorEnergy_of_pair S _ _
    (fun n j _ k _ i ↦ sourceSmoothRectangleFactors_pair_integrable a b c n j k i)
    (fun j _ k _ i ↦ sourceRectangleFactors_pair_integrable a b c j k i)
    (fun j _ k _ i ↦ tendsto_integral_sourceSmoothRectangleFactors_pair a b c j k i)

theorem tendsto_sourceSmoothRectangleFaceEnergy {K : ℕ} {J : Type*}
    (S : Finset J) (a b c : J → Fin K → ℝ) (h : Fin K) :
    Tendsto (fun n ↦ sourceTensorFaceEnergy S (sourceSmoothRectangleFactors a b c n) h) atTop
      (𝓝 (sourceTensorFaceEnergy S (sourceRectangleFactors a b c) h)) :=
  tendsto_sourceTensorFaceEnergy_of_pair S _ _
    (fun n j _ k _ i ↦ sourceSmoothRectangleFactors_pair_integrable a b c n j k i)
    (fun j _ k _ i ↦ sourceRectangleFactors_pair_integrable a b c j k i)
    (fun j _ k _ i ↦ tendsto_integral_sourceSmoothRectangleFactors_pair a b c j k i)
    (fun j _ i ↦ tendsto_integral_sourceSmoothRectangleFactors a b c j i) h

theorem exists_sourceProfile_of_rectangles {K : ℕ} {J : Type*} (hK : 0 < K)
    (S : Finset J) (a b c : J → Fin K → ℝ)
    (hb : ∀ j ∈ S, ∀ i, 0 ≤ b j i)
    (hbudget : ∀ j ∈ S, (∑ i, b j i) ≤ (1 : ℝ) / 10)
    (hI : 0 < sourceTensorEnergy S (sourceRectangleFactors a b c))
    (hJ : ∀ h : Fin K, 0 < sourceTensorFaceEnergy S (sourceRectangleFactors a b c) h)
    {L : ℝ} (hL : L <
      ((∑ h : Fin K, sourceTensorFaceEnergy S (sourceRectangleFactors a b c) h) /
        sourceTensorEnergy S (sourceRectangleFactors a b c)) / sourceCompanionEnergy) :
    ∃ F : J → Fin K → ℝ → ℝ, SourceProfileConditions S F sourceCompanionProfile ∧
      L < sourceProfileRatio S F sourceCompanionProfile := by
  let ψ := sourceSmoothRectangleFactors a b c
  have hlimI := tendsto_sourceSmoothRectangleEnergy S a b c
  have hlimJ := tendsto_sourceSmoothRectangleFaceEnergy S a b c
  have hlimSum := tendsto_finsetSum (Finset.univ : Finset (Fin K)) fun h _ ↦ hlimJ h
  have hlimRatio := (hlimSum.div hlimI hI.ne').div_const sourceCompanionEnergy
  have hposI : ∀ᶠ n in atTop, 0 < sourceTensorEnergy S (ψ n) :=
    hlimI.eventually (Ioi_mem_nhds hI)
  have hposJ : ∀ᶠ n in atTop, ∀ h : Fin K, 0 < sourceTensorFaceEnergy S (ψ n) h :=
    eventually_all.mpr fun h ↦ (hlimJ h).eventually (Ioi_mem_nhds (hJ h))
  obtain ⟨n, hnI, hnJ, hnL⟩ :=
    (hposI.and (hposJ.and (hlimRatio.eventually (Ioi_mem_nhds hL)))).exists
  refine ⟨fun j i ↦ sourceCompactPrimitive (b j i) (ψ n j i), ?_, ?_⟩
  · exact sourcePrimitiveProfileConditions hK S b (ψ n) hb
      (sourceSmoothRectangleFactors_smooth a b c n)
      (fun j i t ht ↦ sourceSmoothRectangleFactors_upper a b c n j i ht) hbudget hnI hnJ
  · rw [sourceProfileRatio_primitive hK S b (ψ n) hb
      (fun j _ i ↦ (sourceSmoothRectangleFactors_smooth a b c n j i).continuous)
      (fun j _ i t ht ↦ sourceSmoothRectangleFactors_upper a b c n j i ht)]
    exact hnL

end

end Erdos4b
