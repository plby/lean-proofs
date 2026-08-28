import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryExponential
import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# A smooth local inverse of the actual complex matrix exponential

The Frobenius norm makes transpose and adjoint isometries. A small
exponential-coordinate ball is chosen inside the inverse chart and
inside the trace bound needed for the determinant-one restriction.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff Topology
open Set Metric Filter

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixLocalLogarithm

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Use the norm topology on both copies of the model space. -/
abbrev SmoothChart (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞

theorem contDiff_exp : ContDiff ℝ ∞ (NormedSpace.exp : Matrix N N ℂ → Matrix N N ℂ) :=
  contDiff_iff_contDiffAt.mpr (fun A ↦ (NormedSpace.exp_analytic (𝕂 := ℝ) A).contDiffAt)

theorem exists_exponentialChart :
    ∃ d : SmoothChart (Matrix N N ℂ),
      0 ∈ d.source ∧ (d : Matrix N N ℂ → Matrix N N ℂ) = NormedSpace.exp := by
  have hd : fderiv ℝ (NormedSpace.exp : Matrix N N ℂ → Matrix N N ℂ) 0 = 1 :=
    (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix N N ℂ)).fderiv
  have hinv : (fderiv ℝ (NormedSpace.exp : Matrix N N ℂ → Matrix N N ℂ) 0).IsInvertible := by
    rw [hd]
    exact ⟨ContinuousLinearEquiv.refl ℝ (Matrix N N ℂ), rfl⟩
  obtain ⟨d, hd0, _, hdf⟩ := NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn
    isOpen_univ (mem_univ (0 : Matrix N N ℂ)) contDiff_exp.contDiffOn hinv
  exact ⟨d, hd0, hdf⟩

def exponentialChart (N : Type*) [Fintype N] [DecidableEq N] :
    SmoothChart (Matrix N N ℂ) := Classical.choose exists_exponentialChart

theorem zero_mem_source : 0 ∈ (exponentialChart N).source :=
  (Classical.choose_spec (exists_exponentialChart (N := N))).1

theorem exponentialChart_apply (A : Matrix N N ℂ) : exponentialChart N A = NormedSpace.exp A :=
  congrFun (Classical.choose_spec (exists_exponentialChart (N := N))).2 A

def logarithm (B : Matrix N N ℂ) : Matrix N N ℂ := (exponentialChart N).symm B

theorem contDiffOn_logarithm :
    ContDiffOn ℝ ∞ (logarithm (N := N)) (exponentialChart N).target := by
  simpa only [logarithm] using! (exponentialChart N).contMDiffOn_invFun.contDiffOn

theorem one_mem_target : 1 ∈ (exponentialChart N).target := by
  have h := (exponentialChart N).map_source' (zero_mem_source (N := N))
  rwa [exponentialChart_apply, NormedSpace.exp_zero] at h

theorem exp_logarithm (B : Matrix N N ℂ) (hB : B ∈ (exponentialChart N).target) :
    NormedSpace.exp (logarithm B) = B := by
  have h := (exponentialChart N).right_inv' hB
  rwa [exponentialChart_apply] at h

theorem logarithm_exp (A : Matrix N N ℂ) (hA : A ∈ (exponentialChart N).source) :
    logarithm (NormedSpace.exp A) = A := by
  have h := (exponentialChart N).left_inv' hA
  rwa [exponentialChart_apply] at h

theorem logarithm_one : logarithm (1 : Matrix N N ℂ) = 0 := by
  simpa only [NormedSpace.exp_zero] using logarithm_exp 0 (zero_mem_source (N := N))

def safeSource (N : Type*) [Fintype N] [DecidableEq N] : Set (Matrix N N ℂ) :=
  (exponentialChart N).source ∩ {A | ‖A.trace‖ < Real.pi}

theorem isOpen_safeSource : IsOpen (safeSource N) :=
  (exponentialChart N).open_source.inter
    (isOpen_lt continuous_id.matrix_trace.norm continuous_const)

theorem zero_mem_safeSource : (0 : Matrix N N ℂ) ∈ safeSource N := by
  refine ⟨zero_mem_source, ?_⟩
  change ‖(0 : Matrix N N ℂ).trace‖ < Real.pi
  simpa only [Matrix.trace_zero, norm_zero] using Real.pi_pos

theorem exists_radius : ∃ r : ℝ, 0 < r ∧ closedBall (0 : Matrix N N ℂ) r ⊆ safeSource N := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (isOpen_safeSource.mem_nhds (zero_mem_safeSource (N := N)))
  refine ⟨ε / 2, by linarith, ?_⟩
  intro A hA
  apply hball
  change dist A 0 < ε
  exact lt_of_le_of_lt hA (show ε / 2 < ε by linarith)

def radius (N : Type*) [Fintype N] [DecidableEq N] : ℝ := Classical.choose (exists_radius (N := N))

theorem radius_pos : 0 < radius N := (Classical.choose_spec (exists_radius (N := N))).1

theorem radius_closedBall : closedBall (0 : Matrix N N ℂ) (radius N) ⊆ safeSource N :=
  (Classical.choose_spec (exists_radius (N := N))).2

theorem mem_safeSource_of_norm_lt (A : Matrix N N ℂ) (hA : ‖A‖ < radius N) :
    A ∈ safeSource N :=
  radius_closedBall (N := N) (by simpa only [mem_closedBall, dist_zero_right] using hA.le)

def domain (N : Type*) [Fintype N] [DecidableEq N] : Set (Matrix N N ℂ) :=
  {B | B ∈ (exponentialChart N).target ∧ ‖logarithm B‖ < radius N}

theorem isOpen_domain : IsOpen (domain N) := by
  apply isOpen_iff_mem_nhds.mpr
  intro B hB
  have hs := (exponentialChart N).open_target.mem_nhds hB.1
  have hc : ContinuousAt (logarithm (N := N)) B :=
    (exponentialChart N).contMDiffOn_invFun.continuousOn.continuousAt hs
  have hn := hc.norm (Iio_mem_nhds hB.2)
  filter_upwards [hs, hn] with C hC hnorm
  exact ⟨hC, hnorm⟩

theorem one_mem_domain : (1 : Matrix N N ℂ) ∈ domain N := by
  refine ⟨one_mem_target, ?_⟩
  rw [logarithm_one, norm_zero]
  exact radius_pos

theorem logarithm_mem_source (B : Matrix N N ℂ) (hB : B ∈ domain N) :
    logarithm B ∈ (exponentialChart N).source :=
  (exponentialChart N).map_target' hB.1

theorem logarithm_trace_lt (B : Matrix N N ℂ) (hB : B ∈ domain N) :
    ‖(logarithm B).trace‖ < Real.pi :=
  (mem_safeSource_of_norm_lt (logarithm B) hB.2).2

theorem exp_mem_domain (A : Matrix N N ℂ) (hA : ‖A‖ < radius N) :
    NormedSpace.exp A ∈ domain N := by
  have hs := (mem_safeSource_of_norm_lt A hA).1
  refine ⟨?_, ?_⟩
  · simpa only [exponentialChart_apply] using (exponentialChart N).map_source' hs
  · rwa [logarithm_exp A hs]

theorem exp_injective_small {A B : Matrix N N ℂ}
    (hA : ‖A‖ < radius N) (hB : ‖B‖ < radius N)
    (h : NormedSpace.exp A = NormedSpace.exp B) : A = B := by
  have ha := (mem_safeSource_of_norm_lt A hA).1
  have hb := (mem_safeSource_of_norm_lt B hB).1
  exact (logarithm_exp A ha).symm.trans ((congrArg logarithm h).trans (logarithm_exp B hb))

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixLocalLogarithm
