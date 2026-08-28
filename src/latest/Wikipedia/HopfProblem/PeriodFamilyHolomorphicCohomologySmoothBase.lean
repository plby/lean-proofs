import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkSections
import Mathlib.Analysis.Matrix.Normed

/-!
# Real smoothness of the original period entries on an open complex base

The base is an arbitrary open subset of the complex line, with its actual
inherited chart. We extend the three original holomorphic scalar functions
by zero solely to express `ContDiffOn` on the ambient normed space. Every
value and every differentiability assertion is on the original open set;
no regularity at its boundary is asserted.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth

/-- An actual holomorphic section is complex differentiable to every order
on its original open set, using its literal ambient representative. -/
theorem extendedSection_contDiffOn_complex (U : Opens ℂ)
    (f : ContMDiffMap 𝓘(ℂ) 𝓘(ℂ) U ℂ ω) (n : ℕ∞ω) :
    ContDiffOn ℂ n (HolomorphicFunctionSheaf.extendSection U f) U := by
  intro z hz
  exact (HolomorphicFunctionSheaf.extendSection_analyticAt U f z hz).contDiffAt.contDiffWithinAt

/-- In particular the literal representative is real smooth inside the open set. -/
theorem extendedSection_contDiffOn_real (U : Opens ℂ)
    (f : ContMDiffMap 𝓘(ℂ) 𝓘(ℂ) U ℂ ω) :
    ContDiffOn ℝ ∞ (HolomorphicFunctionSheaf.extendSection U f) U :=
  (extendedSection_contDiffOn_complex U f ∞).restrict_scalars ℝ

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The original first period entry as a native holomorphic section. -/
def tauSection : ContMDiffMap 𝓘(ℂ) 𝓘(ℂ) U ℂ ω :=
  ⟨fun z => (P.point z).val.τ, P.holomorphic_tau⟩

/-- The original mixed period entry as a native holomorphic section. -/
def muSection : ContMDiffMap 𝓘(ℂ) 𝓘(ℂ) U ℂ ω :=
  ⟨fun z => (P.point z).val.μ, P.holomorphic_mu⟩

/-- The original remaining period entry as a native holomorphic section. -/
def betaSection : ContMDiffMap 𝓘(ℂ) 𝓘(ℂ) U ℂ ω :=
  ⟨fun z => (P.point z).val.β, P.holomorphic_beta⟩

def tauValue : ℂ → ℂ := HolomorphicFunctionSheaf.extendSection U (tauSection P)
def muValue : ℂ → ℂ := HolomorphicFunctionSheaf.extendSection U (muSection P)
def betaValue : ℂ → ℂ := HolomorphicFunctionSheaf.extendSection U (betaSection P)

@[simp] theorem tauValue_apply (z : U) : tauValue P z = (P.point z).val.τ :=
  HolomorphicFunctionSheaf.extendSection_apply U (tauSection P) z z.property

@[simp] theorem muValue_apply (z : U) : muValue P z = (P.point z).val.μ :=
  HolomorphicFunctionSheaf.extendSection_apply U (muSection P) z z.property

@[simp] theorem betaValue_apply (z : U) : betaValue P z = (P.point z).val.β :=
  HolomorphicFunctionSheaf.extendSection_apply U (betaSection P) z z.property

theorem tauValue_contDiffOn_complex : ContDiffOn ℂ ω (tauValue P) U :=
  extendedSection_contDiffOn_complex U (tauSection P) ω

theorem muValue_contDiffOn_complex : ContDiffOn ℂ ω (muValue P) U :=
  extendedSection_contDiffOn_complex U (muSection P) ω

theorem betaValue_contDiffOn_complex : ContDiffOn ℂ ω (betaValue P) U :=
  extendedSection_contDiffOn_complex U (betaSection P) ω

theorem tauValue_contDiffOn_real : ContDiffOn ℝ ∞ (tauValue P) U :=
  extendedSection_contDiffOn_real U (tauSection P)

theorem muValue_contDiffOn_real : ContDiffOn ℝ ∞ (muValue P) U :=
  extendedSection_contDiffOn_real U (muSection P)

theorem betaValue_contDiffOn_real : ContDiffOn ℝ ∞ (betaValue P) U :=
  extendedSection_contDiffOn_real U (betaSection P)

/-- Ambient representatives of the original three period entries. Their
admissibility is used and asserted only on the original base open. -/
def extendedPeriodPoint (z : ℂ) : PeriodPoint :=
  ⟨tauValue P z, muValue P z, betaValue P z⟩

@[simp] theorem extendedPeriodPoint_apply (z : U) :
    extendedPeriodPoint P z = (P.point z).val := by
  apply PeriodPoint.ext
  · exact tauValue_apply P z
  · exact muValue_apply P z
  · exact betaValue_apply P z

/-- The actual real period matrix expressed in the original open base chart. -/
def realPeriodMatrix (z : ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (extendedPeriodPoint P z).realMatrix

@[simp] theorem realPeriodMatrix_apply (z : U) :
    realPeriodMatrix P z = (P.point z).val.realMatrix := by
  rw [realPeriodMatrix, extendedPeriodPoint_apply]

/-- Real smoothness follows from the genuine holomorphic period entries. -/
theorem realPeriodMatrix_contDiffOn : ContDiffOn ℝ ∞ (realPeriodMatrix P) U := by
  have htR := Complex.reCLM.contDiff.comp_contDiffOn (tauValue_contDiffOn_real P)
  have htI := Complex.imCLM.contDiff.comp_contDiffOn (tauValue_contDiffOn_real P)
  have hmR := Complex.reCLM.contDiff.comp_contDiffOn (muValue_contDiffOn_real P)
  have hmI := Complex.imCLM.contDiff.comp_contDiffOn (muValue_contDiffOn_real P)
  have hbR := Complex.reCLM.contDiff.comp_contDiffOn (betaValue_contDiffOn_real P)
  have hbI := Complex.imCLM.contDiff.comp_contDiffOn (betaValue_contDiffOn_real P)
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact contDiffOn_const
    | exact contDiffOn_const.mul hmR
    | exact contDiffOn_const.mul hmI
    | exact htR
    | exact htI
    | exact hmR
    | exact hmI
    | exact hbR
    | exact hbI

/-- The original admissibility proves invertibility at every point of the open base. -/
theorem realPeriodMatrix_det_ne_zero (z : ℂ) (hz : z ∈ U) :
    (realPeriodMatrix P z).det ≠ 0 := by
  have heq : realPeriodMatrix P z = (P.point ⟨z, hz⟩).val.realMatrix :=
    realPeriodMatrix_apply P ⟨z, hz⟩
  rw [heq]
  exact ne_of_lt ((P.point ⟨z, hz⟩).val.det_realMatrix_neg (P.point ⟨z, hz⟩).property)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth
