import Wikipedia.HopfProblem.ExponentialCharts
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Exponential charts in all three logarithmic coordinates

The two fibre coordinates and the base parameter are exponentiated together.
This is an analytic local diffeomorphism from `ℂ × ℂ²` into the dense torus.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts

abbrev LogModel := ℂ × ComplexPlane₂

def logCoordinateLinear : LogModel ≃ₗ[ℂ] CoordinateSpace 3 where
  toFun p := ![p.2 0, p.2 1, p.1]
  invFun w := (w 2, ![w 0, w 1])
  left_inv p := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl
  right_inv w := by
    ext i
    fin_cases i <;> rfl
  map_add' p q := by
    ext i
    fin_cases i <;> rfl
  map_smul' c p := by
    ext i
    fin_cases i <;> rfl

def logCoordinateEquiv : LogModel ≃L[ℂ] CoordinateSpace 3 :=
  logCoordinateLinear.toContinuousLinearEquiv

@[simp] theorem logCoordinateEquiv_apply (p : LogModel) :
    logCoordinateEquiv p = ![p.2 0, p.2 1, p.1] := rfl

def totalExponentialCoordinates (p : LogModel) : CoordinateSpace 3 :=
  ![exponential (p.2 0), exponential (p.2 1), exponential p.1]

@[simp] theorem totalExponentialCoordinates_zero (p : LogModel) :
    totalExponentialCoordinates p 0 = exponential (p.2 0) := rfl

@[simp] theorem totalExponentialCoordinates_one (p : LogModel) :
    totalExponentialCoordinates p 1 = exponential (p.2 1) := rfl

@[simp] theorem totalExponentialCoordinates_two (p : LogModel) :
    totalExponentialCoordinates p 2 = exponential p.1 := rfl

theorem totalExponentialCoordinates_mem_torus (p : LogModel) :
    totalExponentialCoordinates p ∈ torus := by
  intro i
  fin_cases i <;> exact exponential_ne_zero _

theorem totalExponentialCoordinates_holomorphic :
    ContDiff ℂ ω totalExponentialCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 0).comp contDiff_snd)
  · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 1).comp contDiff_snd)
  · exact exponential_holomorphic.comp contDiff_fst

def totalExponentialDerivative (p : LogModel) : LogModel ≃L[ℂ] CoordinateSpace 3 :=
  ((ContinuousLinearEquiv.unitsEquivAut ℂ
      (Units.mk0 (exponential p.1 * (2 * Real.pi * Complex.I))
        (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero))).prodCongr
    (exponentialPairDerivative p.2)).trans logCoordinateEquiv

theorem totalExponentialCoordinates_hasFDerivAt (p : LogModel) :
    HasFDerivAt totalExponentialCoordinates
      (totalExponentialDerivative p : LogModel →L[ℂ] CoordinateSpace 3) p := by
  convert! logCoordinateEquiv.hasFDerivAt.comp p
    (((exponential_hasDerivAt p.1).hasFDerivAt_equiv
      (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero)).prodMap p
        (exponentialPair_hasFDerivAt p.2)) using 1

def totalExponentialChart (p : LogModel) :
    OpenPartialHomeomorph LogModel (CoordinateSpace 3) :=
  totalExponentialCoordinates_holomorphic.contDiffAt.toOpenPartialHomeomorph
    totalExponentialCoordinates (totalExponentialCoordinates_hasFDerivAt p) (by simp)

@[simp] theorem totalExponentialChart_apply (p q : LogModel) :
    totalExponentialChart p q = totalExponentialCoordinates q := rfl

@[simp] theorem totalExponentialChart_coe (p : LogModel) :
    (totalExponentialChart p : LogModel → CoordinateSpace 3) =
      totalExponentialCoordinates := rfl

theorem totalExponentialChart_mem_source (p : LogModel) :
    p ∈ (totalExponentialChart p).source :=
  totalExponentialCoordinates_holomorphic.contDiffAt.mem_toOpenPartialHomeomorph_source
    (totalExponentialCoordinates_hasFDerivAt p) (by simp)

theorem totalExponentialChart_holomorphic (p : LogModel) :
    ContDiffOn ℂ ω (totalExponentialChart p) (totalExponentialChart p).source :=
  totalExponentialCoordinates_holomorphic.contDiffOn

theorem totalExponentialChart_symm_holomorphic (p : LogModel) :
    ContDiffOn ℂ ω (totalExponentialChart p).symm (totalExponentialChart p).target := by
  intro w hw
  exact ((totalExponentialChart p).contDiffAt_symm hw
    (totalExponentialCoordinates_hasFDerivAt ((totalExponentialChart p).symm w))
    totalExponentialCoordinates_holomorphic.contDiffAt).contDiffWithinAt

theorem totalExponentialCoordinates_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω totalExponentialCoordinates := by
  intro p
  refine ⟨{
    toPartialEquiv := (totalExponentialChart p).toPartialEquiv
    open_source := (totalExponentialChart p).open_source
    open_target := (totalExponentialChart p).open_target
    contMDiffOn_toFun := (totalExponentialChart_holomorphic p).contMDiffOn
    contMDiffOn_invFun := (totalExponentialChart_symm_holomorphic p).contMDiffOn },
    totalExponentialChart_mem_source p, ?_⟩
  intro q _
  rfl

end Wikipedia.HopfProblem.CuspUniformization
