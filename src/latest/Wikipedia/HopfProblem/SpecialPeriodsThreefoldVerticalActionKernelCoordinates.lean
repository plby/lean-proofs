import Wikipedia.HopfProblem.SpecialPeriodsExistence
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularElliptic
import Wikipedia.HopfProblem.EllipticFlatTorus
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Constant integer coordinates of a common special period

A fixed complex vector lying in every regular fibre's period lattice has
continuous coordinates in the fixed discrete standard lattice.  The actual
regular triangle domain is path connected, so those integer coordinates are
independent of the base point.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalActionKernel

/-- Integer coordinates for the actual real period equivalence are the
literal integer linear combination of the complex period columns. -/
theorem periodEquiv_integer_coordinates (z : ℍ) (v : Lattice) :
    specialPeriodMap.periodEquiv z (Elliptic.realCast v) =
      (specialPeriodMap.point z).val.matrix *ᵥ (fun i => (v i : ℂ)) := by
  rw [specialPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;>
    simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Elliptic.realCast]

private theorem continuous_inverse_period_coordinates
    {S : Type*} [TopologicalSpace S] (P : HolomorphicPeriodMap ℂ ℍ)
    (q : S → ℍ) (hq : Continuous q) (w : ComplexPlane₂) :
    Continuous (fun z : S => (P.periodEquiv (q z)).symm w) := by
  have hc : Continuous (fun z : S => (q z, w)) := hq.prodMk continuous_const
  simpa only [Function.comp_def] using P.continuous_periodEquiv_symm.comp hc

/-- A common period of the actual regular fibres is represented by a single
integer vector.  Connectedness and continuity come from the constructed
regular domain and period family, not from additional hypotheses. -/
theorem exists_common_integer_period (w : ComplexPlane₂)
    (h : ∀ z : TriangleRegularPoint, w ∈ (specialPeriodMap.point z.val).lattice) :
    ∃ v : Lattice, ∀ z : TriangleRegularPoint,
      (specialPeriodMap.point z.val).val.matrix *ᵥ (fun i => (v i : ℂ)) = w := by
  have hmem (z : TriangleRegularPoint) :
      (specialPeriodMap.periodEquiv z.val).symm w ∈ standardLattice := by
    have hz := h z
    rw [← specialPeriodMap.periodEquiv_map_lattice z.val, Submodule.mem_map] at hz
    obtain ⟨x, hx, hxw⟩ := hz
    change specialPeriodMap.periodEquiv z.val x = w at hxw
    rw [← hxw, LinearEquiv.symm_apply_apply]
    exact hx
  let coordinates : TriangleRegularPoint → standardLattice :=
    fun z => ⟨(specialPeriodMap.periodEquiv z.val).symm w, hmem z⟩
  have hreal : Continuous (fun z : TriangleRegularPoint =>
      (specialPeriodMap.periodEquiv z.val).symm w) :=
    continuous_inverse_period_coordinates specialPeriodMap
      (fun z : TriangleRegularPoint => z.val) continuous_subtype_val w
  have hcontinuous : Continuous coordinates := by
    exact hreal.subtype_mk hmem
  have hlocal : IsLocallyConstant coordinates :=
    (IsLocallyConstant.iff_continuous coordinates).mpr hcontinuous
  obtain ⟨x, hx⟩ := hlocal.exists_eq_const
  obtain ⟨v, hv⟩ := (Elliptic.standardLattice_mem_iff (x : RealPlane₄)).mp x.property
  refine ⟨v, fun z => ?_⟩
  have he : (specialPeriodMap.periodEquiv z.val).symm w = Elliptic.realCast v := by
    have hc := congrArg Subtype.val (congrFun hx z)
    change (specialPeriodMap.periodEquiv z.val).symm w = (x : RealPlane₄) at hc
    exact hc.trans hv
  calc
    (specialPeriodMap.point z.val).val.matrix *ᵥ (fun i => (v i : ℂ)) =
        specialPeriodMap.periodEquiv z.val (Elliptic.realCast v) :=
      (periodEquiv_integer_coordinates z.val v).symm
    _ = specialPeriodMap.periodEquiv z.val
        ((specialPeriodMap.periodEquiv z.val).symm w) :=
      congrArg (specialPeriodMap.periodEquiv z.val) he.symm
    _ = w := (specialPeriodMap.periodEquiv z.val).apply_symm_apply w

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalActionKernel
