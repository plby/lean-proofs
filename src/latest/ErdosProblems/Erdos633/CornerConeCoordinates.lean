import ErdosProblems.Erdos633.LocalConeIsometry

/-!
# The two active inequalities at a triangle corner

At the first vertex the local cone is the coordinate image of the positive
quadrant. Removing its two boundary rays does not change its sector area.
-/

namespace Erdos633

open MeasureTheory

theorem Triangle.coordinateEquiv_symm_a (P : Triangle) : P.coordinateEquiv.symm P.a = 0 := by
  rw [← P.coordinateEquiv_zero, P.coordinateEquiv.symm_apply_apply]

theorem Triangle.mem_localConeAt_a (P : Triangle) (x : ℂ) :
    x ∈ P.localConeAt P.a ↔ 0 ≤ (P.coordinateEquiv.symm x).re ∧
      0 ≤ (P.coordinateEquiv.symm x).im := by
  simp [Triangle.localConeAt, Triangle.barycentric, P.coordinateEquiv_symm_a,
    Fin.forall_fin_succ]

theorem Triangle.mem_localOpenConeAt_a (P : Triangle) (x : ℂ) :
    x ∈ P.localOpenConeAt P.a ↔ 0 < (P.coordinateEquiv.symm x).re ∧
      0 < (P.coordinateEquiv.symm x).im := by
  simp [Triangle.localOpenConeAt, Triangle.barycentric, P.coordinateEquiv_symm_a,
    Fin.forall_fin_succ]

theorem Triangle.localSectorArea_eq_openConeArea (P : Triangle) (z : ℂ) :
    P.localSectorArea z =
      (volume (P.localOpenConeAt z ∩ Metric.ball z 1)).toReal := by
  unfold Triangle.localSectorArea Triangle.localSector
  apply congrArg ENNReal.toReal
  apply measure_congr
  have havoid : ∀ᵐ x ∂volume, x ∉ frontier (P.localConeAt z) := by
    exact measure_eq_zero_iff_ae_notMem.mp (P.volume_frontier_localConeAt z)
  filter_upwards [havoid] with x hx
  rw [← P.interior_localConeAt]
  apply propext
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    by_contra hn
    exact hx ⟨subset_closure h.1, hn⟩
  · intro h
    exact ⟨interior_subset h.1, h.2⟩

end Erdos633
