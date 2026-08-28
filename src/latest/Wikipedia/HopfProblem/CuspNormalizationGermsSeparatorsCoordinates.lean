import Wikipedia.HopfProblem.CuspNormalizationGermsRestriction
import Wikipedia.HopfProblem.CuspNormalizationGermsBasicDomain

/-! # Actual coordinate germs separate the coordinate branches

The ambient coordinate germ restricts to zero on its corresponding
coordinate plane and to a nonzero analytic germ on every other plane.
Nonvanishing is proved using the analytic identity principle and evaluation
of the actual coordinate function, not imposed on abstract branch rings.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open ToricCharts ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

/-- The germ of the actual ambient coordinate function at the origin. -/
def coordinateGerm (j : Fin 3) : AmbientGerm :=
  ofAnalytic (fun z : E₃ => z j) (contDiff_apply ℂ ℂ j).contDiffAt.analyticAt

/-- Coordinate restriction is represented by the literal coordinate-plane
inclusion used in the geometric normalization charts. -/
theorem toBranch_coordinateGerm (i j : Fin 3) :
    toBranch i (coordinateGerm j) =
      ofAnalytic (fun z : E₂ => insertZero i z j)
        ((contDiff_apply ℂ ℂ j).comp (insertZero_holomorphic i)).contDiffAt.analyticAt := by
  rw [coordinateGerm, toBranch_ofAnalytic]
  rfl

@[simp] theorem toBranch_coordinateGerm_self (j : Fin 3) :
    toBranch j (coordinateGerm j) = 0 := by
  rw [toBranch_coordinateGerm]
  apply (ofAnalytic_eq_zero_iff _ _).mpr
  exact Eventually.of_forall fun z => insertZero_at j z

/-- Every other coordinate remains a nonzero germ on a branch.  If it
vanished near the origin, analyticity would make the actual function
vanish everywhere, contradicting its value at the all-ones vector. -/
theorem toBranch_coordinateGerm_ne_zero {i j : Fin 3} (hji : j ≠ i) :
    toBranch i (coordinateGerm j) ≠ 0 := by
  intro hzero
  rw [toBranch_coordinateGerm] at hzero
  have hnear := (ofAnalytic_eq_zero_iff _ _).mp hzero
  have ha : AnalyticOnNhd ℂ (fun z : E₂ => insertZero i z j) univ :=
    fun _ _ =>
      ((contDiff_apply ℂ ℂ j).comp (insertZero_holomorphic i)).contDiffAt.analyticAt
  have hall : (fun z : E₂ => insertZero i z j) = 0 :=
    ha.eq_of_eventuallyEq analyticOnNhd_const hnear
  obtain heq | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · exact hji heq
  have hvalue := congrFun hall (fun _ : Fin 2 => (1 : ℂ))
  have h10 : (1 : ℂ) = 0 := by
    simpa only [insertZero, Fin.insertNth_apply_succAbove, Pi.zero_apply] using hvalue
  exact one_ne_zero h10

end Wikipedia.HopfProblem.CuspNormalization.Germs
