import ErdosProblems.Erdos1197.TorusAverageLinearity

namespace Erdos1197

open scoped BigOperators

noncomputable section

open MeasureTheory
open UnitAddTorus
open MeasureTheory.Measure

variable {d : Type*} [Fintype d]

lemma integral_mFourier_eq_zero_of_nontrivial
    (n : d → ℤ) (H : ClosedAddSubgroup (UnitAddTorus d)) (h : H)
    (hh : UnitAddTorus.mFourier n h ≠ 1) :
    ∫ h : H, UnitAddTorus.mFourier n (h : UnitAddTorus d)
      ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) = 0 := by
  let μ : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hmul :
      ∀ x : H,
        UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) =
          UnitAddTorus.mFourier n (h : UnitAddTorus d) *
            UnitAddTorus.mFourier n (x : UnitAddTorus d) := by
    intro x
    simp [UnitAddTorus.mFourier, fourier_apply, AddCircle.toCircle_add,
      Finset.prod_mul_distrib, mul_comm]
  have htrans :
      ∫ x : H, UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) ∂μ =
        UnitAddTorus.mFourier n (h : UnitAddTorus d) *
          ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
    calc
      ∫ x : H, UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) ∂μ
          = ∫ x : H, UnitAddTorus.mFourier n (h : UnitAddTorus d) *
              UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
              apply integral_congr_ae
              filter_upwards with x
              rw [hmul x]
      _ = UnitAddTorus.mFourier n (h : UnitAddTorus d) *
            ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
            rw [integral_const_mul]
  have hself :
      ∫ x : H, UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) ∂μ =
        ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
    simpa [μ] using
      (MeasureTheory.integral_add_right_eq_self
        (μ := μ) (f := fun x : H => UnitAddTorus.mFourier n (x : UnitAddTorus d)) h)
  have hEq :
      ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ =
        UnitAddTorus.mFourier n (h : UnitAddTorus d) *
          ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ :=
    hself.symm.trans htrans
  have hzero :
      (1 - UnitAddTorus.mFourier n (h : UnitAddTorus d)) *
        ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ = 0 := by
    have hzero' :
        ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ -
          UnitAddTorus.mFourier n (h : UnitAddTorus d) *
            ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ = 0 := by
      exact sub_eq_zero.mpr hEq
    simpa [sub_mul] using hzero'
  rcases mul_eq_zero.mp hzero with hbad | hgood
  · exact False.elim <| hh <| (sub_eq_zero.mp hbad).symm
  · exact hgood



end

end Erdos1197
