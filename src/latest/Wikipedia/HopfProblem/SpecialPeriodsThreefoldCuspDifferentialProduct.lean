import Wikipedia.HopfProblem.ToricFan
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The differential of a normal-crossing coordinate product

At the origin, a nonempty product of distinct coordinates has a surjective
differential precisely when it consists of one coordinate. With at least two
factors its differential is zero. These statements are proved from the explicit
finite-product derivative and can be transported through normal-crossing charts.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.NormalCrossingCoordinates

open ToricCharts

local notation "E₃" => CoordinateSpace 3

/-- The product of the coordinates indexed by `J`. -/
def coordinateProduct (J : Finset (Fin 3)) (w : E₃) : ℂ := ∏ j ∈ J, w j

theorem coordinateProduct_contDiff (J : Finset (Fin 3)) :
    ContDiff ℂ ω (coordinateProduct J) :=
  contDiff_prod (fun j _ => contDiff_apply ℂ ℂ j)

@[simp] theorem coordinateProduct_singleton (j : Fin 3) (w : E₃) :
    coordinateProduct {j} w = w j := by
  simp [coordinateProduct]

theorem coordinateProduct_zero {J : Finset (Fin 3)} (hJ : J.Nonempty) :
    coordinateProduct J 0 = 0 := by
  obtain ⟨j, hj⟩ := hJ
  exact Finset.prod_eq_zero_iff.mpr ⟨j, hj, rfl⟩

/-- The product rule, with each coordinate derivative the corresponding
continuous linear projection. -/
theorem coordinateProduct_hasFDerivAt (J : Finset (Fin 3)) (w : E₃) :
    HasFDerivAt (coordinateProduct J)
      (∑ j ∈ J, (∏ k ∈ J.erase j, w k) •
        (ContinuousLinearMap.proj j : E₃ →L[ℂ] ℂ)) w :=
  HasFDerivAt.finsetProd (fun j _ => hasFDerivAt_apply (𝕜 := ℂ) j w)

@[simp] theorem coordinateProduct_fderiv_singleton (j : Fin 3) :
    fderiv ℂ (coordinateProduct {j}) 0 = ContinuousLinearMap.proj j := by
  simpa only [Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty, one_smul]
    using (coordinateProduct_hasFDerivAt {j} 0).fderiv

theorem coordinateProduct_fderiv_singleton_surjective (j : Fin 3) :
    Function.Surjective (fderiv ℂ (coordinateProduct {j}) 0) := by
  rw [coordinateProduct_fderiv_singleton]
  exact fun z => ⟨fun _ => z, rfl⟩

theorem coordinateProduct_fderiv_zero_of_two_le {J : Finset (Fin 3)}
    (hJ : 2 ≤ J.card) : fderiv ℂ (coordinateProduct J) 0 = 0 := by
  rw [(coordinateProduct_hasFDerivAt J 0).fderiv]
  apply Finset.sum_eq_zero
  intro j hj
  have hne : (J.erase j).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hj]
    omega)
  obtain ⟨k, hk⟩ := hne
  have hz : (∏ k ∈ J.erase j, (0 : E₃) k) = 0 :=
    Finset.prod_eq_zero_iff.mpr ⟨k, hk, rfl⟩
  rw [hz, zero_smul]

theorem coordinateProduct_fderiv_zero_iff {J : Finset (Fin 3)} (hJ : J.Nonempty) :
    fderiv ℂ (coordinateProduct J) 0 = 0 ↔ 2 ≤ J.card := by
  constructor
  · intro hz
    by_contra hcard
    have hpos := Finset.card_pos.mpr hJ
    have hone : J.card = 1 := by omega
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hone
    have he := congrArg (fun L : E₃ →L[ℂ] ℂ => L (fun _ => 1)) hz
    have hzero : (1 : ℂ) = 0 := by
      simpa only [coordinateProduct_fderiv_singleton, ContinuousLinearMap.proj_apply,
        zero_apply] using he
    exact one_ne_zero hzero
  · exact coordinateProduct_fderiv_zero_of_two_le

theorem coordinateProduct_fderiv_surjective_iff {J : Finset (Fin 3)} (hJ : J.Nonempty) :
    Function.Surjective (fderiv ℂ (coordinateProduct J) 0) ↔ J.card = 1 := by
  constructor
  · intro hs
    by_contra hcard
    have hpos := Finset.card_pos.mpr hJ
    have htwo : 2 ≤ J.card := by omega
    obtain ⟨w, hw⟩ := hs 1
    rw [coordinateProduct_fderiv_zero_of_two_le htwo, zero_apply] at hw
    exact zero_ne_one hw
  · intro hcard
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    exact coordinateProduct_fderiv_singleton_surjective j

end Wikipedia.HopfProblem.NormalCrossingCoordinates
