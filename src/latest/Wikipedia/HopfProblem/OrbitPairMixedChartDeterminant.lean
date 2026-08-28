import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Tactic.Ring

/-!
# Determinants in a native/chart comparison square

The native target model, the two-sheet source model and the ordered bigon
model need not be definitionally the same vector space. Fixed continuous
linear equivalences identify them. Conjugation compares determinants
without changing those models, and retains the one constant determinant
factor contributed by the fixed identifications.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.MixedChartDeterminant

variable {S R W : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def fixedCoordinates (K : S ≃L[ℝ] W) (P : S ≃L[ℝ] R) (Q : R ≃L[ℝ] W) :
    S ≃L[ℝ] S := (P.trans Q).trans K.symm

theorem fixedCoordinates_det_ne_zero (K : S ≃L[ℝ] W) (P : S ≃L[ℝ] R)
    (Q : R ≃L[ℝ] W) : (fixedCoordinates K P Q).toContinuousLinearMap.det ≠ 0 :=
  (LinearEquiv.isUnit_det' (fixedCoordinates K P Q).toLinearEquiv).ne_zero

theorem det_of_comparison_square (K : S ≃L[ℝ] W) (P : S ≃L[ℝ] R)
    (Q : R ≃L[ℝ] W) (C : W →L[ℝ] W) (M : R →L[ℝ] R) (D : S →L[ℝ] S)
    (h : K.symm.toContinuousLinearMap.comp
      (C.comp (Q.toContinuousLinearMap.comp (M.comp P.toContinuousLinearMap))) = D) :
    M.det * C.det * (fixedCoordinates K P Q).toContinuousLinearMap.det = D.det := by
  let C' : S →L[ℝ] S := K.symm.toContinuousLinearMap.comp (C.comp K.toContinuousLinearMap)
  let M' : S →L[ℝ] S := P.symm.toContinuousLinearMap.comp (M.comp P.toContinuousLinearMap)
  let F : S →L[ℝ] S := (fixedCoordinates K P Q).toContinuousLinearMap
  have hC : C'.det = C.det := LinearMap.det_conj C.toLinearMap K.symm.toLinearEquiv
  have hM : M'.det = M.det := LinearMap.det_conj M.toLinearMap P.symm.toLinearEquiv
  have hfactor : C'.comp (F.comp M') = D := by
    calc
      C'.comp (F.comp M') = K.symm.toContinuousLinearMap.comp
          (C.comp (Q.toContinuousLinearMap.comp (M.comp P.toContinuousLinearMap))) := by
        apply ContinuousLinearMap.ext
        intro x
        change K.symm (C (K (K.symm (Q (P (P.symm (M (P x)))))))) =
          K.symm (C (Q (M (P x))))
        rw [P.apply_symm_apply, K.apply_symm_apply]
      _ = D := h
  calc
    M.det * C.det * (fixedCoordinates K P Q).toContinuousLinearMap.det =
        C'.det * (F.det * M'.det) := by rw [hC, hM]; ring
    _ = (C'.comp (F.comp M')).det := by
      change C'.toLinearMap.det * (F.toLinearMap.det * M'.toLinearMap.det) =
        (C'.toLinearMap.comp (F.toLinearMap.comp M'.toLinearMap)).det
      rw [LinearMap.det_comp, LinearMap.det_comp]
    _ = D.det := congrArg (fun L : S →L[ℝ] S => L.det) hfactor

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem det_pair_comparison (K : (V × V) ≃L[ℝ] W) (P : (V × V) ≃L[ℝ] R)
    (Q : R ≃L[ℝ] W) (C : W →L[ℝ] W) (M : R →L[ℝ] R)
    (D : (V × V) →L[ℝ] (V × V)) (A B : V →L[ℝ] V)
    (h : K.symm.toContinuousLinearMap.comp
      (C.comp (Q.toContinuousLinearMap.comp (M.comp P.toContinuousLinearMap))) =
        D.comp (A.prodMap B)) :
    M.det * C.det * (fixedCoordinates K P Q).toContinuousLinearMap.det =
      D.det * A.det * B.det := by
  have hs := det_of_comparison_square K P Q C M (D.comp (A.prodMap B)) h
  have hp : (D.comp (A.prodMap B)).det = D.det * (A.det * B.det) := by
    change (D.toLinearMap.comp (A.toLinearMap.prodMap B.toLinearMap)).det = _
    rw [LinearMap.det_comp, LinearMap.det_prodMap]
  rw [hp] at hs
  exact hs.trans (mul_assoc _ _ _).symm

end Wikipedia.HopfProblem.OrbitPair.MixedChartDeterminant
