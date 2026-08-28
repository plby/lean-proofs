import Wikipedia.HopfProblem.ConifoldPolarDefs
import Wikipedia.HopfProblem.ConifoldStandardBoundaryRegularity
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Ambient regularity of the polar coordinate formulas

The coordinate maps are real smooth on the original matrix space with its
product norm and on the original Euclidean base and normal spaces.
-/

open scoped ContDiff Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

/-- The traceless Hermitian matrix depends real smoothly on the Euclidean base. -/
theorem tracelessMatrix_contDiff {n : ℕ∞ω} : ContDiff ℝ n tracelessMatrix := by
  have hc (i : Fin 3) : ContDiff ℝ n (fun b : Base => (b i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply (p := 2) (i := i))
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [tracelessMatrix] using hc 0
  · simpa [tracelessMatrix] using
      (hc 1).add ((hc 2).mul (contDiff_const (c := Complex.I)))
  · simpa [tracelessMatrix] using
      (hc 1).sub ((hc 2).mul (contDiff_const (c := Complex.I)))
  · simpa [tracelessMatrix] using (hc 0).neg

theorem tracelessMatrix_continuous : Continuous tracelessMatrix :=
  (tracelessMatrix_contDiff (n := ∞)).continuous

/-- Completing the normal coordinates to the unitary matrix is real smooth. -/
theorem unitaryMatrix_contDiff {n : ℕ∞ω} : ContDiff ℝ n unitaryMatrix := by
  have hc (i : Fin 4) : ContDiff ℝ n (fun z : Normal => (z i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply (p := 2) (i := i))
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [unitaryMatrix] using
      (hc 2).sub ((hc 3).mul (contDiff_const (c := Complex.I)))
  · simpa [unitaryMatrix] using
      (hc 0).add ((hc 1).mul (contDiff_const (c := Complex.I)))
  · simpa [unitaryMatrix] using
      (hc 0).neg.add ((hc 1).mul (contDiff_const (c := Complex.I)))
  · simpa [unitaryMatrix] using
      (hc 2).add ((hc 3).mul (contDiff_const (c := Complex.I)))

theorem unitaryMatrix_continuous : Continuous unitaryMatrix :=
  (unitaryMatrix_contDiff (n := ∞)).continuous

/-- Reading the original second column into Euclidean normal coordinates is real smooth. -/
theorem normalCoordinates_contDiff {n : ℕ∞ω} : ContDiff ℝ n normalCoordinates := by
  have hre (i j : Fin 2) :
      ContDiff ℝ n (fun M : MatrixSpace => (M i j).re) :=
    Complex.reCLM.contDiff.comp (contDiff_apply_apply ℝ ℂ i j)
  have him (i j : Fin 2) :
      ContDiff ℝ n (fun M : MatrixSpace => (M i j).im) :=
    Complex.imCLM.contDiff.comp (contDiff_apply_apply ℝ ℂ i j)
  apply (contDiff_piLp (p := 2)).mpr
  intro i
  fin_cases i
  · simpa [normalCoordinates, EuclideanSpace.equiv] using hre 0 1
  · simpa [normalCoordinates, EuclideanSpace.equiv] using him 0 1
  · simpa [normalCoordinates, EuclideanSpace.equiv] using hre 1 1
  · simpa [normalCoordinates, EuclideanSpace.equiv] using him 1 1

theorem normalCoordinates_continuous : Continuous normalCoordinates :=
  (normalCoordinates_contDiff (n := ∞)).continuous

/-- Reading the Hermitian traceless coordinates into the Euclidean base is real smooth. -/
theorem baseCoordinates_contDiff {n : ℕ∞ω} : ContDiff ℝ n baseCoordinates := by
  have hre (i j : Fin 2) :
      ContDiff ℝ n (fun M : MatrixSpace => (M i j).re) :=
    Complex.reCLM.contDiff.comp (contDiff_apply_apply ℝ ℂ i j)
  have him (i j : Fin 2) :
      ContDiff ℝ n (fun M : MatrixSpace => (M i j).im) :=
    Complex.imCLM.contDiff.comp (contDiff_apply_apply ℝ ℂ i j)
  apply (contDiff_piLp (p := 2)).mpr
  intro i
  fin_cases i
  · simpa [baseCoordinates, EuclideanSpace.equiv] using ((hre 0 0).sub (hre 1 1)).div_const 2
  · simpa [baseCoordinates, EuclideanSpace.equiv] using hre 0 1
  · simpa [baseCoordinates, EuclideanSpace.equiv] using him 0 1

theorem baseCoordinates_continuous : Continuous baseCoordinates :=
  (baseCoordinates_contDiff (n := ∞)).continuous

end Wikipedia.HopfProblem.ConifoldPolar
