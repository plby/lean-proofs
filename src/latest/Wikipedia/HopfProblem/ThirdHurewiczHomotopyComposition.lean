import Wikipedia.HopfProblem.ThirdHurewiczHomotopyCompositionBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrismOperators

/-!
# Concatenation of coherent simplex-homotopy families

These families consist of actual continuous homotopies of the original
singular simplices. Concatenation runs the first family, then runs the
second family on the first endpoint. Native homotopy concatenation
preserves the exact restrictions to all original faces and preserves
literal constant-input stationarity.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X]

/-- Regard the given cylinder map, with its original-simplex bottom, as
an actual native homotopy to its endpoint. -/
def simplexFamilyHomotopy {n : ℕ}
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (h₀ : ∀ smp s, H smp (0, s) = smp s) (smp : SingularSimplex X n) :
    smp.Homotopy (timeSlice (H smp) 1) :=
  (cylinderHomotopy (H smp)).cast (by ext s; exact h₀ smp s) rfl

@[simp] theorem simplexFamilyHomotopy_toContinuousMap {n : ℕ}
    (H : SingularSimplex X n → C(I × Simplex n, X))
    (h₀ : ∀ smp s, H smp (0, s) = smp s) (smp : SingularSimplex X n) :
    (simplexFamilyHomotopy H h₀ smp).toContinuousMap = H smp := rfl

/-- Run the first genuine simplex homotopy, followed by the second one
evaluated at the first endpoint. -/
def composeSimplexHomotopies {n : ℕ}
    (H G : SingularSimplex X n → C(I × Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s)
    (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularSimplex X n) : C(I × Simplex n, X) :=
  ((simplexFamilyHomotopy H hH₀ smp).trans
    (simplexFamilyHomotopy G hG₀ (timeSlice (H smp) 1))).toContinuousMap

@[simp] theorem composeSimplexHomotopies_zero {n : ℕ}
    (H G : SingularSimplex X n → C(I × Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s)
    (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularSimplex X n) (s : Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (0, s) = smp s :=
  ContinuousMap.Homotopy.apply_zero _ s

@[simp] theorem composeSimplexHomotopies_one {n : ℕ}
    (H G : SingularSimplex X n → C(I × Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s)
    (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularSimplex X n) (s : Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (1, s) =
      G (timeSlice (H smp) 1) (1, s) :=
  ContinuousMap.Homotopy.apply_one _ s

@[simp] theorem timeSlice_composeSimplexHomotopies_zero {n : ℕ}
    (H G : SingularSimplex X n → C(I × Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s)
    (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularSimplex X n) :
    timeSlice (composeSimplexHomotopies H G hH₀ hG₀ smp) 0 = smp := by
  ext s
  exact composeSimplexHomotopies_zero H G hH₀ hG₀ smp s

@[simp] theorem timeSlice_composeSimplexHomotopies_one {n : ℕ}
    (H G : SingularSimplex X n → C(I × Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s)
    (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularSimplex X n) :
    timeSlice (composeSimplexHomotopies H G hH₀ hG₀ smp) 1 =
      timeSlice (G (timeSlice (H smp) 1)) 1 := by
  ext s
  exact composeSimplexHomotopies_one H G hH₀ hG₀ smp s

/-- Native concatenation retains literal face compatibility of the two
families in adjacent dimensions. -/
theorem composeSimplexHomotopies_face {n : ℕ}
    (H G : SingularSimplex X n → C(I × Simplex n, X))
    (H' G' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s)
    (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (hH'₀ : ∀ smp s, H' smp (0, s) = smp s)
    (hG'₀ : ∀ smp s, G' smp (0, s) = smp s)
    (hH : FaceCompatibleHomotopies n H H')
    (hG : FaceCompatibleHomotopies n G G') :
    FaceCompatibleHomotopies n
      (composeSimplexHomotopies H G hH₀ hG₀)
      (composeSimplexHomotopies H' G' hH'₀ hG'₀) := by
  intro smp i
  unfold composeSimplexHomotopies
  rw [homotopyTrans_compContinuousMap]
  apply homotopyTrans_congr
  · change (H' smp).comp ((ContinuousMap.id I).prodMap (simplexFace n i)) =
      H (smp.comp (simplexFace n i))
    exact hH smp i
  · change (G' (timeSlice (H' smp) 1)).comp
        ((ContinuousMap.id I).prodMap (simplexFace n i)) =
      G (timeSlice (H (smp.comp (simplexFace n i))) 1)
    rw [hG (timeSlice (H' smp) 1) i, timeSlice_face hH smp i 1]

/-- If both stages literally fix the constant simplex throughout their
homotopies, their concatenation does so as well. -/
theorem composeSimplexHomotopies_const {n : ℕ}
    (H G : SingularSimplex X n → C(I × Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s)
    (hG₀ : ∀ smp s, G smp (0, s) = smp s) (x : X)
    (hH : H (ContinuousMap.const (Simplex n) x) = ContinuousMap.const (I × Simplex n) x)
    (hG : G (ContinuousMap.const (Simplex n) x) = ContinuousMap.const (I × Simplex n) x) :
    composeSimplexHomotopies H G hH₀ hG₀ (ContinuousMap.const (Simplex n) x) =
      ContinuousMap.const (I × Simplex n) x := by
  have h₁ : timeSlice (H (ContinuousMap.const (Simplex n) x)) 1 =
      ContinuousMap.const (Simplex n) x := by
    rw [hH]
    rfl
  unfold composeSimplexHomotopies
  apply homotopyTrans_const
  · exact hH
  · change G (timeSlice (H (ContinuousMap.const (Simplex n) x)) 1) = _
    rw [h₁]
    exact hG

end Wikipedia.HopfProblem.ThirdHurewicz
