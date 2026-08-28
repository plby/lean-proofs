import Wikipedia.HopfProblem.ThirdHurewiczHomotopyComposition
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexBasic

/-! # The first edge and its exact compatibility with coherent simplex families -/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.SimplexFirstEdge

def inclusion : (n : ℕ) → C(Simplex 1, Simplex (n + 1))
  | 0 => ContinuousMap.id _
  | n + 1 => (simplexFace (n + 1) (Fin.last (n + 2))).comp (inclusion n)

theorem vertex_zero (n : ℕ) :
    inclusion n (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) =
      stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change simplexFace (n + 1) (Fin.last (n + 2))
      (inclusion n (stdSimplex.vertex 0)) = _
    rw [ih, simplexFace_vertex, Fin.succAbove_last]
    rfl

theorem vertex_one (n : ℕ) :
    inclusion n (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) =
      stdSimplex.vertex (S := ℝ) (1 : Fin (n + 2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change simplexFace (n + 1) (Fin.last (n + 2))
      (inclusion n (stdSimplex.vertex 1)) = _
    rw [ih, simplexFace_vertex, Fin.succAbove_last]
    rfl

def path (n : ℕ) :
    Path (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2)))
      (stdSimplex.vertex (S := ℝ) (1 : Fin (n + 2))) :=
  (simplexPath (inclusion n)).cast (vertex_zero n).symm (vertex_one n).symm

theorem path_apply (n : ℕ) (r : I) :
    path n r = inclusion n (stdSimplexHomeomorphUnitInterval.symm r) := rfl

variable {X : Type} [TopologicalSpace X]
  (H : ∀ k, C(Simplex k, X) → C(I × Simplex k, X))
  (hf : ∀ k, FaceCompatibleHomotopies k (H k) (H (k + 1)))

include hf in
theorem endpoint_comp (n : ℕ) (smp : C(Simplex (n + 1), X)) :
    (timeSlice (H (n + 1) smp) 1).comp (inclusion n) =
      timeSlice (H 1 (smp.comp (inclusion n))) 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((timeSlice (H (n + 2) smp) 1).comp
      (simplexFace (n + 1) (Fin.last (n + 2)))).comp (inclusion n) = _
    rw [timeSlice_face (hf (n + 1)), ih]
    rfl

end NoExoticSixSphere.SimplexFirstEdge
