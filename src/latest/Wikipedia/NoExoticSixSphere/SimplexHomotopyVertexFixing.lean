import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrismOperators

/-!
# Coherent simplex homotopies fix already based vertices

If a coherent family fixes the constant zero-simplex at a point, its
restriction to every original vertex with that image stays fixed. The
proof follows the actual coface maps down to the zero-dimensional case.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.SimplexHomotopyVertexFixing

variable {X : Type} [TopologicalSpace X]

theorem vertex_fixed
    (H : (n : ℕ) → C(Simplex n, X) → C(I × Simplex n, X))
    (hface : ∀ n, FaceCompatibleHomotopies n (H n) (H (n + 1)))
    (x : X) (hconst : H 0 (ContinuousMap.const (Simplex 0) x) =
      ContinuousMap.const (I × Simplex 0) x)
    (n : ℕ) (smp : C(Simplex n, X)) (i : Fin (n + 1))
    (hi : smp (stdSimplex.vertex (S := ℝ) i) = x) (t : I) :
    H n smp (t, stdSimplex.vertex i) = x := by
  induction n with
  | zero =>
    have he : smp = ContinuousMap.const (Simplex 0) x := by
      apply ContinuousMap.ext
      intro s
      rw [simplexZero_eq_vertex s]
      exact (congrArg (fun j ↦ smp (stdSimplex.vertex (S := ℝ) j))
        (Subsingleton.elim (0 : Fin 1) i)).trans hi
    rw [he, hconst]
    rfl
  | succ n ih =>
    obtain ⟨j, k, hjk⟩ := simplexVertex_exists_face n i
    have hk : (smp.comp (simplexFace n j)) (stdSimplex.vertex (S := ℝ) k) = x := by
      change smp (simplexFace n j (stdSimplex.vertex k)) = x
      rw [hjk]
      exact hi
    rw [← hjk]
    have hf := congrArg (fun F : C(I × Simplex n, X) ↦ F (t, stdSimplex.vertex k))
      (hface n smp j)
    exact hf.trans (ih (smp.comp (simplexFace n j)) k hk)

end NoExoticSixSphere.SimplexHomotopyVertexFixing
