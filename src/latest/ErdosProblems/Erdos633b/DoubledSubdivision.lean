import ErdosProblems.Erdos633b.PatchRefinement
import ErdosProblems.Erdos633b.CaseTwo

/-! Side permutations do not alter the geometric reference tile or an outer support. -/

namespace Erdos633b

noncomputable def quadratic_patch_permuted (R S : Triangle) (e : Equiv.Perm (Fin 3))
    (n : ℕ) (hn : 0 < n) (hs : ∀ i, S.side i = (n : ℝ) * R.side (e.symm i)) :
    Patch R S.support (n ^ 2) := by
  let R' : Triangle := R.reindex e
  have hside (i : Fin 3) : S.side i = (n : ℝ) * R'.side i := by
    rw [Triangle.side_reindex]
    exact hs i
  exact (quadratic_patch_congruent R' S n hn hside).changeTile (R.support_reindex e)

noncomputable def Patch.quadraticEnlargePermuted {R S : Triangle} {n : ℕ}
    (d : Patch R S.support n) (T : Triangle) (e : Equiv.Perm (Fin 3)) (k : ℕ) (hk : 0 < k)
    (hs : ∀ i, T.side i = (k : ℝ) * S.side (e.symm i)) : Patch R T.support (k ^ 2 * n) := by
  let S' : Triangle := S.reindex e
  have d' : Patch R S'.support n := by simpa only [S', Triangle.support_reindex] using d
  apply d'.quadraticEnlarge T k hk
  intro i
  rw [Triangle.side_reindex]
  exact hs i

end Erdos633b
