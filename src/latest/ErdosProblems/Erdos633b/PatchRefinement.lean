import ErdosProblems.Erdos633b.TriangularPatch

/-! Refinement and integer enlargement preserve a prescribed congruence class of pieces. -/

namespace Erdos633b.Patch

noncomputable def refine {R S T : Triangle} {n m : ℕ}
    (d : Patch S T.support n) (e : Patch R S.support m) : Patch R T.support (n * m) :=
  (d.toTiling.refine e.toTiling).toPatch

noncomputable def quadraticEnlarge {R S : Triangle} {n : ℕ} (d : Patch R S.support n)
    (T : Triangle) (k : ℕ) (hk : 0 < k) (hs : ∀ i, T.side i = (k : ℝ) * S.side i) :
    Patch R T.support (k ^ 2 * n) :=
  (quadratic_patch_congruent S T k hk hs).refine d

end Erdos633b.Patch
