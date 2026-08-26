import ErdosProblems.Erdos750.MycielskiChains
import ErdosProblems.Erdos750.ColorObstruction

/-!
# Stiebitz's theorem for recursively constructed generalized Mycielski graphs

The lower bound is proved by integral signed-biclique chains. The cylinder
contraction extends the chain invariant at each step, and cyclic-resolution
exactness gives the obstruction to a coloring with too few colors.
-/

namespace Erdos750

open SimpleGraph Chains

universe u

lemma recursivelyBuilt_hasResolution : ∀ (r : ℕ) {V : Type u} (G : SimpleGraph V),
    IsRecursivelyBuiltMr r G → ∃ d, r = d + 1 ∧ HasResolution G d := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro V G hG
    cases r with
    | zero => exact hG.elim
    | succ r =>
      cases r with
      | zero => exact hG.elim
      | succ r =>
        cases r with
        | zero =>
          obtain ⟨e⟩ := hG
          exact ⟨1, rfl, hasResolution_complete_two.map e.symm.toHom⟩
        | succ r =>
          obtain ⟨W, H, s, hs, hH, ⟨e⟩⟩ := hG
          obtain ⟨d, hd, hc⟩ := ih (r + 2) (by omega) H hH
          refine ⟨d + 1, by omega, ?_⟩
          exact (hasResolution_genMyc hc (by omega)).map e.symm.toHom

/-- **Stiebitz's lower bound**, with no mathematical assumptions. -/
theorem stiebitz_lower_bound {V : Type u} (G : SimpleGraph V) (r : ℕ)
    (hG : IsRecursivelyBuiltMr r G) : (r : ℕ∞) ≤ G.chromaticNumber := by
  obtain ⟨d, rfl, hd⟩ := recursivelyBuilt_hasResolution r G hG
  by_contra h
  have hle : G.chromaticNumber ≤ (d : ℕ∞) := by
    have hlt := lt_of_not_ge h
    exact ENat.lt_natCast_add_one_iff.mp (by simpa using hlt)
  exact hasResolution_not_colorable hd le_rfl (chromaticNumber_le_iff_colorable.mp hle)

end Erdos750
