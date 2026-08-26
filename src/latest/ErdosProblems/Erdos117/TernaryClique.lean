import ErdosProblems.Erdos117.Symplectic
import Mathlib.Data.Matrix.Basic

/-!
# The rank-six ternary clique

These are the thirteen vectors from Lemma 4.4 of the attached writeup. Their
nonzero pairings are checked by Lean's kernel, without native computation or
changes to the default computational limits.
-/

namespace Erdos117

/-- Three hyperbolic planes over the field with three elements. -/
def ternaryForm : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3) where
  toFun x :=
    { toFun := fun y => x 0 * y 1 - x 1 * y 0 + x 2 * y 3 - x 3 * y 2 +
        x 4 * y 5 - x 5 * y 4
      map_add' := by intros; simp only [Pi.add_apply]; ring
      map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change (x 0 + y 0) * z 1 - (x 1 + y 1) * z 0 + (x 2 + y 2) * z 3 -
      (x 3 + y 3) * z 2 + (x 4 + y 4) * z 5 - (x 5 + y 5) * z 4 =
      (x 0 * z 1 - x 1 * z 0 + x 2 * z 3 - x 3 * z 2 + x 4 * z 5 - x 5 * z 4) +
      (y 0 * z 1 - y 1 * z 0 + y 2 * z 3 - y 3 * z 2 + y 4 * z 5 - y 5 * z 4)
    ring
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    change (a * x 0) * y 1 - (a * x 1) * y 0 + (a * x 2) * y 3 - (a * x 3) * y 2 +
      (a * x 4) * y 5 - (a * x 5) * y 4 =
      a * (x 0 * y 1 - x 1 * y 0 + x 2 * y 3 - x 3 * y 2 + x 4 * y 5 - x 5 * y 4)
    ring

theorem ternaryForm_isAlt : ternaryForm.IsAlt := by
  intro x
  change x 0 * x 1 - x 1 * x 0 + x 2 * x 3 - x 3 * x 2 +
    x 4 * x 5 - x 5 * x 4 = 0
  ring

theorem ternaryForm_nondegenerate : ternaryForm.Nondegenerate := by
  apply ternaryForm_isAlt.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  funext i
  fin_cases i
  · simpa [ternaryForm] using hx ![0, 1, 0, 0, 0, 0]
  · simpa [ternaryForm] using hx ![1, 0, 0, 0, 0, 0]
  · simpa [ternaryForm] using hx ![0, 0, 0, 1, 0, 0]
  · simpa [ternaryForm] using hx ![0, 0, 1, 0, 0, 0]
  · simpa [ternaryForm] using hx ![0, 0, 0, 0, 0, 1]
  · simpa [ternaryForm] using hx ![0, 0, 0, 0, 1, 0]

theorem ternaryForm_rank : Module.finrank (ZMod 3) ternaryForm.range = 6 := by
  have h := ternaryForm.finrank_range_add_finrank_ker
  rw [ternaryForm_nondegenerate.ker_eq_bot] at h
  simpa using h

def ternaryClique : Fin 13 → Fin 6 → ZMod 3 :=
  ![![1, 2, 0, 2, 1, 1], ![0, 1, 1, 0, 0, 2], ![0, 1, 0, 1, 0, 0],
    ![0, 1, 1, 2, 2, 1], ![1, 2, 1, 0, 2, 0], ![1, 1, 0, 1, 2, 2],
    ![1, 0, 0, 1, 2, 0], ![1, 0, 1, 1, 2, 1], ![1, 1, 1, 0, 0, 1],
    ![1, 2, 0, 0, 2, 1], ![1, 0, 0, 1, 1, 1], ![1, 0, 1, 1, 1, 1],
    ![1, 2, 0, 1, 1, 0]]

theorem ternaryClique_pairwise :
    ∀ i j : Fin 13, i ≠ j → ternaryForm (ternaryClique i) (ternaryClique j) ≠ 0 := by
  intro i
  fin_cases i <;> decide

theorem ternaryClique_injective : Function.Injective ternaryClique := by
  intro i j h
  by_contra hij
  exact ternaryClique_pairwise i j hij (h ▸ ternaryForm_isAlt (ternaryClique j))

theorem exists_ternary_rank_six_clique :
    ∃ s : Finset (Fin 6 → ZMod 3), s.card = 13 ∧
      (s : Set (Fin 6 → ZMod 3)).Pairwise (fun x y => ternaryForm x y ≠ 0) := by
  classical
  refine ⟨Finset.univ.image ternaryClique, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ternaryClique_injective]
    simp
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact ternaryClique_pairwise i j (fun h => hxy (congrArg ternaryClique h))

end Erdos117
