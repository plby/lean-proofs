import Mathlib.Data.Set.Image
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! # Pulling back an overlap in an injective orbit -/

open Set Function

namespace Puzzling139335.CentralRotation.FirstOverlap

/-- If a set misses every positive iterate of itself under an injective map,
then all its iterated images are pairwise disjoint. -/
theorem pairwise_disjoint_iterate_images {X : Type*} {F : X → X}
    (hF : Injective F) {A : Set X}
    (hfirst : ∀ n : ℕ, Disjoint A (F^[n + 1] '' A)) :
    Pairwise fun i j : ℕ => Disjoint (F^[i] '' A) (F^[j] '' A) := by
  have hordered (i j : ℕ) (hij : i < j) :
      Disjoint (F^[i] '' A) (F^[j] '' A) := by
    have hji : j = i + ((j - i - 1) + 1) := by omega
    rw [hji, Function.iterate_add, image_comp]
    exact (disjoint_image_iff (hF.iterate i)).2 (hfirst (j - i - 1))
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hordered i j hlt
  · exact (hordered j i hgt).symm

/-- The same pullback argument indexed from the first image: once the first
image misses every later image, all positive images are pairwise disjoint. -/
theorem pairwise_disjoint_positive_images {X : Type*} {F : X → X}
    (hF : Injective F) {A : Set X}
    (hfirst : ∀ n : ℕ, Disjoint (F '' A) (F^[n + 2] '' A)) :
    Pairwise fun i j : ℕ =>
      Disjoint (F^[i + 1] '' A) (F^[j + 1] '' A) := by
  have hzero : ∀ n : ℕ, Disjoint (F '' A) (F^[n + 1] '' (F '' A)) := by
    intro n
    simpa only [Function.iterate_succ, image_comp] using hfirst n
  have hall := pairwise_disjoint_iterate_images hF hzero
  simpa only [Function.iterate_succ, image_comp] using hall

end Puzzling139335.CentralRotation.FirstOverlap
