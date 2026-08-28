import ErdosProblems.Erdos577.FirstPawTransport

/-! A finite insertion table, certified by three-vertex paths on the remaining columns. -/

namespace Erdos577.JointFirstRows

open Finset

def pathVertices : Fin 4 → Fin 3 → Fin 3 → Fin 4 :=
  ![![![1, 2, 3], ![1, 3, 2], ![2, 1, 3]],
    ![![2, 3, 0], ![0, 2, 3], ![2, 0, 3]],
    ![![3, 0, 1], ![0, 3, 1], ![0, 1, 3]],
    ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2]]]

def replacementMask : Fin 4 → Fin 16 → ℕ :=
  ![![0, 0, 0, 0, 0, 10, 0, 10, 0, 0, 5, 5, 0, 10, 5, 15],
    ![0, 0, 0, 8, 0, 10, 8, 10, 0, 2, 5, 15, 2, 10, 15, 15],
    ![0, 0, 0, 4, 0, 10, 1, 15, 0, 4, 5, 5, 1, 15, 5, 15],
    ![0, 0, 0, 12, 0, 10, 9, 15, 0, 6, 5, 15, 3, 15, 15, 15]]

def replacementPath : Fin 4 → Fin 16 → Fin 4 → Fin 3 :=
  ![![![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0]],
    ![![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 1],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 2],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 1, 0, 0],
      ![0, 0, 0, 0],
      ![0, 1, 0, 1],
      ![0, 2, 0, 0],
      ![0, 0, 0, 0],
      ![0, 2, 0, 2],
      ![0, 0, 0, 0]],
    ![![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 1, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![1, 0, 0, 0],
      ![1, 0, 1, 0],
      ![0, 0, 0, 0],
      ![0, 0, 2, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![2, 0, 0, 0],
      ![2, 0, 2, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0]],
    ![![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![0, 0, 1, 1],
      ![0, 0, 0, 0],
      ![0, 0, 0, 0],
      ![1, 0, 0, 2],
      ![1, 0, 1, 0],
      ![0, 0, 0, 0],
      ![0, 1, 2, 0],
      ![0, 0, 0, 0],
      ![0, 1, 0, 1],
      ![2, 2, 0, 0],
      ![2, 0, 2, 0],
      ![0, 2, 0, 2],
      ![0, 0, 0, 0]]]

def GoodPath (d : Fin 4) (row : Fin 16) (u : Fin 4) (t : Fin 3) : Prop :=
  let p := pathVertices u t
  ({p 0, p 1, p 2} : Finset (Fin 4)) = univ.erase u ∧ p 0 ≠ p 2 ∧
    FirstPaw.quadAdj d (Function.Embedding.refl _) (p 0) (p 1) ∧
    FirstPaw.quadAdj d (Function.Embedding.refl _) (p 1) (p 2) ∧
    row.val.testBit (p 0).val = true ∧ row.val.testBit (p 2).val = true

instance (d : Fin 4) (row : Fin 16) (u : Fin 4) (t : Fin 3) :
    Decidable (GoodPath d row u t) := inferInstanceAs (Decidable (_ ∧ _))

private theorem mask_sound_0 : ∀ row : Fin 16, ∀ u : Fin 4,
    (replacementMask 0 row).testBit u.val = true →
      GoodPath 0 row u (replacementPath 0 row u) := by
  decide +kernel

private theorem mask_sound_1 : ∀ row : Fin 16, ∀ u : Fin 4,
    (replacementMask 1 row).testBit u.val = true →
      GoodPath 1 row u (replacementPath 1 row u) := by
  decide +kernel

private theorem mask_sound_2 : ∀ row : Fin 16, ∀ u : Fin 4,
    (replacementMask 2 row).testBit u.val = true →
      GoodPath 2 row u (replacementPath 2 row u) := by
  decide +kernel

private theorem mask_sound_3 : ∀ row : Fin 16, ∀ u : Fin 4,
    (replacementMask 3 row).testBit u.val = true →
      GoodPath 3 row u (replacementPath 3 row u) := by
  decide +kernel

theorem replacement_mask_sound (d : Fin 4) (row : Fin 16) (u : Fin 4)
    (h : (replacementMask d row).testBit u.val = true) :
    GoodPath d row u (replacementPath d row u) := by
  fin_cases d
  · exact mask_sound_0 row u h
  · exact mask_sound_1 row u h
  · exact mask_sound_2 row u h
  · exact mask_sound_3 row u h

end Erdos577.JointFirstRows
