import ErdosProblems.Erdos73.BrickWall

/-! Explicit hexagonal face copies in the elementary brick wall. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph

def brickFacePosition (i : Fin 6) : ℕ × ℕ :=
  match i.val with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (1, 2)
  | 4 => (1, 1)
  | _ => (1, 0)

theorem brickFacePosition_injective : Function.Injective brickFacePosition := by decide

theorem brickFacePosition_bounds : ∀ i, (brickFacePosition i).1 ≤ 1 ∧
    (brickFacePosition i).2 ≤ 2 := by decide

theorem brickFacePosition_covers_rectangle : ∀ a : Fin 2, ∀ b : Fin 3,
    ∃ i : Fin 6, brickFacePosition i = (a.val, b.val) := by decide

theorem brickFacePosition_adj : ∀ i j, (cycleGraph 6).Adj i j →
    ((brickFacePosition i).1 = (brickFacePosition j).1 ∧
      ((brickFacePosition i).2 + 1 = (brickFacePosition j).2 ∨
        (brickFacePosition j).2 + 1 = (brickFacePosition i).2)) ∨
    ((brickFacePosition i).2 = (brickFacePosition j).2 ∧
      (((brickFacePosition i).1 = 0 ∧ (brickFacePosition j).1 = 1) ∨
        ((brickFacePosition j).1 = 0 ∧ (brickFacePosition i).1 = 1)) ∧
      (brickFacePosition i).2 % 2 = 0) := by decide

def rawBrickFaceCopy {c r : ℕ} (a b : ℕ) (hr : a + 1 < r) (hc : b + 2 < 2 * c)
    (hpar : (b + a) % 2 = 1) : (cycleGraph 6).Copy (rawBrickWall c r) where
  toHom := {
    toFun := fun i => (⟨a + (brickFacePosition i).1, by
      have hh := (brickFacePosition_bounds i).1; omega⟩,
      ⟨b + (brickFacePosition i).2, by have hh := (brickFacePosition_bounds i).2; omega⟩)
    map_rel' := by
      intro i j hij
      rcases brickFacePosition_adj i j hij with ⟨he, ha⟩ | ⟨he, ha, hp⟩
      · exact Or.inl ⟨Fin.ext (congrArg (a + ·) he), pathGraph_adj.mpr (by
          change b + (brickFacePosition i).2 + 1 = b + (brickFacePosition j).2 ∨
            b + (brickFacePosition j).2 + 1 = b + (brickFacePosition i).2
          omega)⟩
      · refine Or.inr ⟨Fin.ext (congrArg (b + ·) he), ?_⟩
        change ((a + (brickFacePosition i).1 + 1 = a + (brickFacePosition j).1 ∧
          (b + (brickFacePosition i).2 + (a + (brickFacePosition i).1)) % 2 = 1) ∨
          (a + (brickFacePosition j).1 + 1 = a + (brickFacePosition i).1 ∧
          (b + (brickFacePosition j).2 + (a + (brickFacePosition j).1)) % 2 = 1))
        omega }
  injective' := by
    intro i j hij
    have hr' := congrArg (fun x : Fin r × Fin (2 * c) => x.1.val) hij
    have hc' := congrArg (fun x : Fin r × Fin (2 * c) => x.2.val) hij
    apply brickFacePosition_injective
    apply Prod.ext
    · change a + (brickFacePosition i).1 = a + (brickFacePosition j).1 at hr'
      omega
    · change b + (brickFacePosition i).2 = b + (brickFacePosition j).2 at hc'
      omega

def elementaryBrickFaceCopy {c r : ℕ} (a b : ℕ) (hr : a + 1 < r) (hc : b + 2 < 2 * c)
    (hpar : (b + a) % 2 = 1) : (cycleGraph 6).Copy (elementaryWall c r) where
  toHom := {
    toFun := fun i => ⟨rawBrickFaceCopy a b hr hc hpar i, by
      have hh := (rawBrickFaceCopy a b hr hc hpar).degree_le i
      simpa only [cycleGraph_degree_three_le] using hh⟩
    map_rel' := fun h => (rawBrickFaceCopy a b hr hc hpar).toHom.map_adj h }
  injective' := fun i j he => (rawBrickFaceCopy a b hr hc hpar).injective (congrArg Subtype.val he)

end
end Erdos73
