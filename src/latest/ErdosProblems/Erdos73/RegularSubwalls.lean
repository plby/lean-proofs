import ErdosProblems.Erdos73.BrickWall

/-! Even-coordinate translations give ordinary copies of regular brick subwalls. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph

def rawBrickWallCopyOfOffsets {c r C R : ℕ} (a b : ℕ)
    (hr : 2 * a + r ≤ R) (hc : b + c ≤ C) : (rawBrickWall c r).Copy (rawBrickWall C R) where
  toHom := {
    toFun := fun x => (⟨2 * a + x.1.val, by have hx := x.1.isLt; omega⟩,
      ⟨2 * b + x.2.val, by have hx := x.2.isLt; omega⟩)
    map_rel' := by
      intro x y hxy
      rcases hxy with ⟨hrow, hadj⟩ | ⟨hcol, hup | hdown⟩
      · refine Or.inl ⟨?_, pathGraph_adj.mpr ?_⟩
        · exact Fin.ext (congrArg (fun z : Fin r => 2 * a + z.val) hrow)
        · have hp := pathGraph_adj.mp hadj
          change (2 * b + x.2.val + 1 = 2 * b + y.2.val ∨
            2 * b + y.2.val + 1 = 2 * b + x.2.val)
          omega
      · refine Or.inr ⟨Fin.ext (congrArg (fun z : Fin (2 * c) => 2 * b + z.val) hcol),
          Or.inl ?_⟩
        change 2 * a + x.1.val + 1 = 2 * a + y.1.val ∧
          (2 * b + x.2.val + (2 * a + x.1.val)) % 2 = 1
        omega
      · refine Or.inr ⟨Fin.ext (congrArg (fun z : Fin (2 * c) => 2 * b + z.val) hcol),
          Or.inr ?_⟩
        change 2 * a + y.1.val + 1 = 2 * a + x.1.val ∧
          (2 * b + y.2.val + (2 * a + y.1.val)) % 2 = 1
        omega }
  injective' := by
    intro x y he
    have hrow := congrArg (fun z : Fin R × Fin (2 * C) => z.1.val) he
    have hcol := congrArg (fun z : Fin R × Fin (2 * C) => z.2.val) he
    apply Prod.ext <;> apply Fin.ext
    · change 2 * a + x.1.val = 2 * a + y.1.val at hrow
      omega
    · change 2 * b + x.2.val = 2 * b + y.2.val at hcol
      omega

def elementaryWallCopyOfOffsets {c r C R : ℕ} (a b : ℕ)
    (hr : 2 * a + r ≤ R) (hc : b + c ≤ C) :
    (elementaryWall c r).Copy (elementaryWall C R) where
  toHom := {
    toFun := fun x => ⟨rawBrickWallCopyOfOffsets a b hr hc x.val,
      x.property.trans ((rawBrickWallCopyOfOffsets a b hr hc).degree_le x.val)⟩
    map_rel' := fun hxy => (rawBrickWallCopyOfOffsets a b hr hc).toHom.map_adj hxy }
  injective' := by
    intro x y he
    apply Subtype.ext
    exact (rawBrickWallCopyOfOffsets a b hr hc).injective (congrArg Subtype.val he)

end
end Erdos73
