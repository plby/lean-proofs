import ErdosProblems.Erdos73.BrickWall

/-! Half-turn symmetry of a brick wall of odd height, including degree-two trimming. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph

def rawBrickWallRotation (c r : ℕ) (hr : Odd r) : rawBrickWall c r ≃g rawBrickWall c r where
  toEquiv := Equiv.prodCongr Fin.revPerm Fin.revPerm
  map_rel_iff' := by
    intro x y
    change (rawBrickWall c r).Adj (x.1.rev, x.2.rev) (y.1.rev, y.2.rev) ↔
      (rawBrickWall c r).Adj x y
    simp only [rawBrickWall, Fin.rev_inj, pathGraph_adj, Fin.val_rev]
    have hxr := x.1.isLt
    have hyr := y.1.isLt
    have hxc := x.2.isLt
    have hyc := y.2.isLt
    rw [Nat.odd_iff] at hr
    omega

def brickWallRotation (c r : ℕ) (hr : Odd r) : elementaryWall c r ≃g elementaryWall c r := by
  let e := rawBrickWallRotation c r hr
  have hb : Set.BijOn e {x | 2 ≤ (rawBrickWall c r).degree x}
      {x | 2 ≤ (rawBrickWall c r).degree x} := by
    refine ⟨?_, e.injective.injOn, ?_⟩
    · intro x hx
      change 2 ≤ (rawBrickWall c r).degree (e x)
      rw [e.degree_eq]
      exact hx
    · intro x hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      change 2 ≤ (rawBrickWall c r).degree (e.symm x)
      rw [e.symm.degree_eq]
      exact hx
  exact e.induce hb

theorem brickWallRotation_val {c r : ℕ} (hr : Odd r) (w : ElementaryWallVertex c r) :
    (brickWallRotation c r hr w).val = (w.val.1.rev, w.val.2.rev) := rfl

theorem brickWallRotation_involutive {c r : ℕ} (hr : Odd r) :
    Function.Involutive (brickWallRotation c r hr) := by
  intro w
  apply Subtype.ext
  rw [brickWallRotation_val, brickWallRotation_val]
  simp only [Fin.rev_rev]

end
end Erdos73
