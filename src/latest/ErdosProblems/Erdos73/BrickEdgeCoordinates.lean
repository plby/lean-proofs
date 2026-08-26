import ErdosProblems.Erdos73.OrientedEdgeMaps
import ErdosProblems.Erdos73.BrickWall

/-! Coordinate keys determine unoriented brick-wall edges uniquely. -/

namespace Erdos73
noncomputable section

open SimpleGraph

theorem brickAdj_coordinates {c r : ℕ} {u v : ElementaryWallVertex c r}
    (huv : (elementaryWall c r).Adj u v) :
    (u.val.1.val = v.val.1.val ∧
      (u.val.2.val + 1 = v.val.2.val ∨ v.val.2.val + 1 = u.val.2.val)) ∨
    (u.val.2.val = v.val.2.val ∧
      (u.val.1.val + 1 = v.val.1.val ∨ v.val.1.val + 1 = u.val.1.val)) := by
  rcases huv with ⟨hr, hc⟩ | ⟨hc, hr⟩
  · exact Or.inl ⟨congrArg Fin.val hr, pathGraph_adj.mp hc⟩
  · exact Or.inr ⟨congrArg Fin.val hc, hr.imp And.left And.left⟩

def brickEdgeCode {c r : ℕ} (u v : ElementaryWallVertex c r) : ℕ × ℕ × ℕ :=
  if u.val.1.val = v.val.1.val then
    (0, u.val.1.val, min u.val.2.val v.val.2.val)
  else (1, min u.val.1.val v.val.1.val, u.val.2.val)

theorem brickEdgeCode_symm {c r : ℕ} {u v : ElementaryWallVertex c r}
    (huv : (elementaryWall c r).Adj u v) : brickEdgeCode u v = brickEdgeCode v u := by
  have hh := brickAdj_coordinates huv
  dsimp only [brickEdgeCode]
  split_ifs <;> apply Prod.ext <;> simp only [Prod.mk.injEq] <;> omega

theorem brickEdgeCode_eq_sym2 {c r : ℕ} {u v x y : ElementaryWallVertex c r}
    (huv : (elementaryWall c r).Adj u v) (hxy : (elementaryWall c r).Adj x y)
    (hcode : brickEdgeCode u v = brickEdgeCode x y) : s(u, v) = s(x, y) := by
  have hu := brickAdj_coordinates huv
  have hx := brickAdj_coordinates hxy
  have hcoords :
      (u.val.1.val = x.val.1.val ∧ u.val.2.val = x.val.2.val ∧
        v.val.1.val = y.val.1.val ∧ v.val.2.val = y.val.2.val) ∨
      (u.val.1.val = y.val.1.val ∧ u.val.2.val = y.val.2.val ∧
        v.val.1.val = x.val.1.val ∧ v.val.2.val = x.val.2.val) := by
    dsimp only [brickEdgeCode] at hcode
    split_ifs at hcode <;> simp only [Prod.mk.injEq] at hcode <;> omega
  apply Sym2.eq_iff.mpr
  rcases hcoords with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)),
      Subtype.ext (Prod.ext (Fin.ext h3) (Fin.ext h4))⟩
  · exact Or.inr ⟨Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)),
      Subtype.ext (Prod.ext (Fin.ext h3) (Fin.ext h4))⟩

theorem brickEdgeCode_injective {c r : ℕ} :
    Function.Injective (fun e : OrientedEdge (elementaryWall c r) => brickEdgeCode e.lo e.hi) := by
  intro e f he
  exact OrientedEdge.eq_of_sym2_eq (brickEdgeCode_eq_sym2 e.adj f.adj he)

theorem fin_min_val {n : ℕ} (i j : Fin n) : (min i j).val = min i.val j.val := by
  rcases le_total i j with h | h
  · rw [min_eq_left h, min_eq_left (show i.val ≤ j.val from h)]
  · rw [min_eq_right h, min_eq_right (show j.val ≤ i.val from h)]

theorem fin_max_val {n : ℕ} (i j : Fin n) : (max i j).val = max i.val j.val := by
  rcases le_total i j with h | h
  · rw [max_eq_right h, max_eq_right (show i.val ≤ j.val from h)]
  · rw [max_eq_left h, max_eq_left (show j.val ≤ i.val from h)]

end
end Erdos73
