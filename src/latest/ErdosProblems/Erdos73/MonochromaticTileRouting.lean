import ErdosProblems.Erdos73.MonochromaticTileArms

/-! Bundle both local junction types and check their exposed ports and exact intersections. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

def wallTileArm (down : Bool) (a : Fin 3) : GraphPath (elementaryWall 6 9) :=
  if a = 0 then (if down then wallTileWestDownPath else wallTileWestUpPath)
  else if a = 1 then wallTileEastPath else (if down then wallTileSouthPath else wallTileNorthPath)

def wallTilePort (down : Bool) (a : Fin 3) : Fin 9 × Fin 12 :=
  if a = 0 then (4, 2) else if a = 1 then (4, 10) else if down then (8, 6) else (0, 6)

def wallTileArmRawSupport (down : Bool) (a : Fin 3) : Finset (Fin 9 × Fin 12) :=
  if a = 0 then (if down then univ.image wallTileWestDown else univ.image wallTileWestUp)
  else if a = 1 then univ.image wallTileEast
  else (if down then univ.image wallTileSouth else univ.image wallTileNorth)

theorem wallTileArm_source_val (down : Bool) (a : Fin 3) :
    (wallTileArm down a).source.val = (4, 6) := by
  cases down <;> fin_cases a <;>
    exact tilePathOfPositions_source_val _ (by decide) (by decide)
      (by simp only [rawBrickWall, pathGraph_adj]; decide)

theorem wallTileArm_target_val (down : Bool) (a : Fin 3) :
    (wallTileArm down a).target.val = wallTilePort down a := by
  cases down <;> fin_cases a <;>
    exact tilePathOfPositions_target_val _ (by decide) (by decide)
      (by simp only [rawBrickWall, pathGraph_adj]; decide)

def wallTileCenter : ElementaryWallVertex 6 9 := wallTileEastPath.source

theorem wallTileCenter_val : wallTileCenter.val = (4, 6) :=
  tilePathOfPositions_source_val wallTileEast (by decide) (by decide)
    (by simp only [rawBrickWall, pathGraph_adj]; decide)

theorem wallTileArm_source (down : Bool) (a : Fin 3) :
    (wallTileArm down a).source = wallTileCenter :=
  Subtype.ext ((wallTileArm_source_val down a).trans wallTileCenter_val.symm)

theorem wallTileArm_mem_raw (down : Bool) (a : Fin 3) (w : ElementaryWallVertex 6 9) :
    w ∈ (wallTileArm down a).vertexSet ↔ w.val ∈ wallTileArmRawSupport down a := by
  have hmem {n : ℕ} (f : Fin (n + 1) → Fin 9 × Fin 12) (hi hf hs) :
      w ∈ (tilePathOfPositions f hi hf hs).vertexSet ↔ w.val ∈ univ.image f := by
    rw [tilePathOfPositions_mem]
    simp only [mem_image, mem_univ, true_and]
  cases down <;> fin_cases a <;> exact hmem _ (by decide) (by decide)
    (by simp only [rawBrickWall, pathGraph_adj]; decide)

theorem wallTileArmRawSupport_intersection : ∀ down a b, a ≠ b →
    wallTileArmRawSupport down a ∩ wallTileArmRawSupport down b ⊆ {(4, 6)} := by decide

theorem wallTilePort_ne_center : ∀ down a, wallTilePort down a ≠ (4, 6) := by decide

theorem wallTilePort_not_mem_other : ∀ down a b, a ≠ b →
    wallTilePort down a ∉ wallTileArmRawSupport down b := by decide

theorem wallTileArmRawSupport_column_bounds : ∀ down a, ∀ w ∈ wallTileArmRawSupport down a,
    2 ≤ w.2.val ∧ w.2.val ≤ 10 := by decide

theorem wallTileArmRawSupport_top_bounds : ∀ down a, ∀ w ∈ wallTileArmRawSupport down a,
    w.1.val = 0 → 6 ≤ w.2.val := by decide

theorem wallTileArmRawSupport_bottom_bounds : ∀ down a, ∀ w ∈ wallTileArmRawSupport down a,
    w.1.val = 8 → w.2.val ≤ 6 := by decide

theorem wallTileArm_intersection (down : Bool) {a b : Fin 3} (hab : a ≠ b)
    {w : ElementaryWallVertex 6 9} (hwa : w ∈ (wallTileArm down a).vertexSet)
    (hwb : w ∈ (wallTileArm down b).vertexSet) : w = (wallTileArm down a).source := by
  have hh := wallTileArmRawSupport_intersection down a b hab
    (mem_inter.mpr ⟨(wallTileArm_mem_raw down a w).mp hwa, (wallTileArm_mem_raw down b w).mp hwb⟩)
  exact Subtype.ext ((mem_singleton.mp hh).trans (wallTileArm_source_val down a).symm)

theorem wallTileArm_port_not_mem_other (down : Bool) {a b : Fin 3} (hab : a ≠ b) :
    (wallTileArm down a).target ∉ (wallTileArm down b).vertexSet := by
  intro hh
  have hraw := (wallTileArm_mem_raw down b _).mp hh
  rw [wallTileArm_target_val] at hraw
  exact wallTilePort_not_mem_other down a b hab hraw

end
end Erdos73
