import ErdosProblems.Erdos73.MonochromaticTileRouting
import ErdosProblems.Erdos73.RegularSubwalls
import ErdosProblems.Erdos73.PackingCopy

/-! Spaced arrays of fixed-centre junction tiles, with exact coordinate and separation bounds. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

structure BrickTileArray (c r C R : ℕ) where
  row : Fin r → ℕ
  column : Fin (2 * c) → ℕ
  row_strictMono : StrictMono row
  column_strictMono : StrictMono column
  row_bound : ∀ i, 12 * row i + 9 ≤ R
  column_bound : ∀ j, 8 * column j + 6 ≤ C

namespace BrickTileArray

variable {c r C R : ℕ} (A : BrickTileArray c r C R)

def tileCopy (i : Fin r) (j : Fin (2 * c)) :
    (elementaryWall 6 9).Copy (elementaryWall C R) :=
  elementaryWallCopyOfOffsets (6 * A.row i) (8 * A.column j)
    (by have hh := A.row_bound i; omega) (A.column_bound j)

theorem tileCopy_row (i : Fin r) (j : Fin (2 * c)) (w : ElementaryWallVertex 6 9) :
    ((A.tileCopy i j) w).val.1.val = 12 * A.row i + w.val.1.val := by
  change 2 * (6 * A.row i) + w.val.1.val = 12 * A.row i + w.val.1.val
  omega

theorem tileCopy_column (i : Fin r) (j : Fin (2 * c)) (w : ElementaryWallVertex 6 9) :
    ((A.tileCopy i j) w).val.2.val = 16 * A.column j + w.val.2.val := by
  change 2 * (8 * A.column j) + w.val.2.val = 16 * A.column j + w.val.2.val
  omega

def point (z : Fin r × Fin (2 * c)) : ElementaryWallVertex C R :=
  A.tileCopy z.1 z.2 wallTileCenter

theorem point_row (z : Fin r × Fin (2 * c)) :
    (A.point z).val.1.val = 12 * A.row z.1 + 4 := by
  rw [point, A.tileCopy_row, wallTileCenter_val]
  rfl

theorem point_column (z : Fin r × Fin (2 * c)) :
    (A.point z).val.2.val = 16 * A.column z.2 + 6 := by
  rw [point, A.tileCopy_column, wallTileCenter_val]
  rfl

theorem point_injective : Function.Injective A.point := by
  intro x y hxy
  have hr := congrArg (fun w : ElementaryWallVertex C R => w.val.1.val) hxy
  have hc := congrArg (fun w : ElementaryWallVertex C R => w.val.2.val) hxy
  rw [A.point_row, A.point_row] at hr
  rw [A.point_column, A.point_column] at hc
  exact Prod.ext (A.row_strictMono.injective (by omega))
    (A.column_strictMono.injective (by omega))

def center (w : ElementaryWallVertex c r) : ElementaryWallVertex C R := A.point w.val

theorem center_injective : Function.Injective A.center :=
  A.point_injective.comp Subtype.val_injective

def arm (w : ElementaryWallVertex c r) (a : Fin 3) : GraphPath (elementaryWall C R) :=
  (wallTileArm (decide ((w.val.2.val + w.val.1.val) % 2 = 1)) a).mapCopy
    (A.tileCopy w.val.1 w.val.2)

theorem arm_source (w : ElementaryWallVertex c r) (a : Fin 3) :
    (A.arm w a).source = A.center w := by
  change A.tileCopy w.val.1 w.val.2 (wallTileArm _ a).source = A.center w
  rw [wallTileArm_source]
  rfl

theorem arm_target_row (w : ElementaryWallVertex c r) (a : Fin 3) :
    (A.arm w a).target.val.1.val = 12 * A.row w.val.1 +
      (wallTilePort (decide ((w.val.2.val + w.val.1.val) % 2 = 1)) a).1.val := by
  change (A.tileCopy w.val.1 w.val.2 (wallTileArm _ a).target).val.1.val = _
  rw [A.tileCopy_row, wallTileArm_target_val]

theorem arm_target_column (w : ElementaryWallVertex c r) (a : Fin 3) :
    (A.arm w a).target.val.2.val = 16 * A.column w.val.2 +
      (wallTilePort (decide ((w.val.2.val + w.val.1.val) % 2 = 1)) a).2.val := by
  change (A.tileCopy w.val.1 w.val.2 (wallTileArm _ a).target).val.2.val = _
  rw [A.tileCopy_column, wallTileArm_target_val]

theorem arm_zero_target_coordinates (w : ElementaryWallVertex c r) :
    (A.arm w 0).target.val.1.val = 12 * A.row w.val.1 + 4 ∧
      (A.arm w 0).target.val.2.val = 16 * A.column w.val.2 + 2 := by
  exact ⟨by simpa [wallTilePort] using A.arm_target_row w 0,
    by simpa [wallTilePort] using A.arm_target_column w 0⟩

theorem arm_one_target_coordinates (w : ElementaryWallVertex c r) :
    (A.arm w 1).target.val.1.val = 12 * A.row w.val.1 + 4 ∧
      (A.arm w 1).target.val.2.val = 16 * A.column w.val.2 + 10 := by
  exact ⟨by simpa [wallTilePort] using A.arm_target_row w 1,
    by simpa [wallTilePort] using A.arm_target_column w 1⟩

theorem arm_two_target_coordinates (w : ElementaryWallVertex c r) :
    (A.arm w 2).target.val.1.val = 12 * A.row w.val.1 +
      (if (w.val.2.val + w.val.1.val) % 2 = 1 then 8 else 0) ∧
      (A.arm w 2).target.val.2.val = 16 * A.column w.val.2 + 6 := by
  constructor
  · have hh := A.arm_target_row w 2
    simpa [wallTilePort, apply_ite] using hh
  · have hh := A.arm_target_column w 2
    simpa [wallTilePort, apply_ite] using hh

theorem arm_coordinates (w : ElementaryWallVertex c r) (a : Fin 3)
    {v : ElementaryWallVertex C R} (hv : v ∈ (A.arm w a).vertexSet) :
    ∃ z ∈ wallTileArmRawSupport (decide ((w.val.2.val + w.val.1.val) % 2 = 1)) a,
      v.val.1.val = 12 * A.row w.val.1 + z.1.val ∧
      v.val.2.val = 16 * A.column w.val.2 + z.2.val := by
  obtain ⟨u, hu, rfl⟩ := (GraphPath.mem_mapCopy_vertexSet _ _ v).mp hv
  exact ⟨u.val, (wallTileArm_mem_raw _ _ u).mp hu,
    A.tileCopy_row _ _ u, A.tileCopy_column _ _ u⟩

theorem arm_box (w : ElementaryWallVertex c r) (a : Fin 3)
    {v : ElementaryWallVertex C R} (hv : v ∈ (A.arm w a).vertexSet) :
    12 * A.row w.val.1 ≤ v.val.1.val ∧ v.val.1.val ≤ 12 * A.row w.val.1 + 8 ∧
      16 * A.column w.val.2 + 2 ≤ v.val.2.val ∧ v.val.2.val ≤ 16 * A.column w.val.2 + 10 := by
  obtain ⟨z, hz, hr, hc⟩ := A.arm_coordinates w a hv
  have hcol := wallTileArmRawSupport_column_bounds _ _ z hz
  have hrow := z.1.isLt
  omega

theorem arms_disjoint_of_ne {u w : ElementaryWallVertex c r} (huw : u ≠ w) (a b : Fin 3) :
    Disjoint (A.arm u a).vertexSet (A.arm w b).vertexSet := by
  apply Finset.disjoint_left.mpr
  intro v hvu hvw
  have hu := A.arm_box u a hvu
  have hw := A.arm_box w b hvw
  apply huw
  apply Subtype.ext
  exact Prod.ext (A.row_strictMono.injective (by omega))
    (A.column_strictMono.injective (by omega))

theorem arms_intersection (w : ElementaryWallVertex c r) {a b : Fin 3} (hab : a ≠ b)
    {v : ElementaryWallVertex C R} (hva : v ∈ (A.arm w a).vertexSet)
    (hvb : v ∈ (A.arm w b).vertexSet) : v = A.center w := by
  obtain ⟨u, hu, rfl⟩ := (GraphPath.mem_mapCopy_vertexSet _ _ v).mp hva
  obtain ⟨z, hz, he⟩ := (GraphPath.mem_mapCopy_vertexSet _ _ _).mp hvb
  have hzu : z = u := (A.tileCopy w.val.1 w.val.2).injective he
  subst z
  have hh := (wallTileArm_intersection _ hab hu hz).trans (wallTileArm_source _ _)
  exact congrArg (A.tileCopy w.val.1 w.val.2) hh

theorem arm_target_ne_center (w : ElementaryWallVertex c r) (a : Fin 3) :
    (A.arm w a).target ≠ A.center w := by
  intro h
  change A.tileCopy w.val.1 w.val.2 (wallTileArm _ a).target =
    A.tileCopy w.val.1 w.val.2 wallTileCenter at h
  have hh := congrArg Subtype.val ((A.tileCopy w.val.1 w.val.2).injective h)
  rw [wallTileArm_target_val, wallTileCenter_val] at hh
  exact wallTilePort_ne_center _ _ hh

theorem arm_target_not_mem_other (w : ElementaryWallVertex c r) {a b : Fin 3} (hab : a ≠ b) :
    (A.arm w a).target ∉ (A.arm w b).vertexSet := by
  intro hh
  exact A.arm_target_ne_center w a
    (A.arms_intersection w hab (A.arm w a).target_mem_vertexSet hh)

end BrickTileArray
end
end Erdos73
