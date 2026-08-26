import ErdosProblems.Erdos73.UCombGeometry
import ErdosProblems.Erdos73.BrickRightHooks

/-! Boundary teeth followed by an interior zigzag rail, with no extra bottom tooth. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {c r : ℕ}

def brickBoundaryArm (leftSide : Bool) (a b j : ℕ) : Finset (ElementaryWallVertex c r) :=
  univ.filter (fun w =>
    (w.val.1.val = a ∧ (if leftSide then w.val.2.val ≤ 2 * j + 1 else 2 * j ≤ w.val.2.val)) ∨
    (a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧ 2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * j + 1))

theorem mem_brickBoundaryArm {side : Bool} {a b j : ℕ} {w : ElementaryWallVertex c r} :
    w ∈ brickBoundaryArm side a b j ↔
      (w.val.1.val = a ∧ (if side then w.val.2.val ≤ 2 * j + 1 else 2 * j ≤ w.val.2.val)) ∨
      (a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧ 2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * j + 1) := by
  simp only [brickBoundaryArm, mem_filter, mem_univ, true_and]

theorem exists_brick_boundary_arm (u : ElementaryWallVertex c r) (side : Bool)
    (b j : ℕ) (hub : u.val.1.val ≤ b) (hb : b < r) (hj : 0 < j) (hjc : j + 1 < c)
    (hcol : if side then u.val.2.val ≤ 2 * j + 1 else 2 * j ≤ u.val.2.val) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target.val.1.val = b ∧
      2 * j ≤ P.target.val.2.val ∧ P.target.val.2.val ≤ 2 * j + 1 ∧
      P.vertexSet ⊆ brickBoundaryArm side u.val.1.val b j := by
  obtain ⟨C, hCs, hCt, hC⟩ := exists_brick_column_path u.val.1.val b j hub hb hj hjc
  have hCsc := (hC C.source (by
    simpa only [GraphPath.vertexSet, List.mem_toFinset] using C.source_mem_vertexSet)).2.2
  have hCtc := (hC C.target (by
    simpa only [GraphPath.vertexSet, List.mem_toFinset] using C.target_mem_vertexSet)).2.2
  have hex : ∃ Q : GraphPath (elementaryWall c r), Q.source = u ∧ Q.target = C.source ∧
      ∀ w ∈ Q.vertexSet, w.val.1.val = u.val.1.val ∧
        (if side then w.val.2.val ≤ 2 * j + 1 else 2 * j ≤ w.val.2.val) := by
    cases side
    · obtain ⟨Q, hs, ht, hQ⟩ := exists_brick_horizontal_path_bounded u C.source
        (Fin.ext hCs.symm) (2 * j) (2 * c)
        ⟨hcol, u.val.2.isLt.le⟩ ⟨hCsc.1, C.source.val.2.isLt.le⟩
      refine ⟨Q, hs, ht, fun w hw => ?_⟩
      have hh := hQ w (by simpa only [GraphPath.vertexSet, List.mem_toFinset] using hw)
      exact ⟨congrArg Fin.val hh.1, hh.2.1⟩
    · obtain ⟨Q, hs, ht, hQ⟩ := exists_brick_horizontal_path_bounded u C.source
        (Fin.ext hCs.symm) 0 (2 * j + 1)
        ⟨Nat.zero_le _, hcol⟩ ⟨Nat.zero_le _, hCsc.2⟩
      refine ⟨Q, hs, ht, fun w hw => ?_⟩
      have hh := hQ w (by simpa only [GraphPath.vertexSet, List.mem_toFinset] using hw)
      exact ⟨congrArg Fin.val hh.1, hh.2.2⟩
  obtain ⟨Q, hs, ht, hQ⟩ := hex
  let P := Q.appendWithEqToPath C ht
  refine ⟨P, hs, hCt, hCtc.1, hCtc.2, ?_⟩
  intro w hw
  rcases mem_union.mp (Q.appendWithEqToPath_vertexSet_subset C ht hw) with hw | hw
  · exact mem_brickBoundaryArm.mpr (Or.inl (hQ w hw))
  · exact mem_brickBoundaryArm.mpr (Or.inr
      (hC w (by simpa only [GraphPath.vertexSet, List.mem_toFinset] using hw)))

theorem exists_brick_bottom_u_path (u v : ElementaryWallVertex c r) (b j : ℕ)
    (hu : u.val.1.val ≤ b) (hv : v.val.1.val ≤ b) (hb : b < r)
    (hj : 0 < j) (hjc : 2 * j + 3 ≤ c)
    (huc : u.val.2.val ≤ 2 * j + 1) (hvc : 2 * c - (2 * j + 2) ≤ v.val.2.val) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target = v ∧
      ∀ w ∈ P.vertexSet,
        w ∈ brickBoundaryArm true u.val.1.val b j ∨
        w ∈ brickBoundaryArm false v.val.1.val b (c - j - 1) ∨
        (w.val.1.val = b ∧ 2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * c - (2 * j + 1)) := by
  have heq : 2 * (c - j - 1) = 2 * c - (2 * j + 2) := by omega
  have heq' : 2 * (c - j - 1) + 1 = 2 * c - (2 * j + 1) := by omega
  obtain ⟨P, hPs, hPt, hPc, hPc', hP⟩ :=
    exists_brick_boundary_arm u true b j hu hb hj (by omega) huc
  obtain ⟨Q, hQs, hQt, hQc, hQc', hQ⟩ :=
    exists_brick_boundary_arm v false b (c - j - 1) hv hb (by omega) (by omega)
      (by change 2 * (c - j - 1) ≤ v.val.2.val; omega)
  obtain ⟨A, hAs, hAt, hA⟩ := exists_brick_horizontal_path_bounded P.target Q.target
    (Fin.ext (hPt.trans hQt.symm)) (2 * j) (2 * c - (2 * j + 1))
    ⟨hPc, by omega⟩ ⟨by omega, by omega⟩
  let R := P.append3WithEqToPath A Q.reverse hAs.symm hAt
  refine ⟨R, hPs, hQs, ?_⟩
  intro w hw
  rcases mem_union.mp (P.append3WithEqToPath_vertexSet_subset A Q.reverse hAs.symm hAt hw)
      with hw | hw
  · rcases mem_union.mp hw with hw | hw
    · exact Or.inl (hP hw)
    · have hh := hA w (by simpa only [GraphPath.vertexSet, List.mem_toFinset] using hw)
      exact Or.inr (Or.inr ⟨(congrArg Fin.val hh.1).trans hPt, hh.2⟩)
  · exact Or.inr (Or.inl (hQ (by simpa only [GraphPath.reverse_vertexSet] using hw)))

end
end Erdos73
