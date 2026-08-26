import ErdosProblems.Erdos73.BrickHorizontalPaths

/-! Fixed local three-arm routes with the same prescribed centre for either vertical direction. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

def wallTileEast : Fin 5 → Fin 9 × Fin 12 :=
  ![(4, 6), (4, 7), (4, 8), (4, 9), (4, 10)]

def wallTileWestUp : Fin 5 → Fin 9 × Fin 12 :=
  ![(4, 6), (4, 5), (4, 4), (4, 3), (4, 2)]

def wallTileNorth : Fin 9 → Fin 9 × Fin 12 :=
  ![(4, 6), (3, 6), (3, 7), (2, 7), (2, 6), (1, 6), (1, 7), (0, 7), (0, 6)]

def wallTileWestDown : Fin 7 → Fin 9 × Fin 12 :=
  ![(4, 6), (3, 6), (3, 5), (3, 4), (3, 3), (3, 2), (4, 2)]

def wallTileSouth : Fin 11 → Fin 9 × Fin 12 :=
  ![(4, 6), (4, 5), (5, 5), (5, 4), (6, 4), (6, 5),
    (7, 5), (7, 4), (8, 4), (8, 5), (8, 6)]

def tilePathOfPositions {n : ℕ} (f : Fin (n + 1) → Fin 9 × Fin 12)
    (hinterior : ∀ i, 0 < (f i).2.val ∧ (f i).2.val + 1 < 12)
    (hf : Function.Injective f)
    (hstep : ∀ i : Fin n, (rawBrickWall 6 9).Adj (f i.castSucc) (f i.succ)) :
    GraphPath (elementaryWall 6 9) := by
  let g (i : Fin (n + 1)) : ElementaryWallVertex 6 9 :=
    ⟨f i, rawBrickWall_degree_ge_two_of_interior (c := 6) (r := 9)
      (f i) (hinterior i).1 (hinterior i).2⟩
  have hg : Function.Injective g := fun _ _ he => hf (congrArg Subtype.val he)
  refine GraphPath.ofSequence g hg ?_
  intro i hi
  exact hstep ⟨i, by omega⟩

theorem tilePathOfPositions_source_val {n : ℕ} (f : Fin (n + 1) → Fin 9 × Fin 12)
    (hinterior hf hstep) : (tilePathOfPositions f hinterior hf hstep).source.val = f 0 := by
  let g (i : Fin (n + 1)) : ElementaryWallVertex 6 9 :=
    ⟨f i, rawBrickWall_degree_ge_two_of_interior (c := 6) (r := 9)
      (f i) (hinterior i).1 (hinterior i).2⟩
  exact congrArg Subtype.val (List.head_ofFn (f := g) (by simp))

theorem tilePathOfPositions_target_val {n : ℕ} (f : Fin (n + 1) → Fin 9 × Fin 12)
    (hinterior hf hstep) :
    (tilePathOfPositions f hinterior hf hstep).target.val = f (Fin.last n) := by
  let g (i : Fin (n + 1)) : ElementaryWallVertex 6 9 :=
    ⟨f i, rawBrickWall_degree_ge_two_of_interior (c := 6) (r := 9)
      (f i) (hinterior i).1 (hinterior i).2⟩
  exact congrArg Subtype.val (List.getLast_ofFn_succ g)

theorem tilePathOfPositions_mem {n : ℕ} (f : Fin (n + 1) → Fin 9 × Fin 12)
    (hinterior hf hstep) (w : ElementaryWallVertex 6 9) :
    w ∈ (tilePathOfPositions f hinterior hf hstep).vertexSet ↔ ∃ i, f i = w.val := by
  let g (i : Fin (n + 1)) : ElementaryWallVertex 6 9 :=
    ⟨f i, rawBrickWall_degree_ge_two_of_interior (c := 6) (r := 9)
      (f i) (hinterior i).1 (hinterior i).2⟩
  simp only [tilePathOfPositions, GraphPath.ofSequence, GraphPath.vertexSet,
    Walk.support_ofSupport, List.mem_toFinset]
  change w ∈ List.ofFn g ↔ ∃ i, f i = w.val
  constructor
  · intro hw
    obtain ⟨i, hi⟩ := (@List.mem_ofFn (ElementaryWallVertex 6 9) (n + 1) g w).mp hw
    exact ⟨i, congrArg Subtype.val hi⟩
  · rintro ⟨i, hi⟩
    exact (@List.mem_ofFn (ElementaryWallVertex 6 9) (n + 1) g w).mpr ⟨i, Subtype.ext hi⟩

theorem tilePathOfPositions_intersection {n m : ℕ}
    (f : Fin (n + 1) → Fin 9 × Fin 12) (g : Fin (m + 1) → Fin 9 × Fin 12)
    (hfi hff hfs hgi hgf hgs)
    (hcross : ∀ i j, f i = g j → i = 0 ∧ j = 0)
    {w : ElementaryWallVertex 6 9}
    (hwf : w ∈ (tilePathOfPositions f hfi hff hfs).vertexSet)
    (hwg : w ∈ (tilePathOfPositions g hgi hgf hgs).vertexSet) :
    w = (tilePathOfPositions f hfi hff hfs).source := by
  obtain ⟨i, hi⟩ := (tilePathOfPositions_mem f hfi hff hfs w).mp hwf
  obtain ⟨j, hj⟩ := (tilePathOfPositions_mem g hgi hgf hgs w).mp hwg
  obtain ⟨rfl, _⟩ := hcross i j (hi.trans hj.symm)
  exact Subtype.ext (hi.symm.trans (tilePathOfPositions_source_val f hfi hff hfs).symm)

def wallTileEastPath : GraphPath (elementaryWall 6 9) :=
  tilePathOfPositions wallTileEast (by decide) (by decide)
    (by simp only [rawBrickWall, pathGraph_adj]; decide)

def wallTileWestUpPath : GraphPath (elementaryWall 6 9) :=
  tilePathOfPositions wallTileWestUp (by decide) (by decide)
    (by simp only [rawBrickWall, pathGraph_adj]; decide)

def wallTileNorthPath : GraphPath (elementaryWall 6 9) :=
  tilePathOfPositions wallTileNorth (by decide) (by decide)
    (by simp only [rawBrickWall, pathGraph_adj]; decide)

def wallTileWestDownPath : GraphPath (elementaryWall 6 9) :=
  tilePathOfPositions wallTileWestDown (by decide) (by decide)
    (by simp only [rawBrickWall, pathGraph_adj]; decide)

def wallTileSouthPath : GraphPath (elementaryWall 6 9) :=
  tilePathOfPositions wallTileSouth (by decide) (by decide)
    (by simp only [rawBrickWall, pathGraph_adj]; decide)

theorem wallTileWestUp_east_intersection : ∀ i j,
    wallTileWestUp i = wallTileEast j → i = 0 ∧ j = 0 := by decide

theorem wallTileWestUp_north_intersection : ∀ i j,
    wallTileWestUp i = wallTileNorth j → i = 0 ∧ j = 0 := by decide

theorem wallTileEast_north_intersection : ∀ i j,
    wallTileEast i = wallTileNorth j → i = 0 ∧ j = 0 := by decide

theorem wallTileWestDown_east_intersection : ∀ i j,
    wallTileWestDown i = wallTileEast j → i = 0 ∧ j = 0 := by decide

theorem wallTileWestDown_south_intersection : ∀ i j,
    wallTileWestDown i = wallTileSouth j → i = 0 ∧ j = 0 := by decide

theorem wallTileEast_south_intersection : ∀ i j,
    wallTileEast i = wallTileSouth j → i = 0 ∧ j = 0 := by decide

end
end Erdos73
