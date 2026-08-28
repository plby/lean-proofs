import Wikipedia.NoExoticSixSphere.JamesSphereUnitalAttaching
import Wikipedia.NoExoticSixSphere.CubicalSuspensionEvaluation

/-!
# The actual attaching map on the two suspension-clock square

Keep the two original characteristic blocks, each with its leading
suspension coordinate. On the boundary of their clock square, at least
one block is the pole. Consequently the original attaching map is
exactly the other block's meridian. These are pointwise coordinate
identities, not yet a degree calculation for the boundary parametrization.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

abbrev Parameter (n : ℕ) := Fin 2 → Fin n → I
abbrev ClockBoundary := {t : Fin 2 → I // t ∈ Cube.boundary (Fin 2)}

def packedCube (n : ℕ) :
    C((Fin 2 → I) × Parameter n, Fin (2 * (n + 1)) → I) :=
  ⟨fun p ↦ JamesCellCube.pack (n + 1) 2 (fun i ↦ Fin.cons (p.1 i) (p.2 i)), by
    apply continuous_pi
    intro l
    change Continuous (fun p : (Fin 2 → I) × Parameter n ↦
      Fin.cons (α := fun _ : Fin (n + 1) ↦ I) (p.1 (finProdFinEquiv.symm l).1)
        (p.2 (finProdFinEquiv.symm l).1) (finProdFinEquiv.symm l).2)
    generalize (finProdFinEquiv.symm l).2 = j
    induction j using Fin.cases with
    | zero =>
      change Continuous (fun p : (Fin 2 → I) × Parameter n ↦ p.1 (finProdFinEquiv.symm l).1)
      exact (continuous_apply _).comp continuous_fst
    | succ j =>
      change Continuous (fun p : (Fin 2 → I) × Parameter n ↦ p.2 (finProdFinEquiv.symm l).1 j)
      exact (continuous_apply j).comp ((continuous_apply _).comp continuous_snd)⟩

theorem packedCube_boundary (n : ℕ) (t : ClockBoundary) (v : Parameter n) :
    packedCube n (t.val, v) ∈ Cube.boundary (Fin (2 * (n + 1))) := by
  obtain ⟨i, hi⟩ := t.property
  refine ⟨finProdFinEquiv (i, 0), ?_⟩
  change JamesCellCube.block (n + 1) 2
    (JamesCellCube.pack (n + 1) 2 (fun j ↦ Fin.cons (t.val j) (v j))) i 0 = 0 ∨
      JamesCellCube.block (n + 1) 2
        (JamesCellCube.pack (n + 1) 2 (fun j ↦ Fin.cons (t.val j) (v j))) i 0 = 1
  simpa only [JamesCellCube.block_pack, Fin.cons_zero] using hi

theorem unscale_boundary (m : ℕ) (u : Fin m → I) (hu : u ∈ Cube.boundary (Fin m)) :
    JamesCellCube.unscale m u ∈ sphere (0 : Fin m → ℝ) 1 := by
  apply le_antisymm (JamesCellCube.unscale_mem_closedBall m u)
  apply le_of_not_gt
  intro h
  have hn := (JamesCellCube.cube_not_boundary_iff m (JamesCellCube.unscale m u)).mpr h
  rw [JamesCellCube.cube_unscale] at hn
  exact hn hu

def boundaryMap (n : ℕ) : C(ClockBoundary × Parameter n, CellBoundary.Boundary (n + 1)) :=
  ⟨fun p ↦ ⟨JamesCellCube.unscale (2 * (n + 1)) (packedCube n (p.1.val, p.2)),
      unscale_boundary _ _ (packedCube_boundary n p.1 p.2)⟩,
    ((JamesCellCube.continuous_unscale _).comp ((packedCube n).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))).subtype_mk _⟩

theorem array_boundaryMap (n : ℕ) (t : ClockBoundary) (v : Parameter n) (i : Fin 2) :
    Cell.array (n + 1) 2 (boundaryMap n (t, v)).val i =
      CubicalSphereSuspension.evaluation n (t.val i, SmoothCube.quotient n (v i)) := by
  change SmoothCube.quotient (n + 1) (JamesCellCube.block (n + 1) 2
    (JamesCellCube.cube (2 * (n + 1)) (JamesCellCube.unscale (2 * (n + 1))
      (JamesCellCube.pack (n + 1) 2 (fun j ↦ Fin.cons (t.val j) (v j))))) i) = _
  rw [JamesCellCube.cube_unscale, JamesCellCube.block_pack]
  exact (CubicalSphereSuspension.evaluation_quotient n (t.val i) (v i)).symm

def attaching (n : ℕ) : C(ClockBoundary × Parameter n, Sphere (n + 1)) :=
  (CellBoundary.attaching (n + 1)).comp (boundaryMap n)

theorem attaching_first (n : ℕ) (t : ClockBoundary) (v : Parameter n)
    (ht : t.val 1 = 0 ∨ t.val 1 = 1) :
    attaching n (t, v) =
      CubicalSphereSuspension.evaluation n (t.val 0, SmoothCube.quotient n (v 0)) := by
  change CellBoundary.attaching (n + 1) (boundaryMap n (t, v)) = _
  rw [UnitalAttaching.attaching_eq_first, array_boundaryMap]
  rw [array_boundaryMap]
  rcases ht with ht | ht
  · rw [ht, CubicalSphereSuspension.evaluation_zero]
  · rw [ht, CubicalSphereSuspension.evaluation_one]

theorem attaching_second (n : ℕ) (t : ClockBoundary) (v : Parameter n)
    (ht : t.val 0 = 0 ∨ t.val 0 = 1) :
    attaching n (t, v) =
      CubicalSphereSuspension.evaluation n (t.val 1, SmoothCube.quotient n (v 1)) := by
  change CellBoundary.attaching (n + 1) (boundaryMap n (t, v)) = _
  rw [UnitalAttaching.attaching_eq_second, array_boundaryMap]
  rw [array_boundaryMap]
  rcases ht with ht | ht
  · rw [ht, CubicalSphereSuspension.evaluation_zero]
  · rw [ht, CubicalSphereSuspension.evaluation_one]

def corner00 : ClockBoundary := ⟨![0, 0], ⟨0, Or.inl rfl⟩⟩
def corner10 : ClockBoundary := ⟨![1, 0], ⟨0, Or.inr rfl⟩⟩
def corner11 : ClockBoundary := ⟨![1, 1], ⟨0, Or.inr rfl⟩⟩
def corner01 : ClockBoundary := ⟨![0, 1], ⟨0, Or.inl rfl⟩⟩

def bottom : Path corner00 corner10 where
  toFun t := ⟨![t, 0], ⟨1, Or.inl rfl⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_id
    · exact continuous_const
  source' := rfl
  target' := rfl

def right : Path corner10 corner11 where
  toFun t := ⟨![1, t], ⟨0, Or.inr rfl⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact continuous_id
  source' := rfl
  target' := rfl

def top : Path corner01 corner11 where
  toFun t := ⟨![t, 1], ⟨1, Or.inr rfl⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_id
    · exact continuous_const
  source' := rfl
  target' := rfl

def left : Path corner00 corner01 where
  toFun t := ⟨![0, t], ⟨0, Or.inl rfl⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact continuous_id
  source' := rfl
  target' := rfl

theorem attaching_bottom (n : ℕ) (v : Parameter n) (t : I) :
    attaching n (bottom t, v) =
      CubicalSphereSuspension.evaluation n (t, SmoothCube.quotient n (v 0)) :=
  attaching_first n (bottom t) v (Or.inl rfl)

theorem attaching_right (n : ℕ) (v : Parameter n) (t : I) :
    attaching n (right t, v) =
      CubicalSphereSuspension.evaluation n (t, SmoothCube.quotient n (v 1)) :=
  attaching_second n (right t) v (Or.inr rfl)

theorem attaching_top (n : ℕ) (v : Parameter n) (t : I) :
    attaching n (top t, v) =
      CubicalSphereSuspension.evaluation n (t, SmoothCube.quotient n (v 0)) :=
  attaching_first n (top t) v (Or.inr rfl)

theorem attaching_left (n : ℕ) (v : Parameter n) (t : I) :
    attaching n (left t, v) =
      CubicalSphereSuspension.evaluation n (t, SmoothCube.quotient n (v 1)) :=
  attaching_second n (left t) v (Or.inl rfl)

end NoExoticSixSphere.JamesSphere.AttachingSquare
