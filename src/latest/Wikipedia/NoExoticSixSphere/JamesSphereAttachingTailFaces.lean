import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSquare

/-!
# Contracting the original attaching map on the remaining boundary faces

When a tail block is on its cube boundary, both suspension clocks may
vary freely while remaining on the actual characteristic boundary.
Moving both clocks to zero contracts the original attaching map on
this entire union of faces. The map agrees literally with the clock-
perimeter parametrization on their overlap and fixes the zero-clock
face throughout. No sphere-generator comparison is inferred here.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

abbrev TailFaces (n : ℕ) :=
  {p : (Fin 2 → I) × Parameter n // ∃ i, p.2 i ∈ Cube.boundary (Fin n)}

theorem packedCube_tail_boundary (n : ℕ) (p : TailFaces n) :
    packedCube n p.val ∈ Cube.boundary (Fin (2 * (n + 1))) := by
  obtain ⟨i, j, hj⟩ := p.property
  refine ⟨finProdFinEquiv (i, j.succ), ?_⟩
  change JamesCellCube.block (n + 1) 2
    (JamesCellCube.pack (n + 1) 2 (fun k ↦ Fin.cons (p.val.1 k) (p.val.2 k))) i j.succ = 0 ∨
      JamesCellCube.block (n + 1) 2
        (JamesCellCube.pack (n + 1) 2 (fun k ↦ Fin.cons (p.val.1 k) (p.val.2 k))) i j.succ = 1
  simpa only [JamesCellCube.block_pack, Fin.cons_succ] using hj

def tailBoundaryMap (n : ℕ) : C(TailFaces n, CellBoundary.Boundary (n + 1)) :=
  ⟨fun p ↦ ⟨JamesCellCube.unscale (2 * (n + 1)) (packedCube n p.val),
      unscale_boundary _ _ (packedCube_tail_boundary n p)⟩,
    ((JamesCellCube.continuous_unscale _).comp
      ((packedCube n).continuous.comp continuous_subtype_val)).subtype_mk _⟩

theorem tailBoundaryMap_overlap (n : ℕ) (t : ClockBoundary) (v : Parameter n)
    (hv : ∃ i, v i ∈ Cube.boundary (Fin n)) :
    tailBoundaryMap n ⟨(t.val, v), hv⟩ = boundaryMap n (t, v) := rfl

theorem array_tailBoundaryMap (n : ℕ) (p : TailFaces n) (i : Fin 2) :
    Cell.array (n + 1) 2 (tailBoundaryMap n p).val i =
      CubicalSphereSuspension.evaluation n (p.val.1 i, SmoothCube.quotient n (p.val.2 i)) := by
  change SmoothCube.quotient (n + 1) (JamesCellCube.block (n + 1) 2
    (JamesCellCube.cube (2 * (n + 1)) (JamesCellCube.unscale (2 * (n + 1))
      (JamesCellCube.pack (n + 1) 2 (fun j ↦ Fin.cons (p.val.1 j) (p.val.2 j))))) i) = _
  rw [JamesCellCube.cube_unscale, JamesCellCube.block_pack]
  exact (CubicalSphereSuspension.evaluation_quotient n (p.val.1 i) (p.val.2 i)).symm

def tailAttaching (n : ℕ) : C(TailFaces n, Sphere (n + 1)) :=
  (CellBoundary.attaching (n + 1)).comp (tailBoundaryMap n)

theorem tailAttaching_zero_clocks (n : ℕ) (p : TailFaces n) (hp : p.val.1 = 0) :
    tailAttaching n p = spherePole (n + 1) := by
  change CellBoundary.attaching (n + 1) (tailBoundaryMap n p) = _
  rw [UnitalAttaching.attaching_eq_first, array_tailBoundaryMap, hp,
    Pi.zero_apply, CubicalSphereSuspension.evaluation_zero]
  rw [array_tailBoundaryMap, hp, Pi.zero_apply, CubicalSphereSuspension.evaluation_zero]

def contractTailClocks (n : ℕ) : C(I × TailFaces n, TailFaces n) :=
  ⟨fun u ↦ ⟨((fun i ↦ σ u.1 * u.2.val.1 i), u.2.val.2), u.2.property⟩, by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      exact (unitInterval.continuous_symm.comp continuous_fst).mul
        ((continuous_apply i).comp
          (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))
    · exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)⟩

theorem contractTailClocks_zero (n : ℕ) (p : TailFaces n) :
    contractTailClocks n (0, p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    change σ (0 : I) * p.val.1 i = p.val.1 i
    simp only [unitInterval.symm_zero, one_mul]
  · rfl

theorem contractTailClocks_one (n : ℕ) (p : TailFaces n) :
    (contractTailClocks n (1, p)).val.1 = 0 := by
  funext i
  change σ (1 : I) * p.val.1 i = 0
  simp only [unitInterval.symm_one, zero_mul]

theorem contractTailClocks_fixed (n : ℕ) (s : I) (p : TailFaces n) (hp : p.val.1 = 0) :
    contractTailClocks n (s, p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    change σ s * p.val.1 i = p.val.1 i
    rw [hp, Pi.zero_apply, mul_zero]
  · rfl

def tailNullhomotopy (n : ℕ) :
    (tailAttaching n).HomotopyRel (ContinuousMap.const _ (spherePole (n + 1)))
      {p | p.val.1 = 0} where
  toFun u := tailAttaching n (contractTailClocks n u)
  continuous_toFun := (tailAttaching n).continuous.comp (contractTailClocks n).continuous
  map_zero_left p := congrArg (tailAttaching n) (contractTailClocks_zero n p)
  map_one_left p := tailAttaching_zero_clocks n _ (contractTailClocks_one n p)
  prop' s p hp := congrArg (tailAttaching n) (contractTailClocks_fixed n s p hp)

end NoExoticSixSphere.JamesSphere.AttachingSquare
