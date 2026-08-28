import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivisionHomotopies
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivisionWarp

/-!
# Native second-homotopy subdivision along a collapsed diagonal

A square whose diagonal is based is genuinely homotopic, relative to its
perimeter, to the concatenation of its two positively oriented triangular
parts. First a continuous vertical warp splits each slice at the diagonal;
the preceding explicit homotopies then give the prescribed PL triangle
parametrizations. The class identity uses Mathlib's original homotopy group.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

/-- The continuous vertical warp, on Mathlib's actual two-dimensional cube. -/
def subdivisionWarpMap : C(SubdivisionSquare, SubdivisionSquare) where
  toFun u := ![u 0, subdivisionWarpCoordinate (u 0, u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => subdivisionWarpCoordinate (u 0, u 1)
      exact subdivisionWarpCoordinate.continuous.comp
        (show Continuous (fun u : SubdivisionSquare => (u 0, u 1)) from
          (continuous_apply 0).prodMk (continuous_apply 1))

theorem subdivisionWarpMap_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : SubdivisionSameSide u (subdivisionWarpMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 h (by simp [subdivisionWarpMap, h])
  · exact .one 0 h (by simp [subdivisionWarpMap, h])
  · exact .zero 1 h (by simp [subdivisionWarpMap, h])
  · exact .one 1 h (by simp [subdivisionWarpMap, h])

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem subdivisionWarpMap_based (p : GenLoop (Fin 2) X x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionWarpMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionWarpMap, h])⟩

def subdivisionWarpLoop (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionWarpMap (subdivisionWarpMap_based p)

/-- The warp is joined to the identity by an actual homotopy relative to the perimeter. -/
def subdivisionWarpHomotopy (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    p.val.HomotopyRel (subdivisionWarpLoop p).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd (ContinuousMap.id _) subdivisionWarpMap
    p.property (subdivisionWarpMap_based p) subdivisionWarpMap_sides

/-- The warped square is exactly native concatenation, including its clamped
coordinates and its convention at the joining point. -/
theorem subdivisionWarpLoop_eq_transAt (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    subdivisionWarpLoop p = GenLoop.transAt (1 : Fin 2)
      (subdivisionLowerProductLoop p hd) (subdivisionUpperProductLoop p hd) := by
  apply GenLoop.ext
  intro u
  change p ![u 0, subdivisionWarpCoordinate (u 0, u 1)] =
    if (u 1 : ℝ) ≤ 1 / 2 then
      subdivisionLowerProductLoop p hd
        (Function.update u 1 (Set.projIcc 0 1 zero_le_one (2 * (u 1 : ℝ))))
    else
      subdivisionUpperProductLoop p hd
        (Function.update u 1 (Set.projIcc 0 1 zero_le_one (2 * (u 1 : ℝ) - 1)))
  split_ifs with h
  · simpa [subdivisionLowerProductLoop, subdivisionPullbackLoop,
      subdivisionLowerProductMap] using
      congrArg (fun v : I => p ![u 0, v])
        (subdivisionWarpCoordinate_of_le_half (u 0) (u 1) h)
  · simpa [subdivisionUpperProductLoop, subdivisionPullbackLoop,
      subdivisionUpperProductMap] using
      congrArg (fun v : I => p ![u 0, v])
        (subdivisionWarpCoordinate_of_half_lt (u 0) (u 1) (lt_of_not_ge h))

/-- The explicit native relative homotopy realizing diagonal subdivision. -/
theorem subdivision_homotopic (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    GenLoop.Homotopic p (GenLoop.transAt (1 : Fin 2)
      (subdivisionLowerTriangleLoop p hd) (subdivisionUpperTriangleLoop p hd)) := by
  have hw : GenLoop.Homotopic p (subdivisionWarpLoop p) := ⟨subdivisionWarpHomotopy p hd⟩
  rw [subdivisionWarpLoop_eq_transAt p hd] at hw
  apply hw.trans
  apply subdivision_transAt_homotopic
  · exact ⟨subdivisionLowerTriangleHomotopy p hd⟩
  · exact ⟨(subdivisionUpperConeHomotopy p hd).trans (subdivisionUpperTriangleHomotopy p hd)⟩

/-- Equality in Mathlib's actual second homotopy group, with both triangle orientations positive. -/
theorem subdivision_class (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    (⟦p⟧ : π_ 2 X x) =
      ((· * ·) : π_ 2 X x → π_ 2 X x → π_ 2 X x)
        ⟦subdivisionLowerTriangleLoop p hd⟧ ⟦subdivisionUpperTriangleLoop p hd⟧ := by
  have h : (⟦p⟧ : π_ 2 X x) = (⟦GenLoop.transAt (1 : Fin 2)
      (subdivisionLowerTriangleLoop p hd) (subdivisionUpperTriangleLoop p hd)⟧ : π_ 2 X x) :=
    Quotient.sound (subdivision_homotopic p hd)
  exact h.trans ((HomotopyGroup.mul_spec (i := (1 : Fin 2))
    (p := subdivisionUpperTriangleLoop p hd)
    (q := subdivisionLowerTriangleLoop p hd)).symm.trans (mul_comm _ _))

/-- The same subdivision law in the additive notation used by the triangle-chain construction. -/
theorem subdivision_additiveClass (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      ((· + ·) : Additive (π_ 2 X x) → Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionLowerTriangleLoop p hd⟧ : π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivision_class p hd)

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
