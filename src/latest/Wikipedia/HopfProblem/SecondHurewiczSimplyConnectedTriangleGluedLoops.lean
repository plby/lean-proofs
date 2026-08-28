import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleGluing
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleHomology

/-!
# Gluing two terminal based triangles into a native square

These constructions let simplexwise normalization end in a genuine native
square, without asking for that square or its compatibility as an assumption.
The original lower-positive and upper-negative singular maps are retained.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

private theorem basedTriangles_diagonal (τ υ : BasedTriangle x) (s : Simplex 2)
    (hs : s 1 = 0) : τ.val s = υ.val s :=
  (τ.property s ⟨1, hs⟩).trans (υ.property s ⟨1, hs⟩).symm

/-- The native square obtained from the positive lower and negative upper
based triangle, with their common diagonal collapsed to the base point. -/
def basedTrianglesLoop (τ υ : BasedTriangle x) : GenLoop (Fin 2) X x :=
  ⟨(gluedTriangleHomotopyMap (τ.val.comp ContinuousMap.snd)
    (υ.val.comp ContinuousMap.snd) (fun _ => basedTriangles_diagonal τ υ)).comp
      ⟨fun t => ((0 : I), t), by fun_prop⟩, by
        intro t ht
        exact gluedTriangleHomotopyMap_boundary _ _ (fun _ => basedTriangles_diagonal τ υ) x
          (fun _ s hs => τ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩)))
          (fun _ s hs => υ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩)))
          0 t ht⟩

@[simp] theorem basedTrianglesLoop_apply (τ υ : BasedTriangle x) (t : Fin 2 → I) :
    basedTrianglesLoop τ υ t = if (t 1 : ℝ) ≤ t 0 then
      τ.val (triangleQuotient (t 0, t 1)) else
      υ.val (triangleQuotient (t 1, t 0)) := rfl

theorem basedTrianglesLoop_diagonal (τ υ : BasedTriangle x) (u : I) :
    basedTrianglesLoop τ υ (fun _ => u) = x := by
  rw [basedTrianglesLoop_apply, if_pos le_rfl]
  apply τ.property
  exact ⟨1, by simp only [triangleQuotient_one, min_self, sub_self]⟩

theorem basedTrianglesLoop_lower (τ υ : BasedTriangle x) :
    (basedTrianglesLoop τ υ).val.comp lowerSquareTriangle = τ.val := by
  apply ContinuousMap.ext
  intro s
  change basedTrianglesLoop τ υ (lowerSquareTriangle s) = τ.val s
  rw [basedTrianglesLoop_apply]
  have hle : (lowerSquareTriangle s 1 : ℝ) ≤ lowerSquareTriangle s 0 := by
    rw [lowerSquareTriangle_zero, lowerSquareTriangle_one]
    exact le_add_of_nonneg_left (stdSimplex.zero_le s 1)
  rw [if_pos hle]
  change τ.val (triangleQuotient ((lowerProductTriangle s).1,
    (lowerProductTriangle s).2)) = τ.val s
  exact congrArg τ.val (ContinuousMap.congr_fun triangleQuotient_lowerProductTriangle s)

private theorem triangleQuotient_swapped_upper (s : Simplex 2) :
    triangleQuotient (upperSquareTriangle s 1, upperSquareTriangle s 0) = s := by
  have hpair : (upperSquareTriangle s 1, upperSquareTriangle s 0) = lowerProductTriangle s := by
    apply Prod.ext <;> apply Subtype.ext
    · rw [upperSquareTriangle_one, lowerProductTriangle_fst]
    · rw [upperSquareTriangle_zero, lowerProductTriangle_snd]
  rw [hpair]
  exact ContinuousMap.congr_fun triangleQuotient_lowerProductTriangle s

theorem basedTrianglesLoop_upper (τ υ : BasedTriangle x) :
    (basedTrianglesLoop τ υ).val.comp upperSquareTriangle = υ.val := by
  apply ContinuousMap.ext
  intro s
  change basedTrianglesLoop τ υ (upperSquareTriangle s) = υ.val s
  rw [basedTrianglesLoop_apply]
  split_ifs with h
  · have hs : s 1 = 0 := by
      rw [upperSquareTriangle_zero, upperSquareTriangle_one] at h
      exact le_antisymm (by linarith) (stdSimplex.zero_le s 1)
    have he : upperSquareTriangle s 0 = upperSquareTriangle s 1 := by
      apply Subtype.ext
      rw [upperSquareTriangle_zero, upperSquareTriangle_one, hs, zero_add]
    have hq : triangleQuotient (upperSquareTriangle s 0, upperSquareTriangle s 1) = s := by
      simpa only [he] using triangleQuotient_swapped_upper s
    rw [hq]
    exact basedTriangles_diagonal τ υ s hs
  · rw [triangleQuotient_swapped_upper]

/-- The glued native square retains the literal signed triangle chain. -/
theorem squareChain_basedTrianglesLoop (τ υ : BasedTriangle x) :
    squareChain (basedTrianglesLoop τ υ) =
      simplexChain X 2 τ.val - simplexChain X 2 υ.val := by
  rw [squareChain_two_triangles, basedTrianglesLoop_lower, basedTrianglesLoop_upper]

theorem squareCycle_basedTrianglesLoop (τ υ : BasedTriangle x) :
    squareCycle (basedTrianglesLoop τ υ) = basedTriangleCycle τ - basedTriangleCycle υ := by
  apply Subtype.ext
  change squareChain (basedTrianglesLoop τ υ) =
    (simplexChain X 2 τ.val - simplexChain X 2 (ContinuousMap.const (Simplex 2) x)) -
    (simplexChain X 2 υ.val - simplexChain X 2 (ContinuousMap.const (Simplex 2) x))
  rw [squareChain_basedTrianglesLoop]
  abel

/-- The Hurewicz class of the glued square is the difference of the
two corrected actual singular-triangle classes. -/
theorem hurewiczMap_basedTrianglesLoop (τ υ : BasedTriangle x) :
    hurewiczMap x (Additive.ofMul (⟦basedTrianglesLoop τ υ⟧ : π_ 2 X x)) =
      ModuleHomology.cycleClass (singularComplex X) 2 (basedTriangleCycle τ) -
      ModuleHomology.cycleClass (singularComplex X) 2 (basedTriangleCycle υ) := by
  change ModuleHomology.cycleClass (singularComplex X) 2
    (squareCycle (basedTrianglesLoop τ υ)) = _
  rw [squareCycle_basedTrianglesLoop, map_sub]

/-- The two terminal triangle homotopies produce both the terminal native
square and a homotopy to it relative to the original square perimeter. -/
def basedTrianglesHomotopy {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s))
    (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    p.val.HomotopyRel (basedTrianglesLoop τ υ).val (Cube.boundary (Fin 2)) :=
  gluedTriangleHomotopy
    (L.cast rfl (basedTrianglesLoop_lower τ υ).symm)
    (U.cast rfl (basedTrianglesLoop_upper τ υ).symm) hdiag hL hU

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
