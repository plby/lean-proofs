import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSquareGeometry
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivision

/-!
# The based singular triangles of diagonal subdivision

For a square with based diagonal, its two geometric halves are actual based
singular triangles. The positively oriented parametrizations agree with the
native loops used in the diagonal-subdivision homotopy. We also retain the
original negatively oriented upper triangle from the square chain.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

/-- The positively oriented upper triangle has ordered vertices `00,11,01`. -/
def subdivisionUpperPositiveSquareTriangle : C(Simplex 2, Fin 2 → I) :=
  squareCoordinates.comp (squareAffineTriangle ![(0, 0), (1, 1), (0, 1)])

@[simp] theorem subdivisionUpperPositiveSquareTriangle_zero (s : Simplex 2) :
    (subdivisionUpperPositiveSquareTriangle s 0 : ℝ) = s 1 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_fst_coe, stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

@[simp] theorem subdivisionUpperPositiveSquareTriangle_one (s : Simplex 2) :
    (subdivisionUpperPositiveSquareTriangle s 1 : ℝ) = s 1 + s 2 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_snd_coe, stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

theorem subdivisionTriangle_coordinate_sum (s : Simplex 2) : s 0 + s 1 + s 2 = 1 := by
  have hsum := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change s 0 + (s 1 + s 2) = 1 at hsum
  linarith

variable {X : Type} [TopologicalSpace X] {x : X}

theorem subdivisionLowerSquareTriangle_based (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (s : Simplex 2)
    (hs : s ∈ triangleBoundary) : p (lowerSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle s 0 : ℝ) = 1
    rw [lowerSquareTriangle_zero]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply p.property
    refine ⟨1, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

theorem subdivisionUpperNegativeSquareTriangle_based (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (s : Simplex 2)
    (hs : s ∈ triangleBoundary) : p (upperSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle s 1 : ℝ) = 1
    rw [upperSquareTriangle_one]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply p.property
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

theorem subdivisionUpperPositiveSquareTriangle_based (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (s : Simplex 2)
    (hs : s ∈ triangleBoundary) : p (subdivisionUpperPositiveSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (subdivisionUpperPositiveSquareTriangle s 1 : ℝ) = 1
    rw [subdivisionUpperPositiveSquareTriangle_one]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply p.property
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi
  · change s 2 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]

/-- The actual lower singular triangle of a square whose diagonal is based. -/
def subdivisionLowerBasedTriangle (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp lowerSquareTriangle, subdivisionLowerSquareTriangle_based p hd⟩

/-- The actual upper singular triangle, with its negative-chain orientation. -/
def subdivisionUpperNegativeBasedTriangle (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp upperSquareTriangle, subdivisionUpperNegativeSquareTriangle_based p hd⟩

/-- The actual upper singular triangle with positive square orientation. -/
def subdivisionUpperPositiveBasedTriangle (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp subdivisionUpperPositiveSquareTriangle,
    subdivisionUpperPositiveSquareTriangle_based p hd⟩

theorem subdivisionLowerTriangleLoop_eq_basedTriangleLoop (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    subdivisionLowerTriangleLoop p hd =
      basedTriangleLoop (subdivisionLowerBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  change p ![u 0, min (u 0) (u 1)] =
    p (lowerSquareTriangle (triangleQuotient (u 0, u 1)))
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

theorem subdivisionUpperTriangleLoop_eq_basedTriangleLoop (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    subdivisionUpperTriangleLoop p hd =
      basedTriangleLoop (subdivisionUpperPositiveBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  change p ![subdivisionSubMin (u 0) (u 1), u 0] =
    p (subdivisionUpperPositiveSquareTriangle (triangleQuotient (u 0, u 1)))
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

theorem subdivisionUpperNegativeBasedTriangle_loop_apply (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (u : Fin 2 → I) :
    basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) u =
      p ![min (u 0) (u 1), u 0] := by
  change p (upperSquareTriangle (triangleQuotient (u 0, u 1))) =
    p ![min (u 0) (u 1), u 0]
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

/-- Diagonal subdivision is the sum of the two positively oriented native
based-triangle classes. -/
theorem subdivision_basedTriangleClass_sum (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) +
      basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) := by
  simpa only [subdivisionLowerTriangleLoop_eq_basedTriangleLoop,
    subdivisionUpperTriangleLoop_eq_basedTriangleLoop, basedTriangleClass] using
    subdivision_additiveClass p hd

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
