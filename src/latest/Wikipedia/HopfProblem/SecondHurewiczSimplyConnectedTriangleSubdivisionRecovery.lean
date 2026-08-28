import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivisionTriangles
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivisionOrientation

/-!
# Native class recovery with the singular square's exact signs

These formulas concern the literal lower and upper triangles occurring in
`squareChain_two_triangles`. In particular the upper triangle is retained
with its negative chain orientation, and the second homotopy class is the
difference of the two actual based-triangle classes.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] {x : X}

theorem subdivisionUpperNegativeLoop_eq_basedTriangleLoop (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    subdivisionUpperNegativeLoop p hd =
      basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  exact (subdivisionUpperNegativeBasedTriangle_loop_apply p hd u).symm

/-- The native upper-triangle sign, expressed using the original based-triangle classes. -/
theorem subdivisionUpperPositiveBasedTriangle_class_eq_neg (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) =
      -basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) := by
  unfold basedTriangleClass
  rw [← subdivisionUpperTriangleLoop_eq_basedTriangleLoop,
    ← subdivisionUpperNegativeLoop_eq_basedTriangleLoop]
  exact subdivisionUpperOrientation_additiveClass p hd

/-- The original square class is recovered from the actual two triangles,
with exactly the signs of its original singular square chain. -/
theorem subdivision_basedTriangleClass_sub (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) -
        basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) :=
  subdivision_eq_sub_of_eq_add (A := Additive (π_ 2 X x))
    (subdivision_basedTriangleClass_sum p hd)
    (subdivisionUpperPositiveBasedTriangle_class_eq_neg p hd)

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
