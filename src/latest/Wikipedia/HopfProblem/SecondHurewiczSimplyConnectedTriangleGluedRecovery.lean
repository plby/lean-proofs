import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleFaces
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivisionRecovery

/-!
# Native class recovery after coherent triangle normalization

The terminal glued square has exactly the original lower-positive and
upper-negative based triangles. The explicit diagonal-subdivision homotopy
therefore identifies its native second homotopy class with their difference.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Exact native second-homotopy class of the glued based triangles. -/
theorem basedTrianglesLoop_class (τ υ : BasedTriangle x) :
    Additive.ofMul (⟦basedTrianglesLoop τ υ⟧ : π_ 2 X x) =
      basedTriangleClass τ - basedTriangleClass υ := by
  have hd : ∀ t : I, basedTrianglesLoop τ υ ![t, t] = x := by
    intro t
    have he : (![t, t] : Fin 2 → I) = fun _ => t := by
      funext i
      fin_cases i <;> rfl
    rw [he, basedTrianglesLoop_diagonal]
  have hl : subdivisionLowerBasedTriangle (basedTrianglesLoop τ υ) hd = τ :=
    Subtype.ext (basedTrianglesLoop_lower τ υ)
  have hu : subdivisionUpperNegativeBasedTriangle (basedTrianglesLoop τ υ) hd = υ :=
    Subtype.ext (basedTrianglesLoop_upper τ υ)
  simpa only [hl, hu] using subdivision_basedTriangleClass_sub (basedTrianglesLoop τ υ) hd

/-- A coherent normalization of the two original square triangles recovers
the original native homotopy class, with the actual singular-chain signs. -/
theorem basedTriangleClass_of_homotopies {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s))
    (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) = basedTriangleClass τ - basedTriangleClass υ := by
  have h : (⟦p⟧ : π_ 2 X x) = ⟦basedTrianglesLoop τ υ⟧ :=
    Quotient.sound ⟨basedTrianglesHomotopy τ υ L U hdiag hL hU⟩
  exact (congrArg Additive.ofMul h).trans (basedTrianglesLoop_class τ υ)

/-- The same native recovery theorem with the actual face-map hypotheses
produced by coherent simplexwise homotopies. -/
theorem basedTriangleClass_of_face_homotopies {p : GenLoop (Fin 2) X x}
    (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag : ∀ r s, L (r, simplexFace 1 1 s) = U (r, simplexFace 1 1 s))
    (hL : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, L (r, simplexFace 1 i s) = x)
    (hU : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, U (r, simplexFace 1 i s) = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) = basedTriangleClass τ - basedTriangleClass υ := by
  have h : (⟦p⟧ : π_ 2 X x) = ⟦basedTrianglesLoop τ υ⟧ :=
    Quotient.sound ⟨basedTrianglesHomotopy_of_faces τ υ L U hdiag hL hU⟩
  exact (congrArg Additive.ofMul h).trans (basedTrianglesLoop_class τ υ)

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
