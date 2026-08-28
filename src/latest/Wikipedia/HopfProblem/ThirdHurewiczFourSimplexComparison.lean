import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexBoundary
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeBasic

/-!
# The actual native third-homotopy comparison of the two cube fillings

The two labeled cube maps have a common pair of zero barycentric coordinates
on each boundary facet. Convex interpolation is therefore a based homotopy
after composing with the original four-simplex. The single coordinate
reflection supplies the negative sign in the native homotopy group.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The first actual native generalized loop represented by the filling. -/
def fourSimplexLoopA (τ : BasedFourSimplex x) : GenLoop (Fin 3) X x :=
  ⟨τ.val.comp fourSimplexFillA, fun u hu => τ.property _ (fourSimplexFillA_boundary u hu)⟩

/-- The second filling uses the reflected vertex labeling, before reflection. -/
def fourSimplexLoopB (τ : BasedFourSimplex x) : GenLoop (Fin 3) X x :=
  ⟨τ.val.comp fourSimplexFillB, fun u hu => τ.property _ (fourSimplexFillB_boundary u hu)⟩

@[simp] theorem fourSimplexLoopA_apply (τ : BasedFourSimplex x) (u : Fin 3 → I) :
    fourSimplexLoopA τ u = τ.val (fourSimplexFillA u) := rfl

@[simp] theorem fourSimplexLoopB_apply (τ : BasedFourSimplex x) (u : Fin 3 → I) :
    fourSimplexLoopB τ u = τ.val (fourSimplexFillB u) := rfl

theorem fourSimplexLoopA_internal (τ : BasedFourSimplex x)
    (u : Fin 3 → I) (i j : Fin 3) (hij : i ≠ j) (hu : u i = u j) :
    fourSimplexLoopA τ u = x := τ.property _ (fourSimplexFillA_internal u i j hij hu)

theorem fourSimplexLoopB_internal (τ : BasedFourSimplex x)
    (u : Fin 3 → I) (i j : Fin 3) (hij : i ≠ j) (hu : u i = u j) :
    fourSimplexLoopB τ u = x := τ.property _ (fourSimplexFillB_internal u i j hij hu)

theorem fourSimplexReflectFirst_eq_update (u : Fin 3 → I) :
    fourSimplexReflectFirst u = Function.update u 0 (σ (u 0)) := by
  funext i
  fin_cases i <;> simp

/-- The convex homotopy respects the entire original cube boundary. -/
def fourSimplexFillingsHomotopy (τ : BasedFourSimplex x) :
    (fourSimplexLoopA τ).val.HomotopyRel (GenLoop.symmAt 0 (fourSimplexLoopB τ)).val
      (Cube.boundary (Fin 3)) where
  toFun p := τ.val (tetrahedronSimplexBlend p.1
    (fourSimplexFillA p.2) (fourSimplexFillB (fourSimplexReflectFirst p.2)))
  continuous_toFun := τ.val.continuous.comp
    (tetrahedronSimplexBlendMap fourSimplexFillA
      (fourSimplexFillB.comp fourSimplexReflectFirst)).continuous
  map_zero_left u := by
    change τ.val (tetrahedronSimplexBlend 0 _ _) = τ.val (fourSimplexFillA u)
    rw [tetrahedronSimplexBlend_zero]
  map_one_left u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) =
      τ.val (fourSimplexFillB (Function.update u 0 (σ (u 0))))
    rw [tetrahedronSimplexBlend_one, fourSimplexReflectFirst_eq_update]
  prop' t u hu :=
    (τ.property _ (fourSimplexFill_blend_boundary t u hu)).trans
      ((fourSimplexLoopA τ).property u hu).symm

/-- The equality is in Mathlib's original third homotopy group. -/
theorem fourSimplexFillings_class (τ : BasedFourSimplex x) :
    (⟦fourSimplexLoopA τ⟧ : π_ 3 X x) =
      (Inv.inv : π_ 3 X x → π_ 3 X x) ⟦fourSimplexLoopB τ⟧ := by
  have h : (⟦fourSimplexLoopA τ⟧ : π_ 3 X x) =
      ⟦GenLoop.symmAt (0 : Fin 3) (fourSimplexLoopB τ)⟧ :=
    Quotient.sound (show GenLoop.Homotopic (fourSimplexLoopA τ)
      (GenLoop.symmAt 0 (fourSimplexLoopB τ)) from ⟨fourSimplexFillingsHomotopy τ⟩)
  exact h.trans (HomotopyGroup.inv_spec (i := (0 : Fin 3))).symm

/-- The oriented filling comparison in additive native `π₃`. -/
theorem fourSimplexFillings_additiveClass (τ : BasedFourSimplex x) :
    nativeCubeClass (fourSimplexLoopA τ) = -nativeCubeClass (fourSimplexLoopB τ) :=
  (nativeCubeClass_homotopic ⟨fourSimplexFillingsHomotopy τ⟩).trans
    (nativeCubeClass_symmAt 0 (fourSimplexLoopB τ))

end Wikipedia.HopfProblem.ThirdHurewicz
