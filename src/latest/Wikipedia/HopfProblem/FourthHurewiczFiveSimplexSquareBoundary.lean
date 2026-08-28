import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexCubicalBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexSquareBoundaryGeometry

/-!
# The native boundary relation of a square

The two routes through the four edges are connected by a literal homotopy
relative to their endpoints.  Evaluation therefore gives the alternating
boundary relation, independently of any homology comparison.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

theorem squareFacet_zero (ε : I) (u : Fin 1 → I) :
    cubeFacet 1 0 ε u = ![ε, u 0] := by
  funext i
  fin_cases i
  · exact cubeFacet_apply_self 1 0 ε u
  · change cubeFacet 1 0 ε u ((0 : Fin 2).succAbove 0) = u 0
    exact cubeFacet_apply_succAbove 1 0 ε u 0

theorem squareFacet_one (ε : I) (u : Fin 1 → I) :
    cubeFacet 1 1 ε u = ![u 0, ε] := by
  funext i
  fin_cases i
  · change cubeFacet 1 1 ε u ((1 : Fin 2).succAbove 0) = u 0
    exact cubeFacet_apply_succAbove 1 1 ε u 0
  · exact cubeFacet_apply_self 1 1 ε u

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The bottom-right edge route has exactly the native concatenation parameter. -/
theorem squareLowerRoute_transAt_apply (F : BasedCubicalCell 2 x) (u : Fin 1 → I) :
    GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0) u =
      F.val (squareLowerRoute u) := by
  change (if (u 0 : ℝ) ≤ 1 / 2 then
    F.val (cubeFacet 1 1 0
      (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))))) else
    F.val (cubeFacet 1 0 1
      (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))))) = _
  by_cases hu : (u 0 : ℝ) ≤ 1 / 2
  · rw [if_pos hu, squareLowerRoute_of_le u hu]
    simp only [squareFacet_one, Function.update_self]
  · rw [if_neg hu, squareLowerRoute_of_not_le u hu]
    simp only [squareFacet_zero, Function.update_self]

/-- The left-top edge route has exactly the native concatenation parameter. -/
theorem squareUpperRoute_transAt_apply (F : BasedCubicalCell 2 x) (u : Fin 1 → I) :
    GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1) u =
      F.val (squareUpperRoute u) := by
  change (if (u 0 : ℝ) ≤ 1 / 2 then
    F.val (cubeFacet 1 0 0
      (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))))) else
    F.val (cubeFacet 1 1 1
      (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))))) = _
  by_cases hu : (u 0 : ℝ) ≤ 1 / 2
  · rw [if_pos hu, squareUpperRoute_of_le u hu]
    simp only [squareFacet_zero, Function.update_self]
  · rw [if_neg hu, squareUpperRoute_of_not_le u hu]
    simp only [squareFacet_one, Function.update_self]

/-- Interpolation across the given square is an actual native relative homotopy. -/
def squareCubicalFacesHomotopy (F : BasedCubicalCell 2 x) :
    (GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0)).val.HomotopyRel
      (GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1)).val
      (Cube.boundary (Fin 1)) where
  toFun z := F.val (squareRoutesBlend z)
  continuous_toFun := F.val.continuous.comp squareRoutesBlend.continuous
  map_zero_left u := by
    rw [squareRoutesBlend_zero]
    exact (squareLowerRoute_transAt_apply F u).symm
  map_one_left u := by
    rw [squareRoutesBlend_one]
    exact (squareUpperRoute_transAt_apply F u).symm
  prop' t u hu := by
    change F.val (squareRoutesBlend (t, u)) =
      GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0) u
    refine Eq.trans (b := x) ?_
      ((GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0)).property u hu).symm
    obtain ⟨i, hi⟩ := hu
    have hi0 : u 0 = 0 ∨ u 0 = 1 := by simpa only [Fin.fin_one_eq_zero] using hi
    rcases hi0 with hi0 | hi0
    · exact (congrArg F.val (squareRoutesBlend_endpoint_zero t u hi0)).trans
        (F.property (fun _ => 0) 0 1 (by decide) (Or.inl rfl) (Or.inl rfl))
    · exact (congrArg F.val (squareRoutesBlend_endpoint_one t u hi0)).trans
        (F.property (fun _ => 1) 0 1 (by decide) (Or.inr rfl) (Or.inr rfl))

theorem squareCubicalFaces_homotopic (F : BasedCubicalCell 2 x) :
    GenLoop.Homotopic
      (GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0))
      (GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1)) :=
  ⟨squareCubicalFacesHomotopy F⟩

variable {A : Type*} [AddCommGroup A]

/-- The alternating boundary value of an actual square vanishes. -/
theorem cubicalBoundaryValue_square (E : CubicalEvaluator 1 x A)
    (F : BasedCubicalCell 2 x) : cubicalBoundaryValue E F = 0 := by
  have h := E.map_homotopic (squareCubicalFaces_homotopic F)
  rw [E.map_transAt, E.map_transAt] at h
  unfold cubicalBoundaryValue
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ,
    Nat.zero_add, pow_zero, pow_one, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg]
  change (E (cubicalUpperFace F 0) - E (cubicalLowerFace F 0)) -
    (E (cubicalUpperFace F 1) - E (cubicalLowerFace F 1)) = 0
  apply sub_eq_zero.mpr
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using h

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
