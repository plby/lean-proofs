import Wikipedia.HomotopyGroupsOfSpheres.Circle

/-!
# Circle arguments relative to cube boundaries and fixed parameters

The real universal cover gives an argument zero on the entire boundary of
a based cube of dimension at least two. A relative homotopy between constant
circle maps also lifts relative to its endpoints and its fixed parameters.
-/

noncomputable section

open scoped Topology unitInterval ContinuousMap

namespace Wikipedia.HomotopyGroupsOfSpheres

theorem exists_circle_cube_argument (d : ℕ) (p : GenLoop (Fin (d + 2)) Circle 1) :
    ∃ θ : C(Fin (d + 2) → I, ℝ),
      (∀ u, Circle.exp (θ u) = p u) ∧
      ∀ u ∈ Cube.boundary (Fin (d + 2)), θ u = 0 := by
  have hp₀ : p.val 0 = 1 := p.property 0 ⟨0, Or.inl rfl⟩
  obtain ⟨θ, ⟨hθ₀, hθ⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    p.val 0 0 (Circle.exp_zero.trans hp₀.symm)
  have hl (u : Fin (d + 2) → I) : Circle.exp (θ u) = p u := congrFun hθ u
  refine ⟨θ, hl, ?_⟩
  intro u hu
  exact (realLift_boundary d 1 p θ hl u hu).trans hθ₀

section RelativeHomotopies

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
variable {S : Set X}

def relativeCircleArgument (hS : S.Nonempty)
    (F : (ContinuousMap.const X (1 : Circle)).HomotopyRel (.const X 1) S) :
    (ContinuousMap.const X (0 : ℝ)).HomotopyRel (.const X 0) S :=
  Circle.isCoveringMap_exp.liftHomotopyRel F
    (by obtain ⟨x, hx⟩ := hS; exact ⟨x, hx, rfl⟩)
    (funext fun _ ↦ Circle.exp_zero) (funext fun _ ↦ Circle.exp_zero)

theorem relativeCircleArgument_lifts (hS : S.Nonempty)
    (F : (ContinuousMap.const X (1 : Circle)).HomotopyRel (.const X 1) S)
    (z : I × X) : Circle.exp (relativeCircleArgument hS F z) = F z := by
  exact congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts
    F.toContinuousMap (ContinuousMap.const X 0)
    (fun a ↦ (F.apply_zero a).trans Circle.exp_zero.symm)) z

end RelativeHomotopies

end Wikipedia.HomotopyGroupsOfSpheres
