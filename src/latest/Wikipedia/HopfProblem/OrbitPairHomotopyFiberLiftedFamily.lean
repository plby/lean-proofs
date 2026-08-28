import Wikipedia.HopfProblem.OrbitPairHomotopyFiberTransport

/-!
# Continuous lifted families in the actual homotopy fibre

Currying the explicit transport formula gives a continuous fibre-valued family.
Its projection is exactly the prescribed base family, its initial value is
exactly the prescribed lift, and constant based parameters stay fixed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def transport (f : C(X, Y)) (b : Y) (p : C(Z, Space f b))
    (H : C(unitInterval × Z, X)) (hzero : ∀ z, H (0, z) = projection f b (p z)) :
    C(unitInterval × Z, Space f b) := by
  let F : C(unitInterval × (unitInterval × Z), Y) :=
    ⟨fun z ↦ transportedPathValue f b p H z.2.1 z.1 z.2.2,
      continuous_transportedPathValue f b p H hzero⟩
  let paths : C(unitInterval × Z, C(unitInterval, Y)) :=
    (F.comp ⟨Prod.swap, continuous_swap⟩).curry
  exact {
    toFun z := ⟨(H z, paths z), transportedPathValue_source f b p H z.1 z.2,
      transportedPathValue_target f b p H z.1 z.2⟩
    continuous_toFun := (H.continuous.prodMk paths.continuous).subtype_mk _ }

theorem transport_projection (f : C(X, Y)) (b : Y) (p : C(Z, Space f b))
    (H : C(unitInterval × Z, X)) (hzero : ∀ z, H (0, z) = projection f b (p z)) :
    (projection f b).comp (transport f b p H hzero) = H := rfl

theorem transport_path_apply (f : C(X, Y)) (b : Y) (p : C(Z, Space f b))
    (H : C(unitInterval × Z, X)) (hzero : ∀ z, H (0, z) = projection f b (p z))
    (s t : unitInterval) (z : Z) :
    (transport f b p H hzero (s, z)).val.2 t = transportedPathValue f b p H s t z := rfl

theorem transport_initial (f : C(X, Y)) (b : Y) (p : C(Z, Space f b))
    (H : C(unitInterval × Z, X)) (hzero : ∀ z, H (0, z) = projection f b (p z)) (z : Z) :
    transport f b p H hzero (0, z) = p z := by
  apply Subtype.ext
  apply Prod.ext
  · exact hzero z
  · apply ContinuousMap.ext
    intro t
    exact transportedPathValue_initial f b p H hzero t z

theorem transport_fixed_basepoint (f : C(X, Y)) (x : X) (p : C(Z, Space f (f x)))
    (H : C(unitInterval × Z, X)) (hzero : ∀ z, H (0, z) = projection f (f x) (p z))
    (z : Z) (hp : p z = basepoint f x) (hH : ∀ t, H (t, z) = x) (s : unitInterval) :
    transport f (f x) p H hzero (s, z) = basepoint f x := by
  apply Subtype.ext
  apply Prod.ext
  · exact hH s
  · apply ContinuousMap.ext
    intro t
    change transportedPathValue f (f x) p H s t z = f x
    unfold transportedPathValue
    split_ifs
    · exact congrArg f (hH _)
    · rw [hp]
      rfl

end Wikipedia.HopfProblem.OrbitPair.HomotopyFiber
