import Wikipedia.HopfProblem.SixthHurewiczCube
import Wikipedia.HopfProblem.SixthHurewiczNativeMaps

/-!
# The actual sixth Hurewicz homomorphism

The genuine six-cube class descends through Mathlib's native quotient by
homotopies relative to the cube boundary. The explicit concatenation
seven-chain proves the homomorphism law for the actual native group
operation. Additive notation uses only the standard `Additive` synonym.

This construction asserts no injectivity, surjectivity, or isomorphism.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

/-- The homotopy-invariant cube class on the actual native sixth homotopy group. -/
def hurewiczFunction (x : X) : π_ 6 X x → SingularHomology X 6 :=
  Quotient.lift cubeHomologyClass (fun _ _ h => cubeHomologyClass_homotopic h)

@[simp] theorem hurewiczFunction_mk (x : X) (p : GenLoop (Fin 6) X x) :
    hurewiczFunction x ⟦p⟧ = cubeHomologyClass p := rfl

/-- The genuine sixth Hurewicz homomorphism, translating native
multiplicative `π₆` notation to addition in actual integral homology. -/
def hurewiczPi6 (x : X) : π_ 6 X x →* Multiplicative (SingularHomology X 6) where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (cubeHomologyClass_const (x := x))
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine (congrArg (fun c : π_ 6 X x => Multiplicative.ofAdd (hurewiczFunction x c))
      (HomotopyGroup.mul_spec (i := (0 : Fin 6)) (p := p) (q := q))).trans ?_
    change Multiplicative.ofAdd (cubeHomologyClass (GenLoop.transAt (0 : Fin 6) q p)) =
      Multiplicative.ofAdd (cubeHomologyClass p + cubeHomologyClass q)
    rw [cubeHomologyClass_transAt, add_comm]

@[simp] theorem hurewiczFunction_one (x : X) : hurewiczFunction x 1 = 0 :=
  congrArg Multiplicative.toAdd (hurewiczPi6 x).map_one

theorem hurewiczFunction_mul (x : X) (a b : π_ 6 X x) :
    hurewiczFunction x (a * b) = hurewiczFunction x a + hurewiczFunction x b :=
  congrArg Multiplicative.toAdd ((hurewiczPi6 x).map_mul a b)

@[simp] theorem hurewiczFunction_inv (x : X) (a : π_ 6 X x) :
    hurewiczFunction x a⁻¹ = -hurewiczFunction x a :=
  congrArg Multiplicative.toAdd ((hurewiczPi6 x).map_inv a)

/-- Integral-linear notation for the same map on the additive native group. -/
def hurewiczMap (x : X) : Additive (π_ 6 X x) →ₗ[ℤ] SingularHomology X 6 where
  toFun := (hurewiczPi6 x).toAdditiveLeft
  map_add' := (hurewiczPi6 x).toAdditiveLeft.map_add
  map_smul' n a := by
    simpa using map_intCast_smul (hurewiczPi6 x).toAdditiveLeft ℤ ℤ n a

@[simp] theorem hurewiczMap_mk (x : X) (p : GenLoop (Fin 6) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 6 X x)) = cubeHomologyClass p := rfl

/-- The defining representative uses the original generalized loop on
the fixed actual six-cube chain and the actual integral homology class map. -/
theorem hurewiczMap_representative (x : X) (p : GenLoop (Fin 6) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 6 X x)) =
      ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6 (cubeCycle p) := rfl

end Wikipedia.HopfProblem.SixthHurewicz
