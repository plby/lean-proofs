import Wikipedia.HopfProblem.FifthHurewiczCube
import Wikipedia.HopfProblem.FifthHurewiczNativeMaps

/-!
# The actual fifth Hurewicz homomorphism

The genuine five-cube class descends through Mathlib's native quotient by
homotopies relative to the cube boundary. The explicit concatenation
six-chain proves the homomorphism law for the actual native group
operation. Additive notation uses only the standard `Additive` synonym.

This construction asserts no injectivity, surjectivity, or isomorphism.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FifthHurewicz

open SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

/-- The homotopy-invariant cube class on the actual native fifth homotopy group. -/
def hurewiczFunction (x : X) : π_ 5 X x → SingularHomology X 5 :=
  Quotient.lift cubeHomologyClass (fun _ _ h => cubeHomologyClass_homotopic h)

@[simp] theorem hurewiczFunction_mk (x : X) (p : GenLoop (Fin 5) X x) :
    hurewiczFunction x ⟦p⟧ = cubeHomologyClass p := rfl

/-- The genuine fifth Hurewicz homomorphism, translating native
multiplicative `π₅` notation to addition in actual integral homology. -/
def hurewiczPi5 (x : X) : π_ 5 X x →* Multiplicative (SingularHomology X 5) where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (cubeHomologyClass_const (x := x))
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine (congrArg (fun c : π_ 5 X x => Multiplicative.ofAdd (hurewiczFunction x c))
      (HomotopyGroup.mul_spec (i := (0 : Fin 5)) (p := p) (q := q))).trans ?_
    change Multiplicative.ofAdd (cubeHomologyClass (GenLoop.transAt (0 : Fin 5) q p)) =
      Multiplicative.ofAdd (cubeHomologyClass p + cubeHomologyClass q)
    rw [cubeHomologyClass_transAt, add_comm]

@[simp] theorem hurewiczFunction_one (x : X) : hurewiczFunction x 1 = 0 :=
  congrArg Multiplicative.toAdd (hurewiczPi5 x).map_one

theorem hurewiczFunction_mul (x : X) (a b : π_ 5 X x) :
    hurewiczFunction x (a * b) = hurewiczFunction x a + hurewiczFunction x b :=
  congrArg Multiplicative.toAdd ((hurewiczPi5 x).map_mul a b)

@[simp] theorem hurewiczFunction_inv (x : X) (a : π_ 5 X x) :
    hurewiczFunction x a⁻¹ = -hurewiczFunction x a :=
  congrArg Multiplicative.toAdd ((hurewiczPi5 x).map_inv a)

/-- Integral-linear notation for the same map on the additive native group. -/
def hurewiczMap (x : X) : Additive (π_ 5 X x) →ₗ[ℤ] SingularHomology X 5 where
  toFun := (hurewiczPi5 x).toAdditiveLeft
  map_add' := (hurewiczPi5 x).toAdditiveLeft.map_add
  map_smul' n a := by
    simpa using map_intCast_smul (hurewiczPi5 x).toAdditiveLeft ℤ ℤ n a

@[simp] theorem hurewiczMap_mk (x : X) (p : GenLoop (Fin 5) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 5 X x)) = cubeHomologyClass p := rfl

/-- The defining representative uses the original generalized loop on
the fixed actual five-cube chain and the actual integral homology class map. -/
theorem hurewiczMap_representative (x : X) (p : GenLoop (Fin 5) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 5 X x)) =
      ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5 (cubeCycle p) := rfl

end Wikipedia.HopfProblem.FifthHurewicz
