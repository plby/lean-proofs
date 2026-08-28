import Wikipedia.HopfProblem.SecondHurewiczSquare
import Wikipedia.HopfProblem.SecondHurewiczNativeMaps

/-!
# The actual second Hurewicz homomorphism

The square class descends through Mathlib's native quotient by homotopies
relative to the cube boundary. The explicit concatenation prism proves
the homomorphism law for Mathlib's actual group operation. Additive
notation is obtained only by the standard `Additive` type synonym.

No injectivity, surjectivity, or Hurewicz isomorphism theorem is asserted.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SecondHurewicz

open SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

/-- The homotopy-invariant square class on the actual native second homotopy group. -/
def hurewiczFunction (x : X) : π_ 2 X x → SingularHomology X 2 :=
  Quotient.lift squareHomologyClass (fun _ _ h => squareHomologyClass_homotopic h)

@[simp] theorem hurewiczFunction_mk (x : X) (p : GenLoop (Fin 2) X x) :
    hurewiczFunction x ⟦p⟧ = squareHomologyClass p := rfl

/-- The genuine second Hurewicz homomorphism. The multiplicative notation
on native `π₂` is translated to addition in actual integral singular homology. -/
def hurewiczPi2 (x : X) : π_ 2 X x →* Multiplicative (SingularHomology X 2) where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (squareHomologyClass_const (x := x))
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine (congrArg (fun c : π_ 2 X x => Multiplicative.ofAdd (hurewiczFunction x c))
      (HomotopyGroup.mul_spec (i := (0 : Fin 2)) (p := p) (q := q))).trans ?_
    change Multiplicative.ofAdd (squareHomologyClass (GenLoop.transAt (0 : Fin 2) q p)) =
      Multiplicative.ofAdd (squareHomologyClass p + squareHomologyClass q)
    rw [squareHomologyClass_transAt, add_comm]

@[simp] theorem hurewiczFunction_one (x : X) : hurewiczFunction x 1 = 0 :=
  congrArg Multiplicative.toAdd (hurewiczPi2 x).map_one

theorem hurewiczFunction_mul (x : X) (a b : π_ 2 X x) :
    hurewiczFunction x (a * b) = hurewiczFunction x a + hurewiczFunction x b :=
  congrArg Multiplicative.toAdd ((hurewiczPi2 x).map_mul a b)

@[simp] theorem hurewiczFunction_inv (x : X) (a : π_ 2 X x) :
    hurewiczFunction x a⁻¹ = -hurewiczFunction x a :=
  congrArg Multiplicative.toAdd ((hurewiczPi2 x).map_inv a)

/-- Integral linear form of the same map, on the additive native group. -/
def hurewiczMap (x : X) : Additive (π_ 2 X x) →ₗ[ℤ] SingularHomology X 2 where
  toFun := (hurewiczPi2 x).toAdditiveLeft
  map_add' := (hurewiczPi2 x).toAdditiveLeft.map_add
  map_smul' n a := by
    simpa using map_intCast_smul (hurewiczPi2 x).toAdditiveLeft ℤ ℤ n a

@[simp] theorem hurewiczMap_mk (x : X) (p : GenLoop (Fin 2) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x)) = squareHomologyClass p := rfl

/-- The defining representative is the original generalized loop applied
to the fixed actual square chain, viewed in actual integral homology. -/
theorem hurewiczMap_representative (x : X) (p : GenLoop (Fin 2) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x)) =
      ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 (squareCycle p) := rfl

end Wikipedia.HopfProblem.SecondHurewicz
