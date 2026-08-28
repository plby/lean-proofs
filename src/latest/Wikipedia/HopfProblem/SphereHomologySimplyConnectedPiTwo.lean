import Wikipedia.HopfProblem.SphereHomologySimplyConnectedTopology
import Wikipedia.HopfProblem.SphereHomologyVanishing
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnected

/-!
# Actual second homotopy groups of the Euclidean spheres

The proved simple connectedness of each sphere of dimension at least two
allows the genuine second Hurewicz isomorphism to be applied. Its forward
map remains the native based square's actual singular-cycle class. The
two-sphere marking then uses the previously constructed suspension
marking of top homology; no comparison with an orientation or with the
identity sphere map is assumed. For dimensions at least three the actual
second homotopy group is trivial.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SphereHomology

open SingularMayerVietoris

/-- The genuine second Hurewicz map is an isomorphism for the actual Euclidean spheres. -/
def unitSpherePiTwoHurewiczEquiv (n : ℕ) (x : UnitSphere (n + 2)) :
    Additive (π_ 2 (UnitSphere (n + 2)) x) ≃ₗ[ℤ]
      SingularHomology (UnitSphere (n + 2)) 2 :=
  SecondHurewicz.SimplyConnected.hurewiczLinearEquiv x

@[simp] theorem unitSpherePiTwoHurewiczEquiv_toLinearMap (n : ℕ)
    (x : UnitSphere (n + 2)) :
    (unitSpherePiTwoHurewiczEquiv n x).toLinearMap = SecondHurewicz.hurewiczMap x := rfl

@[simp] theorem unitSpherePiTwoHurewiczEquiv_apply (n : ℕ) (x : UnitSphere (n + 2))
    (a : Additive (π_ 2 (UnitSphere (n + 2)) x)) :
    unitSpherePiTwoHurewiczEquiv n x a = SecondHurewicz.hurewiczMap x a := rfl

/-- On every original based generalized loop, the comparison is its actual square class. -/
@[simp] theorem unitSpherePiTwoHurewiczEquiv_mk (n : ℕ) (x : UnitSphere (n + 2))
    (p : GenLoop (Fin 2) (UnitSphere (n + 2)) x) :
    unitSpherePiTwoHurewiczEquiv n x
        (Additive.ofMul (⟦p⟧ : π_ 2 (UnitSphere (n + 2)) x)) =
      SecondHurewicz.squareHomologyClass p := rfl

/-- The native second homotopy group of the actual two-sphere is infinite cyclic. -/
def sphereTwoPiTwoEquiv (x : UnitSphere 2) : Additive (π_ 2 (UnitSphere 2) x) ≃ₗ[ℤ] ℤ :=
  (unitSpherePiTwoHurewiczEquiv 0 x).trans (unitSphereHomologyTopEquiv 1)

/-- The same equivalence in the additive notation on the native homotopy group. -/
abbrev sphereTwoPiTwoAddEquiv (x : UnitSphere 2) : Additive (π_ 2 (UnitSphere 2) x) ≃+ ℤ :=
  (sphereTwoPiTwoEquiv x).toAddEquiv

/-- The same result in Mathlib's original multiplicative notation for its homotopy groups. -/
def sphereTwoPiTwoMulEquiv (x : UnitSphere 2) : π_ 2 (UnitSphere 2) x ≃* Multiplicative ℤ :=
  (sphereTwoPiTwoAddEquiv x).toMultiplicativeRight

/-- The integer marking first applies the actual native Hurewicz map. -/
theorem sphereTwoPiTwoEquiv_apply (x : UnitSphere 2) (a : Additive (π_ 2 (UnitSphere 2) x)) :
    sphereTwoPiTwoEquiv x a =
      unitSphereHomologyTopEquiv 1 (SecondHurewicz.hurewiczMap x a) := rfl

@[simp] theorem sphereTwoPiTwoEquiv_mk (x : UnitSphere 2)
    (p : GenLoop (Fin 2) (UnitSphere 2) x) :
    sphereTwoPiTwoEquiv x (Additive.ofMul (⟦p⟧ : π_ 2 (UnitSphere 2) x)) =
      unitSphereHomologyTopEquiv 1 (SecondHurewicz.squareHomologyClass p) := rfl

/-- The representative is the actual singular two-cycle of the original based square. -/
theorem sphereTwoPiTwoEquiv_representative (x : UnitSphere 2)
    (p : GenLoop (Fin 2) (UnitSphere 2) x) :
    sphereTwoPiTwoEquiv x (Additive.ofMul (⟦p⟧ : π_ 2 (UnitSphere 2) x)) =
      unitSphereHomologyTopEquiv 1
        (ModuleHomology.cycleClass (FirstHurewicz.singularComplex (UnitSphere 2)) 2
          (SecondHurewicz.squareCycle p)) := rfl

/-- The inverse uses the proved singular-triangle descent of the actual Hurewicz map. -/
theorem sphereTwoPiTwoEquiv_symm_apply (x : UnitSphere 2) (k : ℤ) :
    (sphereTwoPiTwoEquiv x).symm k =
      SecondHurewicz.SimplyConnected.hurewiczInverse x
        ((unitSphereHomologyTopEquiv 1).symm k) := rfl

theorem sphereTwoPiTwoMulEquiv_apply (x : UnitSphere 2) (a : π_ 2 (UnitSphere 2) x) :
    sphereTwoPiTwoMulEquiv x a = Multiplicative.ofAdd
      (unitSphereHomologyTopEquiv 1 (SecondHurewicz.hurewiczFunction x a)) := rfl

/-- An actual native homotopy class mapping to the constructed primitive top homology class. -/
def sphereTwoPiTwoGenerator (x : UnitSphere 2) : Additive (π_ 2 (UnitSphere 2) x) :=
  (sphereTwoPiTwoEquiv x).symm 1

@[simp] theorem sphereTwoPiTwoEquiv_generator (x : UnitSphere 2) :
    sphereTwoPiTwoEquiv x (sphereTwoPiTwoGenerator x) = 1 :=
  (sphereTwoPiTwoEquiv x).apply_symm_apply 1

theorem sphereTwoPiTwoGenerator_hurewicz (x : UnitSphere 2) :
    SecondHurewicz.hurewiczMap x (sphereTwoPiTwoGenerator x) = unitSphereTopClass 1 := by
  apply (unitSphereHomologyTopEquiv 1).injective
  change sphereTwoPiTwoEquiv x (sphereTwoPiTwoGenerator x) =
    unitSphereHomologyTopEquiv 1 (unitSphereTopClass 1)
  rw [sphereTwoPiTwoEquiv_generator, unitSphereHomologyTopEquiv_topClass]

/-- The native second homotopy group of every sphere of dimension at least three is trivial. -/
theorem unitSphere_piTwo_subsingleton (n : ℕ) (x : UnitSphere (n + 3)) :
    Subsingleton (π_ 2 (UnitSphere (n + 3)) x) := by
  let := unitSphere_homology_subsingleton (n + 2) 2 (by decide) (by omega)
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton

/-- Triviality also holds in the standard additive notation on that same native group. -/
theorem unitSphere_additive_piTwo_subsingleton (n : ℕ) (x : UnitSphere (n + 3)) :
    Subsingleton (Additive (π_ 2 (UnitSphere (n + 3)) x)) := by
  let := unitSphere_piTwo_subsingleton n x
  infer_instance

/-- Every original based square in these higher spheres is
nullhomotopic relative to its boundary. -/
theorem unitSphere_genLoop_two_nullhomotopic (n : ℕ) (x : UnitSphere (n + 3))
    (p : GenLoop (Fin 2) (UnitSphere (n + 3)) x) : GenLoop.Homotopic p GenLoop.const := by
  exact Quotient.exact
    (@Subsingleton.elim (π_ 2 (UnitSphere (n + 3)) x)
      (unitSphere_piTwo_subsingleton n x) ⟦p⟧ ⟦GenLoop.const⟧)

end Wikipedia.HopfProblem.SphereHomology
