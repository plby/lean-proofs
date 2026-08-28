import Wikipedia.HopfProblem.SphereHomologyCoefficientsSequence
import Wikipedia.HopfProblem.SphereHomologyVanishing

/-!
# Actual finite-coefficient singular homology of Euclidean spheres

The integral sphere homology has already been computed using genuine
singular suspension maps.  Its proved freeness kills the Bockstein in
the actual coefficient sequence.  Consequently every positive-dimensional
Euclidean sphere has coefficient module `ℤ/p` in degree zero and its top
degree, and zero in every other degree.  The maps record the actual
reductions of the original point and suspension top classes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SphereHomologyCoefficients

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

/-- The native bottom homology of an actual positive-dimensional Euclidean sphere. -/
def unitSphereModHomologyZeroEquiv (p : ℕ) (hp : p ≠ 0) (n : ℕ) :
    ModHomology p (UnitSphere (n + 1)) 0 ≃ₗ[ℤ] ZMod p :=
  modHomologyEquivZMod p hp (UnitSphere (n + 1)) 0 (unitSphereHomologyZeroEquiv n)

/-- The native top homology uses the actual integral suspension marking,
followed by coefficient reduction. -/
def unitSphereModHomologyTopEquiv (p : ℕ) (hp : p ≠ 0) (n : ℕ) :
    ModHomology p (UnitSphere (n + 1)) (n + 1) ≃ₗ[ℤ] ZMod p :=
  modHomologyEquivZMod p hp (UnitSphere (n + 1)) (n + 1) (unitSphereHomologyTopEquiv n)

@[simp] theorem unitSphereModHomologyZeroEquiv_reduction (p : ℕ) (hp : p ≠ 0) (n : ℕ)
    (a : SingularHomology (UnitSphere (n + 1)) 0) :
    unitSphereModHomologyZeroEquiv p hp n
      (reductionHomologyMap p (UnitSphere (n + 1)) 0 a) =
        (unitSphereHomologyZeroEquiv n a : ZMod p) :=
  modHomologyEquivZMod_reduction p hp (UnitSphere (n + 1)) 0 _ a

@[simp] theorem unitSphereModHomologyTopEquiv_reduction (p : ℕ) (hp : p ≠ 0) (n : ℕ)
    (a : SingularHomology (UnitSphere (n + 1)) (n + 1)) :
    unitSphereModHomologyTopEquiv p hp n
      (reductionHomologyMap p (UnitSphere (n + 1)) (n + 1) a) =
        (unitSphereHomologyTopEquiv n a : ZMod p) :=
  modHomologyEquivZMod_reduction p hp (UnitSphere (n + 1)) (n + 1) _ a

/-- The actual coefficient reduction of a point is the positive bottom generator. -/
@[simp] theorem unitSphereModHomologyZeroEquiv_pointClass (p : ℕ) (hp : p ≠ 0) (n : ℕ)
    (x : UnitSphere (n + 1)) :
    unitSphereModHomologyZeroEquiv p hp n
      (reductionHomologyMap p (UnitSphere (n + 1)) 0 (pointClass x)) = 1 := by
  rw [unitSphereModHomologyZeroEquiv_reduction, unitSphereHomologyZeroEquiv_pointClass]
  exact Int.cast_one

/-- The original suspension top cycle reduced through the genuine coefficient chain map. -/
def unitSphereModTopClass (p n : ℕ) : ModHomology p (UnitSphere (n + 1)) (n + 1) :=
  reductionHomologyMap p (UnitSphere (n + 1)) (n + 1) (unitSphereTopClass n)

@[simp] theorem unitSphereModHomologyTopEquiv_topClass (p : ℕ) (hp : p ≠ 0) (n : ℕ) :
    unitSphereModHomologyTopEquiv p hp n (unitSphereModTopClass p n) = 1 := by
  rw [unitSphereModTopClass, unitSphereModHomologyTopEquiv_reduction,
    unitSphereHomologyTopEquiv_topClass]
  exact Int.cast_one

theorem unitSphereModTopClass_ne_zero (p : ℕ) (hp : p ≠ 0) (n : ℕ)
    [Nontrivial (ZMod p)] : unitSphereModTopClass p n ≠ 0 := by
  intro h
  have hh := congrArg (unitSphereModHomologyTopEquiv p hp n) h
  simp at hh

/-- All other genuine finite-coefficient singular homology groups vanish. -/
theorem unitSphereModHomology_subsingleton (p : ℕ) (hp : p ≠ 0) (n k : ℕ)
    (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    Subsingleton (ModHomology p (UnitSphere (n + 1)) k) := by
  let := unitSphere_homology_subsingleton n k hk hkn
  exact modHomology_subsingleton p hp (UnitSphere (n + 1)) k

theorem unitSphereModHomology_isZero (p : ℕ) (hp : p ≠ 0) (n k : ℕ)
    (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    IsZero (ModHomology p (UnitSphere (n + 1)) k) := by
  let := unitSphereModHomology_subsingleton p hp n k hk hkn
  exact ModuleCat.isZero_of_subsingleton _

/-- The actual off-degree group is linearly equivalent to the literal zero coefficient module. -/
def unitSphereModHomologyEquivZero (p : ℕ) (hp : p ≠ 0) (n k : ℕ)
    (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    ModHomology p (UnitSphere (n + 1)) k ≃ₗ[ℤ] (Fin 0 → ZMod p) := by
  let := unitSphereModHomology_subsingleton p hp n k hk hkn
  exact LinearEquiv.ofSubsingleton _ _

end Wikipedia.HopfProblem.SphereHomologyCoefficients
