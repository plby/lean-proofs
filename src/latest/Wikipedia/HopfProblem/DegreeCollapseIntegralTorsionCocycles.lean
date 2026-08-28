import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionCycles

/-!
# Original integral cocycles define characters of the original torsion homology

The residue of a rational primitive kills actual boundaries. Descend it
through the original cycle-class surjection, retaining its value on every
original cycle. Primitive independence proves that this character depends
linearly on the original integral cocycle.
-/

noncomputable section

open CategoryTheory Function

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open SingularCohomologyFree SingularMayerVietoris.ModuleHomology

section Descent

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℤ A] [Module ℤ B] [Module ℤ C]

def descendLinear (q : A →ₗ[ℤ] B) (hq : Surjective q) (f : A →ₗ[ℤ] C)
    (hf : LinearMap.ker q ≤ LinearMap.ker f) : B →ₗ[ℤ] C := by
  let : Module ℤ (A ⧸ LinearMap.ker q) := Submodule.Quotient.module (LinearMap.ker q)
  exact ((LinearMap.ker q).liftQ f hf).comp
    (q.quotKerEquivOfSurjective hq).symm.toLinearMap

theorem descendLinear_apply (q : A →ₗ[ℤ] B) (hq : Surjective q) (f : A →ₗ[ℤ] C)
    (hf : LinearMap.ker q ≤ LinearMap.ker f) (x : A) :
    descendLinear q hq f hf (q x) = f x := by
  let : Module ℤ (A ⧸ LinearMap.ker q) := Submodule.Quotient.module (LinearMap.ker q)
  exact congrArg ((LinearMap.ker q).liftQ f hf)
    (LinearMap.quotKerEquivOfSurjective_symm_apply q hq x)

end Descent

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
  [Subsingleton (K.homology (n + 1))]

def cycleResidue (c : Cocycle (dualComplex K) (n + 1)) :
    Cycle K n →ₗ[ℤ] RationalResidue.Value :=
  RationalResidue.residue.comp ((rationalPrimitive K n c).comp (Cycle K n).subtype)

theorem cycleResidue_boundary (c : Cocycle (dualComplex K) (n + 1))
    (b : K.X (n + 1)) : cycleResidue K n c (boundaryCycle K n b) = 0 := by
  change RationalResidue.residue (rationalPrimitive K n c ((K.d (n + 1) n).hom b)) = 0
  rw [rationalPrimitive_boundary]
  exact RationalResidue.residue_intCast _

theorem cycleResidue_classKernel (c : Cocycle (dualComplex K) (n + 1)) :
    LinearMap.ker (cycleClass K n) ≤ LinearMap.ker (cycleResidue K n c) := by
  intro z hz
  obtain ⟨b, hb⟩ := (cycleClass_eq_zero_iff K n z).mp hz
  have he : boundaryCycle K n b = z := Subtype.ext hb
  exact (congrArg (cycleResidue K n c) he).symm.trans (cycleResidue_boundary K n c b)

def cocycleCharacter (c : Cocycle (dualComplex K) (n + 1)) :
    K.homology n →ₗ[ℤ] RationalResidue.Value :=
  descendLinear (cycleClass K n) (cycleClass_surjective K n)
    (cycleResidue K n c) (cycleResidue_classKernel K n c)

theorem cocycleCharacter_cycle (c : Cocycle (dualComplex K) (n + 1)) (z : Cycle K n) :
    cocycleCharacter K n c (cycleClass K n z) =
      RationalResidue.residue (rationalPrimitive K n c z.val) :=
  descendLinear_apply _ _ _ _ _

variable [Finite (K.homology n)]

def cocycleCharacters :
    Cocycle (dualComplex K) (n + 1) →ₗ[ℤ] (K.homology n →ₗ[ℤ] RationalResidue.Value) where
  toFun := cocycleCharacter K n
  map_add' c d := by
    ext a
    obtain ⟨z, rfl⟩ := cycleClass_surjective K n a
    change cocycleCharacter K n (c + d) (cycleClass K n z) =
      cocycleCharacter K n c (cycleClass K n z) + cocycleCharacter K n d (cycleClass K n z)
    rw [cocycleCharacter_cycle, cocycleCharacter_cycle, cocycleCharacter_cycle,
      rationalPrimitive_add_on_cycles, map_add]
  map_smul' r c := by
    ext a
    obtain ⟨z, rfl⟩ := cycleClass_surjective K n a
    change cocycleCharacter K n (r • c) (cycleClass K n z) =
      r • cocycleCharacter K n c (cycleClass K n z)
    rw [cocycleCharacter_cycle, cocycleCharacter_cycle, rationalPrimitive_smul_on_cycles,
      map_zsmul]

theorem cocycleCharacters_cycle (c : Cocycle (dualComplex K) (n + 1)) (z : Cycle K n) :
    cocycleCharacters K n c (cycleClass K n z) =
      RationalResidue.residue (rationalPrimitive K n c z.val) :=
  cocycleCharacter_cycle K n c z

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
