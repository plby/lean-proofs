import Wikipedia.HopfProblem.SingularCohomologyCupCochainsExact
import Wikipedia.HopfProblem.SingularCohomologyCupDescent
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBilinearMaps

/-!
# The Alexander--Whitney cup product on actual singular cohomology

The actual singular cochain product preserves cocycles by its proved
Leibniz identity.  Its explicit primitives make multiplication by an
incoming coboundary vanish in cohomology, so it descends in both inputs
to the native categorical cohomology objects.  The representative formula
also proves naturality and compatibility with genuine cycle evaluation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyCup

open FirstHurewicz SingularCohomologyFree SingularMayerVietoris
open PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable (X : Type) [TopologicalSpace X]

/-- The native Alexander--Whitney product of two genuine cocycles. -/
def cupCocycles (p q : ℕ) :
    Cocycle (singularCochainComplex X) p →ₗ[ℤ]
      Cocycle (singularCochainComplex X) q →ₗ[ℤ]
        Cocycle (singularCochainComplex X) (p + q) where
  toFun a :=
    { toFun b := mkCocycle _ (p + q) (cup a.val b.val)
        (cup_cocycle a.val b.val (cocycle_condition _ p a) (cocycle_condition _ q b))
      map_add' b c := Subtype.ext (cup_add_right a.val b.val c.val)
      map_smul' r b := Subtype.ext (cup_smul_right r a.val b.val) }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    exact Subtype.ext (cup_add_left a.val b.val c.val)
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    exact Subtype.ext (cup_smul_left r a.val b.val)

@[simp] theorem cupCocycles_val (p q : ℕ)
    (a : Cocycle (singularCochainComplex X) p)
    (b : Cocycle (singularCochainComplex X) q) :
    (cupCocycles X p q a b).val = cup a.val b.val := rfl

/-- A primitive in any equal successor degree gives zero in actual cohomology. -/
theorem cocycleClass_zero_of_primitive {k n : ℕ} (h : k + 1 = n)
    (a : Cocycle (singularCochainComplex X) n) (b : Cochain X k)
    (hab : a.val = castCochain h (coboundary b)) :
    cocycleClass (singularCochainComplex X) n a = 0 := by
  subst n
  apply (cocycleClass_eq_zero_iff (singularCochainComplex X) (k + 1) a).mpr
  exact ⟨b, hab.symm⟩

theorem coboundaryCocycle_zero_val
    (a : (singularCochainComplex X).X (0 - 1)) :
    (coboundaryCocycle (singularCochainComplex X) 0 a).val = 0 := by
  have hd : (singularCochainComplex X).d 0 0 = 0 :=
    (singularCochainComplex X).shape 0 0 (by simp)
  change ((singularCochainComplex X).d 0 0).hom a = 0
  rw [hd]
  rfl

/-- The class of the cup product before quotienting its two inputs. -/
def cupCocycleClasses (p q : ℕ) :
    Cocycle (singularCochainComplex X) p →ₗ[ℤ]
      Cocycle (singularCochainComplex X) q →ₗ[ℤ] SingularCohomology X (p + q) :=
  integerBilinearPostcompose (cupCocycles X p q)
    (cocycleClass (singularCochainComplex X) (p + q))

@[simp] theorem cupCocycleClasses_apply (p q : ℕ)
    (a : Cocycle (singularCochainComplex X) p)
    (b : Cocycle (singularCochainComplex X) q) :
    cupCocycleClasses X p q a b =
      cocycleClass (singularCochainComplex X) (p + q) (cupCocycles X p q a b) := rfl

/-- The actual left primitive proves independence of the left cocycle representative. -/
theorem cupCocycleClasses_coboundary_left (p q : ℕ)
    (a : (singularCochainComplex X).X (p - 1))
    (b : Cocycle (singularCochainComplex X) q) :
    cupCocycleClasses X p q (coboundaryCocycle (singularCochainComplex X) p a) b = 0 := by
  rw [cupCocycleClasses_apply]
  cases p with
  | zero =>
      have hz : cupCocycles X 0 q
          (coboundaryCocycle (singularCochainComplex X) 0 a) b = 0 := by
        apply Subtype.ext
        rw [cupCocycles_val, coboundaryCocycle_zero_val, cup_zero_left]
        rfl
      rw [hz, map_zero]
  | succ p =>
      apply cocycleClass_zero_of_primitive X (show p + q + 1 = (p + 1) + q by omega)
        _ (cup a b.val)
      exact cup_coboundary_left_of_cocycle a b.val (cocycle_condition _ q b)

/-- The signed actual right primitive proves independence of the right representative. -/
theorem cupCocycleClasses_coboundary_right (p q : ℕ)
    (a : Cocycle (singularCochainComplex X) p)
    (b : (singularCochainComplex X).X (q - 1)) :
    cupCocycleClasses X p q a (coboundaryCocycle (singularCochainComplex X) q b) = 0 := by
  rw [cupCocycleClasses_apply]
  cases q with
  | zero =>
      have hz : cupCocycles X p 0 a
          (coboundaryCocycle (singularCochainComplex X) 0 b) = 0 := by
        apply Subtype.ext
        rw [cupCocycles_val, coboundaryCocycle_zero_val, cup_zero_right]
        rfl
      rw [hz, map_zero]
  | succ q =>
      apply cocycleClass_zero_of_primitive X (show p + q + 1 = p + (q + 1) by omega)
        _ ((-1 : ℤ) ^ p • cup a.val b)
      exact cup_coboundary_right_of_cocycle a.val b (cocycle_condition _ p a)

/-- The genuine Alexander--Whitney cup product on actual integral singular cohomology. -/
def cupProduct (p q : ℕ) :
    SingularCohomology X p →ₗ[ℤ]
      SingularCohomology X q →ₗ[ℤ] SingularCohomology X (p + q) :=
  bilinearCohomologyDesc (singularCochainComplex X) p (singularCochainComplex X) q
    (cupCocycleClasses X p q) (cupCocycleClasses_coboundary_right X p q)
    (cupCocycleClasses_coboundary_left X p q)

/-- The class product is represented by the actual native cochain product. -/
@[simp] theorem cupProduct_cocycleClass (p q : ℕ)
    (a : Cocycle (singularCochainComplex X) p)
    (b : Cocycle (singularCochainComplex X) q) :
    cupProduct X p q (cocycleClass (singularCochainComplex X) p a)
        (cocycleClass (singularCochainComplex X) q b) =
      cocycleClass (singularCochainComplex X) (p + q) (cupCocycles X p q a b) :=
  bilinearCohomologyDesc_cocycleClass _ _ _ _ _ _ _ a b

/-- Evaluation of this product on an actual cycle is literal Alexander--Whitney evaluation. -/
theorem cupProduct_evaluate_cocycles (p q : ℕ)
    (a : Cocycle (singularCochainComplex X) p)
    (b : Cocycle (singularCochainComplex X) q)
    (z : ModuleHomology.Cycle (singularComplex X) (p + q)) :
    singularEvaluation X (p + q)
        (cupProduct X p q (cocycleClass (singularCochainComplex X) p a)
          (cocycleClass (singularCochainComplex X) q b))
        (ModuleHomology.cycleClass (singularComplex X) (p + q) z) = cup a.val b.val z.val := by
  rw [cupProduct_cocycleClass, singularEvaluation_cocycle_cycle, cupCocycles_val]

section Naturality

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem cohomologyPullback_cocycleClass (f : C(X, Y)) (n : ℕ)
    (a : Cocycle (singularCochainComplex Y) n) :
    singularCohomologyPullback f n (cocycleClass (singularCochainComplex Y) n a) =
      cocycleClass (singularCochainComplex X) n (mapCocycles (singularPullback f) n a) :=
  homologyMap_cocycleClass (singularPullback f) n a

/-- Pullback preserves the native cocycle product itself. -/
theorem mapCocycles_cup (f : C(X, Y)) (p q : ℕ)
    (a : Cocycle (singularCochainComplex Y) p)
    (b : Cocycle (singularCochainComplex Y) q) :
    mapCocycles (singularPullback f) (p + q) (cupCocycles Y p q a b) =
      cupCocycles X p q (mapCocycles (singularPullback f) p a)
        (mapCocycles (singularPullback f) q b) := by
  apply Subtype.ext
  have ha : (mapCocycles (singularPullback f) p a).val = pullback f p a.val :=
    mapCocycles_val (singularPullback f) p a
  have hb : (mapCocycles (singularPullback f) q b).val = pullback f q b.val :=
    mapCocycles_val (singularPullback f) q b
  exact ((mapCocycles_val (singularPullback f) (p + q) (cupCocycles Y p q a b)).trans
    (pullback_cup f a.val b.val)).trans (congrArg₂ cup ha.symm hb.symm)

/-- Naturality holds for the actual cochain-induced pullbacks and actual cohomology cup product. -/
theorem cupProduct_pullback (f : C(X, Y)) (p q : ℕ)
    (a : SingularCohomology Y p) (b : SingularCohomology Y q) :
    singularCohomologyPullback f (p + q) (cupProduct Y p q a b) =
      cupProduct X p q (singularCohomologyPullback f p a) (singularCohomologyPullback f q b) := by
  obtain ⟨a, rfl⟩ := cocycleClass_surjective (singularCochainComplex Y) p a
  obtain ⟨b, rfl⟩ := cocycleClass_surjective (singularCochainComplex Y) q b
  rw [cupProduct_cocycleClass, cohomologyPullback_cocycleClass,
    cohomologyPullback_cocycleClass, cohomologyPullback_cocycleClass,
    cupProduct_cocycleClass, mapCocycles_cup]

end Naturality
end Wikipedia.HopfProblem.SingularCohomologyCup
