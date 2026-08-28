import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductDescent
import Mathlib.Algebra.Homology.Homotopy

/-!
# A degree-raising homology map from a zero-to-zero chain homotopy

After the two endpoints of a prism vanish in a relative complex, its
components take cycles to cycles and boundaries to boundaries, with
the required minus sign. This gives a map on the original categorical
homology objects, raising degree by one.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris ModuleHomology PeriodTorusHigherHomology

namespace NoExoticSixSphere.ChainHomotopyDegreeShift

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (H : _root_.Homotopy (0 : K ⟶ L) 0)

def prism (n : ℕ) : K.X n →ₗ[ℤ] L.X (n + 1) := (H.hom n (n + 1)).hom

theorem prism_boundary (n : ℕ) (c : K.X (n + 1)) :
    (L.d (n + 2) (n + 1)).hom (prism H (n + 1) c) =
      -prism H n ((K.d (n + 1) n).hom c) := by
  have h := H.comm (n + 1)
  rw [dNext_eq H.hom (show (ComplexShape.down ℕ).Rel (n + 1) n by rfl),
    prevD_eq H.hom (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) by rfl)] at h
  have hh := congrArg (fun m : K.X (n + 1) ⟶ L.X (n + 1) ↦ m.hom c) h
  change 0 = prism H n ((K.d (n + 1) n).hom c) +
    (L.d (n + 2) (n + 1)).hom (prism H (n + 1) c) + 0 at hh
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_zero, zero_add, add_comm] using hh.symm

theorem prism_cycle (n : ℕ) (c : Cycle K n) :
    (L.d (n + 1) n).hom (prism H n c.val) = 0 := by
  have h := H.comm n
  rw [dNext_nat,
    prevD_eq H.hom (show (ComplexShape.down ℕ).Rel (n + 1) n by rfl)] at h
  have hh := congrArg (fun m : K.X n ⟶ L.X n ↦ m.hom c.val) h
  change 0 = (H.hom (n - 1) n).hom ((K.d n (n - 1)).hom c.val) +
    (L.d (n + 1) n).hom (prism H n c.val) + 0 at hh
  rw [cycle_condition K n c, map_zero, zero_add, add_zero] at hh
  exact hh.symm

def cycleMap (n : ℕ) : Cycle K n →ₗ[ℤ] Cycle L (n + 1) where
  toFun c := mkCycle L (n + 1) (prism H n c.val) (by simpa using prism_cycle H n c)
  map_add' c d := Subtype.ext ((prism H n).map_add c.val d.val)
  map_smul' r c := Subtype.ext ((prism H n).map_smul r c.val)

theorem cycleMap_val (n : ℕ) (c : Cycle K n) : (cycleMap H n c).val = prism H n c.val := rfl

theorem cycleClass_boundary (n : ℕ) (b : K.X (n + 1)) :
    cycleClass L (n + 1) (cycleMap H n (boundaryCycle K n b)) = 0 := by
  apply (cycleClass_eq_zero_iff L (n + 1) _).mpr
  refine ⟨-prism H (n + 1) b, ?_⟩
  rw [map_neg, prism_boundary, neg_neg]
  rfl

def homologyMap (n : ℕ) : K.homology n →ₗ[ℤ] L.homology (n + 1) :=
  homologyDesc K n ((cycleClass L (n + 1)).comp (cycleMap H n)) (cycleClass_boundary H n)

theorem homologyMap_cycleClass (n : ℕ) (c : Cycle K n) :
    homologyMap H n (cycleClass K n c) = cycleClass L (n + 1) (cycleMap H n c) :=
  homologyDesc_cycleClass K n _ _ c

end NoExoticSixSphere.ChainHomotopyDegreeShift
