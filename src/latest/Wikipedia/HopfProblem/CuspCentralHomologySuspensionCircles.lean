import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircle
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleDisjoint
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The three actual circles in the suspension model

The input is the topological disjoint union of three unit complex circles.
Its actual integral singular homology and the degree-zero map into every
path-connected space are computed using the proved circle homology and
the actual disjoint-union chain decomposition.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- Three literal unit complex circles, with the disjoint-union topology. -/
abbrev ThreeCircles := _root_.Circle ⊕ (_root_.Circle ⊕ _root_.Circle)

def unitCircleHomologyZeroEquiv : SingularHomology _root_.Circle 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv _root_.Circle

def unitCircleHomologyOneEquiv : SingularHomology _root_.Circle 1 ≃ₗ[ℤ] ℤ :=
  (homeomorphHomologyEquiv
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm 1).trans
      circleHomologyOneEquiv

theorem unitCircle_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology _root_.Circle (n + 2)) := by
  let := circle_homology_subsingleton n
  exact (homeomorphHomologyEquiv
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (n + 2)).injective.subsingleton

/-- The actual homology splitting by the three original summands. -/
def threeCirclesHomologySplit (n : ℕ) :
    SingularHomology ThreeCircles n ≃ₗ[ℤ]
      (SingularHomology _root_.Circle n ×
        (SingularHomology _root_.Circle n × SingularHomology _root_.Circle n)) :=
  ((sumHomologyEquiv _root_.Circle (_root_.Circle ⊕ _root_.Circle) n).toAddEquiv.trans
    ((AddEquiv.refl _).prodCongr
      (sumHomologyEquiv _root_.Circle _root_.Circle n).toAddEquiv)).toIntLinearEquiv

def integerTripleEquiv : (ℤ × (ℤ × ℤ)) ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ({ toFun a := ![a.1, a.2.1, a.2.2]
     invFun a := (a 0, (a 1, a 2))
     left_inv _ := rfl
     right_inv a := by ext i; fin_cases i <;> rfl
     map_add' a b := by ext i; fin_cases i <;> rfl } :
    (ℤ × (ℤ × ℤ)) ≃+ (Fin 3 → ℤ)).toIntLinearEquiv

/-- Degree zero has one generator for each of the three actual components. -/
def threeCirclesHomologyZeroEquiv : SingularHomology ThreeCircles 0 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ((threeCirclesHomologySplit 0).toAddEquiv.trans
    ((unitCircleHomologyZeroEquiv.toAddEquiv.prodCongr
      (unitCircleHomologyZeroEquiv.toAddEquiv.prodCongr
        unitCircleHomologyZeroEquiv.toAddEquiv)).trans
          integerTripleEquiv.toAddEquiv)).toIntLinearEquiv

/-- Degree one has the three actual circle generators. -/
def threeCirclesHomologyOneEquiv : SingularHomology ThreeCircles 1 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ((threeCirclesHomologySplit 1).toAddEquiv.trans
    ((unitCircleHomologyOneEquiv.toAddEquiv.prodCongr
      (unitCircleHomologyOneEquiv.toAddEquiv.prodCongr
        unitCircleHomologyOneEquiv.toAddEquiv)).trans
          integerTripleEquiv.toAddEquiv)).toIntLinearEquiv

theorem threeCircles_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology ThreeCircles (n + 2)) := by
  let := unitCircle_homology_subsingleton n
  exact (threeCirclesHomologySplit (n + 2)).injective.subsingleton

/-- The integral augmentation of three component coordinates. -/
def sumCoordinates : (Fin 3 → ℤ) →ₗ[ℤ] ℤ where
  toFun a := ∑ i, a i
  map_add' a b := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r a := by simp only [RingHom.id_apply, Pi.smul_apply, Finset.smul_sum]

@[simp] theorem sumCoordinates_apply (a : Fin 3 → ℤ) :
    sumCoordinates a = a 0 + a 1 + a 2 := by
  simp only [sumCoordinates, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_three]

private theorem sumHomology_map {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X ⊕ Y, Z)) (n : ℕ)
    (a : SingularHomology (X ⊕ Y) n) :
    singularHomologyMap f n a =
      singularHomologyMap (f.comp (sumInlMap X Y)) n (sumHomologyEquiv X Y n a).1 +
      singularHomologyMap (f.comp (sumInrMap X Y)) n (sumHomologyEquiv X Y n a).2 := by
  have hf : f = sumElimMap (f.comp (sumInlMap X Y)) (f.comp (sumInrMap X Y)) := by
    ext x
    cases x <;> rfl
  conv_lhs => rw [hf]
  exact sumHomologyEquiv_sumElim _ _ n a

/-- Every continuous map to a path-connected space adds the three
degree-zero component coordinates under the canonical augmentation. -/
theorem threeCirclesHomologyZeroEquiv_map {Y : Type} [TopologicalSpace Y]
    [PathConnectedSpace Y] (f : C(ThreeCircles, Y)) (a : SingularHomology ThreeCircles 0) :
    connectedHomologyZeroEquiv Y (singularHomologyMap f 0 a) =
      sumCoordinates (threeCirclesHomologyZeroEquiv a) := by
  rw [sumHomology_map f, map_add]
  rw [sumHomology_map (f.comp (sumInrMap _root_.Circle (_root_.Circle ⊕ _root_.Circle))),
    map_add]
  rw [connectedHomologyZeroEquiv_natural, connectedHomologyZeroEquiv_natural,
    connectedHomologyZeroEquiv_natural, sumCoordinates_apply]
  exact (add_assoc _ _ _).symm

/-- The same formula transported through any genuine homotopy equivalence
with the three actual circles; this applies to the suspension's open belt. -/
theorem threeCirclesHomologyZeroEquiv_map_homotopyEquiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace Y]
    (e : X ≃ₕ ThreeCircles) (f : C(X, Y)) (a : SingularHomology X 0) :
    connectedHomologyZeroEquiv Y (singularHomologyMap f 0 a) =
      sumCoordinates (threeCirclesHomologyZeroEquiv (homotopyEquivHomologyEquiv e 0 a)) := by
  obtain ⟨b, rfl⟩ := (homotopyEquivHomologyEquiv e 0).symm.surjective a
  rw [LinearEquiv.apply_symm_apply, homotopyEquivHomologyEquiv_symm_apply]
  change connectedHomologyZeroEquiv Y
    (((singularHomologyMap f 0).comp (singularHomologyMap e.invFun 0)) b) = _
  rw [← singularHomologyMap_comp]
  exact threeCirclesHomologyZeroEquiv_map (f.comp e.invFun) b

/-- The actual kernel of the three-component augmentation has an
integral basis of two independent component differences. -/
def sumCoordinatesKernelEquiv : LinearMap.ker sumCoordinates ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ({ toFun a := ![a.1 1, a.1 2]
     invFun a := ⟨![-a 0 - a 1, a 0, a 1], by
       change sumCoordinates ![-a 0 - a 1, a 0, a 1] = 0
       rw [sumCoordinates_apply]
       change -a 0 - a 1 + a 0 + a 1 = 0
       ring⟩
     left_inv a := by
       apply Subtype.ext
       have ha : a.1 0 + a.1 1 + a.1 2 = 0 := by
         simpa only [LinearMap.mem_ker, sumCoordinates_apply] using a.2
       ext i
       fin_cases i
       · change -a.1 1 - a.1 2 = a.1 0
         omega
       · rfl
       · rfl
     right_inv a := by ext i; fin_cases i <;> rfl
     map_add' a b := by ext i; fin_cases i <;> rfl } :
    LinearMap.ker sumCoordinates ≃+ (Fin 2 → ℤ)).toIntLinearEquiv

end Wikipedia.HopfProblem.CuspCentralHomology
