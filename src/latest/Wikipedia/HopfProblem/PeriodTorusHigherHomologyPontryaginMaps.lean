import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBilinearMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Actual addition maps used in the Pontryagin products

The addition, reassociation, and permutation maps below are continuous maps
on the actual spaces. Their identities therefore give identities between the
actual singular-homology functor maps in every degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin

open SingularMayerVietoris PeriodTorusHigherHomology

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def swapMap (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] : C(X × Y, Y × X) :=
  ⟨Prod.swap, continuous_swap⟩

def associatorMap (X Y Z : Type)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] :
    C((X × Y) × Z, X × (Y × Z)) :=
  (Homeomorph.prodAssoc X Y Z : C((X × Y) × Z, X × (Y × Z)))

/-- The even cyclic permutation from `(y,(z,x))` to `(x,(y,z))`. -/
def cyclicMap (X Y Z : Type)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] :
    C(Y × (Z × X), X × (Y × Z)) :=
  ⟨fun p => (p.2.2, (p.1, p.2.1)), by fun_prop⟩

variable (G : Type) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]

/-- The actual continuous addition map of the topological group. -/
def additionMap : C(G × G, G) :=
  ⟨fun p => p.1 + p.2, continuous_fst.add continuous_snd⟩

def rightAdditionMap : C(G × (G × G), G) :=
  (additionMap G).comp ((ContinuousMap.id G).prodMap (additionMap G))

def leftAdditionMap : C((G × G) × G, G) :=
  (additionMap G).comp ((additionMap G).prodMap (ContinuousMap.id G))

@[simp] theorem additionMap_apply (x y : G) : additionMap G (x, y) = x + y := rfl

@[simp] theorem rightAdditionMap_apply (x y z : G) :
    rightAdditionMap G (x, (y, z)) = x + (y + z) := rfl

@[simp] theorem leftAdditionMap_apply (x y z : G) :
    leftAdditionMap G ((x, y), z) = (x + y) + z := rfl

@[simp] theorem additionMap_comp_swap :
    (additionMap G).comp (swapMap G G) = additionMap G := by
  ext p
  exact add_comm p.2 p.1

@[simp] theorem rightAdditionMap_comp_associator :
    (rightAdditionMap G).comp (associatorMap G G G) = leftAdditionMap G := by
  ext p
  exact (add_assoc p.1.1 p.1.2 p.2).symm

@[simp] theorem rightAdditionMap_comp_cyclic :
    (rightAdditionMap G).comp (cyclicMap G G G) = rightAdditionMap G := by
  ext p
  change p.2.2 + (p.1 + p.2.1) = p.1 + (p.2.1 + p.2.2)
  abel

theorem addition_homology_swap (n : ℕ) :
    (singularHomologyMap (additionMap G) n).comp
        (singularHomologyMap (swapMap G G) n) = singularHomologyMap (additionMap G) n := by
  rw [← singularHomologyMap_comp, additionMap_comp_swap]

theorem rightAddition_homology_associator (n : ℕ) :
    (singularHomologyMap (rightAdditionMap G) n).comp
        (singularHomologyMap (associatorMap G G G) n) =
      singularHomologyMap (leftAdditionMap G) n := by
  rw [← singularHomologyMap_comp, rightAdditionMap_comp_associator]

theorem rightAddition_homology_cyclic (n : ℕ) :
    (singularHomologyMap (rightAdditionMap G) n).comp
        (singularHomologyMap (cyclicMap G G G) n) =
      singularHomologyMap (rightAdditionMap G) n := by
  rw [← singularHomologyMap_comp, rightAdditionMap_comp_cyclic]

variable {G} {H : Type} [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]

theorem additionMap_natural (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) :
    f.comp (additionMap G) = (additionMap H).comp (f.prodMap f) := by
  ext p
  exact hf p.1 p.2

theorem rightAdditionMap_natural (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) :
    f.comp (rightAdditionMap G) =
      (rightAdditionMap H).comp (f.prodMap (f.prodMap f)) := by
  ext p
  change f (p.1 + (p.2.1 + p.2.2)) = f p.1 + (f p.2.1 + f p.2.2)
  rw [hf, hf]

theorem addition_homology_natural (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) (n : ℕ) :
    (singularHomologyMap f n).comp (singularHomologyMap (additionMap G) n) =
      (singularHomologyMap (additionMap H) n).comp
        (singularHomologyMap (f.prodMap f) n) := by
  rw [← singularHomologyMap_comp, additionMap_natural f hf, singularHomologyMap_comp]

end Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin
