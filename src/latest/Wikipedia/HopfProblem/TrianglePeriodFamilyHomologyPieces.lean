import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyCharts
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyProducts
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsPeriod

/-!
# Actual homology of the regular-family cover pieces

The already constructed product charts and actual contractions of the
slit factors give homotopy equivalences from all five cover pieces to
the real torus. Their singular-homology markings use the literal second
projection. Consequently the upper overlap inclusions induce identity
maps, while the lower ones induce the actual constant triangle-torus
maps, in every degree.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris
open PeriodTorusHigherHomology PeriodTorusHigherHomology.CircleTopology

variable (D : Data ℂ TriangleRegularPoint) (b : SlitBaseLift)

/-- The actual upper cover member retracts to the unchanged torus factor. -/
def upperHomotopyEquiv : upperFamily D ≃ₕ RealTorus₄ :=
  (upperChart D b).toHomotopyEquiv.trans
    (contractibleProdHomotopyEquiv upperBase RealTorus₄)

/-- The actual lower cover member has the same torus homotopy type. -/
def lowerHomotopyEquiv : lowerFamily D ≃ₕ RealTorus₄ :=
  (lowerChart D b).toHomotopyEquiv.trans
    (contractibleProdHomotopyEquiv lowerBase RealTorus₄)

/-- Each actual overlap component retracts to its upper-chart torus factor. -/
def overlapHomotopyEquiv (i : Fin 3) : overlapFamily D i ≃ₕ RealTorus₄ :=
  (overlapChart D b i).toHomotopyEquiv.trans
    (contractibleProdHomotopyEquiv (overlapBase i) RealTorus₄)

@[simp] theorem upperHomotopyEquiv_apply (x : upperFamily D) :
    upperHomotopyEquiv D b x = (upperChart D b x).2 := rfl

@[simp] theorem lowerHomotopyEquiv_apply (x : lowerFamily D) :
    lowerHomotopyEquiv D b x = (lowerChart D b x).2 := rfl

@[simp] theorem overlapHomotopyEquiv_apply (i : Fin 3) (x : overlapFamily D i) :
    overlapHomotopyEquiv D b i x = (overlapChart D b i x).2 := rfl

/-- The upper diagram commutes as actual continuous maps before passing to homology. -/
theorem upperHomotopyEquiv_comp_overlap (i : Fin 3) :
    (upperHomotopyEquiv D b).toFun.comp (overlapFamilyToUpper D i) =
      (overlapHomotopyEquiv D b i).toFun := by
  apply ContinuousMap.ext
  intro x
  exact congrArg Prod.snd (upperChart_overlapFamilyToUpper D b i x)

/-- The lower diagram has the actual triangle action as its fibre map. -/
theorem lowerHomotopyEquiv_comp_overlap (i : Fin 3) :
    (lowerHomotopyEquiv D b).toFun.comp (overlapFamilyToLower D i) =
      (triangleTorusHomeomorph (overlapTransition b i) : C(RealTorus₄, RealTorus₄)).comp
        (overlapHomotopyEquiv D b i).toFun := by
  apply ContinuousMap.ext
  intro x
  exact congrArg Prod.snd (lowerChart_overlapFamilyToLower D b i x)

/-- The actual singular-homology marking of the upper cover member in every degree. -/
def upperHomologyEquiv (n : ℕ) :
    SingularHomology (upperFamily D) n ≃ₗ[ℤ] SingularHomology RealTorus₄ n :=
  homotopyEquivHomologyEquiv (upperHomotopyEquiv D b) n

/-- The actual singular-homology marking of the lower cover member in every degree. -/
def lowerHomologyEquiv (n : ℕ) :
    SingularHomology (lowerFamily D) n ≃ₗ[ℤ] SingularHomology RealTorus₄ n :=
  homotopyEquivHomologyEquiv (lowerHomotopyEquiv D b) n

/-- The actual homology marking of each overlap component. -/
def overlapHomologyEquiv (i : Fin 3) (n : ℕ) :
    SingularHomology (overlapFamily D i) n ≃ₗ[ℤ] SingularHomology RealTorus₄ n :=
  homotopyEquivHomologyEquiv (overlapHomotopyEquiv D b i) n

@[simp] theorem upperHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (upperFamily D) n) :
    upperHomologyEquiv D b n a = singularHomologyMap (upperHomotopyEquiv D b).toFun n a := rfl

@[simp] theorem lowerHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (lowerFamily D) n) :
    lowerHomologyEquiv D b n a = singularHomologyMap (lowerHomotopyEquiv D b).toFun n a := rfl

@[simp] theorem overlapHomologyEquiv_apply (i : Fin 3) (n : ℕ)
    (a : SingularHomology (overlapFamily D i) n) :
    overlapHomologyEquiv D b i n a =
      singularHomologyMap (overlapHomotopyEquiv D b i).toFun n a := rfl

/-- The upper overlap inclusion induces precisely the identity in the actual torus markings. -/
theorem upperHomologyEquiv_overlap (i : Fin 3) (n : ℕ)
    (a : SingularHomology (overlapFamily D i) n) :
    upperHomologyEquiv D b n (singularHomologyMap (overlapFamilyToUpper D i) n a) =
      overlapHomologyEquiv D b i n a := by
  rw [upperHomologyEquiv_apply, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    upperHomotopyEquiv_comp_overlap]
  rfl

/-- The lower inclusion induces the actual constant triangle-torus map in every degree. -/
theorem lowerHomologyEquiv_overlap (i : Fin 3) (n : ℕ)
    (a : SingularHomology (overlapFamily D i) n) :
    lowerHomologyEquiv D b n (singularHomologyMap (overlapFamilyToLower D i) n a) =
      singularHomologyMap
        (triangleTorusHomeomorph (overlapTransition b i) : C(RealTorus₄, RealTorus₄)) n
        (overlapHomologyEquiv D b i n a) := by
  rw [lowerHomologyEquiv_apply, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    lowerHomotopyEquiv_comp_overlap, singularHomologyMap_comp]
  rfl

/-- The genuine pair of homology markings on the two members of the open cover. -/
def pairHomologyEquiv (n : ℕ) :
    (SingularHomology (upperFamily D) n × SingularHomology (lowerFamily D) n) ≃ₗ[ℤ]
      (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) :=
  ((upperHomologyEquiv D b n).toAddEquiv.prodCongr
    (lowerHomologyEquiv D b n).toAddEquiv).toIntLinearEquiv

@[simp] theorem pairHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (upperFamily D) n × SingularHomology (lowerFamily D) n) :
    pairHomologyEquiv D b n a =
      (upperHomologyEquiv D b n a.1, lowerHomologyEquiv D b n a.2) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
