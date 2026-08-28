import Wikipedia.HopfProblem.EllipticQuotientFibration
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusQuotient

/-!
# Comparing the two genuine orbit quotients

An equivariant open quotient between the original covering spaces descends
through their given group actions.  Its fibres downstairs are exactly the
descended fibres upstairs.  This is used with the literal fourth-coordinate
circle quotient, retaining the complete finite elliptic action.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit.QuotientModel

open Elliptic

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
  (q : X → Y) (he : ∀ (g : G) (x : X), q (g • x) = g • q x)

/-- The map induced between the two actual group orbit quotients. -/
def orbitMap : FiniteQuotient.Space G X → FiniteQuotient.Space G Y :=
  FiniteQuotient.descend (FiniteQuotient.project G Y ∘ q) (by
    intro g x
    change FiniteQuotient.project G Y (q (g • x)) = FiniteQuotient.project G Y (q x)
    rw [he, FiniteQuotient.project_smul])

@[simp] theorem orbitMap_project (x : X) :
    orbitMap q he (FiniteQuotient.project G X x) = FiniteQuotient.project G Y (q x) := rfl

theorem orbitMap_surjective (hq : Function.Surjective q) :
    Function.Surjective (orbitMap q he) := by
  intro y
  obtain ⟨z, rfl⟩ := FiniteQuotient.project_surjective G Y y
  obtain ⟨x, rfl⟩ := hq z
  exact ⟨FiniteQuotient.project G X x, rfl⟩

section Topology

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem orbitMap_continuous (hq : Continuous q) : Continuous (orbitMap q he) :=
  (FiniteQuotient.project_isQuotientMap G X).continuous_iff.mpr
    ((FiniteQuotient.project_continuous G Y).comp hq)

/-- Openness is proved using the actual quotient topologies on both sides. -/
theorem orbitMap_isOpenQuotientMap [ContinuousConstSMul G Y]
    (hq : IsOpenQuotientMap q) : IsOpenQuotientMap (orbitMap q he) := by
  refine ⟨orbitMap_surjective q he hq.surjective,
    orbitMap_continuous q he hq.continuous, ?_⟩
  apply IsOpenMap.of_comp (FiniteQuotient.project_continuous G X)
    (FiniteQuotient.project_surjective G X)
  exact (FiniteQuotient.project_isOpenQuotientMap G Y).isOpenMap.comp hq.isOpenMap

end Topology

variable {H : Type*}
  (shift : H → X → X)
  (shiftQ : H → FiniteQuotient.Space G X → FiniteQuotient.Space G X)
  (hshift : ∀ d x, shiftQ d (FiniteQuotient.project G X x) =
    FiniteQuotient.project G X (shift d x))
  (hfibre : ∀ x y, q x = q y ↔ ∃ d, shift d y = x)

include hshift hfibre in
/-- The induced quotient map has exactly the original descended shift-orbits
as its fibres. No freeness or unproved orbit classification is assumed. -/
theorem orbitMap_eq_iff_shift (x y : FiniteQuotient.Space G X) :
    orbitMap q he x = orbitMap q he y ↔ ∃ d, shiftQ d y = x := by
  obtain ⟨u, rfl⟩ := FiniteQuotient.project_surjective G X x
  obtain ⟨v, rfl⟩ := FiniteQuotient.project_surjective G X y
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (FiniteQuotient.project_eq_iff_mem_orbit G Y (q u) (q v)).mp h
    have hq : q u = q (g • v) := by
      rw [he]
      exact hg.symm
    obtain ⟨d, hd⟩ := (hfibre u (g • v)).mp hq
    refine ⟨d, ?_⟩
    calc
      shiftQ d (FiniteQuotient.project G X v) =
          shiftQ d (FiniteQuotient.project G X (g • v)) := by
            rw [FiniteQuotient.project_smul]
      _ = FiniteQuotient.project G X (shift d (g • v)) := hshift d _
      _ = FiniteQuotient.project G X u := congrArg (FiniteQuotient.project G X) hd
  · rintro ⟨d, hd⟩
    rw [← hd, hshift, orbitMap_project, orbitMap_project]
    exact congrArg (FiniteQuotient.project G Y)
      ((hfibre (shift d v) v).mpr ⟨d, rfl⟩)

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit.QuotientModel
