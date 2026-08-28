import Wikipedia.HopfProblem.MappingTorusHomologyCoveringCharts
import Wikipedia.HopfProblem.MappingTorusHomologyCoveringMap
import Wikipedia.HopfProblem.MappingTorusHomologyCoveringCircleArcs
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProductDefinition

/-!
# The actual cyclic covering on subdivided cross-chains

On each of the finitely many lifted circle arcs, the given covering map
is exactly the corresponding strip in the actual mapping-torus chart.
Functoriality of the genuine singular cross product therefore identifies
the ambient images of the charted cross-chains with the covering image
of the subdivided positive circle cycle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.MappingTorusHomology.Covering

open MappingTorus MappingTorus.HomologyCover
open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X]

/-- The first small circle arc, as an actual continuous map of the interval. -/
def uCircleMap (m k : ℕ) : C(unitInterval, Circle) :=
  ⟨uPath m k, (uPath m k).continuous⟩

/-- The second small circle arc, with its unchanged interval parametrization. -/
def vCircleMap (m k : ℕ) : C(unitInterval, Circle) :=
  ⟨vPath m k, (vPath m k).continuous⟩

@[simp] theorem uCircleMap_pathChain (m k : ℕ) :
    inducedChain (uCircleMap m k) 1 (pathChain Path.id) = pathChain (uPath m k) := by
  rw [inducedChain_pathChain]
  rfl

@[simp] theorem vCircleMap_pathChain (m k : ℕ) :
    inducedChain (vCircleMap m k) 1 (pathChain Path.id) = pathChain (vPath m k) := by
  rw [inducedChain_pathChain]
  rfl

variable [CompactSpace X] [T2Space X]
  (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)

/-- On the first lifted arc the actual cyclic map is the first charted strip. -/
theorem productCover_uCircleMap (k : ℕ) :
    (productCover m B hB).comp ((uCircleMap m k).prodMap (ContinuousMap.id X)) =
      (inclusionU B.symm).comp (uStrip B.symm k) := by
  apply ContinuousMap.ext
  intro p
  change productCover m B hB (uPath m k p.1, p.2) = (uStrip B.symm k p : Torus B.symm)
  rw [uPath_apply, productCover_real_apply, uStrip_val]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [div_mul_cancel₀ _ hm]
  have ht : (k : ℝ) + 1 / 4 + (p.1 : ℝ) / 2 =
      (1 / 4 : ℝ) + (p.1 : ℝ) / 2 + ((k : ℤ) : ℝ) := by
    push_cast
    ring
  rw [ht, mk_add_int]
  simp only [zpow_natCast]

/-- The return arc uses the next monodromy iterate in the second chart. -/
theorem productCover_vCircleMap (k : ℕ) :
    (productCover m B hB).comp ((vCircleMap m k).prodMap (ContinuousMap.id X)) =
      (inclusionV B.symm).comp (vStrip B.symm k) := by
  apply ContinuousMap.ext
  intro p
  change productCover m B hB (vPath m k p.1, p.2) = (vStrip B.symm k p : Torus B.symm)
  rw [vPath_apply, productCover_real_apply, vStrip_val]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [div_mul_cancel₀ _ hm]
  have ht : (k : ℝ) + 3 / 4 + (p.1 : ℝ) / 2 =
      -(1 / 4 : ℝ) + (p.1 : ℝ) / 2 + (((k + 1 : ℕ) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [ht, mk_add_int]
  simp only [zpow_natCast]

/-- The first strip chain has exactly the covering image of the actual
small circle-path cross-chain as its ambient image. -/
theorem uStrip_inclusion_crossProduct (k n : ℕ) (b : Chains X n) :
    inducedChain (inclusionU B.symm) (n + 1)
        (inducedChain (uStrip B.symm k) (n + 1)
          (crossProductEdge unitInterval X n (pathChain Path.id) b)) =
      inducedChain (productCover m B hB) (n + 1)
        (crossProductEdge Circle X n (pathChain (uPath m k)) b) := by
  have h := congrArg
    (fun F => inducedChain F (n + 1)
      (crossProductEdge unitInterval X n (pathChain Path.id) b))
    (productCover_uCircleMap m B hB k)
  simp only [inducedChain_comp, LinearMap.comp_apply, crossProductEdge_natural,
    inducedChain_id, LinearMap.id_apply, uCircleMap_pathChain] at h
  exact h.symm

/-- The same exact chain identity holds for each return strip. -/
theorem vStrip_inclusion_crossProduct (k n : ℕ) (b : Chains X n) :
    inducedChain (inclusionV B.symm) (n + 1)
        (inducedChain (vStrip B.symm k) (n + 1)
          (crossProductEdge unitInterval X n (pathChain Path.id) b)) =
      inducedChain (productCover m B hB) (n + 1)
        (crossProductEdge Circle X n (pathChain (vPath m k)) b) := by
  have h := congrArg
    (fun F => inducedChain F (n + 1)
      (crossProductEdge unitInterval X n (pathChain Path.id) b))
    (productCover_vCircleMap m B hB k)
  simp only [inducedChain_comp, LinearMap.comp_apply, crossProductEdge_natural,
    inducedChain_id, LinearMap.id_apply, vCircleMap_pathChain] at h
  exact h.symm

variable (n : ℕ) (b : ModuleHomology.Cycle (singularComplex X) n)

omit [CompactSpace X] [T2Space X] in
/-- The subdivided source cycle represents the same actual positive circle
cross product, before applying the cyclic covering. -/
theorem positiveCircleCross_subdivision_cycleClass :
    positiveCircleCross X n (ModuleHomology.cycleClass (singularComplex X) n b) =
      ModuleHomology.cycleClass (singularComplex (Circle × X)) (n + 1)
        (crossProductCycles Circle X n (arcSumCycle m) b) := by
  have h : ModuleHomology.cycleClass (singularComplex Circle) 1 (arcSumCycle m) =
      loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop :=
    arcSumCycle_positiveLoop_class m
  change crossProductHomology Circle X n
    (loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop)
    (ModuleHomology.cycleClass (singularComplex X) n b) = _
  rw [← h]
  exact crossProductHomology_cycleClass Circle X n (arcSumCycle m) b

end Wikipedia.HopfProblem.MappingTorusHomology.Covering
