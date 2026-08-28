import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairBodyNewEnd
import Wikipedia.HopfProblem.DegreeCollapseEmbeddedHandleHomology

/-!
# Both actual endpoint sequences for the same surgery-pair attachment

The old and new whole-handle presentations are constructed, not supplied
as extra assumptions. The two attaching maps in their sequences are the
original attaching sphere and the actual belt sphere of the given pair.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody

open Wikipedia.SmoothSixDPoincare PuncturedHandle MorseHandle
open SingularMayerVietoris

variable {E F R X Y : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace R] [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [CompactSpace Y] (d : SurgeryBoundaryPair E F R X Y)

def oldHandleData : EmbeddedHandle E F X (Space d) where
  oldMap := oldMap d
  handle := handleMap d
  old_closed := oldMap_closed d
  handle_closed := handleMap_closed d
  cover := old_cover d
  face := handle_mem_old_iff d
  attaching := d.attachingSphere
  boundary := core_boundary d

def newHandleData : EmbeddedHandle F E Y (Space d) where
  oldMap := newMap d
  handle := reverseHandle d
  old_closed := newMap_closed d
  handle_closed := reverseHandle_closed d
  cover := reverse_cover d
  face := reverseHandle_mem_new_iff d
  attaching := d.beltSphere
  boundary := reverseCore_boundary d

def oldConnecting (k : ℕ) :
    SingularHomology (Space d) (k + 1) →ₗ[ℤ] SingularHomology (UnitSphere E) k :=
  (oldHandleData d).connecting k

def newConnecting (k : ℕ) :
    SingularHomology (Space d) (k + 1) →ₗ[ℤ] SingularHomology (UnitSphere F) k :=
  (newHandleData d).connecting k

theorem exact_at_old (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (singularHomologyMap d.attachingSphere k) =
      LinearMap.ker (singularHomologyMap (oldMap d) k) :=
  (oldHandleData d).exact_at_old k hk

theorem exact_at_body_old (k : ℕ) :
    LinearMap.range (singularHomologyMap (oldMap d) (k + 1)) =
      LinearMap.ker (oldConnecting d k) :=
  (oldHandleData d).exact_at_ambient k

theorem exact_at_attaching (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (oldConnecting d k) =
      LinearMap.ker (singularHomologyMap d.attachingSphere k) :=
  (oldHandleData d).exact_at_sphere k hk

theorem exact_at_new (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (singularHomologyMap d.beltSphere k) =
      LinearMap.ker (singularHomologyMap (newMap d) k) :=
  (newHandleData d).exact_at_old k hk

theorem exact_at_body_new (k : ℕ) :
    LinearMap.range (singularHomologyMap (newMap d) (k + 1)) =
      LinearMap.ker (newConnecting d k) :=
  (newHandleData d).exact_at_ambient k

theorem exact_at_belt (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (newConnecting d k) =
      LinearMap.ker (singularHomologyMap d.beltSphere k) :=
  (newHandleData d).exact_at_sphere k hk

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryPairBody
