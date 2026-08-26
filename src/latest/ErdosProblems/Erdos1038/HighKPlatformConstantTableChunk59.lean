import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 59 through 59. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk59

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_059 :
    geometryCheck (table.cell ⟨59, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_059 :
    crossingCheck (table.cell ⟨59, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_059 :
    scalarCheck (table.cell ⟨59, by decide⟩) = true := by
  kernel_decide

theorem certificate_059 :
    Certificate (table.cell ⟨59, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_059,
    crossing_of_check crossingCheck_059,
    scalar_of_check scalarCheck_059⟩

end Erdos1038.HighKPlatformConstantTableChunk59
