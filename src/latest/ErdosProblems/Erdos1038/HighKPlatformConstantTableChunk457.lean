import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 457 through 457. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk457

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_457 :
    geometryCheck (table.cell ⟨457, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_457 :
    crossingCheck (table.cell ⟨457, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_457 :
    scalarCheck (table.cell ⟨457, by decide⟩) = true := by
  kernel_decide

theorem certificate_457 :
    Certificate (table.cell ⟨457, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_457,
    crossing_of_check crossingCheck_457,
    scalar_of_check scalarCheck_457⟩

end Erdos1038.HighKPlatformConstantTableChunk457
