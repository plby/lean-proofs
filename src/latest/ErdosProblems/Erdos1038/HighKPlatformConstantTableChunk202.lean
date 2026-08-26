import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 202 through 202. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk202

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_202 :
    geometryCheck (table.cell ⟨202, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_202 :
    crossingCheck (table.cell ⟨202, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_202 :
    scalarCheck (table.cell ⟨202, by decide⟩) = true := by
  kernel_decide

theorem certificate_202 :
    Certificate (table.cell ⟨202, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_202,
    crossing_of_check crossingCheck_202,
    scalar_of_check scalarCheck_202⟩

end Erdos1038.HighKPlatformConstantTableChunk202
