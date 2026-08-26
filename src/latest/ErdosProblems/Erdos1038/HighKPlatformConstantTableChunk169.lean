import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 169 through 169. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk169

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_169 :
    geometryCheck (table.cell ⟨169, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_169 :
    crossingCheck (table.cell ⟨169, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_169 :
    scalarCheck (table.cell ⟨169, by decide⟩) = true := by
  kernel_decide

theorem certificate_169 :
    Certificate (table.cell ⟨169, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_169,
    crossing_of_check crossingCheck_169,
    scalar_of_check scalarCheck_169⟩

end Erdos1038.HighKPlatformConstantTableChunk169
