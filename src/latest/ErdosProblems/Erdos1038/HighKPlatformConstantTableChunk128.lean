import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 128 through 128. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk128

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_128 :
    geometryCheck (table.cell ⟨128, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_128 :
    crossingCheck (table.cell ⟨128, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_128 :
    scalarCheck (table.cell ⟨128, by decide⟩) = true := by
  kernel_decide

theorem certificate_128 :
    Certificate (table.cell ⟨128, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_128,
    crossing_of_check crossingCheck_128,
    scalar_of_check scalarCheck_128⟩

end Erdos1038.HighKPlatformConstantTableChunk128
