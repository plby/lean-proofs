import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 110 through 110. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk110

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_110 :
    geometryCheck (table.cell ⟨110, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_110 :
    crossingCheck (table.cell ⟨110, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_110 :
    scalarCheck (table.cell ⟨110, by decide⟩) = true := by
  kernel_decide

theorem certificate_110 :
    Certificate (table.cell ⟨110, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_110,
    crossing_of_check crossingCheck_110,
    scalar_of_check scalarCheck_110⟩

end Erdos1038.HighKPlatformConstantTableChunk110
