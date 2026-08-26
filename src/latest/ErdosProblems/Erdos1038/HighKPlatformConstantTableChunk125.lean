import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 125 through 125. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk125

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_125 :
    geometryCheck (table.cell ⟨125, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_125 :
    crossingCheck (table.cell ⟨125, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_125 :
    scalarCheck (table.cell ⟨125, by decide⟩) = true := by
  kernel_decide

theorem certificate_125 :
    Certificate (table.cell ⟨125, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_125,
    crossing_of_check crossingCheck_125,
    scalar_of_check scalarCheck_125⟩

end Erdos1038.HighKPlatformConstantTableChunk125
