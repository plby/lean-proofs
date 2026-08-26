import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 69 through 69. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk69

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_069 :
    geometryCheck (table.cell ⟨69, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_069 :
    crossingCheck (table.cell ⟨69, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_069 :
    scalarCheck (table.cell ⟨69, by decide⟩) = true := by
  kernel_decide

theorem certificate_069 :
    Certificate (table.cell ⟨69, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_069,
    crossing_of_check crossingCheck_069,
    scalar_of_check scalarCheck_069⟩

end Erdos1038.HighKPlatformConstantTableChunk69
