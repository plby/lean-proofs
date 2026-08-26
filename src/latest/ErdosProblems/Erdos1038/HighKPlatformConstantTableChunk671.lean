import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 671 through 671. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk671

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_671 :
    geometryCheck (table.cell ⟨671, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_671 :
    crossingCheck (table.cell ⟨671, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_671 :
    scalarCheck (table.cell ⟨671, by decide⟩) = true := by
  kernel_decide

theorem certificate_671 :
    Certificate (table.cell ⟨671, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_671,
    crossing_of_check crossingCheck_671,
    scalar_of_check scalarCheck_671⟩

end Erdos1038.HighKPlatformConstantTableChunk671
