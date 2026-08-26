import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 698 through 698. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk698

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_698 :
    geometryCheck (table.cell ⟨698, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_698 :
    crossingCheck (table.cell ⟨698, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_698 :
    scalarCheck (table.cell ⟨698, by decide⟩) = true := by
  kernel_decide

theorem certificate_698 :
    Certificate (table.cell ⟨698, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_698,
    crossing_of_check crossingCheck_698,
    scalar_of_check scalarCheck_698⟩

end Erdos1038.HighKPlatformConstantTableChunk698
