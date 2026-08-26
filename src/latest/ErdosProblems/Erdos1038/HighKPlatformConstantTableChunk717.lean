import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 717 through 717. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk717

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_717 :
    geometryCheck (table.cell ⟨717, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_717 :
    crossingCheck (table.cell ⟨717, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_717 :
    scalarCheck (table.cell ⟨717, by decide⟩) = true := by
  kernel_decide

theorem certificate_717 :
    Certificate (table.cell ⟨717, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_717,
    crossing_of_check crossingCheck_717,
    scalar_of_check scalarCheck_717⟩

end Erdos1038.HighKPlatformConstantTableChunk717
