import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 624 through 624. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk624

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_624 :
    geometryCheck (table.cell ⟨624, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_624 :
    crossingCheck (table.cell ⟨624, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_624 :
    scalarCheck (table.cell ⟨624, by decide⟩) = true := by
  kernel_decide

theorem certificate_624 :
    Certificate (table.cell ⟨624, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_624,
    crossing_of_check crossingCheck_624,
    scalar_of_check scalarCheck_624⟩

end Erdos1038.HighKPlatformConstantTableChunk624
