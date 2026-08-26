import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 547 through 547. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk547

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_547 :
    geometryCheck (table.cell ⟨547, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_547 :
    crossingCheck (table.cell ⟨547, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_547 :
    scalarCheck (table.cell ⟨547, by decide⟩) = true := by
  kernel_decide

theorem certificate_547 :
    Certificate (table.cell ⟨547, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_547,
    crossing_of_check crossingCheck_547,
    scalar_of_check scalarCheck_547⟩

end Erdos1038.HighKPlatformConstantTableChunk547
