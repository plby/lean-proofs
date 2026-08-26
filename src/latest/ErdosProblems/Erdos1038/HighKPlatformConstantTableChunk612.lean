import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 612 through 612. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk612

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_612 :
    geometryCheck (table.cell ⟨612, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_612 :
    crossingCheck (table.cell ⟨612, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_612 :
    scalarCheck (table.cell ⟨612, by decide⟩) = true := by
  kernel_decide

theorem certificate_612 :
    Certificate (table.cell ⟨612, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_612,
    crossing_of_check crossingCheck_612,
    scalar_of_check scalarCheck_612⟩

end Erdos1038.HighKPlatformConstantTableChunk612
