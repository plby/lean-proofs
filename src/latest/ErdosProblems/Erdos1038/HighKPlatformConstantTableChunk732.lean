import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 732 through 732. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk732

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_732 :
    geometryCheck (table.cell ⟨732, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_732 :
    crossingCheck (table.cell ⟨732, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_732 :
    scalarCheck (table.cell ⟨732, by decide⟩) = true := by
  kernel_decide

theorem certificate_732 :
    Certificate (table.cell ⟨732, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_732,
    crossing_of_check crossingCheck_732,
    scalar_of_check scalarCheck_732⟩

end Erdos1038.HighKPlatformConstantTableChunk732
