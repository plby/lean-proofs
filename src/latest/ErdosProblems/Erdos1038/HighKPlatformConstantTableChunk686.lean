import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 686 through 686. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk686

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_686 :
    geometryCheck (table.cell ⟨686, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_686 :
    crossingCheck (table.cell ⟨686, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_686 :
    scalarCheck (table.cell ⟨686, by decide⟩) = true := by
  kernel_decide

theorem certificate_686 :
    Certificate (table.cell ⟨686, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_686,
    crossing_of_check crossingCheck_686,
    scalar_of_check scalarCheck_686⟩

end Erdos1038.HighKPlatformConstantTableChunk686
