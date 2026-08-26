import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 644 through 644. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk644

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_644 :
    geometryCheck (table.cell ⟨644, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_644 :
    crossingCheck (table.cell ⟨644, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_644 :
    scalarCheck (table.cell ⟨644, by decide⟩) = true := by
  kernel_decide

theorem certificate_644 :
    Certificate (table.cell ⟨644, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_644,
    crossing_of_check crossingCheck_644,
    scalar_of_check scalarCheck_644⟩

end Erdos1038.HighKPlatformConstantTableChunk644
