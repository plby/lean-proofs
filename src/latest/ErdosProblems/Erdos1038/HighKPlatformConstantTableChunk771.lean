import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 771 through 771. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk771

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_771 :
    geometryCheck (table.cell ⟨771, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_771 :
    crossingCheck (table.cell ⟨771, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_771 :
    scalarCheck (table.cell ⟨771, by decide⟩) = true := by
  kernel_decide

theorem certificate_771 :
    Certificate (table.cell ⟨771, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_771,
    crossing_of_check crossingCheck_771,
    scalar_of_check scalarCheck_771⟩

end Erdos1038.HighKPlatformConstantTableChunk771
