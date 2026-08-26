import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 730 through 730. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk730

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_730 :
    geometryCheck (table.cell ⟨730, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_730 :
    crossingCheck (table.cell ⟨730, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_730 :
    scalarCheck (table.cell ⟨730, by decide⟩) = true := by
  kernel_decide

theorem certificate_730 :
    Certificate (table.cell ⟨730, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_730,
    crossing_of_check crossingCheck_730,
    scalar_of_check scalarCheck_730⟩

end Erdos1038.HighKPlatformConstantTableChunk730
