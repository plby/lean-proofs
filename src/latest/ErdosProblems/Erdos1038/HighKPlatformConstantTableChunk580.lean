import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 580 through 580. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk580

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_580 :
    geometryCheck (table.cell ⟨580, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_580 :
    crossingCheck (table.cell ⟨580, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_580 :
    scalarCheck (table.cell ⟨580, by decide⟩) = true := by
  kernel_decide

theorem certificate_580 :
    Certificate (table.cell ⟨580, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_580,
    crossing_of_check crossingCheck_580,
    scalar_of_check scalarCheck_580⟩

end Erdos1038.HighKPlatformConstantTableChunk580
