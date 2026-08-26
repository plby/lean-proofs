import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 8 through 8. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk08

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_008 :
    geometryCheck (table.cell ⟨8, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_008 :
    crossingCheck (table.cell ⟨8, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_008 :
    scalarCheck (table.cell ⟨8, by decide⟩) = true := by
  kernel_decide

theorem certificate_008 :
    Certificate (table.cell ⟨8, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_008,
    crossing_of_check crossingCheck_008,
    scalar_of_check scalarCheck_008⟩

end Erdos1038.HighKPlatformConstantTableChunk08
