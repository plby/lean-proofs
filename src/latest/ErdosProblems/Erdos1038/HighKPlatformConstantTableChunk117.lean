import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 117 through 117. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk117

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_117 :
    geometryCheck (table.cell ⟨117, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_117 :
    crossingCheck (table.cell ⟨117, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_117 :
    scalarCheck (table.cell ⟨117, by decide⟩) = true := by
  kernel_decide

theorem certificate_117 :
    Certificate (table.cell ⟨117, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_117,
    crossing_of_check crossingCheck_117,
    scalar_of_check scalarCheck_117⟩

end Erdos1038.HighKPlatformConstantTableChunk117
