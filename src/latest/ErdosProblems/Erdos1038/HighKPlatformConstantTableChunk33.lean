import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 33 through 33. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk33

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_033 :
    geometryCheck (table.cell ⟨33, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_033 :
    crossingCheck (table.cell ⟨33, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_033 :
    scalarCheck (table.cell ⟨33, by decide⟩) = true := by
  kernel_decide

theorem certificate_033 :
    Certificate (table.cell ⟨33, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_033,
    crossing_of_check crossingCheck_033,
    scalar_of_check scalarCheck_033⟩

end Erdos1038.HighKPlatformConstantTableChunk33
