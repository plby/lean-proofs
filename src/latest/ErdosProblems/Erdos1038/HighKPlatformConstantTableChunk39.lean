import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 39 through 39. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk39

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_039 :
    geometryCheck (table.cell ⟨39, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_039 :
    crossingCheck (table.cell ⟨39, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_039 :
    scalarCheck (table.cell ⟨39, by decide⟩) = true := by
  kernel_decide

theorem certificate_039 :
    Certificate (table.cell ⟨39, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_039,
    crossing_of_check crossingCheck_039,
    scalar_of_check scalarCheck_039⟩

end Erdos1038.HighKPlatformConstantTableChunk39
