import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 183 through 183. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk183

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_183 :
    geometryCheck (table.cell ⟨183, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_183 :
    crossingCheck (table.cell ⟨183, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_183 :
    scalarCheck (table.cell ⟨183, by decide⟩) = true := by
  kernel_decide

theorem certificate_183 :
    Certificate (table.cell ⟨183, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_183,
    crossing_of_check crossingCheck_183,
    scalar_of_check scalarCheck_183⟩

end Erdos1038.HighKPlatformConstantTableChunk183
