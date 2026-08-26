import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 233 through 233. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk233

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_233 :
    geometryCheck (table.cell ⟨233, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_233 :
    crossingCheck (table.cell ⟨233, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_233 :
    scalarCheck (table.cell ⟨233, by decide⟩) = true := by
  kernel_decide

theorem certificate_233 :
    Certificate (table.cell ⟨233, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_233,
    crossing_of_check crossingCheck_233,
    scalar_of_check scalarCheck_233⟩

end Erdos1038.HighKPlatformConstantTableChunk233
