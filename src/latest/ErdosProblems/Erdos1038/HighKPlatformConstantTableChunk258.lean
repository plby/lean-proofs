import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 258 through 258. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk258

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_258 :
    geometryCheck (table.cell ⟨258, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_258 :
    crossingCheck (table.cell ⟨258, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_258 :
    scalarCheck (table.cell ⟨258, by decide⟩) = true := by
  kernel_decide

theorem certificate_258 :
    Certificate (table.cell ⟨258, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_258,
    crossing_of_check crossingCheck_258,
    scalar_of_check scalarCheck_258⟩

end Erdos1038.HighKPlatformConstantTableChunk258
