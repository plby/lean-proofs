import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 214 through 214. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk214

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_214 :
    geometryCheck (table.cell ⟨214, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_214 :
    crossingCheck (table.cell ⟨214, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_214 :
    scalarCheck (table.cell ⟨214, by decide⟩) = true := by
  kernel_decide

theorem certificate_214 :
    Certificate (table.cell ⟨214, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_214,
    crossing_of_check crossingCheck_214,
    scalar_of_check scalarCheck_214⟩

end Erdos1038.HighKPlatformConstantTableChunk214
