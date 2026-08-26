import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 304 through 304. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk304

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_304 :
    geometryCheck (table.cell ⟨304, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_304 :
    crossingCheck (table.cell ⟨304, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_304 :
    scalarCheck (table.cell ⟨304, by decide⟩) = true := by
  kernel_decide

theorem certificate_304 :
    Certificate (table.cell ⟨304, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_304,
    crossing_of_check crossingCheck_304,
    scalar_of_check scalarCheck_304⟩

end Erdos1038.HighKPlatformConstantTableChunk304
