import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 216 through 216. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk216

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_216 :
    geometryCheck (table.cell ⟨216, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_216 :
    crossingCheck (table.cell ⟨216, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_216 :
    scalarCheck (table.cell ⟨216, by decide⟩) = true := by
  kernel_decide

theorem certificate_216 :
    Certificate (table.cell ⟨216, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_216,
    crossing_of_check crossingCheck_216,
    scalar_of_check scalarCheck_216⟩

end Erdos1038.HighKPlatformConstantTableChunk216
