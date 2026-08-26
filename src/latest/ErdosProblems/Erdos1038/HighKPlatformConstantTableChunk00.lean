import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 0 through 0. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk00

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_000 :
    geometryCheck (table.cell ⟨0, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_000 :
    crossingCheck (table.cell ⟨0, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_000 :
    scalarCheck (table.cell ⟨0, by decide⟩) = true := by
  kernel_decide

theorem certificate_000 :
    Certificate (table.cell ⟨0, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_000,
    crossing_of_check crossingCheck_000,
    scalar_of_check scalarCheck_000⟩

end Erdos1038.HighKPlatformConstantTableChunk00
