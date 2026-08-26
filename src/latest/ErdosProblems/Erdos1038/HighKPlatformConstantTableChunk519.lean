import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 519 through 519. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk519

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_519 :
    geometryCheck (table.cell ⟨519, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_519 :
    crossingCheck (table.cell ⟨519, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_519 :
    scalarCheck (table.cell ⟨519, by decide⟩) = true := by
  kernel_decide

theorem certificate_519 :
    Certificate (table.cell ⟨519, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_519,
    crossing_of_check crossingCheck_519,
    scalar_of_check scalarCheck_519⟩

end Erdos1038.HighKPlatformConstantTableChunk519
