import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 19 through 19. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk19

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_019 :
    geometryCheck (table.cell ⟨19, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_019 :
    crossingCheck (table.cell ⟨19, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_019 :
    scalarCheck (table.cell ⟨19, by decide⟩) = true := by
  kernel_decide

theorem certificate_019 :
    Certificate (table.cell ⟨19, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_019,
    crossing_of_check crossingCheck_019,
    scalar_of_check scalarCheck_019⟩

end Erdos1038.HighKPlatformConstantTableChunk19
