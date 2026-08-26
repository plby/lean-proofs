import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 654 through 654. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk654

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_654 :
    geometryCheck (table.cell ⟨654, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_654 :
    crossingCheck (table.cell ⟨654, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_654 :
    scalarCheck (table.cell ⟨654, by decide⟩) = true := by
  kernel_decide

theorem certificate_654 :
    Certificate (table.cell ⟨654, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_654,
    crossing_of_check crossingCheck_654,
    scalar_of_check scalarCheck_654⟩

end Erdos1038.HighKPlatformConstantTableChunk654
