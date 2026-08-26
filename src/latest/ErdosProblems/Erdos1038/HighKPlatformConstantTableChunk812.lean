import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 812 through 812. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk812

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_812 :
    geometryCheck (table.cell ⟨812, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_812 :
    crossingCheck (table.cell ⟨812, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_812 :
    scalarCheck (table.cell ⟨812, by decide⟩) = true := by
  kernel_decide

theorem certificate_812 :
    Certificate (table.cell ⟨812, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_812,
    crossing_of_check crossingCheck_812,
    scalar_of_check scalarCheck_812⟩

end Erdos1038.HighKPlatformConstantTableChunk812
