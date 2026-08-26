import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 154 through 154. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk154

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_154 :
    geometryCheck (table.cell ⟨154, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_154 :
    crossingCheck (table.cell ⟨154, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_154 :
    scalarCheck (table.cell ⟨154, by decide⟩) = true := by
  kernel_decide

theorem certificate_154 :
    Certificate (table.cell ⟨154, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_154,
    crossing_of_check crossingCheck_154,
    scalar_of_check scalarCheck_154⟩

end Erdos1038.HighKPlatformConstantTableChunk154
