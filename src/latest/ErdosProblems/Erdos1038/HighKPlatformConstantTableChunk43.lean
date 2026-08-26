import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 43 through 43. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk43

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_043 :
    geometryCheck (table.cell ⟨43, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_043 :
    crossingCheck (table.cell ⟨43, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_043 :
    scalarCheck (table.cell ⟨43, by decide⟩) = true := by
  kernel_decide

theorem certificate_043 :
    Certificate (table.cell ⟨43, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_043,
    crossing_of_check crossingCheck_043,
    scalar_of_check scalarCheck_043⟩

end Erdos1038.HighKPlatformConstantTableChunk43
