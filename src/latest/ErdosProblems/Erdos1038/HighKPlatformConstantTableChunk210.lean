import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 210 through 210. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk210

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_210 :
    geometryCheck (table.cell ⟨210, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_210 :
    crossingCheck (table.cell ⟨210, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_210 :
    scalarCheck (table.cell ⟨210, by decide⟩) = true := by
  kernel_decide

theorem certificate_210 :
    Certificate (table.cell ⟨210, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_210,
    crossing_of_check crossingCheck_210,
    scalar_of_check scalarCheck_210⟩

end Erdos1038.HighKPlatformConstantTableChunk210
