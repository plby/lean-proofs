import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 399 through 399. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk399

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_399 :
    geometryCheck (table.cell ⟨399, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_399 :
    crossingCheck (table.cell ⟨399, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_399 :
    scalarCheck (table.cell ⟨399, by decide⟩) = true := by
  kernel_decide

theorem certificate_399 :
    Certificate (table.cell ⟨399, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_399,
    crossing_of_check crossingCheck_399,
    scalar_of_check scalarCheck_399⟩

end Erdos1038.HighKPlatformConstantTableChunk399
