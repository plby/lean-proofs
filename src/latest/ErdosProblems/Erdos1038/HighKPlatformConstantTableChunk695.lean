import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 695 through 695. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk695

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_695 :
    geometryCheck (table.cell ⟨695, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_695 :
    crossingCheck (table.cell ⟨695, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_695 :
    scalarCheck (table.cell ⟨695, by decide⟩) = true := by
  kernel_decide

theorem certificate_695 :
    Certificate (table.cell ⟨695, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_695,
    crossing_of_check crossingCheck_695,
    scalar_of_check scalarCheck_695⟩

end Erdos1038.HighKPlatformConstantTableChunk695
