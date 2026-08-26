import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 148 through 148. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk148

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_148 :
    geometryCheck (table.cell ⟨148, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_148 :
    crossingCheck (table.cell ⟨148, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_148 :
    scalarCheck (table.cell ⟨148, by decide⟩) = true := by
  kernel_decide

theorem certificate_148 :
    Certificate (table.cell ⟨148, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_148,
    crossing_of_check crossingCheck_148,
    scalar_of_check scalarCheck_148⟩

end Erdos1038.HighKPlatformConstantTableChunk148
