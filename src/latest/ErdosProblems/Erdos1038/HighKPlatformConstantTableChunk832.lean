import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 832 through 832. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk832

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_832 :
    geometryCheck (table.cell ⟨832, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_832 :
    crossingCheck (table.cell ⟨832, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_832 :
    scalarCheck (table.cell ⟨832, by decide⟩) = true := by
  kernel_decide

theorem certificate_832 :
    Certificate (table.cell ⟨832, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_832,
    crossing_of_check crossingCheck_832,
    scalar_of_check scalarCheck_832⟩

end Erdos1038.HighKPlatformConstantTableChunk832
