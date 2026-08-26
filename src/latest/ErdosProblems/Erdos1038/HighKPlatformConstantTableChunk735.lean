import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 735 through 735. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk735

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_735 :
    geometryCheck (table.cell ⟨735, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_735 :
    crossingCheck (table.cell ⟨735, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_735 :
    scalarCheck (table.cell ⟨735, by decide⟩) = true := by
  kernel_decide

theorem certificate_735 :
    Certificate (table.cell ⟨735, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_735,
    crossing_of_check crossingCheck_735,
    scalar_of_check scalarCheck_735⟩

end Erdos1038.HighKPlatformConstantTableChunk735
