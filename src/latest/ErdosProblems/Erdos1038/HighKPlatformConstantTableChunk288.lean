import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 288 through 288. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk288

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_288 :
    geometryCheck (table.cell ⟨288, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_288 :
    crossingCheck (table.cell ⟨288, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_288 :
    scalarCheck (table.cell ⟨288, by decide⟩) = true := by
  kernel_decide

theorem certificate_288 :
    Certificate (table.cell ⟨288, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_288,
    crossing_of_check crossingCheck_288,
    scalar_of_check scalarCheck_288⟩

end Erdos1038.HighKPlatformConstantTableChunk288
