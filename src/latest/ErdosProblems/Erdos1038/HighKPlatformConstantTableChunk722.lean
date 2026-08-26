import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 722 through 722. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk722

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_722 :
    geometryCheck (table.cell ⟨722, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_722 :
    crossingCheck (table.cell ⟨722, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_722 :
    scalarCheck (table.cell ⟨722, by decide⟩) = true := by
  kernel_decide

theorem certificate_722 :
    Certificate (table.cell ⟨722, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_722,
    crossing_of_check crossingCheck_722,
    scalar_of_check scalarCheck_722⟩

end Erdos1038.HighKPlatformConstantTableChunk722
