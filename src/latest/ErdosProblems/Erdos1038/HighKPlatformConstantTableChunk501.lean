import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 501 through 501. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk501

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_501 :
    geometryCheck (table.cell ⟨501, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_501 :
    crossingCheck (table.cell ⟨501, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_501 :
    scalarCheck (table.cell ⟨501, by decide⟩) = true := by
  kernel_decide

theorem certificate_501 :
    Certificate (table.cell ⟨501, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_501,
    crossing_of_check crossingCheck_501,
    scalar_of_check scalarCheck_501⟩

end Erdos1038.HighKPlatformConstantTableChunk501
