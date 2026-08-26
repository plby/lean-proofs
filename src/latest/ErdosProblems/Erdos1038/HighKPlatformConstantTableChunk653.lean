import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 653 through 653. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk653

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_653 :
    geometryCheck (table.cell ⟨653, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_653 :
    crossingCheck (table.cell ⟨653, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_653 :
    scalarCheck (table.cell ⟨653, by decide⟩) = true := by
  kernel_decide

theorem certificate_653 :
    Certificate (table.cell ⟨653, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_653,
    crossing_of_check crossingCheck_653,
    scalar_of_check scalarCheck_653⟩

end Erdos1038.HighKPlatformConstantTableChunk653
