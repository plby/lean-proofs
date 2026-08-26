import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 648 through 648. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk648

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_648 :
    geometryCheck (table.cell ⟨648, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_648 :
    crossingCheck (table.cell ⟨648, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_648 :
    scalarCheck (table.cell ⟨648, by decide⟩) = true := by
  kernel_decide

theorem certificate_648 :
    Certificate (table.cell ⟨648, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_648,
    crossing_of_check crossingCheck_648,
    scalar_of_check scalarCheck_648⟩

end Erdos1038.HighKPlatformConstantTableChunk648
