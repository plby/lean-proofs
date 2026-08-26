import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 751 through 751. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk751

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_751 :
    geometryCheck (table.cell ⟨751, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_751 :
    crossingCheck (table.cell ⟨751, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_751 :
    scalarCheck (table.cell ⟨751, by decide⟩) = true := by
  kernel_decide

theorem certificate_751 :
    Certificate (table.cell ⟨751, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_751,
    crossing_of_check crossingCheck_751,
    scalar_of_check scalarCheck_751⟩

end Erdos1038.HighKPlatformConstantTableChunk751
