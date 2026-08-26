import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 76 through 76. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk76

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_076 :
    geometryCheck (table.cell ⟨76, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_076 :
    crossingCheck (table.cell ⟨76, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_076 :
    scalarCheck (table.cell ⟨76, by decide⟩) = true := by
  kernel_decide

theorem certificate_076 :
    Certificate (table.cell ⟨76, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_076,
    crossing_of_check crossingCheck_076,
    scalar_of_check scalarCheck_076⟩

end Erdos1038.HighKPlatformConstantTableChunk76
