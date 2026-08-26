import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 152 through 152. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk152

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_152 :
    geometryCheck (table.cell ⟨152, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_152 :
    crossingCheck (table.cell ⟨152, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_152 :
    scalarCheck (table.cell ⟨152, by decide⟩) = true := by
  kernel_decide

theorem certificate_152 :
    Certificate (table.cell ⟨152, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_152,
    crossing_of_check crossingCheck_152,
    scalar_of_check scalarCheck_152⟩

end Erdos1038.HighKPlatformConstantTableChunk152
