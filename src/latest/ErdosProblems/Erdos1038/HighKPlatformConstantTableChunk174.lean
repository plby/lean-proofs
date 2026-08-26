import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 174 through 174. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk174

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_174 :
    geometryCheck (table.cell ⟨174, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_174 :
    crossingCheck (table.cell ⟨174, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_174 :
    scalarCheck (table.cell ⟨174, by decide⟩) = true := by
  kernel_decide

theorem certificate_174 :
    Certificate (table.cell ⟨174, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_174,
    crossing_of_check crossingCheck_174,
    scalar_of_check scalarCheck_174⟩

end Erdos1038.HighKPlatformConstantTableChunk174
