import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 821 through 821. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk821

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_821 :
    geometryCheck (table.cell ⟨821, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_821 :
    crossingCheck (table.cell ⟨821, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_821 :
    scalarCheck (table.cell ⟨821, by decide⟩) = true := by
  kernel_decide

theorem certificate_821 :
    Certificate (table.cell ⟨821, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_821,
    crossing_of_check crossingCheck_821,
    scalar_of_check scalarCheck_821⟩

end Erdos1038.HighKPlatformConstantTableChunk821
