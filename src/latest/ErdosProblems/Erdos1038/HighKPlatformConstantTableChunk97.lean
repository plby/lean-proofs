import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 97 through 97. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk97

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_097 :
    geometryCheck (table.cell ⟨97, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_097 :
    crossingCheck (table.cell ⟨97, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_097 :
    scalarCheck (table.cell ⟨97, by decide⟩) = true := by
  kernel_decide

theorem certificate_097 :
    Certificate (table.cell ⟨97, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_097,
    crossing_of_check crossingCheck_097,
    scalar_of_check scalarCheck_097⟩

end Erdos1038.HighKPlatformConstantTableChunk97
