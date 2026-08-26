import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 828 through 828. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk828

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_828 :
    geometryCheck (table.cell ⟨828, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_828 :
    crossingCheck (table.cell ⟨828, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_828 :
    scalarCheck (table.cell ⟨828, by decide⟩) = true := by
  kernel_decide

theorem certificate_828 :
    Certificate (table.cell ⟨828, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_828,
    crossing_of_check crossingCheck_828,
    scalar_of_check scalarCheck_828⟩

end Erdos1038.HighKPlatformConstantTableChunk828
