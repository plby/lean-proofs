import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 404 through 404. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk404

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_404 :
    geometryCheck (table.cell ⟨404, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_404 :
    crossingCheck (table.cell ⟨404, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_404 :
    scalarCheck (table.cell ⟨404, by decide⟩) = true := by
  kernel_decide

theorem certificate_404 :
    Certificate (table.cell ⟨404, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_404,
    crossing_of_check crossingCheck_404,
    scalar_of_check scalarCheck_404⟩

end Erdos1038.HighKPlatformConstantTableChunk404
