import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 826 through 826. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk826

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_826 :
    geometryCheck (table.cell ⟨826, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_826 :
    crossingCheck (table.cell ⟨826, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_826 :
    scalarCheck (table.cell ⟨826, by decide⟩) = true := by
  kernel_decide

theorem certificate_826 :
    Certificate (table.cell ⟨826, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_826,
    crossing_of_check crossingCheck_826,
    scalar_of_check scalarCheck_826⟩

end Erdos1038.HighKPlatformConstantTableChunk826
