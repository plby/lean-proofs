import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 825 through 825. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk825

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_825 :
    geometryCheck (table.cell ⟨825, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_825 :
    crossingCheck (table.cell ⟨825, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_825 :
    scalarCheck (table.cell ⟨825, by decide⟩) = true := by
  kernel_decide

theorem certificate_825 :
    Certificate (table.cell ⟨825, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_825,
    crossing_of_check crossingCheck_825,
    scalar_of_check scalarCheck_825⟩

end Erdos1038.HighKPlatformConstantTableChunk825
