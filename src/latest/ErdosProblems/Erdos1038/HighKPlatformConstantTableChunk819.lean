import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 819 through 819. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk819

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_819 :
    geometryCheck (table.cell ⟨819, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_819 :
    crossingCheck (table.cell ⟨819, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_819 :
    scalarCheck (table.cell ⟨819, by decide⟩) = true := by
  kernel_decide

theorem certificate_819 :
    Certificate (table.cell ⟨819, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_819,
    crossing_of_check crossingCheck_819,
    scalar_of_check scalarCheck_819⟩

end Erdos1038.HighKPlatformConstantTableChunk819
