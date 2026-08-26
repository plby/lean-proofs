import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 716 through 716. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk716

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_716 :
    geometryCheck (table.cell ⟨716, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_716 :
    crossingCheck (table.cell ⟨716, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_716 :
    scalarCheck (table.cell ⟨716, by decide⟩) = true := by
  kernel_decide

theorem certificate_716 :
    Certificate (table.cell ⟨716, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_716,
    crossing_of_check crossingCheck_716,
    scalar_of_check scalarCheck_716⟩

end Erdos1038.HighKPlatformConstantTableChunk716
