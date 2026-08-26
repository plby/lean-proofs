import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 744 through 744. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk744

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_744 :
    geometryCheck (table.cell ⟨744, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_744 :
    crossingCheck (table.cell ⟨744, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_744 :
    scalarCheck (table.cell ⟨744, by decide⟩) = true := by
  kernel_decide

theorem certificate_744 :
    Certificate (table.cell ⟨744, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_744,
    crossing_of_check crossingCheck_744,
    scalar_of_check scalarCheck_744⟩

end Erdos1038.HighKPlatformConstantTableChunk744
