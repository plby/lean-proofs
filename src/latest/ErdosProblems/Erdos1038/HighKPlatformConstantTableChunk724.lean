import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 724 through 724. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk724

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_724 :
    geometryCheck (table.cell ⟨724, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_724 :
    crossingCheck (table.cell ⟨724, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_724 :
    scalarCheck (table.cell ⟨724, by decide⟩) = true := by
  kernel_decide

theorem certificate_724 :
    Certificate (table.cell ⟨724, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_724,
    crossing_of_check crossingCheck_724,
    scalar_of_check scalarCheck_724⟩

end Erdos1038.HighKPlatformConstantTableChunk724
