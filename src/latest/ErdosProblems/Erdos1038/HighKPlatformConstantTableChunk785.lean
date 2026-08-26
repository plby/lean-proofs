import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 785 through 785. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk785

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_785 :
    geometryCheck (table.cell ⟨785, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_785 :
    crossingCheck (table.cell ⟨785, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_785 :
    scalarCheck (table.cell ⟨785, by decide⟩) = true := by
  kernel_decide

theorem certificate_785 :
    Certificate (table.cell ⟨785, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_785,
    crossing_of_check crossingCheck_785,
    scalar_of_check scalarCheck_785⟩

end Erdos1038.HighKPlatformConstantTableChunk785
