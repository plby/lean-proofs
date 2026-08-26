import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 727 through 727. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk727

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_727 :
    geometryCheck (table.cell ⟨727, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_727 :
    crossingCheck (table.cell ⟨727, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_727 :
    scalarCheck (table.cell ⟨727, by decide⟩) = true := by
  kernel_decide

theorem certificate_727 :
    Certificate (table.cell ⟨727, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_727,
    crossing_of_check crossingCheck_727,
    scalar_of_check scalarCheck_727⟩

end Erdos1038.HighKPlatformConstantTableChunk727
