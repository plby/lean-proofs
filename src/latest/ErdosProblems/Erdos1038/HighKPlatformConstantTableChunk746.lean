import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 746 through 746. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk746

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_746 :
    geometryCheck (table.cell ⟨746, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_746 :
    crossingCheck (table.cell ⟨746, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_746 :
    scalarCheck (table.cell ⟨746, by decide⟩) = true := by
  kernel_decide

theorem certificate_746 :
    Certificate (table.cell ⟨746, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_746,
    crossing_of_check crossingCheck_746,
    scalar_of_check scalarCheck_746⟩

end Erdos1038.HighKPlatformConstantTableChunk746
