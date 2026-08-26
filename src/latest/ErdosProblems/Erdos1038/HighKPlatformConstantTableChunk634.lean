import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 634 through 634. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk634

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_634 :
    geometryCheck (table.cell ⟨634, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_634 :
    crossingCheck (table.cell ⟨634, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_634 :
    scalarCheck (table.cell ⟨634, by decide⟩) = true := by
  kernel_decide

theorem certificate_634 :
    Certificate (table.cell ⟨634, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_634,
    crossing_of_check crossingCheck_634,
    scalar_of_check scalarCheck_634⟩

end Erdos1038.HighKPlatformConstantTableChunk634
