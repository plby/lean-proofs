import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 704 through 704. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk704

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_704 :
    geometryCheck (table.cell ⟨704, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_704 :
    crossingCheck (table.cell ⟨704, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_704 :
    scalarCheck (table.cell ⟨704, by decide⟩) = true := by
  kernel_decide

theorem certificate_704 :
    Certificate (table.cell ⟨704, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_704,
    crossing_of_check crossingCheck_704,
    scalar_of_check scalarCheck_704⟩

end Erdos1038.HighKPlatformConstantTableChunk704
