import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 608 through 608. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk608

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_608 :
    geometryCheck (table.cell ⟨608, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_608 :
    crossingCheck (table.cell ⟨608, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_608 :
    scalarCheck (table.cell ⟨608, by decide⟩) = true := by
  kernel_decide

theorem certificate_608 :
    Certificate (table.cell ⟨608, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_608,
    crossing_of_check crossingCheck_608,
    scalar_of_check scalarCheck_608⟩

end Erdos1038.HighKPlatformConstantTableChunk608
