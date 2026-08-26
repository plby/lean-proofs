import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 592 through 592. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk592

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_592 :
    geometryCheck (table.cell ⟨592, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_592 :
    crossingCheck (table.cell ⟨592, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_592 :
    scalarCheck (table.cell ⟨592, by decide⟩) = true := by
  kernel_decide

theorem certificate_592 :
    Certificate (table.cell ⟨592, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_592,
    crossing_of_check crossingCheck_592,
    scalar_of_check scalarCheck_592⟩

end Erdos1038.HighKPlatformConstantTableChunk592
