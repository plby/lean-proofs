import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 776 through 776. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk776

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_776 :
    geometryCheck (table.cell ⟨776, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_776 :
    crossingCheck (table.cell ⟨776, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_776 :
    scalarCheck (table.cell ⟨776, by decide⟩) = true := by
  kernel_decide

theorem certificate_776 :
    Certificate (table.cell ⟨776, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_776,
    crossing_of_check crossingCheck_776,
    scalar_of_check scalarCheck_776⟩

end Erdos1038.HighKPlatformConstantTableChunk776
