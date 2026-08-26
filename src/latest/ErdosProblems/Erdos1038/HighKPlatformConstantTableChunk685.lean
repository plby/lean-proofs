import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 685 through 685. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk685

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_685 :
    geometryCheck (table.cell ⟨685, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_685 :
    crossingCheck (table.cell ⟨685, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_685 :
    scalarCheck (table.cell ⟨685, by decide⟩) = true := by
  kernel_decide

theorem certificate_685 :
    Certificate (table.cell ⟨685, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_685,
    crossing_of_check crossingCheck_685,
    scalar_of_check scalarCheck_685⟩

end Erdos1038.HighKPlatformConstantTableChunk685
