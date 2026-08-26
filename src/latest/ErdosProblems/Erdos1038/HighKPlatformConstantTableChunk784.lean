import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 784 through 784. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk784

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_784 :
    geometryCheck (table.cell ⟨784, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_784 :
    crossingCheck (table.cell ⟨784, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_784 :
    scalarCheck (table.cell ⟨784, by decide⟩) = true := by
  kernel_decide

theorem certificate_784 :
    Certificate (table.cell ⟨784, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_784,
    crossing_of_check crossingCheck_784,
    scalar_of_check scalarCheck_784⟩

end Erdos1038.HighKPlatformConstantTableChunk784
