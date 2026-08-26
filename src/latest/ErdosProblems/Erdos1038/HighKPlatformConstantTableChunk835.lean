import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 835 through 835. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk835

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_835 :
    geometryCheck (table.cell ⟨835, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_835 :
    crossingCheck (table.cell ⟨835, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_835 :
    scalarCheck (table.cell ⟨835, by decide⟩) = true := by
  kernel_decide

theorem certificate_835 :
    Certificate (table.cell ⟨835, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_835,
    crossing_of_check crossingCheck_835,
    scalar_of_check scalarCheck_835⟩

end Erdos1038.HighKPlatformConstantTableChunk835
