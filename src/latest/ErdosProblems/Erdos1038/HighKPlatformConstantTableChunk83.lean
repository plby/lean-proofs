import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 83 through 83. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk83

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_083 :
    geometryCheck (table.cell ⟨83, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_083 :
    crossingCheck (table.cell ⟨83, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_083 :
    scalarCheck (table.cell ⟨83, by decide⟩) = true := by
  kernel_decide

theorem certificate_083 :
    Certificate (table.cell ⟨83, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_083,
    crossing_of_check crossingCheck_083,
    scalar_of_check scalarCheck_083⟩

end Erdos1038.HighKPlatformConstantTableChunk83
