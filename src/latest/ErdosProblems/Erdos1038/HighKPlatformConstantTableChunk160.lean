import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 160 through 160. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk160

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_160 :
    geometryCheck (table.cell ⟨160, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_160 :
    crossingCheck (table.cell ⟨160, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_160 :
    scalarCheck (table.cell ⟨160, by decide⟩) = true := by
  kernel_decide

theorem certificate_160 :
    Certificate (table.cell ⟨160, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_160,
    crossing_of_check crossingCheck_160,
    scalar_of_check scalarCheck_160⟩

end Erdos1038.HighKPlatformConstantTableChunk160
