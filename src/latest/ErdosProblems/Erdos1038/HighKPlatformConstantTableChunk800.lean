import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 800 through 800. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk800

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_800 :
    geometryCheck (table.cell ⟨800, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_800 :
    crossingCheck (table.cell ⟨800, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_800 :
    scalarCheck (table.cell ⟨800, by decide⟩) = true := by
  kernel_decide

theorem certificate_800 :
    Certificate (table.cell ⟨800, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_800,
    crossing_of_check crossingCheck_800,
    scalar_of_check scalarCheck_800⟩

end Erdos1038.HighKPlatformConstantTableChunk800
