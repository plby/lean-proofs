import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 518 through 518. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk518

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_518 :
    geometryCheck (table.cell ⟨518, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_518 :
    crossingCheck (table.cell ⟨518, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_518 :
    scalarCheck (table.cell ⟨518, by decide⟩) = true := by
  kernel_decide

theorem certificate_518 :
    Certificate (table.cell ⟨518, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_518,
    crossing_of_check crossingCheck_518,
    scalar_of_check scalarCheck_518⟩

end Erdos1038.HighKPlatformConstantTableChunk518
