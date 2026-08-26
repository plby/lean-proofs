import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 313 through 313. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk313

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_313 :
    geometryCheck (table.cell ⟨313, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_313 :
    crossingCheck (table.cell ⟨313, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_313 :
    scalarCheck (table.cell ⟨313, by decide⟩) = true := by
  kernel_decide

theorem certificate_313 :
    Certificate (table.cell ⟨313, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_313,
    crossing_of_check crossingCheck_313,
    scalar_of_check scalarCheck_313⟩

end Erdos1038.HighKPlatformConstantTableChunk313
