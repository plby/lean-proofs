import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 242 through 242. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk242

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_242 :
    geometryCheck (table.cell ⟨242, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_242 :
    crossingCheck (table.cell ⟨242, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_242 :
    scalarCheck (table.cell ⟨242, by decide⟩) = true := by
  kernel_decide

theorem certificate_242 :
    Certificate (table.cell ⟨242, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_242,
    crossing_of_check crossingCheck_242,
    scalar_of_check scalarCheck_242⟩

end Erdos1038.HighKPlatformConstantTableChunk242
