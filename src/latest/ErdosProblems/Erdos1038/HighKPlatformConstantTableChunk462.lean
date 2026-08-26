import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 462 through 462. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk462

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_462 :
    geometryCheck (table.cell ⟨462, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_462 :
    crossingCheck (table.cell ⟨462, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_462 :
    scalarCheck (table.cell ⟨462, by decide⟩) = true := by
  kernel_decide

theorem certificate_462 :
    Certificate (table.cell ⟨462, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_462,
    crossing_of_check crossingCheck_462,
    scalar_of_check scalarCheck_462⟩

end Erdos1038.HighKPlatformConstantTableChunk462
