import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 657 through 657. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk657

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_657 :
    geometryCheck (table.cell ⟨657, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_657 :
    crossingCheck (table.cell ⟨657, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_657 :
    scalarCheck (table.cell ⟨657, by decide⟩) = true := by
  kernel_decide

theorem certificate_657 :
    Certificate (table.cell ⟨657, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_657,
    crossing_of_check crossingCheck_657,
    scalar_of_check scalarCheck_657⟩

end Erdos1038.HighKPlatformConstantTableChunk657
