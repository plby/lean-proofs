import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 535 through 535. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk535

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_535 :
    geometryCheck (table.cell ⟨535, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_535 :
    crossingCheck (table.cell ⟨535, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_535 :
    scalarCheck (table.cell ⟨535, by decide⟩) = true := by
  kernel_decide

theorem certificate_535 :
    Certificate (table.cell ⟨535, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_535,
    crossing_of_check crossingCheck_535,
    scalar_of_check scalarCheck_535⟩

end Erdos1038.HighKPlatformConstantTableChunk535
