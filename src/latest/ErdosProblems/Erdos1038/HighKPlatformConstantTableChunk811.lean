import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 811 through 811. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk811

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_811 :
    geometryCheck (table.cell ⟨811, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_811 :
    crossingCheck (table.cell ⟨811, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_811 :
    scalarCheck (table.cell ⟨811, by decide⟩) = true := by
  kernel_decide

theorem certificate_811 :
    Certificate (table.cell ⟨811, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_811,
    crossing_of_check crossingCheck_811,
    scalar_of_check scalarCheck_811⟩

end Erdos1038.HighKPlatformConstantTableChunk811
