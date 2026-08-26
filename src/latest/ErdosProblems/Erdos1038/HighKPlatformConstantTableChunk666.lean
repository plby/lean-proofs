import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 666 through 666. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk666

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_666 :
    geometryCheck (table.cell ⟨666, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_666 :
    crossingCheck (table.cell ⟨666, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_666 :
    scalarCheck (table.cell ⟨666, by decide⟩) = true := by
  kernel_decide

theorem certificate_666 :
    Certificate (table.cell ⟨666, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_666,
    crossing_of_check crossingCheck_666,
    scalar_of_check scalarCheck_666⟩

end Erdos1038.HighKPlatformConstantTableChunk666
