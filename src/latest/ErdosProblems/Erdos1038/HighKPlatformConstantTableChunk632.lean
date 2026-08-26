import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 632 through 632. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk632

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_632 :
    geometryCheck (table.cell ⟨632, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_632 :
    crossingCheck (table.cell ⟨632, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_632 :
    scalarCheck (table.cell ⟨632, by decide⟩) = true := by
  kernel_decide

theorem certificate_632 :
    Certificate (table.cell ⟨632, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_632,
    crossing_of_check crossingCheck_632,
    scalar_of_check scalarCheck_632⟩

end Erdos1038.HighKPlatformConstantTableChunk632
