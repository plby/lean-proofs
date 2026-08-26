import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 126 through 126. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk126

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_126 :
    geometryCheck (table.cell ⟨126, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_126 :
    crossingCheck (table.cell ⟨126, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_126 :
    scalarCheck (table.cell ⟨126, by decide⟩) = true := by
  kernel_decide

theorem certificate_126 :
    Certificate (table.cell ⟨126, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_126,
    crossing_of_check crossingCheck_126,
    scalar_of_check scalarCheck_126⟩

end Erdos1038.HighKPlatformConstantTableChunk126
