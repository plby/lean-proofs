import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 166 through 166. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk166

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_166 :
    geometryCheck (table.cell ⟨166, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_166 :
    crossingCheck (table.cell ⟨166, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_166 :
    scalarCheck (table.cell ⟨166, by decide⟩) = true := by
  kernel_decide

theorem certificate_166 :
    Certificate (table.cell ⟨166, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_166,
    crossing_of_check crossingCheck_166,
    scalar_of_check scalarCheck_166⟩

end Erdos1038.HighKPlatformConstantTableChunk166
