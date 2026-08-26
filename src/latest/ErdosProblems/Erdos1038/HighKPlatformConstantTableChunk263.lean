import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 263 through 263. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk263

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_263 :
    geometryCheck (table.cell ⟨263, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_263 :
    crossingCheck (table.cell ⟨263, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_263 :
    scalarCheck (table.cell ⟨263, by decide⟩) = true := by
  kernel_decide

theorem certificate_263 :
    Certificate (table.cell ⟨263, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_263,
    crossing_of_check crossingCheck_263,
    scalar_of_check scalarCheck_263⟩

end Erdos1038.HighKPlatformConstantTableChunk263
