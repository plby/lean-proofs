import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 244 through 244. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk244

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_244 :
    geometryCheck (table.cell ⟨244, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_244 :
    crossingCheck (table.cell ⟨244, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_244 :
    scalarCheck (table.cell ⟨244, by decide⟩) = true := by
  kernel_decide

theorem certificate_244 :
    Certificate (table.cell ⟨244, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_244,
    crossing_of_check crossingCheck_244,
    scalar_of_check scalarCheck_244⟩

end Erdos1038.HighKPlatformConstantTableChunk244
