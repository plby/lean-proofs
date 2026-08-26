import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 241 through 241. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk241

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_241 :
    geometryCheck (table.cell ⟨241, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_241 :
    crossingCheck (table.cell ⟨241, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_241 :
    scalarCheck (table.cell ⟨241, by decide⟩) = true := by
  kernel_decide

theorem certificate_241 :
    Certificate (table.cell ⟨241, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_241,
    crossing_of_check crossingCheck_241,
    scalar_of_check scalarCheck_241⟩

end Erdos1038.HighKPlatformConstantTableChunk241
