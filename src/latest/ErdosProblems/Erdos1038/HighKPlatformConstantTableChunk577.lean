import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 577 through 577. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk577

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_577 :
    geometryCheck (table.cell ⟨577, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_577 :
    crossingCheck (table.cell ⟨577, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_577 :
    scalarCheck (table.cell ⟨577, by decide⟩) = true := by
  kernel_decide

theorem certificate_577 :
    Certificate (table.cell ⟨577, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_577,
    crossing_of_check crossingCheck_577,
    scalar_of_check scalarCheck_577⟩

end Erdos1038.HighKPlatformConstantTableChunk577
