import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 493 through 493. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk493

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_493 :
    geometryCheck (table.cell ⟨493, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_493 :
    crossingCheck (table.cell ⟨493, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_493 :
    scalarCheck (table.cell ⟨493, by decide⟩) = true := by
  kernel_decide

theorem certificate_493 :
    Certificate (table.cell ⟨493, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_493,
    crossing_of_check crossingCheck_493,
    scalar_of_check scalarCheck_493⟩

end Erdos1038.HighKPlatformConstantTableChunk493
