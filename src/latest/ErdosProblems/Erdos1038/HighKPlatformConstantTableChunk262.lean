import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 262 through 262. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk262

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_262 :
    geometryCheck (table.cell ⟨262, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_262 :
    crossingCheck (table.cell ⟨262, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_262 :
    scalarCheck (table.cell ⟨262, by decide⟩) = true := by
  kernel_decide

theorem certificate_262 :
    Certificate (table.cell ⟨262, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_262,
    crossing_of_check crossingCheck_262,
    scalar_of_check scalarCheck_262⟩

end Erdos1038.HighKPlatformConstantTableChunk262
