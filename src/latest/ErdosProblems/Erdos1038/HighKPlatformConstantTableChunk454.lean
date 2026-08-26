import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 454 through 454. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk454

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_454 :
    geometryCheck (table.cell ⟨454, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_454 :
    crossingCheck (table.cell ⟨454, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_454 :
    scalarCheck (table.cell ⟨454, by decide⟩) = true := by
  kernel_decide

theorem certificate_454 :
    Certificate (table.cell ⟨454, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_454,
    crossing_of_check crossingCheck_454,
    scalar_of_check scalarCheck_454⟩

end Erdos1038.HighKPlatformConstantTableChunk454
