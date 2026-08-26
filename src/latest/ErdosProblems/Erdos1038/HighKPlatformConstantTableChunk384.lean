import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 384 through 384. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk384

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_384 :
    geometryCheck (table.cell ⟨384, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_384 :
    crossingCheck (table.cell ⟨384, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_384 :
    scalarCheck (table.cell ⟨384, by decide⟩) = true := by
  kernel_decide

theorem certificate_384 :
    Certificate (table.cell ⟨384, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_384,
    crossing_of_check crossingCheck_384,
    scalar_of_check scalarCheck_384⟩

end Erdos1038.HighKPlatformConstantTableChunk384
