import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 144 through 144. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk144

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_144 :
    geometryCheck (table.cell ⟨144, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_144 :
    crossingCheck (table.cell ⟨144, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_144 :
    scalarCheck (table.cell ⟨144, by decide⟩) = true := by
  kernel_decide

theorem certificate_144 :
    Certificate (table.cell ⟨144, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_144,
    crossing_of_check crossingCheck_144,
    scalar_of_check scalarCheck_144⟩

end Erdos1038.HighKPlatformConstantTableChunk144
