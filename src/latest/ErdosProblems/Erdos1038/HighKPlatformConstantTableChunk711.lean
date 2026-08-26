import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 711 through 711. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk711

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_711 :
    geometryCheck (table.cell ⟨711, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_711 :
    crossingCheck (table.cell ⟨711, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_711 :
    scalarCheck (table.cell ⟨711, by decide⟩) = true := by
  kernel_decide

theorem certificate_711 :
    Certificate (table.cell ⟨711, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_711,
    crossing_of_check crossingCheck_711,
    scalar_of_check scalarCheck_711⟩

end Erdos1038.HighKPlatformConstantTableChunk711
