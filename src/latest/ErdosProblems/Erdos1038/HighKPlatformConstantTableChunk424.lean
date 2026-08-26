import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 424 through 424. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk424

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_424 :
    geometryCheck (table.cell ⟨424, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_424 :
    crossingCheck (table.cell ⟨424, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_424 :
    scalarCheck (table.cell ⟨424, by decide⟩) = true := by
  kernel_decide

theorem certificate_424 :
    Certificate (table.cell ⟨424, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_424,
    crossing_of_check crossingCheck_424,
    scalar_of_check scalarCheck_424⟩

end Erdos1038.HighKPlatformConstantTableChunk424
