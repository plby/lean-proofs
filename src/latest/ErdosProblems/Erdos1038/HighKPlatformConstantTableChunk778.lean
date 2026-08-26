import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 778 through 778. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk778

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_778 :
    geometryCheck (table.cell ⟨778, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_778 :
    crossingCheck (table.cell ⟨778, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_778 :
    scalarCheck (table.cell ⟨778, by decide⟩) = true := by
  kernel_decide

theorem certificate_778 :
    Certificate (table.cell ⟨778, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_778,
    crossing_of_check crossingCheck_778,
    scalar_of_check scalarCheck_778⟩

end Erdos1038.HighKPlatformConstantTableChunk778
