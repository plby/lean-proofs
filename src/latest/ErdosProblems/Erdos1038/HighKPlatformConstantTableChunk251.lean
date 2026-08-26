import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 251 through 251. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk251

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_251 :
    geometryCheck (table.cell ⟨251, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_251 :
    crossingCheck (table.cell ⟨251, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_251 :
    scalarCheck (table.cell ⟨251, by decide⟩) = true := by
  kernel_decide

theorem certificate_251 :
    Certificate (table.cell ⟨251, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_251,
    crossing_of_check crossingCheck_251,
    scalar_of_check scalarCheck_251⟩

end Erdos1038.HighKPlatformConstantTableChunk251
