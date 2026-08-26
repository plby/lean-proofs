import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 14 through 14. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk14

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_014 :
    geometryCheck (table.cell ⟨14, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_014 :
    crossingCheck (table.cell ⟨14, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_014 :
    scalarCheck (table.cell ⟨14, by decide⟩) = true := by
  kernel_decide

theorem certificate_014 :
    Certificate (table.cell ⟨14, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_014,
    crossing_of_check crossingCheck_014,
    scalar_of_check scalarCheck_014⟩

end Erdos1038.HighKPlatformConstantTableChunk14
