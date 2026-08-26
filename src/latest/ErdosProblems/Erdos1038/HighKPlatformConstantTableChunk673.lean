import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 673 through 673. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk673

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_673 :
    geometryCheck (table.cell ⟨673, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_673 :
    crossingCheck (table.cell ⟨673, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_673 :
    scalarCheck (table.cell ⟨673, by decide⟩) = true := by
  kernel_decide

theorem certificate_673 :
    Certificate (table.cell ⟨673, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_673,
    crossing_of_check crossingCheck_673,
    scalar_of_check scalarCheck_673⟩

end Erdos1038.HighKPlatformConstantTableChunk673
