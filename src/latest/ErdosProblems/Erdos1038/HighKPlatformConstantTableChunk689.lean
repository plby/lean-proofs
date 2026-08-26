import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 689 through 689. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk689

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_689 :
    geometryCheck (table.cell ⟨689, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_689 :
    crossingCheck (table.cell ⟨689, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_689 :
    scalarCheck (table.cell ⟨689, by decide⟩) = true := by
  kernel_decide

theorem certificate_689 :
    Certificate (table.cell ⟨689, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_689,
    crossing_of_check crossingCheck_689,
    scalar_of_check scalarCheck_689⟩

end Erdos1038.HighKPlatformConstantTableChunk689
