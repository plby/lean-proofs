import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 631 through 631. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk631

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_631 :
    geometryCheck (table.cell ⟨631, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_631 :
    crossingCheck (table.cell ⟨631, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_631 :
    scalarCheck (table.cell ⟨631, by decide⟩) = true := by
  kernel_decide

theorem certificate_631 :
    Certificate (table.cell ⟨631, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_631,
    crossing_of_check crossingCheck_631,
    scalar_of_check scalarCheck_631⟩

end Erdos1038.HighKPlatformConstantTableChunk631
