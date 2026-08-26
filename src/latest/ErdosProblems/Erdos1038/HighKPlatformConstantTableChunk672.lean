import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 672 through 672. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk672

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_672 :
    geometryCheck (table.cell ⟨672, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_672 :
    crossingCheck (table.cell ⟨672, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_672 :
    scalarCheck (table.cell ⟨672, by decide⟩) = true := by
  kernel_decide

theorem certificate_672 :
    Certificate (table.cell ⟨672, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_672,
    crossing_of_check crossingCheck_672,
    scalar_of_check scalarCheck_672⟩

end Erdos1038.HighKPlatformConstantTableChunk672
