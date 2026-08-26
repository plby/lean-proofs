import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 714 through 714. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk714

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_714 :
    geometryCheck (table.cell ⟨714, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_714 :
    crossingCheck (table.cell ⟨714, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_714 :
    scalarCheck (table.cell ⟨714, by decide⟩) = true := by
  kernel_decide

theorem certificate_714 :
    Certificate (table.cell ⟨714, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_714,
    crossing_of_check crossingCheck_714,
    scalar_of_check scalarCheck_714⟩

end Erdos1038.HighKPlatformConstantTableChunk714
