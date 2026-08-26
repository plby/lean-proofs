import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 661 through 661. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk661

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_661 :
    geometryCheck (table.cell ⟨661, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_661 :
    crossingCheck (table.cell ⟨661, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_661 :
    scalarCheck (table.cell ⟨661, by decide⟩) = true := by
  kernel_decide

theorem certificate_661 :
    Certificate (table.cell ⟨661, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_661,
    crossing_of_check crossingCheck_661,
    scalar_of_check scalarCheck_661⟩

end Erdos1038.HighKPlatformConstantTableChunk661
