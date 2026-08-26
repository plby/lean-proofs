import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 799 through 799. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk799

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_799 :
    geometryCheck (table.cell ⟨799, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_799 :
    crossingCheck (table.cell ⟨799, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_799 :
    scalarCheck (table.cell ⟨799, by decide⟩) = true := by
  kernel_decide

theorem certificate_799 :
    Certificate (table.cell ⟨799, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_799,
    crossing_of_check crossingCheck_799,
    scalar_of_check scalarCheck_799⟩

end Erdos1038.HighKPlatformConstantTableChunk799
