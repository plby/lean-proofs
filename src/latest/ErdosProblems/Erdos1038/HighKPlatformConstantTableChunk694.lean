import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 694 through 694. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk694

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_694 :
    geometryCheck (table.cell ⟨694, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_694 :
    crossingCheck (table.cell ⟨694, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_694 :
    scalarCheck (table.cell ⟨694, by decide⟩) = true := by
  kernel_decide

theorem certificate_694 :
    Certificate (table.cell ⟨694, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_694,
    crossing_of_check crossingCheck_694,
    scalar_of_check scalarCheck_694⟩

end Erdos1038.HighKPlatformConstantTableChunk694
