import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 814 through 814. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk814

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_814 :
    geometryCheck (table.cell ⟨814, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_814 :
    crossingCheck (table.cell ⟨814, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_814 :
    scalarCheck (table.cell ⟨814, by decide⟩) = true := by
  kernel_decide

theorem certificate_814 :
    Certificate (table.cell ⟨814, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_814,
    crossing_of_check crossingCheck_814,
    scalar_of_check scalarCheck_814⟩

end Erdos1038.HighKPlatformConstantTableChunk814
