import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 829 through 829. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk829

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_829 :
    geometryCheck (table.cell ⟨829, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_829 :
    crossingCheck (table.cell ⟨829, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_829 :
    scalarCheck (table.cell ⟨829, by decide⟩) = true := by
  kernel_decide

theorem certificate_829 :
    Certificate (table.cell ⟨829, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_829,
    crossing_of_check crossingCheck_829,
    scalar_of_check scalarCheck_829⟩

end Erdos1038.HighKPlatformConstantTableChunk829
