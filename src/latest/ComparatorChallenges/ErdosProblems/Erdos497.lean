import Mathlib

namespace Erdos497

set_option linter.style.setOption false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

open Equiv
open Filter
open Finset
open Nat
open Real

set_option maxHeartbeats 50000000
set_option linter.style.cases false

def PP (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.powerset

noncomputable def antichains (n : ℕ) : Finset (Finset (Finset (Fin n))) :=
  (PP n).powerset.filter (fun ℱ => IsAntichain (· ⊆ ·) (ℱ : Set (Finset (Fin n))))

noncomputable def A (n : ℕ) : ℕ :=
  (antichains n).card
end Erdos497

attribute [local instance] Classical.propDecidable

open Equiv
open Filter
open Finset
open Nat
open Real

namespace Erdos497

theorem erdos_497 :
    Asymptotics.IsEquivalent Filter.atTop (fun n => Real.logb 2 (A n)) (fun n =>
      (n.choose (n / 2) : ℝ)) := by
  sorry

end Erdos497
