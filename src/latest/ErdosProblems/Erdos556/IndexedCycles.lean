import ErdosProblems.Erdos556.IndexedCyclePaths
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! Building a simple cycle from an explicit cyclic enumeration. -/

namespace Erdos556

open SimpleGraph

theorem cycleGraph_adj_of_lt_iff {m : ℕ} {i j : Fin m} (hij : i.val < j.val) :
    (cycleGraph m).Adj i j ↔ i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val + 1 = m) := by
  rw [cycleGraph_adj', Fin.coe_sub_iff_lt.mpr hij, Fin.sub_val_of_le hij.le]
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem exists_cycle_of_indexed_vertices {V : Type*} (G : SimpleGraph V)
    (m : ℕ) (hm : 3 ≤ m) (f : ℕ → V)
    (hinj : Set.InjOn f (Set.Iio m))
    (hadj : ∀ i, i + 1 < m → G.Adj (f i) (f (i + 1)))
    (hclose : G.Adj (f (m - 1)) (f 0)) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = m := by
  have hf : Function.Injective (fun i : Fin m => f i.val) := by
    intro i j hij
    exact Fin.ext (hinj i.isLt j.isLt hij)
  have hmap : ∀ i j : Fin m, (cycleGraph m).Adj i j → G.Adj (f i.val) (f j.val) := by
    intro i j hij
    have hne : i.val ≠ j.val := fun h => hij.ne (Fin.ext h)
    wlog hlt : i.val < j.val generalizing i j
    · exact (this j i hij.symm hne.symm (by omega)).symm
    rcases (cycleGraph_adj_of_lt_iff hlt).mp hij with hnext | ⟨hzero, hlast⟩
    · simpa only [hnext] using hadj i.val (by omega)
    · have hlast' : j.val = m - 1 := by omega
      simpa only [hzero, hlast'] using hclose.symm
  apply (cycleGraph_isContained_iff (by omega : 2 < m)).mp
  exact ⟨{ toHom := { toFun := fun i => f i.val, map_rel' := fun h => hmap _ _ h }
           injective' := hf }⟩

#print axioms exists_cycle_of_indexed_vertices

end Erdos556
