/- Pairing horizontal grid vertices without discarding any column. -/
import ErdosProblems.Erdos73.ColumnWitnesses

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph SimpleGraph

def doubleColumn {g : ℕ} (c : Fin g) (b : Fin 2) : Fin (2 * g) :=
  ⟨2 * c.val + b.val, by omega⟩

theorem doubleColumn_injective {g : ℕ} {c d : Fin g} {b e : Fin 2}
    (h : doubleColumn c b = doubleColumn d e) : c = d ∧ b = e := by
  have hval := congrArg Fin.val h
  dsimp only [doubleColumn] at hval
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

def gridColumnPair {g : ℕ} (x : Fin g × Fin g) : Finset (Fin g × Fin (2 * g)) :=
  {(x.1, doubleColumn x.2 0), (x.1, doubleColumn x.2 1)}

theorem mem_gridColumnPair {g : ℕ} (x : Fin g × Fin g) (b : Fin 2) :
    (x.1, doubleColumn x.2 b) ∈ gridColumnPair x := by
  have hb : b = 0 ∨ b = 1 := by omega
  rcases hb with rfl | rfl <;> simp only [gridColumnPair, Finset.mem_insert,
    Finset.mem_singleton, true_or, or_true]

def pairedGridMinorModel (g : ℕ) :
    MinorModel (squareGrid g) (pathGraph g □ pathGraph (2 * g)) where
  branchSet := gridColumnPair
  branch_nonempty := fun x => ⟨_, mem_gridColumnPair x 0⟩
  branch_connected := by
    intro x
    have hadj : (pathGraph g □ pathGraph (2 * g)).Adj
        (x.1, doubleColumn x.2 0) (x.1, doubleColumn x.2 1) :=
      Or.inr ⟨pathGraph_adj.mpr (Or.inl (by rfl)), rfl⟩
    have hset : {v | v ∈ gridColumnPair x} =
        ({(x.1, doubleColumn x.2 0), (x.1, doubleColumn x.2 1)} :
          Set (Fin g × Fin (2 * g))) := by
      ext v
      simp only [gridColumnPair, Finset.mem_insert, Finset.mem_singleton,
        Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hset]
    exact induce_pair_connected_of_adj hadj
  branch_disjoint := by
    intro x y hxy
    rw [Finset.disjoint_left]
    intro v hvx hvy
    have hx : ∃ b : Fin 2, v = (x.1, doubleColumn x.2 b) := by
      rcases Finset.mem_insert.mp hvx with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, Finset.mem_singleton.mp h⟩
    have hy : ∃ b : Fin 2, v = (y.1, doubleColumn y.2 b) := by
      rcases Finset.mem_insert.mp hvy with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, Finset.mem_singleton.mp h⟩
    obtain ⟨b, rfl⟩ := hx
    obtain ⟨e, he⟩ := hy
    exact hxy (Prod.ext (congrArg (fun z : Fin g × Fin (2 * g) => z.1) he)
      (doubleColumn_injective (congrArg Prod.snd he)).1)
  adjacent := by
    intro x y hxy
    rcases hxy with ⟨hr, hc⟩ | ⟨hc, hr⟩
    · exact ⟨_, mem_gridColumnPair x 0, _, mem_gridColumnPair y 0,
        Or.inl ⟨hr, congrArg (fun c => doubleColumn c 0) hc⟩⟩
    · rcases pathGraph_adj.mp hc with hnext | hprev
      · refine ⟨_, mem_gridColumnPair x 1, _, mem_gridColumnPair y 0,
          Or.inr ⟨pathGraph_adj.mpr (Or.inl ?_), hr⟩⟩
        change 2 * x.2.val + 1 + 1 = 2 * y.2.val + 0
        omega
      · refine ⟨_, mem_gridColumnPair x 0, _, mem_gridColumnPair y 1,
          Or.inr ⟨pathGraph_adj.mpr (Or.inr ?_), hr⟩⟩
        change 2 * y.2.val + 1 + 1 = 2 * x.2.val + 0
        omega

/-- Pair contraction retains every vertex of every horizontal row. -/
theorem pairedGridMinorModel_row_covers {g : ℕ} (r : Fin g) (c : Fin (2 * g)) :
    (r, c) ∈ gridRowSupport (pairedGridMinorModel g) r := by
  let j : Fin g := ⟨c.val / 2, by omega⟩
  let b : Fin 2 := ⟨c.val % 2, Nat.mod_lt _ (by omega)⟩
  have he : doubleColumn j b = c := Fin.ext (by
    change 2 * (c.val / 2) + c.val % 2 = c.val
    omega)
  apply (mem_gridRowSupport _ _ _).mpr
  refine ⟨j, ?_⟩
  rw [← he]
  exact mem_gridColumnPair (r, j) b

end
end Erdos73
