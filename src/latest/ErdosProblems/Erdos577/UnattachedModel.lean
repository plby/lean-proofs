import ErdosProblems.Erdos577.LocalFactors

/-! Finite triangle/singleton/cycle models for the weighted attachment bound. -/

namespace Erdos577.Unattached

open Finset

/-- The two-bit diagonal mask records the actual extra edges of the old block. -/
def oldEdges (diagonal : Fin 4) : ℕ :=
  4 + (diagonal.val.testBit 0).toNat + (diagonal.val.testBit 1).toNat

def basePairs (diagonal : Fin 4) : Finset (Fin 8 × Fin 8) :=
  {(1, 2), (1, 3), (2, 3), (4, 5), (5, 6), (6, 7), (4, 7)} ∪
    (if diagonal.val.testBit 0 then {(4, 6)} else ∅) ∪
    (if diagonal.val.testBit 1 then {(5, 7)} else ∅)

def relation (diagonal : Fin 4) (m : ℕ) (a b : Fin 8) : Prop :=
  (a, b) ∈ basePairs diagonal ∨
    (a.val < 4 ∧ 4 ≤ b.val ∧ m.testBit (4 * a.val + b.val - 4) = true)

instance (diagonal : Fin 4) (m : ℕ) : DecidableRel (relation diagonal m) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Labels 1,2,3 form the triangle, 0 is its unattached singleton, and
4,5,6,7 form the quadrilateral. Cross edges are the only remaining bits. -/
def graph (diagonal : Fin 4) (m : ℕ) : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel (relation diagonal m)

instance (diagonal : Fin 4) (m : ℕ) : DecidableRel (graph diagonal m).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (relation diagonal m)).Adj)

def weightedCount (m : ℕ) : ℕ :=
  3 * ((List.range 4).map fun i ↦ (m.testBit i).toNat).sum +
    ((List.range 12).map fun i ↦ (m.testBit (i + 4)).toNat).sum

def Positive (diagonal : Fin 4) (m : ℕ) : Prop :=
  LocalFactor (graph diagonal m) univ ∨
    LocalImprovement (G := graph diagonal m) univ (oldEdges diagonal)

lemma graph_mono (diagonal : Fin 4) {small large : ℕ} (h : large &&& small = small) :
    graph diagonal small ≤ graph diagonal large := by
  have hb (i : ℕ) (hi : small.testBit i = true) : large.testBit i = true := by
    have he := congrArg (fun n : ℕ ↦ n.testBit i) h
    simpa only [Nat.testBit_and, hi, Bool.and_true] using he
  have hr {a b : Fin 8} (h : relation diagonal small a b) : relation diagonal large a b := by
    rcases h with h | ⟨ha, hb', hbit⟩
    · exact Or.inl h
    · exact Or.inr ⟨ha, hb', hb _ hbit⟩
  intro a b hab
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨hne, hab | hba⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl (hr hab)⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inr (hr hba)⟩

lemma Positive.mono {diagonal : Fin 4} {small large : ℕ}
    (hs : Positive diagonal small) (h : large &&& small = small) : Positive diagonal large := by
  let f := SimpleGraph.Copy.ofLE (graph diagonal small) (graph diagonal large)
    (graph_mono diagonal h)
  rcases hs with hs | hs
  · left
    simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f
  · right
    simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f

end Erdos577.Unattached
