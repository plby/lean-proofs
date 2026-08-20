import ErdosProblems.Erdos720.Arithmetic

namespace Erdos720

open Finset SimpleGraph

/-- The canonical three-part vertex type used by the cycle-or-hole lemma. -/
abbrev TripType (m : ℕ) :=
  ((Fin (128 * m) ⊕ Fin (128 * m)) ⊕ Fin (2 * m - 1))

@[simp] lemma card_tripType (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (TripType m) = 258 * m - 1 := by
  simp [TripType]
  omega

/-- With the logarithmic height chosen canonically, every colouring on the
tripartite template either contains the required cycle or has a prescribed
empty bipartite hole. -/
lemma one_cycle_or_hole {m n : ℕ} (hn : 16512 ≤ n)
    (hnm : n ≤ m) (hmn : m ≤ 258 * n) (R : SimpleGraph (TripType m)) :
    cycleGraph n ⊑ R ∨
      ∃ X Y : Finset (TripType m),
        Disjoint X Y ∧ X.card = m ∧ Y.card = m ∧
          ∀ x ∈ X, ∀ y ∈ Y, ¬ R.Adj x y := by
  have hd := clog_height_data_between hn hnm hmn
  exact tripartite_cycle_or_hole m (Nat.clog 2 m) n hd.1 (by omega)
    hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2 R

lemma one_cycle_or_hole_linear {C m n : ℕ} (hC : 1 ≤ C)
    (hn : 64 * C ≤ n) (hnm : n ≤ m) (hmn : m ≤ C * n)
    (R : SimpleGraph (TripType m)) :
    cycleGraph n ⊑ R ∨
      ∃ X Y : Finset (TripType m),
        Disjoint X Y ∧ X.card = m ∧ Y.card = m ∧
          ∀ x ∈ X, ∀ y ∈ Y, ¬ R.Adj x y := by
  have hd := clog_height_data_linear hC hn hnm hmn
  exact tripartite_cycle_or_hole m (Nat.clog 2 m) n hd.1 (by omega)
    hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2 R

end Erdos720
