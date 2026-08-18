/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos921.Cycles

open SimpleGraph

namespace Erdos921

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The exact witnesses occurring in the definition of Problem 921. -/
def Admissible (k n m : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n),
    G.chromaticNumber = (k : ℕ∞) ∧ ¬ HasOddCycleAtMost G m

/-- Erdős's extremal function. The cutoff at `n` is valid because a
non-bipartite finite graph has an odd cycle no longer than its vertex set. -/
def f (k n : ℕ) : ℕ :=
  Nat.findGreatest (Admissible k n) n

lemma f_le (k n : ℕ) : f k n ≤ n :=
  Nat.findGreatest_le n

lemma le_f_of_admissible {k n m : ℕ} (hmn : m ≤ n)
    (h : Admissible k n m) : m ≤ f k n :=
  Nat.le_findGreatest hmn h

/-- For `k ≥ 4`, every admissible threshold is at most the number of
vertices. Thus the cutoff in `f` does not change Erdős's extremal function. -/
lemma admissible_le_vertices {k n m : ℕ} (hk : 4 ≤ k)
    (h : Admissible k n m) : m ≤ n := by
  obtain ⟨G, hχ, hodd⟩ := h
  have hfour : (4 : ℕ∞) ≤ G.chromaticNumber := by
    rw [hχ]
    exact_mod_cast hk
  obtain ⟨v, w, hwc, hwo, hwlen⟩ :=
    hasOddCycleAtMost_card_of_four_le_chromaticNumber hfour
  have hwlen' : w.length ≤ n := by simpa using hwlen
  by_contra hmn
  apply hodd
  exact ⟨v, w, hwc, hwo, hwlen'.trans (by omega)⟩

/-- The defining maximum dominates every genuine witness, without an extra
cutoff hypothesis, in the range of Problem 921. -/
lemma admissible_le_f {k n m : ℕ} (hk : 4 ≤ k)
    (h : Admissible k n m) : m ≤ f k n :=
  le_f_of_admissible (admissible_le_vertices hk h) h

lemma admissible_f {k n : ℕ} (h : Admissible k n 0) :
    Admissible k n (f k n) :=
  Nat.findGreatest_spec (Nat.zero_le n) h

lemma admissible_antitone {k n a b : ℕ} (hab : a ≤ b)
    (h : Admissible k n b) : Admissible k n a := by
  obtain ⟨G, hχ, hodd⟩ := h
  refine ⟨G, hχ, ?_⟩
  intro ha
  exact hodd <| by
    obtain ⟨v, w, hwc, hwo, hwa⟩ := ha
    exact ⟨v, w, hwc, hwo, hwa.trans hab⟩

/-- If the feasible set is nonempty, `f` is a feasible threshold and is
greater than every feasible threshold: it is the exact maximum in Problem 921. -/
theorem f_isGreatest_of_admissible {k n m : ℕ} (hk : 4 ≤ k)
    (h : Admissible k n m) :
    Admissible k n (f k n) ∧ ∀ t, Admissible k n t → t ≤ f k n := by
  refine ⟨admissible_f (admissible_antitone (Nat.zero_le m) h), ?_⟩
  intro t ht
  exact admissible_le_f hk ht

end

end Erdos921
