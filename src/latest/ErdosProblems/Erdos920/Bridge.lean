/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.Ramsey

/-!
# Chromatic-number and Ramsey bridges for Erdős Problem 920

This file supplies the elementary finite-graph reductions used in the proof of Problem 920.
The `ENat`-valued chromatic number from Mathlib is converted to a natural number; this conversion
is harmless for graphs on `Fin n`, since such graphs are colorable with at most `n` colors.
-/

open Finset

noncomputable section

namespace Erdos920

/-- The finite chromatic numbers occurring in the definition of `f k n`. -/
def chromaticValues (k n : ℕ) : Set ℕ :=
  {q | ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ q = G.chromaticNumber.toNat}

/--
`f k n` is the maximum chromatic number of a `K_k`-free graph on `n` vertices.

Mathlib's chromatic number is `ENat`-valued.  All graphs here have finite vertex type, so taking
`ENat.toNat` recovers their ordinary natural-valued chromatic number.
-/
noncomputable def f (k n : ℕ) : ℕ :=
  sSup {(G.chromaticNumber) | (G : SimpleGraph (Fin n)) (_ : G.CliqueFree k)}

lemma chromaticNumber_toNat_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.chromaticNumber.toNat ≤ Fintype.card V := by
  exact ENat.toNat_le_of_le_natCast G.colorable_of_fintype.chromaticNumber_le

/-- Every chromatic value in the defining set for `f k n` is at most `n`. -/
lemma chromaticValues_bddAbove (k n : ℕ) : BddAbove (chromaticValues k n) := by
  refine ⟨n, ?_⟩
  rintro q ⟨G, _hG, rfl⟩
  simpa using chromaticNumber_toNat_le_card G

lemma chromaticNumber_toNat_mem_chromaticValues {k n : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.CliqueFree k) :
    G.chromaticNumber.toNat ∈ chromaticValues k n := by
  exact ⟨G, hG, rfl⟩

/-- Any admissible graph witnesses a lower bound for `f`. -/
lemma chromaticNumber_toNat_le_f {k n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree k) : G.chromaticNumber.toNat ≤ f k n := by
  unfold f
  apply le_csSup
  · refine ⟨n, ?_⟩
    rintro q ⟨H, _hH, hq⟩
    have hq' : q = H.chromaticNumber.toNat := by
      simpa using (congrArg ENat.toNat hq).symm
    rw [hq']
    simpa using chromaticNumber_toNat_le_card H
  · refine ⟨G, hG, ?_⟩
    have hne : G.chromaticNumber ≠ ⊤ :=
      SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨_, G.colorable_of_fintype⟩
    exact (ENat.natCast_toNat_eq_self.mpr hne).symm

/-- The defining supremum is finite and bounded by the number of vertices. -/
lemma f_le_vertices (k n : ℕ) : f k n ≤ n := by
  unfold f
  apply csSup_le'
  intro q hq
  rcases hq with ⟨G, _hG, hq⟩
  have hq' : q = G.chromaticNumber.toNat := by
    simpa using (congrArg ENat.toNat hq).symm
  rw [hq']
  simpa using chromaticNumber_toNat_le_card G

/-- Below the Ramsey threshold there is a graph avoiding both forbidden configurations. -/
lemma exists_cliqueFree_indepSetFree_of_lt_ramseyNumber {k m n : ℕ}
    (h : n < Ramsey.ramseyNumber k m) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ G.IndepSetFree m := by
  have hnot : ¬ Ramsey.RamseyProperty k m n := by
    intro hprop
    exact (Nat.not_le_of_gt h) (Ramsey.ramseyNumber_le_of_property hprop)
  unfold Ramsey.RamseyProperty at hnot
  push Not at hnot
  exact hnot

end Erdos920

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {m : ℕ}

/-- In a graph with no independent set of size `m`, every finite independent set has size `< m`. -/
lemma IndepSetFree.card_lt (hfree : G.IndepSetFree m) {s : Finset V}
    (hs : G.IsIndepSet (s : Set V)) : s.card < m := by
  by_contra! hms
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hms
  apply hfree t
  refine ⟨hs.mono ?_, htcard⟩
  intro v hv
  exact hts hv

/-- Every color class has fewer than `m` vertices in an `m`-independent-set-free graph. -/
lemma IndepSetFree.card_colorClass_lt [Fintype V] (hfree : G.IndepSetFree m)
    {q : ℕ} (C : G.Coloring (Fin q)) (c : Fin q) :
    (Finset.univ.filter fun v ↦ C v = c).card < m := by
  apply hfree.card_lt
  refine (C.isIndepSet_colorClass c).mono ?_
  intro v hv
  simpa [Coloring.colorClass] using hv

/--
If an `n`-vertex graph has no independent set of size `m`, each color class has at most `m - 1`
vertices, so `n ≤ χ(G) (m - 1)`.
-/
lemma IndepSetFree.card_le_chromaticNumber_toNat_mul_pred [Fintype V]
    (hfree : G.IndepSetFree m) :
    Fintype.card V ≤ G.chromaticNumber.toNat * (m - 1) := by
  classical
  let q : ℕ := G.chromaticNumber.toNat
  let C : G.Coloring (Fin q) :=
    (SimpleGraph.colorable_chromaticNumber_of_fintype G).some
  have hfiber : ∀ c ∈ (Finset.univ : Finset (Fin q)),
      (Finset.univ.filter fun v ↦ C v = c).card ≤ m - 1 := by
    intro c _hc
    have hlt : (Finset.univ.filter fun v ↦ C v = c).card < m :=
      hfree.card_colorClass_lt C c
    omega
  have hcard := Finset.card_le_mul_card_image_of_maps_to
    (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset (Fin q)))
    (f := fun v ↦ C v) (fun _ _ ↦ Finset.mem_univ _) (m - 1) hfiber
  simpa [q, mul_comm] using hcard

end SimpleGraph

namespace Erdos920

/--
Ramsey-to-chromatic bridge: below `R(k,m)`, the extremal chromatic number satisfies
`n ≤ f_k(n)(m-1)`.
-/
theorem card_le_f_mul_pred_of_lt_ramseyNumber {k m n : ℕ}
    (h : n < Ramsey.ramseyNumber k m) : n ≤ f k n * (m - 1) := by
  obtain ⟨G, hclique, hindep⟩ := exists_cliqueFree_indepSetFree_of_lt_ramseyNumber h
  have hcard : n ≤ G.chromaticNumber.toNat * (m - 1) := by
    simpa using hindep.card_le_chromaticNumber_toNat_mul_pred
  exact hcard.trans (Nat.mul_le_mul_right (m - 1) (chromaticNumber_toNat_le_f G hclique))

/-- A convenient division form of the Ramsey-to-chromatic bridge. -/
theorem div_le_f_of_lt_ramseyNumber {k m n : ℕ}
    (h : n < Ramsey.ramseyNumber k (m + 1)) : n / m ≤ f k n := by
  apply Nat.div_le_of_le_mul
  simpa [Nat.add_sub_cancel, mul_comm] using card_le_f_mul_pred_of_lt_ramseyNumber h

/-- Real-valued form of `div_le_f_of_lt_ramseyNumber`. -/
theorem natCast_div_le_f_of_lt_ramseyNumber {k m n : ℕ}
    (h : n < Ramsey.ramseyNumber k (m + 1)) :
    (n / m : ℕ) ≤ (f k n : ℝ) := by
  exact_mod_cast div_le_f_of_lt_ramseyNumber h

/--
The exact real-division form of the bridge.  Unlike the natural-division corollary, this loses no
floor term; positivity of `m` permits division of `n ≤ f_k(n) m` in `ℝ`.
-/
theorem real_div_le_f_of_lt_ramseyNumber {k m n : ℕ} (hm : 0 < m)
    (h : n < Ramsey.ramseyNumber k (m + 1)) :
    (n : ℝ) / (m : ℝ) ≤ (f k n : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hm)]
  have hnat : n ≤ f k n * m := by
    simpa [Nat.add_sub_cancel] using card_le_f_mul_pred_of_lt_ramseyNumber h
  exact_mod_cast hnat

end Erdos920
