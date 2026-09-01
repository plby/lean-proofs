/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 801.
https://www.erdosproblems.com/forum/thread/801

Informal authors:
- Noga Alon

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos801.md
-/
/-
This is a Lean formalization of the affirmative solution to Erdős Problem 801.
https://www.erdosproblems.com/801

Informal author:
- Noga Alon

Formal author:
- Codex

Reference:
N. Alon, "Independence numbers of locally sparse graphs and a Ramsey type problem",
Random Structures & Algorithms 9 (1996), 271--278.
-/
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open Finset
open scoped Finset

noncomputable section

namespace Erdos801

/-! ## Induced edge and triangle counts -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `G` whose two endpoints lie in `S`. -/
def edgesInside (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e ↦ e.toFinset ⊆ S)

/-- The number of edges induced by `S`, presented without a decidability
parameter for use in the public statement. -/
noncomputable def edgeCountInside (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (@edgesInside V _ _ G (Classical.decRel G.Adj) S).card

/-- The triangles of `G` whose vertices lie in `S`. -/
def trianglesInside (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Finset V) :=
  (G.cliqueFinset 3).filter (· ⊆ S)

@[simp] theorem mem_edgesInside_iff {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset V} {e : Sym2 V} :
    e ∈ edgesInside G S ↔ e ∈ G.edgeSet ∧ e.toFinset ⊆ S := by
  simp [edgesInside]

@[simp] theorem mem_trianglesInside_iff {G : SimpleGraph V} [DecidableRel G.Adj]
    {S T : Finset V} : T ∈ trianglesInside G S ↔ G.IsNClique 3 T ∧ T ⊆ S := by
  simp [trianglesInside]

/-- Endpoint sets of the edges lying in `S`.  This auxiliary family turns the
canonical `Sym2` edge representation into a 2-uniform set family for sampling. -/
def edgeVertexSets (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Finset V) :=
  (edgesInside G S).image Sym2.toFinset

lemma sym2_toFinset_injOn_edgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Set.InjOn Sym2.toFinset (G.edgeFinset : Set (Sym2 V)) := by
  intro e he f hf hef
  induction e, f using Sym2.inductionOn₂ with
  | _ a b c d =>
      have hab : a ≠ b := by
        intro hab
        subst b
        have haa : G.Adj a a := by simpa using (SimpleGraph.mem_edgeFinset.mp he)
        exact haa.ne rfl
      have hcd : c ≠ d := by
        intro hcd
        subst d
        have hcc : G.Adj c c := by simpa using (SimpleGraph.mem_edgeFinset.mp hf)
        exact hcc.ne rfl
      have hsets : ({a, b} : Finset V) = {c, d} := by
        simpa [Sym2.toFinset_mk_eq] using hef
      have ha : a = c ∨ a = d := by
        have : a ∈ ({c, d} : Finset V) := by rw [← hsets]; simp
        simpa using this
      have hb : b = c ∨ b = d := by
        have : b ∈ ({c, d} : Finset V) := by rw [← hsets]; simp
        simpa using this
      rcases ha with hac | had <;> rcases hb with hbc | hbd
      · exact (hab (hac.trans hbc.symm)).elim
      · exact Sym2.eq_iff.mpr (Or.inl ⟨hac, hbd⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨had, hbc⟩)
      · exact (hab (had.trans hbd.symm)).elim

@[simp] theorem card_edgeVertexSets
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (edgeVertexSets G S).card = (edgesInside G S).card := by
  rw [edgeVertexSets, Finset.card_image_iff]
  exact (sym2_toFinset_injOn_edgeFinset G).mono (by
    intro e he
    exact Finset.mem_filter.mp he |>.1)

theorem edgeVertexSets_uniform
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∀ A ∈ edgeVertexSets G S, A.card = 2 := by
  intro A hA
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hA
  exact G.card_toFinset_mem_edgeFinset
    ⟨e, Finset.mem_filter.mp he |>.1⟩

theorem edgeVertexSets_subset
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∀ A ∈ edgeVertexSets G S, A ⊆ S := by
  intro A hA
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hA
  exact Finset.mem_filter.mp he |>.2

@[simp] theorem mem_edgeVertexSets_iff
    {G : SimpleGraph V} [DecidableRel G.Adj] {S A : Finset V} :
    A ∈ edgeVertexSets G S ↔ G.IsNClique 2 A ∧ A ⊆ S := by
  constructor
  · intro hA
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hA
    have he' := Finset.mem_filter.mp he
    induction e using Sym2.inductionOn with
    | _ a b =>
        have hab : G.Adj a b := by
          simpa using (SimpleGraph.mem_edgeFinset.mp he'.1)
        have hclique : G.IsClique ((s(a, b) : Sym2 V).toFinset : Set V) := by
          intro x hx y hy hxy
          simp only [Sym2.toFinset_mk_eq, Finset.mem_coe,
            Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact (hxy rfl).elim
          · exact hab
          · exact G.adj_symm hab
          · exact (hxy rfl).elim
        exact ⟨⟨hclique, by
          simpa using G.card_toFinset_mem_edgeFinset ⟨s(a, b), he'.1⟩⟩, he'.2⟩
  · rintro ⟨hA, hAS⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hA.card_eq
    have hadj : G.Adj a b := hA.isClique (by simp) (by simp) hab
    refine Finset.mem_image.mpr ⟨s(a, b), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨by simpa using hadj, by
        simpa [Sym2.toFinset_mk_eq] using hAS⟩
    · exact Sym2.toFinset_mk_eq

theorem filter_edgeVertexSets_subset_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {S U : Finset V} (hUS : U ⊆ S) :
    (edgeVertexSets G S).filter (· ⊆ U) = edgeVertexSets G U := by
  classical
  rw [edgeVertexSets, Finset.filter_image]
  congr 1
  ext e
  simp only [edgesInside, Finset.mem_filter]
  constructor
  · rintro ⟨⟨he, _⟩, heU⟩
    exact ⟨he, heU⟩
  · rintro ⟨he, heU⟩
    exact ⟨⟨he, heU.trans hUS⟩, heU⟩

theorem filter_trianglesInside_subset_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] {S U : Finset V} (hUS : U ⊆ S) :
    (trianglesInside G S).filter (· ⊆ U) = trianglesInside G U := by
  ext T
  simp only [mem_filter, mem_trianglesInside_iff]
  constructor
  · rintro ⟨⟨hT, _⟩, hTU⟩
    exact ⟨hT, hTU⟩
  · rintro ⟨hT, hTU⟩
    exact ⟨⟨hT, hTU.trans hUS⟩, hTU⟩

/-- Triangles through `v` are in bijection with edges among the neighbors of
`v`; only the inequality needed later is recorded. -/
theorem card_triangles_through_le_neighbor_edges
    (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) {v : V} :
    ((trianglesInside G Y).filter (fun T ↦ v ∈ T)).card ≤
      (edgesInside G (G.neighborFinset v ∩ Y)).card := by
  classical
  let Tv := (trianglesInside G Y).filter (fun T ↦ v ∈ T)
  let eraseV : Finset V → Finset V := fun T ↦ T.erase v
  have hinj : Set.InjOn eraseV (Tv : Set (Finset V)) := by
    intro A hA B hB hEq
    have hvA : v ∈ A := (Finset.mem_filter.mp hA).2
    have hvB : v ∈ B := (Finset.mem_filter.mp hB).2
    change A.erase v = B.erase v at hEq
    rw [← Finset.insert_erase hvA, ← Finset.insert_erase hvB, hEq]
  have himage : Tv.image eraseV ⊆
      edgeVertexSets G (G.neighborFinset v ∩ Y) := by
    intro A hA
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hA
    have hT' := Finset.mem_filter.mp hT
    have hclique := (mem_trianglesInside_iff.mp hT'.1).1
    have hTY := (mem_trianglesInside_iff.mp hT'.1).2
    have hvT := hT'.2
    refine mem_edgeVertexSets_iff.mpr ⟨?_, ?_⟩
    · refine ⟨hclique.isClique.subset ?_, ?_⟩
      · intro u hu
        exact Finset.mem_of_mem_erase hu
      rw [Finset.card_erase_of_mem hvT, hclique.card_eq]
    · intro u hu
      have huT : u ∈ T := Finset.mem_of_mem_erase hu
      have huv : u ≠ v := Finset.ne_of_mem_erase hu
      exact Finset.mem_inter.mpr ⟨by
        simpa [SimpleGraph.mem_neighborFinset] using
          hclique.isClique hvT huT (Ne.symm huv), hTY huT⟩
  calc
    Tv.card = (Tv.image eraseV).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (edgeVertexSets G (G.neighborFinset v ∩ Y)).card :=
      Finset.card_le_card himage
    _ = (edgesInside G (G.neighborFinset v ∩ Y)).card :=
      card_edgeVertexSets G _

/-- Double-count vertex--triangle incidences. -/
theorem sum_card_triangles_through
    (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) :
    ∑ v ∈ Y, ((trianglesInside G Y).filter (fun T ↦ v ∈ T)).card =
      3 * (trianglesInside G Y).card := by
  classical
  let T := trianglesInside G Y
  calc
    ∑ v ∈ Y, (T.filter (fun Q ↦ v ∈ Q)).card =
        ∑ v ∈ Y, #(T.bipartiteAbove (fun v Q ↦ v ∈ Q) v) := by
      apply Finset.sum_congr rfl
      intro v _
      rfl
    _ = ∑ Q ∈ T, #(Y.bipartiteBelow (fun v Q ↦ v ∈ Q) Q) :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun (v : V) (Q : Finset V) ↦ v ∈ Q) (s := Y) (t := T)
    _ = ∑ Q ∈ T, Q.card := by
      apply Finset.sum_congr rfl
      intro Q hQ
      congr 1
      ext v
      have hQY : Q ⊆ Y := (mem_trianglesInside_iff.mp hQ).2
      simp [Finset.bipartiteBelow, hQY]
    _ = 3 * T.card := by
      calc
        ∑ Q ∈ T, Q.card = ∑ _Q ∈ T, 3 := by
          apply Finset.sum_congr rfl
          intro Q hQ
          exact (mem_trianglesInside_iff.mp hQ).1.card_eq
        _ = 3 * T.card := by simp [Nat.mul_comm]

/-- If every neighborhood in `Y` spans at most `B` edges, then the number of
triangles in `Y` is at most `Y.card * B / 3`. -/
theorem three_mul_card_trianglesInside_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) (B : ℕ)
    (hlocal : ∀ v ∈ Y,
      (edgesInside G (G.neighborFinset v ∩ Y)).card ≤ B) :
    3 * (trianglesInside G Y).card ≤ Y.card * B := by
  rw [← sum_card_triangles_through G Y]
  calc
    ∑ v ∈ Y, ((trianglesInside G Y).filter (fun T ↦ v ∈ T)).card ≤
        ∑ v ∈ Y, (edgesInside G (G.neighborFinset v ∩ Y)).card := by
      apply Finset.sum_le_sum
      intro v hv
      exact card_triangles_through_le_neighbor_edges G Y
    _ ≤ ∑ _v ∈ Y, B := by
      apply Finset.sum_le_sum
      intro v hv
      exact hlocal v hv
    _ = Y.card * B := by simp

/-! ## Uniform-subset double counting -/

omit [Fintype V] in
/-- Double-count incidences between an `r`-uniform family and the `k`-subsets
containing one of its members. -/
theorem sum_card_uniformFamily_inside
    (X : Finset V) (F : Finset (Finset V)) (r k : ℕ)
    (hFX : ∀ A ∈ F, A ⊆ X) (hFr : ∀ A ∈ F, A.card = r) (hrk : r ≤ k) :
    ∑ U ∈ X.powersetCard k, #(F.filter (· ⊆ U)) =
      #F * Nat.choose (#X - r) (k - r) := by
  classical
  have hdouble :
      ∑ U ∈ X.powersetCard k, #(F.filter (· ⊆ U)) =
        ∑ A ∈ F, #((X.powersetCard k).filter (fun U ↦ A ⊆ U)) := by
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun U A : Finset V => A ⊆ U)
        (s := X.powersetCard k) (t := F))
  rw [hdouble]
  calc
    ∑ A ∈ F, #((X.powersetCard k).filter (fun U ↦ A ⊆ U)) =
        ∑ A ∈ F, Nat.choose (#X - r) (k - r) := by
      apply sum_congr rfl
      intro A hA
      rw [Finset.card_filter_powersetCard_subset A X k (hFX A hA)]
      · rw [hFr A hA]
      · simpa [hFr A hA]
    _ = #F * Nat.choose (#X - r) (k - r) := by simp

/-- Some member of a nonempty finite family is at least its average, in
cross-multiplied natural-number form. -/
lemma exists_card_mul_le_card_mul_of_nonempty
    {α : Type*} {s : Finset α} (hs : s.Nonempty) (f : α → ℕ) :
    ∃ x ∈ s, ∑ y ∈ s, f y ≤ #s * f x := by
  classical
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image s f hs
  refine ⟨x, hx, ?_⟩
  calc
    ∑ y ∈ s, f y ≤ ∑ _y ∈ s, f x := by
      exact Finset.sum_le_sum fun y hy ↦ hmax y hy
    _ = #s * f x := by simp

/-- Some member of a nonempty finite family is at most its average, in
cross-multiplied natural-number form. -/
lemma exists_card_mul_ge_card_mul_of_nonempty
    {α : Type*} {s : Finset α} (hs : s.Nonempty) (f : α → ℕ) :
    ∃ x ∈ s, #s * f x ≤ ∑ y ∈ s, f y := by
  classical
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image s f hs
  refine ⟨x, hx, ?_⟩
  calc
    #s * f x = ∑ _y ∈ s, f x := by simp
    _ ≤ ∑ y ∈ s, f y := by
      exact Finset.sum_le_sum fun y hy ↦ hmin y hy

omit [Fintype V] in
/-- A lower-average consequence of uniform-subset double counting. -/
theorem exists_subset_uniformFamily_many
    (X : Finset V) (F : Finset (Finset V)) (r k : ℕ)
    (hFX : ∀ A ∈ F, A ⊆ X) (hFr : ∀ A ∈ F, A.card = r)
    (hrk : r ≤ k) (hkX : k ≤ X.card) :
    ∃ U ∈ X.powersetCard k,
      F.card * Nat.choose (X.card - r) (k - r) ≤
        Nat.choose X.card k * #(F.filter (· ⊆ U)) := by
  classical
  have hpow : (X.powersetCard k).Nonempty := by
    exact Finset.powersetCard_nonempty.mpr hkX
  obtain ⟨U, hU, hAv⟩ :=
    exists_card_mul_le_card_mul_of_nonempty hpow
      (fun U ↦ #(F.filter (· ⊆ U)))
  refine ⟨U, hU, ?_⟩
  rw [card_powersetCard] at hAv
  rw [sum_card_uniformFamily_inside X F r k hFX hFr hrk] at hAv
  exact hAv

omit [Fintype V] in
/-- An upper-average consequence of uniform-subset double counting. -/
theorem exists_subset_uniformFamily_few
    (X : Finset V) (F : Finset (Finset V)) (r k : ℕ)
    (hFX : ∀ A ∈ F, A ⊆ X) (hFr : ∀ A ∈ F, A.card = r)
    (hrk : r ≤ k) (hkX : k ≤ X.card) :
    ∃ U ∈ X.powersetCard k,
      Nat.choose X.card k * #(F.filter (· ⊆ U)) ≤
        F.card * Nat.choose (X.card - r) (k - r) := by
  classical
  have hpow : (X.powersetCard k).Nonempty := by
    exact Finset.powersetCard_nonempty.mpr hkX
  obtain ⟨U, hU, hAv⟩ :=
    exists_card_mul_ge_card_mul_of_nonempty hpow
      (fun U ↦ #(F.filter (· ⊆ U)))
  refine ⟨U, hU, ?_⟩
  rw [card_powersetCard] at hAv
  rw [sum_card_uniformFamily_inside X F r k hFX hFr hrk] at hAv
  exact hAv

omit [Fintype V] in
/-- Lower-average uniform sampling in falling-factorial form.  This is the
division-free form used for edge-density estimates. -/
theorem exists_subset_uniformFamily_many_descFactorial
    (X : Finset V) (F : Finset (Finset V)) (r k : ℕ)
    (hFX : ∀ A ∈ F, A ⊆ X) (hFr : ∀ A ∈ F, A.card = r)
    (hrk : r ≤ k) (hkX : k ≤ X.card) :
    ∃ U ∈ X.powersetCard k,
      F.card * k.descFactorial r ≤
        #(F.filter (· ⊆ U)) * X.card.descFactorial r := by
  classical
  obtain ⟨U, hU, hsample⟩ :=
    exists_subset_uniformFamily_many X F r k hFX hFr hrk hkX
  refine ⟨U, hU, ?_⟩
  let c := Nat.choose (X.card - r) (k - r)
  have hcpos : 0 < c := Nat.choose_pos (by omega)
  have hchoose : Nat.choose X.card k * Nat.choose k r =
      Nat.choose X.card r * c := by
    simpa [c] using (Nat.choose_mul (n := X.card) hrk)
  have hmul := Nat.mul_le_mul_right (Nat.factorial r * Nat.choose k r) hsample
  have hcancel : c * (F.card * k.descFactorial r) ≤
      c * (#(F.filter (· ⊆ U)) * X.card.descFactorial r) := by
    calc
      c * (F.card * k.descFactorial r) =
          (F.card * c) * (Nat.factorial r * Nat.choose k r) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        ring
      _ ≤ (Nat.choose X.card k * #(F.filter (· ⊆ U))) *
          (Nat.factorial r * Nat.choose k r) := hmul
      _ = (Nat.choose X.card k * Nat.choose k r) *
          (#(F.filter (· ⊆ U)) * Nat.factorial r) := by ring
      _ = (Nat.choose X.card r * c) *
          (#(F.filter (· ⊆ U)) * Nat.factorial r) := by rw [hchoose]
      _ = c * (#(F.filter (· ⊆ U)) * X.card.descFactorial r) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        ring
  exact Nat.le_of_mul_le_mul_left hcancel hcpos

omit [Fintype V] in
/-- Upper-average uniform sampling in falling-factorial form. -/
theorem exists_subset_uniformFamily_few_descFactorial
    (X : Finset V) (F : Finset (Finset V)) (r k : ℕ)
    (hFX : ∀ A ∈ F, A ⊆ X) (hFr : ∀ A ∈ F, A.card = r)
    (hrk : r ≤ k) (hkX : k ≤ X.card) :
    ∃ U ∈ X.powersetCard k,
      #(F.filter (· ⊆ U)) * X.card.descFactorial r ≤
        F.card * k.descFactorial r := by
  classical
  obtain ⟨U, hU, hsample⟩ :=
    exists_subset_uniformFamily_few X F r k hFX hFr hrk hkX
  refine ⟨U, hU, ?_⟩
  let c := Nat.choose (X.card - r) (k - r)
  have hcpos : 0 < c := Nat.choose_pos (by omega)
  have hchoose : Nat.choose X.card k * Nat.choose k r =
      Nat.choose X.card r * c := by
    simpa [c] using (Nat.choose_mul (n := X.card) hrk)
  have hmul := Nat.mul_le_mul_right (Nat.factorial r * Nat.choose k r) hsample
  have hcancel : c * (#(F.filter (· ⊆ U)) * X.card.descFactorial r) ≤
      c * (F.card * k.descFactorial r) := by
    calc
      c * (#(F.filter (· ⊆ U)) * X.card.descFactorial r) =
          (Nat.choose X.card k * #(F.filter (· ⊆ U))) *
            (Nat.factorial r * Nat.choose k r) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        calc
          c * (#(F.filter (· ⊆ U)) * (Nat.factorial r * Nat.choose X.card r)) =
              (Nat.choose X.card r * c) *
                (#(F.filter (· ⊆ U)) * Nat.factorial r) := by ring
          _ = (Nat.choose X.card k * Nat.choose k r) *
                (#(F.filter (· ⊆ U)) * Nat.factorial r) := by rw [hchoose]
          _ = (Nat.choose X.card k * #(F.filter (· ⊆ U))) *
                (Nat.factorial r * Nat.choose k r) := by ring
      _ ≤ (F.card * c) * (Nat.factorial r * Nat.choose k r) := hmul
      _ = c * (F.card * k.descFactorial r) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        ring
  exact Nat.le_of_mul_le_mul_left hcancel hcpos

/-- Edge-sampling specialization. -/
theorem exists_subset_edges_many_descFactorial
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (k : ℕ)
    (h2k : 2 ≤ k) (hkX : k ≤ X.card) :
    ∃ U ∈ X.powersetCard k,
      (edgesInside G X).card * k.descFactorial 2 ≤
        (edgesInside G U).card * X.card.descFactorial 2 := by
  obtain ⟨U, hU, hineq⟩ :=
    exists_subset_uniformFamily_many_descFactorial X (edgeVertexSets G X) 2 k
      (edgeVertexSets_subset G X) (edgeVertexSets_uniform G X) h2k hkX
  refine ⟨U, hU, ?_⟩
  have hUX : U ⊆ X := (Finset.mem_powersetCard.mp hU).1
  rw [card_edgeVertexSets] at hineq
  rw [filter_edgeVertexSets_subset_eq G hUX, card_edgeVertexSets] at hineq
  exact hineq

/-- Triangle-sampling specialization. -/
theorem exists_subset_triangles_few_descFactorial
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (k : ℕ)
    (h3k : 3 ≤ k) (hkX : k ≤ X.card) :
    ∃ U ∈ X.powersetCard k,
      (trianglesInside G U).card * X.card.descFactorial 3 ≤
        (trianglesInside G X).card * k.descFactorial 3 := by
  have hTX : ∀ T ∈ trianglesInside G X, T ⊆ X := by
    intro T hT
    exact (mem_trianglesInside_iff.mp hT).2
  have hT3 : ∀ T ∈ trianglesInside G X, T.card = 3 := by
    intro T hT
    exact (mem_trianglesInside_iff.mp hT).1.card_eq
  obtain ⟨U, hU, hineq⟩ :=
    exists_subset_uniformFamily_few_descFactorial X (trianglesInside G X) 3 k
      hTX hT3 h3k hkX
  refine ⟨U, hU, ?_⟩
  have hUX : U ⊆ X := (Finset.mem_powersetCard.mp hU).1
  rw [filter_trianglesInside_subset_eq G hUX] at hineq
  exact hineq

/-! ## Deleting one vertex from each triangle -/

/-- Removing at most one chosen vertex per triangle leaves a triangle-free
induced subgraph. -/
theorem exists_triangleFree_subset
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    ∃ U' ⊆ U,
      U.card - (trianglesInside G U).card ≤ U'.card ∧
        (G.induce (U' : Set V)).CliqueFree 3 := by
  classical
  let T := trianglesInside G U
  let qNonempty : ∀ Q : T, ∃ v, v ∈ Q.1 := fun Q ↦ by
      have hcard : Q.1.card = 3 := (mem_trianglesInside_iff.mp Q.2).1.card_eq
      have hpos : 0 < Q.1.card := by omega
      exact Finset.card_pos.mp hpos
  let pick : T → V := fun Q ↦ Classical.choose (qNonempty Q)
  let R : Finset V := T.attach.image pick
  let U' := U \ R
  have hRcard : R.card ≤ T.card := by
    exact (Finset.card_image_le.trans_eq Finset.card_attach)
  have hcard : U.card - T.card ≤ U'.card := by
    have hdiff := Finset.le_card_sdiff R U
    dsimp [U']
    omega
  have hfreeOn : G.CliqueFreeOn (U' : Set V) 3 := by
    intro Q hQU' hQ
    have hQU'fin : Q ⊆ U' := by simpa using hQU'
    have hQU : Q ⊆ U := hQU'fin.trans Finset.sdiff_subset
    have hQT : Q ∈ T := by
      exact mem_trianglesInside_iff.mpr ⟨hQ, hQU⟩
    let q : T := ⟨Q, hQT⟩
    have hpQ : pick q ∈ Q := by
      exact Classical.choose_spec (qNonempty q)
    have hpR : pick q ∈ R := by
      exact Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩
    have hpU' : pick q ∈ U' := hQU'fin hpQ
    exact (Finset.mem_sdiff.mp hpU').2 hpR
  refine ⟨U', Finset.sdiff_subset, ?_, ?_⟩
  · simpa [T] using hcard
  · exact (SimpleGraph.cliqueFree_induce_iff (G := G) (U' : Set V) 3).mpr hfreeOn

/-! ## Degree cores and induced graphs -/

@[simp] theorem card_edgesInside_univ
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (edgesInside G Finset.univ).card = G.edgeFinset.card := by
  congr 1
  ext e
  simp [edgesInside]

omit [DecidableEq V] in
/-- A finite Markov inequality for graph degrees: if four times the edge count
is at most `|V| D`, at least half the vertices have degree at most `D`. -/
theorem exists_lowDegree_core
    (G : SimpleGraph V) [DecidableRel G.Adj] {D : ℕ} (hD : 0 < D)
    (hedge : 4 * G.edgeFinset.card ≤ Fintype.card V * D) :
    ∃ Y : Finset V, Fintype.card V ≤ 2 * Y.card ∧
      ∀ v ∈ Y, G.degree v ≤ D := by
  classical
  let Y := (Finset.univ : Finset V).filter (fun v ↦ G.degree v ≤ D)
  let B := (Finset.univ : Finset V) \ Y
  have hBD : B.card * D ≤ ∑ v ∈ B, G.degree v := by
    calc
      B.card * D = ∑ _v ∈ B, D := by simp
      _ ≤ ∑ v ∈ B, G.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        have hvnot : v ∉ Y := (Finset.mem_sdiff.mp hv).2
        have : ¬ G.degree v ≤ D := by simpa [Y] using hvnot
        omega
  have hBsum : ∑ v ∈ B, G.degree v ≤ ∑ v : V, G.degree v := by
    exact Finset.sum_le_sum_of_subset (by intro v hv; simp)
  have hmul : D * (2 * B.card) ≤ D * Fintype.card V := by
    calc
      D * (2 * B.card) = 2 * (B.card * D) := by ring
      _ ≤ 2 * (∑ v ∈ B, G.degree v) := Nat.mul_le_mul_left 2 hBD
      _ ≤ 2 * (∑ v : V, G.degree v) := Nat.mul_le_mul_left 2 hBsum
      _ = 4 * G.edgeFinset.card := by
        rw [G.sum_degrees_eq_twice_card_edges]
        ring
      _ ≤ Fintype.card V * D := hedge
      _ = D * Fintype.card V := by ring
  have hBcard : 2 * B.card ≤ Fintype.card V :=
    Nat.le_of_mul_le_mul_left hmul hD
  have hpartition : B.card + Y.card = Fintype.card V := by
    have hYsub : Y ⊆ (Finset.univ : Finset V) := Finset.filter_subset _ _
    simpa [B] using Finset.card_sdiff_add_card_eq_card hYsub
  refine ⟨Y, by omega, ?_⟩
  intro v hv
  simpa [Y] using hv

omit [DecidableEq V] in
/-- The induced degree is bounded by the ambient degree. -/
theorem degree_induce_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v ≤ G.degree v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree]
  refine Fintype.card_le_of_injective
    (fun u : (G.induce (S : Set V)).neighborSet v ↦
      (⟨(u.1 : S).1, u.2⟩ : G.neighborSet (v : V))) ?_
  intro a b hab
  have hv : ((a.1 : S).1 : V) = ((b.1 : S).1 : V) :=
    congrArg (fun z : G.neighborSet (v : V) ↦ (z.1 : V)) hab
  exact Subtype.ext (Subtype.ext hv)

/-- The canonical edge count inside `S` is the edge count of the induced graph. -/
theorem card_edgesInside_eq_induce
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (edgesInside G S).card = (G.induce (S : Set V)).edgeFinset.card := by
  simpa [edgesInside] using G.card_filter_edgeFinset_toFinset_subset S

omit [Fintype V] [DecidableEq V] in
/-- Passing to an induced subgraph cannot increase the independence number. -/
theorem indepNum_induce_le
    [Finite V] (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S : Set V)).indepNum ≤ G.indepNum := by
  classical
  obtain ⟨I, hI⟩ :=
    (G.induce (S : Set V)).exists_isNIndepSet_indepNum
  let emb : S ↪ V := Function.Embedding.subtype (fun x ↦ x ∈ (S : Set V))
  have hImap : G.IsIndepSet ((I.map emb : Finset V) : Set V) := by
    intro a ha b hb hab
    obtain ⟨a', ha'I, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb'I, rfl⟩ := Finset.mem_map.mp hb
    intro hadj
    exact hI.isIndepSet ha'I hb'I
      (fun h ↦ hab (congrArg Subtype.val h)) hadj
  calc
    (G.induce (S : Set V)).indepNum = I.card := hI.card_eq.symm
    _ = (I.map emb).card := by rw [Finset.card_map]
    _ ≤ G.indepNum := hImap.card_le_indepNum

/-! ## Independent sets and the Alon score -/

/-- The finite family of all independent vertex sets of a finite graph. -/
def independentFinsets (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Finset V) :=
  Finset.univ.powerset.filter (fun I ↦ G.IsIndepSet (I : Set V))

@[simp] theorem mem_independentFinsets_iff
    {G : SimpleGraph V} [DecidableRel G.Adj] {I : Finset V} :
    I ∈ independentFinsets G ↔ G.IsIndepSet (I : Set V) := by
  simp [independentFinsets]

theorem independentFinsets_nonempty
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (independentFinsets G).Nonempty := by
  exact ⟨∅, by simp⟩

theorem card_le_indepNum_of_mem_independentFinsets
    {G : SimpleGraph V} [DecidableRel G.Adj] {I : Finset V}
    (hI : I ∈ independentFinsets G) : I.card ≤ G.indepNum := by
  exact (mem_independentFinsets_iff.mp hI).card_le_indepNum

/-- Alon's local score for an independent set.  The first summand charges
membership of `v`; the second charges chosen neighbors of `v`. -/
def alonScore (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (v : V) (I : Finset V) : ℕ :=
  (if v ∈ I then D else 0) + #(G.neighborFinset v ∩ I)

/-- Double-count incidences between vertices and the neighbors of those
vertices which lie in `I`. -/
theorem sum_card_neighbor_inter_eq_sum_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) :
    ∑ v : V, #(G.neighborFinset v ∩ I) = ∑ u ∈ I, G.degree u := by
  classical
  calc
    ∑ v : V, #(G.neighborFinset v ∩ I) =
        ∑ v ∈ (Finset.univ : Finset V),
          #(I.bipartiteAbove (fun v u : V ↦ G.Adj v u) v) := by
      apply Finset.sum_congr rfl
      intro v _
      congr 1
      ext u
      simp [Finset.bipartiteAbove, SimpleGraph.mem_neighborFinset, and_comm]
    _ = ∑ u ∈ I,
        #((Finset.univ : Finset V).bipartiteBelow
          (fun v u : V ↦ G.Adj v u) u) :=
      by
        simpa using
          (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (r := fun v u : V ↦ G.Adj v u)
            (s := (Finset.univ : Finset V)) (t := I))
    _ = ∑ u ∈ I, G.degree u := by
      apply Finset.sum_congr rfl
      intro u _
      congr 1
      ext v
      simp [Finset.bipartiteBelow, SimpleGraph.mem_neighborFinset,
        SimpleGraph.adj_comm]

/-- The total score of one independent set is at most twice the degree cap
times its cardinality. -/
theorem sum_alonScore_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hdeg : ∀ v, G.degree v ≤ D) (I : Finset V) :
    ∑ v : V, alonScore G D v I ≤ 2 * D * I.card := by
  classical
  rw [show (∑ v : V, alonScore G D v I) =
      ∑ v : V, (if v ∈ I then D else 0) +
        ∑ v : V, #(G.neighborFinset v ∩ I) by
    simp_rw [alonScore, Finset.sum_add_distrib]]
  rw [sum_card_neighbor_inter_eq_sum_degree]
  have hmem : ∑ v : V, (if v ∈ I then D else 0) = D * I.card := by
    calc
      ∑ v : V, (if v ∈ I then D else 0) = ∑ v ∈ I, D := by simp
      _ = D * I.card := by simp [Nat.mul_comm]
  rw [hmem]
  have hdegree : ∑ u ∈ I, G.degree u ≤ I.card * D := by
    calc
      ∑ u ∈ I, G.degree u ≤ ∑ _u ∈ I, D := by
        exact Finset.sum_le_sum fun u _ ↦ hdeg u
      _ = I.card * D := by simp
  calc
    D * I.card + ∑ u ∈ I, G.degree u ≤ D * I.card + I.card * D :=
      Nat.add_le_add_left hdegree _
    _ = 2 * D * I.card := by ring

/-- Summing the preceding estimate over all independent sets. -/
theorem sum_independentFinsets_sum_alonScore_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hdeg : ∀ v, G.degree v ≤ D) :
    ∑ I ∈ independentFinsets G, ∑ v : V, alonScore G D v I ≤
      (independentFinsets G).card * (2 * D * G.indepNum) := by
  calc
    ∑ I ∈ independentFinsets G, ∑ v : V, alonScore G D v I ≤
        ∑ _I ∈ independentFinsets G, 2 * D * G.indepNum := by
      apply Finset.sum_le_sum
      intro I hI
      exact (sum_alonScore_le G D hdeg I).trans
        (Nat.mul_le_mul_left (2 * D)
          (card_le_indepNum_of_mem_independentFinsets hI))
    _ = (independentFinsets G).card * (2 * D * G.indepNum) := by simp

/-! ## The triangle-free logarithmic independence estimate -/

/-- The half logarithm is small enough that its product with the corresponding
power of two still lies below the original positive integer.  This is the
numerical scale used in the entropy argument below. -/
lemma half_log_mul_two_pow_half_log_le {D : ℕ} (hD : D ≠ 0) :
    Nat.log 2 D / 2 * 2 ^ (Nat.log 2 D / 2) ≤ D := by
  let k := Nat.log 2 D
  let L := k / 2
  have hLpow : L ≤ 2 ^ L := (Nat.lt_two_pow_self).le
  have hdouble : L + L ≤ k := by
    dsimp [L]
    omega
  calc
    Nat.log 2 D / 2 * 2 ^ (Nat.log 2 D / 2) = L * 2 ^ L := by rfl
    _ ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul_right _ hLpow
    _ = 2 ^ (L + L) := by rw [pow_add]
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hdouble
    _ ≤ D := Nat.pow_log_le_self 2 hD

omit [Fintype V] [DecidableEq V] in
/-- The sum of the cardinalities of all subsets of a finite set. -/
lemma sum_card_powerset (A : Finset V) :
    ∑ X ∈ A.powerset, X.card = A.card * 2 ^ (A.card - 1) := by
  rw [Finset.sum_powerset_apply_card (f := fun n : ℕ ↦ n)]
  simpa [nsmul_eq_mul, Nat.mul_comm] using Nat.sum_range_mul_choose A.card

/-- The elementary numerical inequality behind the conditional independent-set
calculation.  The two cases say that the available neighborhood is either no
larger than the logarithmic scale, or itself supplies the logarithmic charge. -/
lemma fiber_numeric_bound (D L x : ℕ) (hscale : L * 2 ^ L ≤ D) :
    (1 + 2 ^ x) * L ≤ 4 * (D + x * 2 ^ (x - 1)) := by
  by_cases hx : x ≤ L
  · have hpow : 2 ^ x ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hx
    calc
      (1 + 2 ^ x) * L ≤ (2 ^ L + 2 ^ L) * L := by
        exact Nat.mul_le_mul_right L (Nat.add_le_add Nat.one_le_two_pow hpow)
      _ = 2 * (L * 2 ^ L) := by ring
      _ ≤ 2 * D := Nat.mul_le_mul_left 2 hscale
      _ ≤ 4 * (D + x * 2 ^ (x - 1)) := by omega
  · have hLx : L ≤ x := by omega
    have hx0 : x ≠ 0 := by omega
    have hpowone : 1 ≤ 2 ^ x := Nat.one_le_two_pow
    calc
      (1 + 2 ^ x) * L ≤ (2 ^ x + 2 ^ x) * x := by
        exact Nat.mul_le_mul (Nat.add_le_add hpowone le_rfl) hLx
      _ = 4 * (x * 2 ^ (x - 1)) := by
        rw [← mul_pow_sub_one hx0 2]
        ring
      _ ≤ 4 * (D + x * 2 ^ (x - 1)) := by omega

/-- The vertices of an independent set outside the closed neighborhood of
`v`.  This is the conditioning variable in Alon's entropy argument. -/
def outsidePart (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (I : Finset V) : Finset V :=
  I \ insert v (G.neighborFinset v)

/-- Neighbors of `v` which can be adjoined to the conditioned outside part
without creating an edge across the two parts. -/
def availableNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) : Finset V :=
  (G.neighborFinset v).filter (fun u ↦ ∀ w ∈ S, ¬ G.Adj u w)

@[simp] lemma mem_outsidePart_iff
    {G : SimpleGraph V} [DecidableRel G.Adj] {v u : V} {I : Finset V} :
    u ∈ outsidePart G v I ↔ u ∈ I ∧ u ≠ v ∧ ¬ G.Adj v u := by
  simp [outsidePart, SimpleGraph.mem_neighborFinset]

@[simp] lemma mem_availableNeighbors_iff
    {G : SimpleGraph V} [DecidableRel G.Adj] {v u : V} {S : Finset V} :
    u ∈ availableNeighbors G v S ↔
      G.Adj v u ∧ ∀ w ∈ S, ¬ G.Adj u w := by
  simp [availableNeighbors, SimpleGraph.mem_neighborFinset]

omit [Fintype V] [DecidableEq V] in
lemma not_adj_of_mem_independent
    {G : SimpleGraph V} {I : Finset V} (hI : G.IsIndepSet (I : Set V))
    {u w : V} (hu : u ∈ I) (hw : w ∈ I) : ¬ G.Adj u w := by
  intro huw
  exact hI hu hw huw.ne huw

omit [Fintype V] [DecidableEq V] in
lemma isIndepSet_mono_finset
    {G : SimpleGraph V} {I J : Finset V} (hI : G.IsIndepSet (I : Set V))
    (hJI : J ⊆ I) : G.IsIndepSet (J : Set V) := by
  exact Set.Pairwise.mono (by simpa using hJI) hI

lemma outsidePart_isIndepSet
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {I : Finset V}
    (hI : G.IsIndepSet (I : Set V)) :
    G.IsIndepSet (outsidePart G v I : Set V) := by
  exact isIndepSet_mono_finset hI (Finset.sdiff_subset)

omit [Fintype V] in
lemma insert_vertex_isIndepSet
    {G : SimpleGraph V} {v : V} {S : Finset V}
    (hS : G.IsIndepSet (S : Set V))
    (hSv : v ∉ S) (hSneigh : ∀ u ∈ S, ¬ G.Adj v u) :
    G.IsIndepSet ((↑(insert v S) : Set V)) := by
  intro a ha b hb hab
  change a ∈ insert v S at ha
  change b ∈ insert v S at hb
  rw [mem_insert] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact (hab rfl).elim
    · exact hSneigh b hb
  · rcases hb with rfl | hb
    · simpa [SimpleGraph.adj_comm] using hSneigh a ha
    · exact hS ha hb hab

lemma union_available_isIndepSet
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {S X : Finset V}
    (htriangle : G.CliqueFree 3) (hS : G.IsIndepSet (S : Set V))
    (hX : X ⊆ availableNeighbors G v S) :
    G.IsIndepSet ((↑(S ∪ X) : Set V)) := by
  have hN : G.IsIndepSet (G.neighborSet v) :=
    G.isIndepSet_neighborSet_of_triangleFree htriangle v
  intro a ha b hb hab
  change a ∈ S ∪ X at ha
  change b ∈ S ∪ X at hb
  rw [mem_union] at ha hb
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact hS ha hb hab
    · have hbA := mem_availableNeighbors_iff.mp (hX hb)
      simpa [SimpleGraph.adj_comm] using hbA.2 a ha
  · rcases hb with hb | hb
    · exact (mem_availableNeighbors_iff.mp (hX ha)).2 b hb
    · exact hN
        (by simpa [SimpleGraph.mem_neighborSet] using
          (mem_availableNeighbors_iff.mp (hX ha)).1)
        (by simpa [SimpleGraph.mem_neighborSet] using
          (mem_availableNeighbors_iff.mp (hX hb)).1)
        hab

lemma outsidePart_insert_vertex
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {S : Finset V}
    (hSv : v ∉ S) (hSneigh : ∀ u ∈ S, ¬ G.Adj v u) :
    outsidePart G v (insert v S) = S := by
  ext u
  rw [mem_outsidePart_iff]
  simp only [mem_insert]
  constructor
  · rintro ⟨hu, huv, _⟩
    exact hu.resolve_left huv
  · intro hu
    exact ⟨Or.inr hu, fun huv ↦ hSv (huv ▸ hu), hSneigh u hu⟩

lemma outsidePart_union_available
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {S X : Finset V}
    (hSv : v ∉ S) (hSneigh : ∀ u ∈ S, ¬ G.Adj v u)
    (hX : X ⊆ availableNeighbors G v S) :
    outsidePart G v (S ∪ X) = S := by
  ext u
  rw [mem_outsidePart_iff]
  simp only [mem_union]
  constructor
  · rintro ⟨huS | huX, _, hnot⟩
    · exact huS
    · exact (hnot (mem_availableNeighbors_iff.mp (hX huX)).1).elim
  · intro huS
    exact ⟨Or.inl huS, fun huv ↦ hSv (huv ▸ huS), hSneigh u huS⟩

/-- The finite set of conditioning values actually attained by independent
sets. -/
def outsideBases (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Finset (Finset V) :=
  (independentFinsets G).image (outsidePart G v)

/-- The fibre of independent sets with a prescribed outside part. -/
def independentFiber (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) : Finset (Finset V) :=
  (independentFinsets G).filter (fun I ↦ outsidePart G v I = S)

/-- The explicit conditional family: either choose `v`, or choose an arbitrary
subset of the available neighbors of `v`. -/
def independentFiberCode (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) : Finset (Finset V) :=
  insert (insert v S)
    ((availableNeighbors G v S).powerset.image (fun X ↦ S ∪ X))

lemma outsideBase_properties
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {S : Finset V}
    (hS : S ∈ outsideBases G v) :
    G.IsIndepSet (S : Set V) ∧ v ∉ S ∧
      ∀ u ∈ S, ¬ G.Adj v u := by
  obtain ⟨I, hI, hout⟩ := Finset.mem_image.mp hS
  have hIind : G.IsIndepSet (I : Set V) :=
    mem_independentFinsets_iff.mp hI
  have hSind : G.IsIndepSet (S : Set V) := by
    rw [← hout]
    exact outsidePart_isIndepSet hIind
  have hSv : v ∉ S := by
    intro hv
    have hv' : v ∈ outsidePart G v I := by simpa [hout] using hv
    exact (mem_outsidePart_iff.mp hv').2.1 rfl
  refine ⟨hSind, hSv, ?_⟩
  intro u hu
  have hu' : u ∈ outsidePart G v I := by simpa [hout] using hu
  exact (mem_outsidePart_iff.mp hu').2.2

/-- In a triangle-free graph, every conditional fibre of independent sets has
the claimed explicit form. -/
theorem independentFiber_eq_code
    {G : SimpleGraph V} [DecidableRel G.Adj] (htriangle : G.CliqueFree 3)
    (v : V) {S : Finset V} (hS : S ∈ outsideBases G v) :
    independentFiber G v S = independentFiberCode G v S := by
  classical
  obtain ⟨I₀, hI₀, hout₀⟩ := Finset.mem_image.mp hS
  have hI₀ind : G.IsIndepSet (I₀ : Set V) :=
    mem_independentFinsets_iff.mp hI₀
  have hSind : G.IsIndepSet (S : Set V) := by
    rw [← hout₀]
    exact outsidePart_isIndepSet hI₀ind
  have hSv : v ∉ S := by
    intro hv
    have hv' : v ∈ outsidePart G v I₀ := by simpa [hout₀] using hv
    exact (mem_outsidePart_iff.mp hv').2.1 rfl
  have hSneigh : ∀ u ∈ S, ¬ G.Adj v u := by
    intro u hu
    have hu' : u ∈ outsidePart G v I₀ := by simpa [hout₀] using hu
    exact (mem_outsidePart_iff.mp hu').2.2
  ext J
  simp only [independentFiber, independentFiberCode, mem_filter,
    mem_insert, mem_image, mem_powerset]
  constructor
  · rintro ⟨hJ, hout⟩
    have hJind : G.IsIndepSet (J : Set V) :=
      mem_independentFinsets_iff.mp hJ
    by_cases hv : v ∈ J
    · left
      apply Finset.ext
      intro u
      constructor
      · intro huJ
        by_cases huv : u = v
        · simp [huv]
        · have huout : u ∈ outsidePart G v J :=
            mem_outsidePart_iff.mpr
              ⟨huJ, huv, not_adj_of_mem_independent hJind hv huJ⟩
          have huS : u ∈ S := by simpa [hout] using huout
          simp [huS]
      · intro hu
        rcases (mem_insert.mp hu) with rfl | huS
        · exact hv
        · have huout : u ∈ outsidePart G v J := by simpa [hout] using huS
          exact (mem_outsidePart_iff.mp huout).1
    · right
      let X := G.neighborFinset v ∩ J
      have hXA : X ⊆ availableNeighbors G v S := by
        intro u hu
        have hu' : u ∈ G.neighborFinset v ∩ J := by simpa [X] using hu
        have hu'' := Finset.mem_inter.mp hu'
        have huN : G.Adj v u := by
          simpa [SimpleGraph.mem_neighborFinset] using hu''.1
        have huJ : u ∈ J := hu''.2
        refine mem_availableNeighbors_iff.mpr ⟨huN, ?_⟩
        intro w hwS
        have hwout : w ∈ outsidePart G v J := by simpa [hout] using hwS
        exact not_adj_of_mem_independent hJind huJ
          (mem_outsidePart_iff.mp hwout).1
      refine ⟨X, hXA, ?_⟩
      apply Finset.ext
      intro u
      constructor
      · intro hu
        rcases (mem_union.mp hu) with huS | huX
        · have huout : u ∈ outsidePart G v J := by simpa [hout] using huS
          exact (mem_outsidePart_iff.mp huout).1
        · have huX' : u ∈ G.neighborFinset v ∩ J := by
            simpa [X] using huX
          exact (Finset.mem_inter.mp huX').2
      · intro huJ
        by_cases huN : G.Adj v u
        · exact mem_union.mpr (Or.inr (by
            show u ∈ X
            simp [X, SimpleGraph.mem_neighborFinset, huN, huJ]))
        · have huv : u ≠ v := by
            intro huv
            exact hv (huv ▸ huJ)
          exact mem_union.mpr (Or.inl (by
            have : u ∈ outsidePart G v J :=
              mem_outsidePart_iff.mpr ⟨huJ, huv, huN⟩
            simpa [hout] using this))
  · intro hJ
    rcases hJ with hJ | ⟨X, hXA, hJ⟩
    · subst J
      exact ⟨mem_independentFinsets_iff.mpr
        (insert_vertex_isIndepSet hSind hSv hSneigh),
        outsidePart_insert_vertex hSv hSneigh⟩
    · subst J
      exact ⟨mem_independentFinsets_iff.mpr
        (union_available_isIndepSet htriangle hSind hXA),
        outsidePart_union_available hSv hSneigh hXA⟩

/-- Exact size of a conditional fibre. -/
theorem card_independentFiber
    {G : SimpleGraph V} [DecidableRel G.Adj] (htriangle : G.CliqueFree 3)
    (v : V) {S : Finset V} (hS : S ∈ outsideBases G v) :
    (independentFiber G v S).card =
      1 + 2 ^ (availableNeighbors G v S).card := by
  classical
  obtain ⟨_, hSv, hSneigh⟩ := outsideBase_properties hS
  let A := availableNeighbors G v S
  let f : Finset V → Finset V := fun X ↦ S ∪ X
  have hmapinj : Set.InjOn f (A.powerset : Set (Finset V)) := by
    intro X hX Y hY hXY
    have hXA : X ⊆ A := Finset.mem_powerset.mp hX
    have hYA : Y ⊆ A := Finset.mem_powerset.mp hY
    apply Finset.ext
    intro u
    constructor
    · intro huX
      have huA := hXA huX
      have huN : G.Adj v u := by
        simpa [A] using (mem_availableNeighbors_iff.mp huA).1
      have huNotS : u ∉ S := fun huS ↦ hSneigh u huS huN
      have huUnion : u ∈ f X := mem_union.mpr (Or.inr huX)
      have huUnionY : u ∈ f Y := by simpa [hXY] using huUnion
      exact (mem_union.mp huUnionY).resolve_left huNotS
    · intro huY
      have huA := hYA huY
      have huN : G.Adj v u := by
        simpa [A] using (mem_availableNeighbors_iff.mp huA).1
      have huNotS : u ∉ S := fun huS ↦ hSneigh u huS huN
      have huUnion : u ∈ f Y := mem_union.mpr (Or.inr huY)
      have huUnionX : u ∈ f X := by simpa [hXY] using huUnion
      exact (mem_union.mp huUnionX).resolve_left huNotS
  have hnot : insert v S ∉ A.powerset.image f := by
    intro h
    obtain ⟨X, hX, hEq⟩ := Finset.mem_image.mp h
    have hvUnion : v ∈ f X := by
      rw [hEq]
      exact mem_insert_self v S
    rcases mem_union.mp hvUnion with hvS | hvX
    · exact hSv hvS
    · have hvA : v ∈ A := Finset.mem_powerset.mp hX hvX
      have hvv : G.Adj v v := by
        simpa [A] using (mem_availableNeighbors_iff.mp hvA).1
      exact hvv.ne rfl
  rw [independentFiber_eq_code htriangle v hS]
  change (insert (insert v S) (A.powerset.image f)).card = 1 + 2 ^ A.card
  rw [Finset.card_insert_of_notMem hnot]
  rw [(Finset.card_image_iff.mpr hmapinj), Finset.card_powerset]
  omega

lemma alonScore_insert_vertex
    {G : SimpleGraph V} [DecidableRel G.Adj] (D : ℕ) {v : V} {S : Finset V}
    (hSneigh : ∀ u ∈ S, ¬ G.Adj v u) :
    alonScore G D v (insert v S) = D := by
  have hinter : G.neighborFinset v ∩ insert v S = ∅ := by
    apply Finset.ext
    intro u
    constructor
    · intro hu
      have hu' := Finset.mem_inter.mp hu
      have huv : G.Adj v u := by
        simpa [SimpleGraph.mem_neighborFinset] using hu'.1
      rcases Finset.mem_insert.mp hu'.2 with rfl | huS
      · exact (huv.ne rfl).elim
      · exact (hSneigh u huS huv).elim
    · simp
  simp [alonScore, hinter]

lemma alonScore_union_available
    {G : SimpleGraph V} [DecidableRel G.Adj] (D : ℕ) {v : V} {S X : Finset V}
    (hSv : v ∉ S) (hSneigh : ∀ u ∈ S, ¬ G.Adj v u)
    (hX : X ⊆ availableNeighbors G v S) :
    alonScore G D v (S ∪ X) = X.card := by
  have hvX : v ∉ X := by
    intro hv
    have hvv := (mem_availableNeighbors_iff.mp (hX hv)).1
    exact hvv.ne rfl
  have hv : v ∉ S ∪ X := by simp [hSv, hvX]
  have hinter : G.neighborFinset v ∩ (S ∪ X) = X := by
    apply Finset.ext
    intro u
    constructor
    · intro hu
      have hu' := Finset.mem_inter.mp hu
      have huN : G.Adj v u := by
        simpa [SimpleGraph.mem_neighborFinset] using hu'.1
      rcases Finset.mem_union.mp hu'.2 with huS | huX
      · exact (hSneigh u huS huN).elim
      · exact huX
    · intro huX
      have huA := mem_availableNeighbors_iff.mp (hX huX)
      exact Finset.mem_inter.mpr
        ⟨by simpa [SimpleGraph.mem_neighborFinset] using huA.1,
          Finset.mem_union.mpr (Or.inr huX)⟩
  simp [alonScore, hv, hinter]

lemma union_available_injOn
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {S : Finset V}
    (hSneigh : ∀ u ∈ S, ¬ G.Adj v u) :
    Set.InjOn (fun X : Finset V ↦ S ∪ X)
      ((availableNeighbors G v S).powerset : Set (Finset V)) := by
  intro X hX Y hY hXY
  have hXA : X ⊆ availableNeighbors G v S := Finset.mem_powerset.mp hX
  have hYA : Y ⊆ availableNeighbors G v S := Finset.mem_powerset.mp hY
  have hXY' : S ∪ X = S ∪ Y := hXY
  apply Finset.ext
  intro u
  constructor
  · intro huX
    have huN := (mem_availableNeighbors_iff.mp (hXA huX)).1
    have huNotS : u ∉ S := fun huS ↦ hSneigh u huS huN
    have huUnionY : u ∈ S ∪ Y := by
      rw [← hXY']
      exact Finset.mem_union.mpr (Or.inr huX)
    exact (Finset.mem_union.mp huUnionY).resolve_left huNotS
  · intro huY
    have huN := (mem_availableNeighbors_iff.mp (hYA huY)).1
    have huNotS : u ∉ S := fun huS ↦ hSneigh u huS huN
    have huUnionX : u ∈ S ∪ X := by
      rw [hXY']
      exact Finset.mem_union.mpr (Or.inr huY)
    exact (Finset.mem_union.mp huUnionX).resolve_left huNotS

lemma insert_vertex_not_mem_union_available_image
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {S : Finset V}
    (hSv : v ∉ S) :
    insert v S ∉ (availableNeighbors G v S).powerset.image (fun X ↦ S ∪ X) := by
  intro h
  obtain ⟨X, hX, hEq⟩ := Finset.mem_image.mp h
  have hvUnion : v ∈ S ∪ X := by
    rw [hEq]
    exact Finset.mem_insert_self v S
  rcases Finset.mem_union.mp hvUnion with hvS | hvX
  · exact hSv hvS
  · have hvA := Finset.mem_powerset.mp hX hvX
    have hvv := (mem_availableNeighbors_iff.mp hvA).1
    exact hvv.ne rfl

/-- Exact conditional score sum. -/
theorem sum_alonScore_independentFiber
    {G : SimpleGraph V} [DecidableRel G.Adj] (htriangle : G.CliqueFree 3)
    (D : ℕ) (v : V) {S : Finset V} (hS : S ∈ outsideBases G v) :
    ∑ I ∈ independentFiber G v S, alonScore G D v I =
      D + (availableNeighbors G v S).card *
        2 ^ ((availableNeighbors G v S).card - 1) := by
  classical
  obtain ⟨_, hSv, hSneigh⟩ := outsideBase_properties hS
  let A := availableNeighbors G v S
  let f : Finset V → Finset V := fun X ↦ S ∪ X
  have hinj : Set.InjOn f (A.powerset : Set (Finset V)) := by
    simpa [A, f] using union_available_injOn (G := G) (v := v) hSneigh
  have hnot : insert v S ∉ A.powerset.image f := by
    simpa [A, f] using
      insert_vertex_not_mem_union_available_image (G := G) (v := v) hSv
  rw [independentFiber_eq_code htriangle v hS]
  change ∑ I ∈ insert (insert v S) (A.powerset.image f),
      alonScore G D v I = D + A.card * 2 ^ (A.card - 1)
  rw [Finset.sum_insert hnot]
  rw [Finset.sum_image hinj]
  rw [alonScore_insert_vertex D hSneigh]
  have hscore : ∀ X ∈ A.powerset, alonScore G D v (f X) = X.card := by
    intro X hX
    exact alonScore_union_available D hSv hSneigh (by
      simpa [A] using Finset.mem_powerset.mp hX)
  congr 1
  calc
    ∑ X ∈ A.powerset, alonScore G D v (f X) =
        ∑ X ∈ A.powerset, X.card := Finset.sum_congr rfl hscore
    _ = A.card * 2 ^ (A.card - 1) := sum_card_powerset A

/-- Every conditional fibre carries at least a fixed logarithmic fraction of
the Alon score. -/
theorem card_independentFiber_mul_le_four_sum_alonScore
    {G : SimpleGraph V} [DecidableRel G.Adj] (htriangle : G.CliqueFree 3)
    (D L : ℕ) (hscale : L * 2 ^ L ≤ D) (v : V)
    {S : Finset V} (hS : S ∈ outsideBases G v) :
    (independentFiber G v S).card * L ≤
      4 * ∑ I ∈ independentFiber G v S, alonScore G D v I := by
  rw [card_independentFiber htriangle v hS]
  rw [sum_alonScore_independentFiber htriangle D v hS]
  exact fiber_numeric_bound D L (availableNeighbors G v S).card hscale

/-- The fixed-vertex version of Alon's entropy estimate, obtained by summing
the preceding inequality over all conditioning fibres. -/
theorem independentFinsets_card_mul_le_four_sum_alonScore
    {G : SimpleGraph V} [DecidableRel G.Adj] (htriangle : G.CliqueFree 3)
    (D L : ℕ) (hscale : L * 2 ^ L ≤ D) (v : V) :
    (independentFinsets G).card * L ≤
      4 * ∑ I ∈ independentFinsets G, alonScore G D v I := by
  classical
  have hmaps : ∀ I ∈ independentFinsets G,
      outsidePart G v I ∈ outsideBases G v := by
    intro I hI
    exact Finset.mem_image.mpr ⟨I, hI, rfl⟩
  have hmapsSet : Set.MapsTo (outsidePart G v)
      (independentFinsets G : Set (Finset V))
      (outsideBases G v : Set (Finset V)) := by
    intro I hI
    exact hmaps I hI
  have hcard : (independentFinsets G).card =
      ∑ S ∈ outsideBases G v, (independentFiber G v S).card := by
    simpa [independentFiber] using
      (Finset.card_eq_sum_card_fiberwise hmapsSet)
  have hsum :
      ∑ S ∈ outsideBases G v,
          ∑ I ∈ independentFiber G v S, alonScore G D v I =
        ∑ I ∈ independentFinsets G, alonScore G D v I := by
    simpa [independentFiber] using
      (Finset.sum_fiberwise_of_maps_to hmaps (fun I ↦ alonScore G D v I))
  calc
    (independentFinsets G).card * L =
        (∑ S ∈ outsideBases G v, (independentFiber G v S).card) * L := by
      rw [hcard]
    _ = ∑ S ∈ outsideBases G v, (independentFiber G v S).card * L := by
      rw [Finset.sum_mul]
    _ ≤ ∑ S ∈ outsideBases G v,
        4 * ∑ I ∈ independentFiber G v S, alonScore G D v I := by
      apply Finset.sum_le_sum
      intro S hS
      exact card_independentFiber_mul_le_four_sum_alonScore
        htriangle D L hscale v hS
    _ = 4 * (∑ S ∈ outsideBases G v,
        ∑ I ∈ independentFiber G v S, alonScore G D v I) := by
      rw [Finset.mul_sum]
    _ = 4 * ∑ I ∈ independentFinsets G, alonScore G D v I := by
      rw [hsum]

omit [DecidableEq V] in
/-- A fully explicit form of the logarithmic independence bound for finite
triangle-free graphs of bounded maximum degree. -/
theorem triangleFree_card_mul_scale_le
    {G : SimpleGraph V} [DecidableRel G.Adj] (htriangle : G.CliqueFree 3)
    (D L : ℕ) (hdeg : ∀ v, G.degree v ≤ D)
    (hscale : L * 2 ^ L ≤ D) :
    Fintype.card V * L ≤ 8 * D * G.indepNum := by
  classical
  let F := independentFinsets G
  have hFpos : 0 < F.card := Finset.card_pos.mpr (independentFinsets_nonempty G)
  have hfixed : ∀ v : V,
      F.card * L ≤ 4 * ∑ I ∈ F, alonScore G D v I := by
    intro v
    exact independentFinsets_card_mul_le_four_sum_alonScore
      htriangle D L hscale v
  have hswap :
      ∑ v : V, ∑ I ∈ F, alonScore G D v I =
        ∑ I ∈ F, ∑ v : V, alonScore G D v I := by
    rw [Finset.sum_comm]
  have hprod : F.card * (Fintype.card V * L) ≤
      F.card * (8 * D * G.indepNum) := by
    calc
      F.card * (Fintype.card V * L) =
          Fintype.card V * (F.card * L) := by ring
      _ = ∑ _v : V, F.card * L := by
        simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
      _ ≤ ∑ v : V, 4 * ∑ I ∈ F, alonScore G D v I := by
        exact Finset.sum_le_sum fun v _ ↦ hfixed v
      _ = 4 * (∑ v : V, ∑ I ∈ F, alonScore G D v I) := by
        rw [Finset.mul_sum]
      _ = 4 * (∑ I ∈ F, ∑ v : V, alonScore G D v I) := by
        rw [hswap]
      _ ≤ 4 * (F.card * (2 * D * G.indepNum)) := by
        exact Nat.mul_le_mul_left 4
          (sum_independentFinsets_sum_alonScore_le G D hdeg)
      _ = F.card * (8 * D * G.indepNum) := by ring
  exact Nat.le_of_mul_le_mul_left hprod hFpos

omit [DecidableEq V] in
/-- The convenient half-logarithmic specialization. -/
theorem triangleFree_card_mul_half_log_le
    {G : SimpleGraph V} [DecidableRel G.Adj] (htriangle : G.CliqueFree 3)
    {D : ℕ} (hD : D ≠ 0) (hdeg : ∀ v, G.degree v ≤ D) :
    Fintype.card V * (Nat.log 2 D / 2) ≤ 8 * D * G.indepNum := by
  exact triangleFree_card_mul_scale_le htriangle D (Nat.log 2 D / 2) hdeg
    (half_log_mul_two_pow_half_log_le hD)

/-! ## The finite outer argument -/

lemma sq_le_two_mul_descFactorial_two {a : ℕ} (ha : 2 ≤ a) :
    a ^ 2 ≤ 2 * a.descFactorial 2 := by
  rw [show a.descFactorial 2 = (a - 1) * a by
    simp [Nat.descFactorial_succ, Nat.mul_comm]]
  have hsub : a - 1 + 1 = a := by omega
  nlinarith

lemma cube_le_four_mul_descFactorial_three {a : ℕ} (ha : 4 ≤ a) :
    a ^ 3 ≤ 4 * a.descFactorial 3 := by
  have h₁ : a ≤ 2 * (a - 1) := by omega
  have h₂ : a ≤ 2 * (a - 2) := by omega
  rw [show a.descFactorial 3 = (a - 2) * ((a - 1) * a) by
    simp [Nat.descFactorial_succ]]
  calc
    a ^ 3 = a * a * a := by ring
    _ ≤ (2 * (a - 2)) * (2 * (a - 1)) * a := by gcongr
    _ = 4 * ((a - 2) * ((a - 1) * a)) := by ring

lemma sixth_pow_le_oneTwentyEight_mul_half_descFactorial_three
    {m n : ℕ} (hm : 4 ≤ m) (hmn : m ^ 2 ≤ n) :
    m ^ 6 ≤ 128 * (n / 2).descFactorial 3 := by
  have hx : 4 ≤ n / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    nlinarith
  have hmn' : m ^ 2 ≤ 2 * (n / 2) + 1 := by
    omega
  have hcube := cube_le_four_mul_descFactorial_three hx
  have hhalfpos : 1 ≤ n / 2 := by omega
  calc
    m ^ 6 = (m ^ 2) ^ 3 := by ring
    _ ≤ (2 * (n / 2) + 1) ^ 3 := Nat.pow_le_pow_left hmn' 3
    _ ≤ (3 * (n / 2)) ^ 3 := by
      apply Nat.pow_le_pow_left
      omega
    _ = 27 * (n / 2) ^ 3 := by ring
    _ ≤ 27 * (4 * (n / 2).descFactorial 3) := Nat.mul_le_mul_left 27 hcube
    _ = 108 * (n / 2).descFactorial 3 := by ring
    _ ≤ 128 * (n / 2).descFactorial 3 := by omega

/-- The completely finite parameter form of Alon's dense-subset argument.
All asymptotic estimates have been isolated as the displayed natural-number
inequalities, so this theorem contains only graph theory and double counting. -/
theorem exists_dense_small_set_of_parameters
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m k D₀ B D L E₀ W : ℕ)
    (h2m : 2 ≤ m) (h3k : 3 ≤ k)
    (hmn : m ≤ Fintype.card V)
    (hmk : 2 * m ≤ k) (hkn : 2 * k ≤ Fintype.card V)
    (hD₀ : 0 < D₀)
    (hglobal :
      4 * W * (Fintype.card V).descFactorial 2 ≤
        Fintype.card V * D₀ * m.descFactorial 2)
    (hWB : W ≤ B)
    (hneighborhood : W * D₀.descFactorial 2 ≤ B * m.descFactorial 2)
    (htriangles :
      2 * Fintype.card V * B * k.descFactorial 3 ≤
        3 * k * (Fintype.card V / 2).descFactorial 3)
    (hD : 0 < D) (hscale : L * 2 ^ L ≤ D)
    (hE₀ : 8 * E₀ ≤ k * D)
    (hforce : 32 * D * m < k * L)
    (hfinal : W * k.descFactorial 2 ≤ E₀ * m.descFactorial 2)
    (halpha : G.indepNum ≤ m) :
    ∃ S : Finset V, S.card ≤ m ∧ W ≤ (edgesInside G S).card := by
  classical
  by_contra! hnowitness
  let n := Fintype.card V
  have hn : n = Fintype.card V := rfl
  have hm2pos : 0 < m.descFactorial 2 := Nat.descFactorial_pos.mpr h2m
  have hn2pos : 0 < n.descFactorial 2 :=
    Nat.descFactorial_pos.mpr (h2m.trans hmn)
  /- A failure of the conclusion first forces the whole graph to be sparse. -/
  obtain ⟨S₀, hS₀, hsamp₀⟩ :=
    exists_subset_edges_many_descFactorial G (Finset.univ : Finset V) m h2m (by
      simpa using hmn)
  have hS₀card : S₀.card ≤ m := by
    exact (Finset.mem_powersetCard.mp hS₀).2.le
  have hS₀small : (edgesInside G S₀).card < W := hnowitness S₀ hS₀card
  have hsparseMul :
      4 * G.edgeFinset.card * m.descFactorial 2 <
        (n * D₀) * m.descFactorial 2 := by
    calc
      4 * G.edgeFinset.card * m.descFactorial 2 =
          4 * ((edgesInside G (Finset.univ : Finset V)).card *
            m.descFactorial 2) := by rw [card_edgesInside_univ]; ring
      _ ≤ 4 * ((edgesInside G S₀).card * n.descFactorial 2) := by
        simpa [n] using Nat.mul_le_mul_left 4 hsamp₀
      _ < 4 * (W * n.descFactorial 2) := by
        exact Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_right hS₀small hn2pos) (by norm_num)
      _ ≤ (n * D₀) * m.descFactorial 2 := by
        convert hglobal using 1
        all_goals simp [n]
        all_goals ring
  have hsparse : 4 * G.edgeFinset.card ≤ n * D₀ :=
    (Nat.lt_of_mul_lt_mul_right hsparseMul).le
  obtain ⟨Y, hYlarge, hYdeg⟩ := exists_lowDegree_core G hD₀ (by
    simpa [n] using hsparse)
  have hYn : Y.card ≤ n := by simpa [n] using Finset.card_le_card (Finset.subset_univ Y)
  have hhalfY : n / 2 ≤ Y.card := by omega
  /- Otherwise an overfull neighborhood, sampled down to `m` vertices when
  necessary, would itself be the required witness. -/
  have hlocal : ∀ v ∈ Y,
      (edgesInside G (G.neighborFinset v ∩ Y)).card ≤ B := by
    intro v hv
    let N := G.neighborFinset v ∩ Y
    have hNdeg : N.card ≤ D₀ := by
      calc
        N.card ≤ (G.neighborFinset v).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = G.degree v := G.card_neighborFinset_eq_degree v
        _ ≤ D₀ := hYdeg v hv
    by_cases hNm : N.card ≤ m
    · exact (hnowitness N hNm).le.trans hWB
    · have hmN : m ≤ N.card := by omega
      obtain ⟨S, hS, hsamp⟩ :=
        exists_subset_edges_many_descFactorial G N m h2m hmN
      have hScard : S.card ≤ m := (Finset.mem_powersetCard.mp hS).2.le
      have hSsmall : (edgesInside G S).card < W := hnowitness S hScard
      have hNdf : N.card.descFactorial 2 ≤ D₀.descFactorial 2 :=
        Nat.descFactorial_le 2 hNdeg
      have hmul :
          (edgesInside G N).card * m.descFactorial 2 <
            B * m.descFactorial 2 := by
        calc
          (edgesInside G N).card * m.descFactorial 2 ≤
              (edgesInside G S).card * N.card.descFactorial 2 := hsamp
          _ ≤ (edgesInside G S).card * D₀.descFactorial 2 :=
            Nat.mul_le_mul_left _ hNdf
          _ < W * D₀.descFactorial 2 :=
            Nat.mul_lt_mul_of_pos_right hSsmall
              (Nat.descFactorial_pos.mpr (h2m.trans (hmN.trans hNdeg)))
          _ ≤ B * m.descFactorial 2 := hneighborhood
      exact (Nat.lt_of_mul_lt_mul_right hmul).le
  have htriangleCount : 3 * (trianglesInside G Y).card ≤ n * B := by
    calc
      3 * (trianglesInside G Y).card ≤ Y.card * B :=
        three_mul_card_trianglesInside_le G Y B hlocal
      _ ≤ n * B := Nat.mul_le_mul_right B hYn
  /- Sample a medium-sized set and delete one vertex from every surviving
  triangle. -/
  have hkY : k ≤ Y.card := by omega
  obtain ⟨U, hU, hsampT⟩ :=
    exists_subset_triangles_few_descFactorial G Y k h3k hkY
  have hUcard : U.card = k := (Finset.mem_powersetCard.mp hU).2
  have hY3pos : 0 < Y.card.descFactorial 3 :=
    Nat.descFactorial_pos.mpr (h3k.trans hkY)
  have hhalfDf : (n / 2).descFactorial 3 ≤ Y.card.descFactorial 3 :=
    Nat.descFactorial_le 3 hhalfY
  have hfewMul :
      (2 * (trianglesInside G U).card) * (3 * Y.card.descFactorial 3) ≤
        k * (3 * Y.card.descFactorial 3) := by
    calc
      (2 * (trianglesInside G U).card) * (3 * Y.card.descFactorial 3) =
          6 * ((trianglesInside G U).card * Y.card.descFactorial 3) := by ring
      _ ≤ 6 * ((trianglesInside G Y).card * k.descFactorial 3) :=
        Nat.mul_le_mul_left 6 hsampT
      _ = 2 * (3 * (trianglesInside G Y).card) * k.descFactorial 3 := by ring
      _ ≤ 2 * (n * B) * k.descFactorial 3 := by
        exact Nat.mul_le_mul_right (k.descFactorial 3)
          (Nat.mul_le_mul_left 2 htriangleCount)
      _ = 2 * n * B * k.descFactorial 3 := by ring
      _ ≤ 3 * k * (n / 2).descFactorial 3 := by
        simpa [n] using htriangles
      _ ≤ 3 * k * Y.card.descFactorial 3 :=
        Nat.mul_le_mul_left (3 * k) hhalfDf
      _ = k * (3 * Y.card.descFactorial 3) := by ring
  have hfew : 2 * (trianglesInside G U).card ≤ k :=
    Nat.le_of_mul_le_mul_right hfewMul (by positivity)
  obtain ⟨U', hU'U, hU'card, hU'free⟩ := exists_triangleFree_subset G U
  have hkU' : k ≤ 2 * U'.card := by omega
  have hmU' : m ≤ U'.card := by omega
  /- The triangle-free logarithmic estimate forces many edges in `U'`. -/
  have hmanyU' : E₀ ≤ (edgesInside G U').card := by
    by_contra! hfewEdges
    let H := G.induce (U' : Set V)
    have hedgeH : 4 * H.edgeFinset.card ≤ Fintype.card U' * D := by
      have hcardH : H.edgeFinset.card = (edgesInside G U').card := by
        simpa [H] using (card_edgesInside_eq_induce G U').symm
      have h8 : 8 * (edgesInside G U').card < 8 * E₀ :=
        Nat.mul_lt_mul_of_pos_left hfewEdges (by norm_num)
      have hkD : k * D ≤ (2 * U'.card) * D := Nat.mul_le_mul_right D hkU'
      have hlt : 8 * (edgesInside G U').card < 2 * (U'.card * D) := by
        calc
          8 * (edgesInside G U').card < 8 * E₀ := h8
          _ ≤ k * D := hE₀
          _ ≤ (2 * U'.card) * D := hkD
          _ = 2 * (U'.card * D) := by ring
      have hlt' : 4 * (edgesInside G U').card < U'.card * D := by
        apply Nat.lt_of_mul_lt_mul_left (a := 2)
        convert hlt using 1
        all_goals ring
      rw [hcardH]
      simpa using hlt'.le
    obtain ⟨Z, hZlarge, hZdeg⟩ := exists_lowDegree_core H hD hedgeH
    let K := H.induce (Z : Set U')
    have hKfree : K.CliqueFree 3 := by
      apply (SimpleGraph.cliqueFree_induce_iff (G := H) (Z : Set U') 3).mpr
      exact hU'free.cliqueFreeOn
    have hKdeg : ∀ z, K.degree z ≤ D := by
      intro z
      exact (degree_induce_le H Z z).trans (hZdeg z z.property)
    have hKindep : K.indepNum ≤ m := by
      calc
        K.indepNum ≤ H.indepNum := indepNum_induce_le H Z
        _ ≤ G.indepNum := by simpa [H] using indepNum_induce_le G U'
        _ ≤ m := halpha
    have hlog := triangleFree_card_mul_scale_le hKfree D L hKdeg hscale
    have hZbound : Z.card * L ≤ 8 * D * m := by
      calc
        Z.card * L = Fintype.card Z * L := by simp
        _ ≤ 8 * D * K.indepNum := hlog
        _ ≤ 8 * D * m := Nat.mul_le_mul_left (8 * D) hKindep
    have hZU : U'.card ≤ 2 * Z.card := by simpa using hZlarge
    have hkZ : k ≤ 4 * Z.card := by
      calc
        k ≤ 2 * U'.card := hkU'
        _ ≤ 2 * (2 * Z.card) := Nat.mul_le_mul_left 2 hZU
        _ = 4 * Z.card := by ring
    have : k * L ≤ 32 * D * m := by
      calc
        k * L ≤ (4 * Z.card) * L := Nat.mul_le_mul_right L hkZ
        _ = 4 * (Z.card * L) := by ring
        _ ≤ 4 * (8 * D * m) := Nat.mul_le_mul_left 4 hZbound
        _ = 32 * D * m := by ring
    omega
  obtain ⟨S, hS, hsampFinal⟩ :=
    exists_subset_edges_many_descFactorial G U' m h2m hmU'
  have hScard : S.card ≤ m := (Finset.mem_powersetCard.mp hS).2.le
  have hU'df : U'.card.descFactorial 2 ≤ k.descFactorial 2 := by
    apply Nat.descFactorial_le 2
    exact Finset.card_le_card hU'U |>.trans_eq hUcard
  have hWmul : W * U'.card.descFactorial 2 ≤
      (edgesInside G S).card * U'.card.descFactorial 2 := by
    calc
      W * U'.card.descFactorial 2 ≤ W * k.descFactorial 2 :=
        Nat.mul_le_mul_left W hU'df
      _ ≤ E₀ * m.descFactorial 2 := hfinal
      _ ≤ (edgesInside G U').card * m.descFactorial 2 :=
        Nat.mul_le_mul_right (m.descFactorial 2) hmanyU'
      _ ≤ (edgesInside G S).card * U'.card.descFactorial 2 := hsampFinal
  exact Nat.not_le_of_lt (hnowitness S hScard)
    (Nat.le_of_mul_le_mul_right hWmul
      (Nat.descFactorial_pos.mpr (h2m.trans hmU')))

/-! ## Explicit scales and the final statement -/

/-- An explicit natural-number version of Problem 801.  The constant is very
far from optimal; its only purpose is to make every rounding step transparent. -/
theorem erdos_801_explicit_decidable
    {n : ℕ} (hnlarge : 2 ^ (2 ^ 11) ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (halpha : G.indepNum ≤ Nat.sqrt n) :
    ∃ S : Finset (Fin n), S.card ≤ Nat.sqrt n ∧
      Nat.sqrt n * Nat.log 2 n ≤ 2 ^ 24 * (edgesInside G S).card := by
  classical
  let m := Nat.sqrt n
  let q := Nat.log 2 n
  let L := q / 1024
  let p := 2 ^ L
  let k := 64 * m * p
  let D₀ := 64 * m * q
  let B := 2 * m * q ^ 3
  let D := L * p
  let E₀ := 4 * m * L * p ^ 2
  let W := m * L / 4096
  have hnpos : n ≠ 0 := by
    exact ((Nat.pow_pos (by norm_num : 0 < 2)).trans_le hnlarge).ne'
  have hq : 2048 ≤ q := by
    dsimp [q]
    have hq' : 2 ^ 11 ≤ Nat.log 2 n :=
      Nat.le_log_of_pow_le (Nat.succ_lt_succ (Nat.zero_lt_succ 0)) hnlarge
    norm_num at hq'
    exact hq'
  have hL : 2 ≤ L := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 1024)).2
    simpa [L] using hq
  have h1024L : 1024 * L ≤ q := by
    simpa [L, Nat.mul_comm] using Nat.div_mul_le_self q 1024
  have hqL : q ≤ 2048 * L := by
    have hlt := Nat.lt_mul_div_succ q (by norm_num : 0 < 1024)
    change q < 1024 * (L + 1) at hlt
    omega
  have hLp : L ≤ p := by
    exact (@Nat.lt_two_pow_self L).le
  have hp2 : 2 ≤ p := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = p := rfl
  have hqP : q ≤ 2048 * p := hqL.trans (Nat.mul_le_mul_left 2048 hLp)
  have hp256sq_m : p ^ 256 * p ^ 256 ≤ m := by
    apply Nat.le_sqrt.mpr
    calc
      (p ^ 256 * p ^ 256) * (p ^ 256 * p ^ 256) =
          (2 ^ (L * 256) * 2 ^ (L * 256)) *
            (2 ^ (L * 256) * 2 ^ (L * 256)) := by
        rw [show p = 2 ^ L from rfl, ← Nat.pow_mul]
      _ = 2 ^ (L * 256 + L * 256) * 2 ^ (L * 256 + L * 256) := by
        rw [Nat.pow_add]
      _ = 2 ^ ((L * 256 + L * 256) + (L * 256 + L * 256)) := by
        rw [Nat.pow_add]
        ring
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ n := Nat.pow_log_le_self 2 hnpos
  have hdom : 2 ^ 24 * q ^ 3 * p ^ 2 ≤ m := by
    have hqcube : q ^ 3 ≤ (2048 * p) ^ 3 := Nat.pow_le_pow_left hqP 3
    have hconst : 2 ^ 57 ≤ p ^ 251 := by
      calc
        2 ^ 57 ≤ p ^ 57 := Nat.pow_le_pow_left hp2 57
        _ ≤ p ^ 251 := Nat.pow_le_pow_right (by positivity) (by norm_num)
    calc
      2 ^ 24 * q ^ 3 * p ^ 2 ≤
          2 ^ 24 * (2048 * p) ^ 3 * p ^ 2 := by gcongr
      _ = 2 ^ 57 * p ^ 5 := by ring
      _ ≤ p ^ 251 * p ^ 5 := Nat.mul_le_mul_right (p ^ 5) hconst
      _ = p ^ 256 := by rw [← Nat.pow_add]
      _ ≤ p ^ 256 * p ^ 256 := by
        simpa using Nat.mul_le_mul_left (p ^ 256) (Nat.one_le_pow 256 p (by omega))
      _ ≤ m := hp256sq_m
  have hm4 : 4 ≤ m := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
      _ ≤ p ^ 256 := Nat.pow_le_pow_right (by positivity) (by norm_num)
      _ ≤ p ^ 256 * p ^ 256 := by
        simpa using Nat.mul_le_mul_left (p ^ 256) (Nat.one_le_pow 256 p (by omega))
      _ ≤ m := hp256sq_m
  have hm2 : 2 ≤ m := hm4.trans' (by norm_num)
  have hmSq : m ^ 2 ≤ n := by simpa [m] using Nat.sqrt_le' n
  have hnup : n ≤ 2 * m ^ 2 := by
    have hlt : n < (m + 1) ^ 2 := by simpa [m] using Nat.lt_succ_sqrt' n
    have hlin : 2 * m + 1 ≤ m ^ 2 := by
      calc
        2 * m + 1 ≤ 3 * m := by omega
        _ ≤ m * m := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left m (show 3 ≤ m by omega)
        _ = m ^ 2 := by ring
    have hquad : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by
      calc
        (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
        _ ≤ m ^ 2 + m ^ 2 := Nat.add_le_add_left hlin _
        _ = 2 * m ^ 2 := by ring
    omega
  have hmSqDf : m ^ 2 ≤ 2 * m.descFactorial 2 :=
    sq_le_two_mul_descFactorial_two hm2
  have hW4096 : 4096 * W ≤ m * L := by
    simpa [W, Nat.mul_comm] using Nat.div_mul_le_self (m * L) 4096
  have hWle : W ≤ m * L := (Nat.div_le_self _ _)
  have hLq : L ≤ q := (Nat.div_le_self _ _)
  have h2m : 2 ≤ m := hm2
  have h3k : 3 ≤ k := by
    calc
      3 ≤ 64 * 2 * 2 := by norm_num
      _ ≤ 64 * m * p := by gcongr
      _ = k := rfl
  have hmn : m ≤ n := by
    simpa [m] using Nat.sqrt_le_self n
  have hmk : 2 * m ≤ k := by
    calc
      2 * m ≤ (64 * p) * m := Nat.mul_le_mul_right m (by omega)
      _ = k := by simp [k]; ring
  have h128p : 128 * p ≤ m := by
    calc
      128 * p ≤ 2 ^ 24 * q ^ 3 * p ^ 2 := by
        have hqpos : 1 ≤ q := by omega
        calc
          128 * p ≤ 2 ^ 24 * (1 : ℕ) ^ 3 * p ^ 2 := by
            have hpp : p ≤ p ^ 2 := by
              calc p = p * 1 := by simp
                   _ ≤ p * p := Nat.mul_le_mul_left p (by omega)
                   _ = p ^ 2 := by ring
            norm_num at hpp ⊢
            exact Nat.mul_le_mul (by norm_num) hpp
          _ ≤ 2 ^ 24 * q ^ 3 * p ^ 2 := by gcongr
      _ ≤ m := hdom
  have hkn : 2 * k ≤ n := by
    calc
      2 * k = m * (128 * p) := by simp [k]; ring
      _ ≤ m * m := Nat.mul_le_mul_left m h128p
      _ = m ^ 2 := by ring
      _ ≤ n := hmSq
  have hD₀ : 0 < D₀ := by positivity
  have hglobal :
      4 * W * n.descFactorial 2 ≤ n * D₀ * m.descFactorial 2 := by
    have hnDf : n.descFactorial 2 ≤ n ^ 2 := Nat.descFactorial_le_pow n 2
    calc
      4 * W * n.descFactorial 2 ≤ 4 * W * n ^ 2 :=
        Nat.mul_le_mul_left (4 * W) hnDf
      _ ≤ 4 * (m * L) * n ^ 2 := by
        convert Nat.mul_le_mul_right (4 * n ^ 2) hWle using 1 <;> ring
      _ ≤ 4 * (m * q) * n ^ 2 := by
        convert Nat.mul_le_mul_right (4 * n ^ 2) (Nat.mul_le_mul_left m hLq) using 1 <;> ring
      _ = 4 * m * q * n * n := by ring
      _ ≤ 4 * m * q * n * (2 * m ^ 2) :=
        Nat.mul_le_mul_left (4 * m * q * n) hnup
      _ = 8 * n * m * q * m ^ 2 := by ring
      _ ≤ 8 * n * m * q * (2 * m.descFactorial 2) :=
        Nat.mul_le_mul_left (8 * n * m * q) hmSqDf
      _ = 16 * (n * m * q * m.descFactorial 2) := by ring
      _ ≤ 64 * (n * m * q * m.descFactorial 2) :=
        Nat.mul_le_mul_right _ (by norm_num)
      _ = n * D₀ * m.descFactorial 2 := by simp [D₀]; ring
  have hWB : W ≤ B := by
    have hqpow : q ≤ q ^ 3 := by
      calc
        q = q ^ 1 := by simp
        _ ≤ q ^ 3 := Nat.pow_le_pow_right (show 0 < q by omega) (by norm_num)
    calc
      W ≤ m * L := hWle
      _ ≤ m * q := Nat.mul_le_mul_left m hLq
      _ ≤ m * q ^ 3 := Nat.mul_le_mul_left m hqpow
      _ ≤ 2 * (m * q ^ 3) := by
        simpa using Nat.mul_le_mul_right (m * q ^ 3) (show 1 ≤ 2 by norm_num)
      _ = 2 * m * q ^ 3 := by ring
      _ = B := rfl
  have hneighborhood : W * D₀.descFactorial 2 ≤ B * m.descFactorial 2 := by
    have hDdf : D₀.descFactorial 2 ≤ D₀ ^ 2 := Nat.descFactorial_le_pow D₀ 2
    calc
      W * D₀.descFactorial 2 ≤ W * D₀ ^ 2 := Nat.mul_le_mul_left W hDdf
      _ = (4096 * W) * (m ^ 2 * q ^ 2) := by simp [D₀]; ring
      _ ≤ (m * L) * (m ^ 2 * q ^ 2) :=
        Nat.mul_le_mul_right (m ^ 2 * q ^ 2) hW4096
      _ ≤ (m * q) * (m ^ 2 * q ^ 2) :=
        Nat.mul_le_mul_right (m ^ 2 * q ^ 2) (Nat.mul_le_mul_left m hLq)
      _ = m * q ^ 3 * m ^ 2 := by ring
      _ ≤ m * q ^ 3 * (2 * m.descFactorial 2) :=
        Nat.mul_le_mul_left (m * q ^ 3) hmSqDf
      _ = B * m.descFactorial 2 := by simp [B]; ring
  have htriangles :
      2 * n * B * k.descFactorial 3 ≤
        3 * k * (n / 2).descFactorial 3 := by
    have hkDf : k.descFactorial 3 ≤ k ^ 3 := Nat.descFactorial_le_pow k 3
    have hsix := sixth_pow_le_oneTwentyEight_mul_half_descFactorial_three hm4 hmSq
    calc
      2 * n * B * k.descFactorial 3 ≤ 2 * n * B * k ^ 3 :=
        Nat.mul_le_mul_left (2 * n * B) hkDf
      _ ≤ 2 * (2 * m ^ 2) * B * k ^ 3 := by
        convert Nat.mul_le_mul_right (2 * B * k ^ 3) hnup using 1 <;> ring
      _ = 2 ^ 21 * m ^ 6 * q ^ 3 * p ^ 3 := by simp [B, k]; ring
      _ ≤ m ^ 7 * p := by
        calc
          2 ^ 21 * m ^ 6 * q ^ 3 * p ^ 3 ≤
              2 ^ 24 * q ^ 3 * p ^ 2 * (m ^ 6 * p) := by
            calc
              2 ^ 21 * m ^ 6 * q ^ 3 * p ^ 3 =
                  2 ^ 21 * q ^ 3 * p ^ 2 * (m ^ 6 * p) := by ring
              _ ≤ 2 ^ 24 * q ^ 3 * p ^ 2 * (m ^ 6 * p) := by
                have hc : (2 : ℕ) ^ 21 ≤ 2 ^ 24 :=
                  Nat.pow_le_pow_right (show 0 < (2 : ℕ) by norm_num) (by norm_num)
                convert Nat.mul_le_mul_right (q ^ 3 * p ^ 2 * (m ^ 6 * p)) hc using 1 <;> ring
          _ ≤ m * (m ^ 6 * p) := Nat.mul_le_mul_right (m ^ 6 * p) hdom
          _ = m ^ 7 * p := by ring
      _ ≤ 3 * k * (n / 2).descFactorial 3 := by
        calc
          m ^ 7 * p = m * p * m ^ 6 := by ring
          _ ≤ m * p * (128 * (n / 2).descFactorial 3) :=
            Nat.mul_le_mul_left (m * p) hsix
          _ ≤ 3 * k * (n / 2).descFactorial 3 := by
            let T := (n / 2).descFactorial 3
            calc
              m * p * (128 * T) = 128 * (m * p * T) := by ring
              _ ≤ 192 * (m * p * T) := Nat.mul_le_mul_right _ (by norm_num)
              _ = 3 * k * T := by simp [k]; ring
  have hD : 0 < D := by
    exact Nat.mul_pos (by omega) (by omega)
  have hscale : L * 2 ^ L ≤ D := by simp [D, p]
  have hE₀ : 8 * E₀ ≤ k * D := by
    calc
      8 * E₀ = 32 * (m * L * p ^ 2) := by simp [E₀]; ring
      _ ≤ 64 * (m * L * p ^ 2) := Nat.mul_le_mul_right _ (by norm_num)
      _ = k * D := by simp [k, D]; ring
  have hforce : 32 * D * m < k * L := by
    have hx : 0 < m * L * p := by positivity
    calc
      32 * D * m = 32 * (m * L * p) := by simp [D]; ring
      _ < 64 * (m * L * p) := Nat.mul_lt_mul_of_pos_right (by norm_num) hx
      _ = k * L := by simp [k]; ring
  have hfinal : W * k.descFactorial 2 ≤ E₀ * m.descFactorial 2 := by
    have hkDf : k.descFactorial 2 ≤ k ^ 2 := Nat.descFactorial_le_pow k 2
    calc
      W * k.descFactorial 2 ≤ W * k ^ 2 := Nat.mul_le_mul_left W hkDf
      _ = (4096 * W) * (m ^ 2 * p ^ 2) := by simp [k]; ring
      _ ≤ (m * L) * (m ^ 2 * p ^ 2) :=
        Nat.mul_le_mul_right (m ^ 2 * p ^ 2) hW4096
      _ = m * L * p ^ 2 * m ^ 2 := by ring
      _ ≤ m * L * p ^ 2 * (2 * m.descFactorial 2) :=
        Nat.mul_le_mul_left (m * L * p ^ 2) hmSqDf
      _ ≤ E₀ * m.descFactorial 2 := by
        calc
          m * L * p ^ 2 * (2 * m.descFactorial 2) =
              2 * (m * L * p ^ 2 * m.descFactorial 2) := by ring
          _ ≤ 4 * (m * L * p ^ 2 * m.descFactorial 2) :=
            Nat.mul_le_mul_right _ (by norm_num)
          _ = E₀ * m.descFactorial 2 := by simp [E₀]; ring
  obtain ⟨S, hScard, hWedges⟩ := exists_dense_small_set_of_parameters G
    m k D₀ B D L E₀ W h2m h3k (by simpa [m] using hmn) hmk
    (by simpa using hkn) hD₀ (by simpa using hglobal) hWB hneighborhood
    (by simpa using htriangles) hD hscale hE₀ hforce hfinal (by simpa [m] using halpha)
  refine ⟨S, by simpa [m] using hScard, ?_⟩
  have hm4096 : 4096 ≤ m := by
    calc
      4096 = 2 ^ 12 := by norm_num
      _ ≤ p ^ 12 := Nat.pow_le_pow_left hp2 12
      _ ≤ p ^ 256 := Nat.pow_le_pow_right (by positivity) (by norm_num)
      _ ≤ p ^ 256 * p ^ 256 := by
        simpa using Nat.mul_le_mul_left (p ^ 256) (Nat.one_le_pow 256 p (by omega))
      _ ≤ m := hp256sq_m
  have hmLlarge : 4096 ≤ m * L :=
    hm4096.trans (by simpa using Nat.mul_le_mul_left m (show 1 ≤ L by omega))
  have hWpos : 1 ≤ W := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4096)).2
    simpa [W] using hmLlarge
  have hmLW : m * L ≤ 8192 * W := by
    have hlt := Nat.lt_div_mul_add (a := m * L) (by norm_num : 0 < 4096)
    change m * L < W * 4096 + 4096 at hlt
    have h4096 : 4096 ≤ W * 4096 := by
      simpa using Nat.mul_le_mul_right 4096 hWpos
    omega
  calc
    Nat.sqrt n * Nat.log 2 n = m * q := rfl
    _ ≤ m * (2048 * L) := Nat.mul_le_mul_left m hqL
    _ = 2048 * (m * L) := by ring
    _ ≤ 2048 * (8192 * W) := Nat.mul_le_mul_left 2048 hmLW
    _ = 2 ^ 24 * W := by norm_num; ring
    _ ≤ 2 ^ 24 * (edgesInside G S).card := Nat.mul_le_mul_left (2 ^ 24) hWedges

/-- The explicit result without an auxiliary decidability parameter. -/
theorem erdos_801_explicit
    {n : ℕ} (hnlarge : 2 ^ (2 ^ 11) ≤ n)
    (G : SimpleGraph (Fin n))
    (halpha : G.indepNum ≤ Nat.sqrt n) :
    ∃ S : Finset (Fin n), S.card ≤ Nat.sqrt n ∧
      Nat.sqrt n * Nat.log 2 n ≤ 2 ^ 24 * edgeCountInside G S := by
  classical
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  simpa [edgeCountInside] using erdos_801_explicit_decidable hnlarge G halpha

/-- Resolution of Erdős Problem 801, with `≫` expressed by explicit
absolute constants and base-two logarithm. -/
theorem erdos_801 :
    ∃ C N : ℕ, 0 < C ∧ ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      G.indepNum ≤ Nat.sqrt n →
        ∃ S : Finset (Fin n), S.card ≤ Nat.sqrt n ∧
          Nat.sqrt n * Nat.log 2 n ≤ C * edgeCountInside G S := by
  refine ⟨2 ^ 24, 2 ^ (2 ^ 11), by positivity, ?_⟩
  intro n hn G halpha
  exact erdos_801_explicit hn G halpha

end Erdos801

#print axioms Erdos801.erdos_801
