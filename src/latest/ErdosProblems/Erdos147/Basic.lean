/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import ErdosProblems.Erdos888.ColoredGraph

/-!
# Erdős Problem 147

This file formalizes the negative resolution of the Erdős--Simonovits
minimum-degree conjecture.  The concrete counterexample is the two-fold
blow-up of the twelve-cycle, `C₁₂[2]`.  It is bipartite and 4-regular, while
Janzer's blow-up-cycle estimate gives an extremal exponent strictly below
`2 - 1 / (4 - 1) = 5 / 3`.

The detailed mathematical reconstruction, including the complete dependency
list for Janzer's counting argument, is in `tex/147.tex`.
-/

open Filter
open Asymptotics
open scoped SimpleGraph Topology

namespace Erdos147

set_option autoImplicit false

/-- The real-valued extremal-number function of a fixed finite graph. -/
noncomputable def extremalGrowth {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℝ :=
  SimpleGraph.extremalNumber n H

/-- The real power `n ↦ n ^ a` on natural inputs. -/
noncomputable def polynomialGrowth (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ a

/-- The lower bound predicted by Erdős and Simonovits for a graph of minimum
degree `r`.  The division in the exponent is real division. -/
def HasConjecturedLowerBound {W : Type*} (H : SimpleGraph W) (r : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    (polynomialGrowth (2 - 1 / ((r : ℝ) - 1) + ε)) =O[atTop] extremalGrowth H

/-- The literal universal assertion in Erdős Problem 147. -/
def ErdosSimonovitsConjecture : Prop :=
  ∀ (W : Type) [Fintype W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (r : ℕ),
      H.IsBipartite → H.minDegree = r → HasConjecturedLowerBound H r

/-- The `r`-fold blow-up of the cycle on `m` vertices. -/
def blowupCycle (m r : ℕ) : SimpleGraph (Fin m × Fin r) :=
  (SimpleGraph.cycleGraph m).comap Prod.fst

instance blowupCycle.instDecidableAdj (m r : ℕ) :
    DecidableRel (blowupCycle m r).Adj := by
  dsimp only [blowupCycle]
  infer_instance

/-- The fixed graph used to refute the conjecture. -/
abbrev counterexampleGraph : SimpleGraph (Fin 12 × Fin 2) := blowupCycle 12 2

lemma counterexampleGraph_isBipartite : counterexampleGraph.IsBipartite := by
  let c : (SimpleGraph.cycleGraph 12).Coloring Bool :=
    SimpleGraph.cycleGraph.bicoloring_of_even 12 ⟨6, by norm_num⟩
  exact (c.comap (SimpleGraph.Hom.comap Prod.fst
    (SimpleGraph.cycleGraph 12))).colorable

lemma counterexampleGraph_isRegular : counterexampleGraph.IsRegularOfDegree 4 := by
  intro v
  fin_cases v <;> decide

lemma counterexampleGraph_minDegree : counterexampleGraph.minDegree = 4 :=
  counterexampleGraph_isRegular.minDegree_eq

/-! ## The ordered-pair auxiliary graph -/

/-- Ordered pairs of distinct vertices.  Retaining the order removes all
quotients from the finite counting argument; each unordered two-set occurs
twice. -/
abbrev OrderedPair (V : Type*) := {p : V × V // p.1 ≠ p.2}

def orderedPairSupport {V : Type*} [DecidableEq V] (p : OrderedPair V) : Finset V :=
  {p.1.1, p.1.2}

@[simp] lemma mem_orderedPairSupport {V : Type*} [DecidableEq V]
    (p : OrderedPair V) (v : V) :
    v ∈ orderedPairSupport p ↔ v = p.1.1 ∨ v = p.1.2 := by
  simp [orderedPairSupport]

/-- Two ordered pairs are adjacent when they span a complete bipartite
`K₂,₂` in the host graph. -/
def pairComplete {V : Type*} (G : SimpleGraph V)
    (p q : OrderedPair V) : Prop :=
  G.Adj p.1.1 q.1.1 ∧ G.Adj p.1.1 q.1.2 ∧
    G.Adj p.1.2 q.1.1 ∧ G.Adj p.1.2 q.1.2

lemma pairComplete_comm {V : Type*} (G : SimpleGraph V) (p q : OrderedPair V) :
    pairComplete G p q ↔ pairComplete G q p := by
  constructor
  · rintro ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩
    exact ⟨h₁₁.symm, h₂₁.symm, h₁₂.symm, h₂₂.symm⟩
  · rintro ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩
    exact ⟨h₁₁.symm, h₂₁.symm, h₁₂.symm, h₂₂.symm⟩

lemma pairComplete_irrefl {V : Type*} (G : SimpleGraph V) (p : OrderedPair V) :
    ¬pairComplete G p p := by
  intro h
  exact G.irrefl h.1

def pairAuxGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph (OrderedPair V) where
  Adj := pairComplete G
  symm := by
    constructor
    exact fun _ _ h ↦ (pairComplete_comm G _ _).mp h
  loopless := by
    constructor
    exact pairComplete_irrefl G

instance pairAuxGraph.instDecidableAdj {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] : DecidableRel (pairAuxGraph G).Adj := by
  intro p q
  dsimp only [pairAuxGraph, pairComplete]
  infer_instance

lemma pairComplete_support_disjoint {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {p q : OrderedPair V} (hpq : pairComplete G p q) :
    Disjoint (orderedPairSupport p) (orderedPairSupport q) := by
  rw [Finset.disjoint_left]
  intro v hvp hvq
  simp only [mem_orderedPairSupport] at hvp hvq
  rcases hvp with hvp | hvp <;> rcases hvq with hvq | hvq
  · exact hpq.1.ne (hvp.symm.trans hvq)
  · exact hpq.2.1.ne (hvp.symm.trans hvq)
  · exact hpq.2.2.1.ne (hvp.symm.trans hvq)
  · exact hpq.2.2.2.ne (hvp.symm.trans hvq)

def orderedPairEntry {V : Type*} (p : OrderedPair V) (i : Fin 2) : V :=
  if i = 0 then p.1.1 else p.1.2

def pairCommonFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : OrderedPair V) : Finset V :=
  G.neighborFinset p.1.1 ∩ G.neighborFinset p.1.2

@[simp] lemma mem_pairCommonFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : OrderedPair V) (v : V) :
    v ∈ pairCommonFinset G p ↔ G.Adj p.1.1 v ∧ G.Adj p.1.2 v := by
  simp [pairCommonFinset]

lemma pairAuxGraph_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : OrderedPair V) :
    (pairAuxGraph G).degree p =
      (pairCommonFinset G p).card * ((pairCommonFinset G p).card - 1) := by
  classical
  let s := pairCommonFinset G p
  have hcard : ((pairAuxGraph G).neighborFinset p).card = s.offDiag.card := by
    apply Finset.card_bij (fun q _ ↦ q.1)
    · intro q hq
      rw [Finset.mem_offDiag]
      have hadj := ((pairAuxGraph G).mem_neighborFinset p q).mp hq
      exact ⟨by simpa [s] using ⟨hadj.1, hadj.2.2.1⟩,
        by simpa [s] using ⟨hadj.2.1, hadj.2.2.2⟩, q.property⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      exact Subtype.ext heq
    · intro z hz
      rw [Finset.mem_offDiag] at hz
      let q : OrderedPair V := ⟨z, hz.2.2⟩
      refine ⟨q, ?_, rfl⟩
      rw [(pairAuxGraph G).mem_neighborFinset]
      have hz₁ := (mem_pairCommonFinset G p z.1).mp (by simpa [s] using hz.1)
      have hz₂ := (mem_pairCommonFinset G p z.2).mp (by simpa [s] using hz.2.1)
      exact ⟨hz₁.1, hz₂.1, hz₁.2, hz₂.2⟩
  rw [SimpleGraph.degree, hcard, Finset.offDiag_card]
  simp [s, mul_tsub_one]

abbrev LocalConflictNeighbor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : OrderedPair V) :=
  {z : OrderedPair V // pairComplete G y z ∧
    ¬Disjoint (orderedPairSupport x) (orderedPairSupport z)}

def conflictDecoder {V : Type*} (x : OrderedPair V) (r : Fin 4 × V) : V × V :=
  if r.1 = 0 then (x.1.1, r.2)
  else if r.1 = 1 then (x.1.2, r.2)
  else if r.1 = 2 then (r.2, x.1.1)
  else (r.2, x.1.2)

lemma localConflictNeighbor_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : OrderedPair V) :
    Nat.card (LocalConflictNeighbor G x y) ≤
      4 * (pairCommonFinset G y).card := by
  classical
  let : Fintype (LocalConflictNeighbor G x y) := Fintype.ofFinite _
  let s := pairCommonFinset G y
  have hrepr : ∀ z : LocalConflictNeighbor G x y,
      ∃ r : Fin 4 × {v // v ∈ s}, conflictDecoder x (r.1, r.2.1) = z.1.1 := by
    intro z
    have hadj := z.2.1
    have hcases :
        z.1.1.1 = x.1.1 ∨ z.1.1.1 = x.1.2 ∨
        z.1.1.2 = x.1.1 ∨ z.1.1.2 = x.1.2 := by
      have hn := z.2.2
      simp only [Finset.not_disjoint_iff] at hn
      obtain ⟨v, hvx, hvz⟩ := hn
      simp only [mem_orderedPairSupport] at hvx hvz
      rcases hvx with hvx | hvx <;> rcases hvz with hvz | hvz
      · exact Or.inl (hvz.symm.trans hvx)
      · exact Or.inr (Or.inr (Or.inl (hvz.symm.trans hvx)))
      · exact Or.inr (Or.inl (hvz.symm.trans hvx))
      · exact Or.inr (Or.inr (Or.inr (hvz.symm.trans hvx)))
    rcases hcases with h | h | h | h
    · refine ⟨(0, ⟨z.1.1.2, ?_⟩), ?_⟩
      · simpa [s] using (show G.Adj y.1.1 z.1.1.2 ∧ G.Adj y.1.2 z.1.1.2 from
          ⟨hadj.2.1, hadj.2.2.2⟩)
      · apply Prod.ext
        · simpa [conflictDecoder] using h.symm
        · simp [conflictDecoder]
    · refine ⟨(1, ⟨z.1.1.2, ?_⟩), ?_⟩
      · simpa [s] using (show G.Adj y.1.1 z.1.1.2 ∧ G.Adj y.1.2 z.1.1.2 from
          ⟨hadj.2.1, hadj.2.2.2⟩)
      · apply Prod.ext
        · simpa [conflictDecoder] using h.symm
        · simp [conflictDecoder]
    · refine ⟨(2, ⟨z.1.1.1, ?_⟩), ?_⟩
      · simpa [s] using (show G.Adj y.1.1 z.1.1.1 ∧ G.Adj y.1.2 z.1.1.1 from
          ⟨hadj.1, hadj.2.2.1⟩)
      · apply Prod.ext
        · simp [conflictDecoder]
        · simpa [conflictDecoder] using h.symm
    · refine ⟨(3, ⟨z.1.1.1, ?_⟩), ?_⟩
      · simpa [s] using (show G.Adj y.1.1 z.1.1.1 ∧ G.Adj y.1.2 z.1.1.1 from
          ⟨hadj.1, hadj.2.2.1⟩)
      · have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        apply Prod.ext
        · simp [conflictDecoder, h30, h31, h32]
        · simpa [conflictDecoder, h30, h31, h32] using h.symm
  let encode : LocalConflictNeighbor G x y → Fin 4 × {v // v ∈ s} :=
    fun z ↦ Classical.choose (hrepr z)
  have hencode : ∀ z, conflictDecoder x ((encode z).1, (encode z).2.1) = z.1.1 :=
    fun z ↦ Classical.choose_spec (hrepr z)
  have hinj : Function.Injective encode := by
    intro z w hzw
    apply Subtype.ext
    apply Subtype.ext
    rw [← hencode z, ← hencode w, hzw]
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (LocalConflictNeighbor G x y) ≤
        Fintype.card (Fin 4 × {v // v ∈ s}) := Fintype.card_le_of_injective encode hinj
    _ = 4 * s.card := by simp [Fintype.card_prod]
    _ = 4 * (pairCommonFinset G y).card := by rfl

lemma commonCard_le_sqrt_degree_add_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : OrderedPair V) :
    ((pairCommonFinset G p).card : ℝ) ≤
      Real.sqrt ((pairAuxGraph G).degree p : ℝ) + 1 := by
  let d := (pairCommonFinset G p).card
  by_cases hd : d = 0
  · have hdegree0 : (pairAuxGraph G).degree p = 0 := by
      rw [pairAuxGraph_degree]
      simp [d, hd]
    simp [d, hd, hdegree0]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have hd1nat : (1 : ℕ) ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  have hdegree : ((pairAuxGraph G).degree p : ℝ) = (d : ℝ) * (d - 1) := by
    rw [pairAuxGraph_degree]
    change (↑(d * (d - 1)) : ℝ) = (d : ℝ) * (d - 1)
    rw [Nat.cast_mul, Nat.cast_sub hd1nat, Nat.cast_one]
  have hprod : 0 ≤ (d : ℝ) * (d - 1) := mul_nonneg (by positivity) (sub_nonneg.mpr hd1)
  have hsqrt_sq : (Real.sqrt ((d : ℝ) * (d - 1))) ^ 2 = (d : ℝ) * (d - 1) :=
    Real.sq_sqrt hprod
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((d : ℝ) * (d - 1)) := Real.sqrt_nonneg _
  rw [hdegree]
  nlinarith [sq_nonneg ((d : ℝ) - 1)]

lemma localConflictNeighbor_card_real_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : OrderedPair V) :
    (Nat.card (LocalConflictNeighbor G x y) : ℝ) ≤
      4 * (Real.sqrt ((pairAuxGraph G).degree y : ℝ) + 1) := by
  calc
    (Nat.card (LocalConflictNeighbor G x y) : ℝ) ≤
        4 * ((pairCommonFinset G y).card : ℝ) := by
      exact_mod_cast localConflictNeighbor_card_le G x y
    _ ≤ 4 * (Real.sqrt ((pairAuxGraph G).degree y : ℝ) + 1) := by
      gcongr
      exact commonCard_le_sqrt_degree_add_one G y

lemma orderedPairEntry_mem_support {V : Type*} [DecidableEq V]
    (p : OrderedPair V) (i : Fin 2) :
    orderedPairEntry p i ∈ orderedPairSupport p := by
  fin_cases i <;> simp [orderedPairEntry, orderedPairSupport]

lemma orderedPairEntry_injective {V : Type*} (p : OrderedPair V) :
    Function.Injective (orderedPairEntry p) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact (p.property (by simpa [orderedPairEntry] using hij)).elim
  · exact (p.property (by simpa [orderedPairEntry] using hij.symm)).elim
  · rfl

lemma pairComplete_entries {V : Type*} (G : SimpleGraph V)
    {p q : OrderedPair V} (hpq : pairComplete G p q) (i j : Fin 2) :
    G.Adj (orderedPairEntry p i) (orderedPairEntry q j) := by
  fin_cases i <;> fin_cases j
  · simpa [orderedPairEntry] using hpq.1
  · simpa [orderedPairEntry] using hpq.2.1
  · simpa [orderedPairEntry] using hpq.2.2.1
  · simpa [orderedPairEntry] using hpq.2.2.2

/-- A cycle in the auxiliary graph whose ordered pairs have pairwise
disjoint supports is an actual copy of `C₁₂[2]` in the host graph. -/
lemma counterexampleGraph_isContained_of_disjoint_auxCycle
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (c : SimpleGraph.cycleGraph 12 →g pairAuxGraph G)
    (hdisjoint : ∀ i j : Fin 12, i ≠ j →
      Disjoint (orderedPairSupport (c i)) (orderedPairSupport (c j))) :
    counterexampleGraph ⊑ G := by
  let f : Fin 12 × Fin 2 → V := fun x ↦ orderedPairEntry (c x.1) x.2
  let hom : counterexampleGraph →g G :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        exact pairComplete_entries G (c.map_adj hxy) x.2 y.2 }
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hfirst : x.1 = y.1
    · apply Prod.ext hfirst
      apply orderedPairEntry_injective (c x.1)
      simpa [f, hfirst] using hxy
    · have hxmem : f x ∈ orderedPairSupport (c x.1) :=
        orderedPairEntry_mem_support _ _
      have hymem : f y ∈ orderedPairSupport (c y.1) :=
        orderedPairEntry_mem_support _ _
      have hd := Finset.disjoint_left.mp (hdisjoint x.1 y.1 hfirst)
      exact (hd hxmem (hxy ▸ hymem)).elim
  exact ⟨hom.toCopy hinj⟩

/-! ## Closed-walk counts -/

noncomputable def walkCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u v : V) : ℝ :=
  (G.adjMatrix ℝ ^ j) u v

noncomputable def homCycleCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) : ℝ :=
  Matrix.trace (G.adjMatrix ℝ ^ j)

lemma walkCount_eq_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u v : V) :
    walkCount G j u v = Fintype.card {p : G.Walk u v // p.length = j} := by
  exact G.adjMatrix_pow_apply_eq_card_walk j u v

lemma walkCount_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u v : V) :
    0 ≤ walkCount G j u v := by
  rw [walkCount_eq_card]
  positivity

lemma walkCount_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u v : V) :
    walkCount G j u v = walkCount G j v u := by
  change (G.adjMatrix ℝ ^ j) u v = (G.adjMatrix ℝ ^ j) v u
  have htranspose : Matrix.transpose (G.adjMatrix ℝ ^ j) = G.adjMatrix ℝ ^ j := by
    rw [Matrix.transpose_pow, G.transpose_adjMatrix]
  simpa [Matrix.transpose_apply] using congrFun₂ htranspose v u

lemma homCycleCount_even_eq_sum_sq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) :
    homCycleCount G (2 * j) = ∑ u : V, ∑ v : V, walkCount G j u v ^ 2 := by
  rw [homCycleCount]
  have hpow : G.adjMatrix ℝ ^ (2 * j) =
      G.adjMatrix ℝ ^ j * G.adjMatrix ℝ ^ j := by
    rw [show 2 * j = j + j by omega, pow_add]
  rw [hpow]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  change walkCount G j u v * walkCount G j v u = walkCount G j u v ^ 2
  rw [walkCount_comm]
  ring

lemma homCycleCount_even_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) :
    0 ≤ homCycleCount G (2 * j) := by
  rw [homCycleCount_even_eq_sum_sq]
  positivity

lemma homCycleCount_add_eq_sum_mul {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : ℕ) :
    homCycleCount G (a + b) =
      ∑ u : V, ∑ v : V, walkCount G a u v * walkCount G b u v := by
  rw [homCycleCount, pow_add]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  change walkCount G a u v * walkCount G b v u =
    walkCount G a u v * walkCount G b u v
  rw [walkCount_comm G b v u]

lemma homCycleCount_logConvex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (hj : 1 ≤ j) :
    homCycleCount G (2 * j) ^ 2 ≤
      homCycleCount G (2 * (j - 1)) * homCycleCount G (2 * (j + 1)) := by
  let f : V × V → ℝ := fun z ↦ walkCount G (j - 1) z.1 z.2
  let g : V × V → ℝ := fun z ↦ walkCount G (j + 1) z.1 z.2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (V × V)) f g
  have hmiddle : homCycleCount G (2 * j) = ∑ z : V × V, f z * g z := by
    rw [show 2 * j = (j - 1) + (j + 1) by omega,
      homCycleCount_add_eq_sum_mul]
    simp only [f, g, Fintype.sum_prod_type]
  have hleft : homCycleCount G (2 * (j - 1)) = ∑ z : V × V, f z ^ 2 := by
    rw [homCycleCount_even_eq_sum_sq]
    simp only [f, Fintype.sum_prod_type]
  have hright : homCycleCount G (2 * (j + 1)) = ∑ z : V × V, g z ^ 2 := by
    rw [homCycleCount_even_eq_sum_sq]
    simp only [g, Fintype.sum_prod_type]
  rwa [← hmiddle, ← hleft, ← hright] at hcs

lemma homCycleCount_ten_pow_five_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    homCycleCount G 10 ^ 5 ≤ homCycleCount G 2 * homCycleCount G 12 ^ 4 := by
  let h1 := homCycleCount G 2
  let h2 := homCycleCount G 4
  let h3 := homCycleCount G 6
  let h4 := homCycleCount G 8
  let h5 := homCycleCount G 10
  let h6 := homCycleCount G 12
  have hn1 : 0 ≤ h1 := by simpa [h1] using homCycleCount_even_nonneg G 1
  have hn2 : 0 ≤ h2 := by simpa [h2] using homCycleCount_even_nonneg G 2
  have hn3 : 0 ≤ h3 := by simpa [h3] using homCycleCount_even_nonneg G 3
  have hn4 : 0 ≤ h4 := by simpa [h4] using homCycleCount_even_nonneg G 4
  have hn5 : 0 ≤ h5 := by simpa [h5] using homCycleCount_even_nonneg G 5
  have hn6 : 0 ≤ h6 := by simpa [h6] using homCycleCount_even_nonneg G 6
  have hc2 : h2 ^ 2 ≤ h1 * h3 := by
    simpa [h1, h2, h3] using homCycleCount_logConvex G 2 (by omega)
  have hc3 : h3 ^ 2 ≤ h2 * h4 := by
    simpa [h2, h3, h4] using homCycleCount_logConvex G 3 (by omega)
  have hc4 : h4 ^ 2 ≤ h3 * h5 := by
    simpa [h3, h4, h5] using homCycleCount_logConvex G 4 (by omega)
  have hc5 : h5 ^ 2 ≤ h4 * h6 := by
    simpa [h4, h5, h6] using homCycleCount_logConvex G 5 (by omega)
  change h5 ^ 5 ≤ h1 * h6 ^ 4
  by_cases hz : h5 = 0
  · simpa [hz] using mul_nonneg hn1 (pow_nonneg hn6 4)
  have hp5 : 0 < h5 := lt_of_le_of_ne hn5 (Ne.symm hz)
  have hp4 : 0 < h4 := by
    have hp : 0 < h4 * h6 := (sq_pos_of_pos hp5).trans_le hc5
    exact pos_of_mul_pos_left hp hn6
  have hp3 : 0 < h3 := by
    have hp : 0 < h3 * h5 := (sq_pos_of_pos hp4).trans_le hc4
    exact pos_of_mul_pos_left hp hn5
  have hp2 : 0 < h2 := by
    have hp : 0 < h2 * h4 := (sq_pos_of_pos hp3).trans_le hc3
    exact pos_of_mul_pos_left hp hn4
  have hp1 : 0 < h1 := by
    have hp : 0 < h1 * h3 := (sq_pos_of_pos hp2).trans_le hc2
    exact pos_of_mul_pos_left hp hn3
  have hr2 : h2 / h1 ≤ h3 / h2 := by
    rw [div_le_div_iff₀ hp1 hp2]
    simpa [pow_two, mul_comm] using hc2
  have hr3 : h3 / h2 ≤ h4 / h3 := by
    rw [div_le_div_iff₀ hp2 hp3]
    simpa [pow_two, mul_comm] using hc3
  have hr4 : h4 / h3 ≤ h5 / h4 := by
    rw [div_le_div_iff₀ hp3 hp4]
    simpa [pow_two, mul_comm] using hc4
  have hr5 : h5 / h4 ≤ h6 / h5 := by
    rw [div_le_div_iff₀ hp4 hp5]
    simpa [pow_two, mul_comm] using hc5
  have htel : h5 / h1 =
      (h2 / h1) * (h3 / h2) * (h4 / h3) * (h5 / h4) := by
    field_simp
  have hq : 0 ≤ h6 / h5 := div_nonneg hn6 hn5
  have hs2 : h2 ≤ (h6 / h5) * h1 :=
    (div_le_iff₀ hp1).mp (hr2.trans (hr3.trans (hr4.trans hr5)))
  have hs3 : h3 ≤ (h6 / h5) * h2 :=
    (div_le_iff₀ hp2).mp (hr3.trans (hr4.trans hr5))
  have hs4 : h4 ≤ (h6 / h5) * h3 :=
    (div_le_iff₀ hp3).mp (hr4.trans hr5)
  have hs5 : h5 ≤ (h6 / h5) * h4 :=
    (div_le_iff₀ hp4).mp hr5
  have hratio' : h5 ≤ (h6 / h5) ^ 4 * h1 := by
    calc
      h5 ≤ (h6 / h5) * h4 := hs5
      _ ≤ (h6 / h5) * ((h6 / h5) * h3) :=
        mul_le_mul_of_nonneg_left hs4 hq
      _ ≤ (h6 / h5) * ((h6 / h5) * ((h6 / h5) * h2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs3 hq) hq
      _ ≤ (h6 / h5) * ((h6 / h5) * ((h6 / h5) * ((h6 / h5) * h1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hs2 hq) hq) hq
      _ = (h6 / h5) ^ 4 * h1 := by ring
  calc
    h5 ^ 5 = h5 * h5 ^ 4 := by ring
    _ ≤ ((h6 / h5) ^ 4 * h1) * h5 ^ 4 :=
      mul_le_mul_of_nonneg_right hratio' (pow_nonneg hn5 4)
    _ = h1 * h6 ^ 4 := by field_simp

abbrev ClosedWalk {V : Type*} (G : SimpleGraph V) (j : ℕ) :=
  Σ v : V, {p : G.Walk v v // p.length = j}

lemma homCycleCount_eq_card_closedWalk {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) :
    homCycleCount G j = Nat.card (ClosedWalk G j) := by
  rw [homCycleCount, Matrix.trace]
  simp only [Matrix.diag_apply, G.adjMatrix_pow_apply_eq_card_walk]
  rw [← Nat.cast_sum]
  norm_cast
  rw [Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card]
  apply Finset.sum_congr rfl
  intro v hv
  rfl

lemma cycleGraph12_adj_iff (i j : Fin 12) :
    (SimpleGraph.cycleGraph 12).Adj i j ↔
      i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 ∨
      (i.1 = 11 ∧ j.1 = 0) ∨ (j.1 = 11 ∧ i.1 = 0) := by
  decide +revert

def ClosedWalk.HasDisjointPairSupports {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : ClosedWalk (pairAuxGraph G) 12) : Prop :=
  ∀ i j : Fin 12, i ≠ j →
    Disjoint (orderedPairSupport (w.2.1.getVert i.1))
      (orderedPairSupport (w.2.1.getVert j.1))

lemma counterexampleGraph_isContained_of_goodClosedWalk
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : ClosedWalk (pairAuxGraph G) 12)
    (hw : w.HasDisjointPairSupports G) :
    counterexampleGraph ⊑ G := by
  let p := w.2.1
  have hpLength : p.length = 12 := w.2.2
  let c : SimpleGraph.cycleGraph 12 →g pairAuxGraph G :=
    { toFun := fun i ↦ p.getVert i.1
      map_rel' := by
        intro i j hij
        rcases (cycleGraph12_adj_iff i j).mp hij with h | h | h | h
        · have hadj := p.adj_getVert_succ (i := i.1) (by omega : i.1 < p.length)
          simpa [h] using hadj
        · have hadj := p.adj_getVert_succ (i := j.1) (by omega : j.1 < p.length)
          simpa [h] using hadj.symm
        · have hadj := p.adj_getVert_succ (i := 11) (by omega : 11 < p.length)
          have hend : p.getVert 12 = p.getVert 0 := by
            rw [p.getVert_of_length_le (by omega), p.getVert_zero]
          simpa [h.1, h.2, hend] using hadj
        · have hadj := p.adj_getVert_succ (i := 11) (by omega : 11 < p.length)
          have hend : p.getVert 12 = p.getVert 0 := by
            rw [p.getVert_of_length_le (by omega), p.getVert_zero]
          simpa [h.1, h.2, hend] using hadj.symm }
  apply counterexampleGraph_isContained_of_disjoint_auxCycle G c
  intro i j hij
  exact hw i j hij

abbrev BadClosedWalk {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {w : ClosedWalk (pairAuxGraph G) 12 // ¬w.HasDisjointPairSupports G}

lemma homCycleCount_eq_card_badClosedWalk_of_free
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : counterexampleGraph.Free G) :
    homCycleCount (pairAuxGraph G) 12 = Nat.card (BadClosedWalk G) := by
  rw [homCycleCount_eq_card_closedWalk]
  apply congrArg Nat.cast
  apply Nat.card_congr
  let toBad : ClosedWalk (pairAuxGraph G) 12 → BadClosedWalk G := fun w ↦
    ⟨w, fun hw ↦ hfree (counterexampleGraph_isContained_of_goodClosedWalk G w hw)⟩
  exact
    { toFun := toBad
      invFun := fun w ↦ w.1
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-! ## The fixed `5+1+6` decomposition of a twelve-cycle -/

abbrev WalkOfLength {V : Type*} (G : SimpleGraph V) (j : ℕ) (u v : V) :=
  {p : G.Walk u v // p.length = j}

structure CycleSplit {V : Type*} (G : SimpleGraph V) where
  x₁ : V
  x₂ : V
  x₈ : V
  bridge : G.Adj x₁ x₂
  middle : WalkOfLength G 6 x₂ x₈
  tail : WalkOfLength G 5 x₈ x₁

instance CycleSplit.instFinite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finite (CycleSplit G) := by
  let e : CycleSplit G →
      Σ x₁ x₂ x₈ : V,
        WalkOfLength G 6 x₂ x₈ × WalkOfLength G 5 x₈ x₁ := fun c ↦
    ⟨c.x₁, c.x₂, c.x₈, c.middle, c.tail⟩
  exact Finite.of_injective e (by
    intro c d h
    cases c
    cases d
    cases h
    rfl)

def CycleSplit.toClosedWalk {V : Type*} {G : SimpleGraph V}
    (c : CycleSplit G) : ClosedWalk G 12 :=
  ⟨c.x₁, ⟨(c.middle.1.cons c.bridge).append c.tail.1, by
    simp [c.middle.2, c.tail.2]⟩⟩

noncomputable def CycleSplit.ofClosedWalk {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) : CycleSplit G := by
  let p := w.2.1
  have hp : p.length = 12 := w.2.2
  let x₂ := p.getVert 1
  let x₈ := p.getVert 7
  have hb : G.Adj w.1 x₂ := by
    simpa [p, x₂] using p.adj_getVert_succ (i := 0) (by omega)
  have hmLen : ((p.drop 1).take 6).length = 6 := by
    simp [hp]
  have hmEnd : (p.drop 1).getVert 6 = x₈ := by simp [x₈]
  let middle : WalkOfLength G 6 x₂ x₈ :=
    ⟨((p.drop 1).take 6).copy (by simp [x₂]) hmEnd, by simpa using hmLen⟩
  have htLen : (p.drop 7).length = 5 := by simp [hp]
  let tail : WalkOfLength G 5 x₈ w.1 :=
    ⟨(p.drop 7).copy (by simp [x₈]) rfl, by simpa using htLen⟩
  exact ⟨w.1, x₂, x₈, hb, middle, tail⟩

lemma CycleSplit.toClosedWalk_ofClosedWalk {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) :
    (CycleSplit.ofClosedWalk w).toClosedWalk = w := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_getVert_le_length
  · exact (CycleSplit.ofClosedWalk w).toClosedWalk.2.2.trans w.2.2.symm
  intro k hk
  have hk' : k ≤ 12 := by
    rw [(CycleSplit.ofClosedWalk w).toClosedWalk.2.2] at hk
    exact hk
  interval_cases k <;>
    simp [CycleSplit.toClosedWalk, CycleSplit.ofClosedWalk, w.2.2,
      SimpleGraph.Walk.getVert_append, SimpleGraph.Walk.getVert_cons,
      SimpleGraph.Walk.take_getVert, SimpleGraph.Walk.drop_getVert]

lemma CycleSplit.ofClosedWalk_injective {V : Type*} {G : SimpleGraph V} :
    Function.Injective (CycleSplit.ofClosedWalk : ClosedWalk G 12 → CycleSplit G) := by
  intro w z h
  rw [← CycleSplit.toClosedWalk_ofClosedWalk w,
    ← CycleSplit.toClosedWalk_ofClosedWalk z, h]

@[simp] lemma CycleSplit.ofClosedWalk_middle_getVert {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) (i : Fin 6) :
    (CycleSplit.ofClosedWalk w).middle.1.getVert i.1 =
      w.2.1.getVert (i.1 + 1) := by
  simp [CycleSplit.ofClosedWalk, SimpleGraph.Walk.take_getVert,
    SimpleGraph.Walk.drop_getVert, Nat.add_comm]

/-- Cyclically move the first `i` edges of a closed twelve-walk to its end. -/
noncomputable def ClosedWalk.rotate12 {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) (i : Fin 12) : ClosedWalk G 12 := by
  let p := w.2.1
  have hp : p.length = 12 := w.2.2
  let q := (p.drop i.1).append (p.take i.1)
  have hq : q.length = 12 := by
    simp [q, hp]
  exact ⟨p.getVert i.1, ⟨q, hq⟩⟩

def ClosedWalk.cycleSupport {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) : List V :=
  w.2.1.support.dropLast

lemma ClosedWalk.cycleSupport_length {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) : w.cycleSupport.length = 12 := by
  simp [ClosedWalk.cycleSupport, w.2.2]

lemma ClosedWalk.cycleSupport_getElem? {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) (k : Fin 12) :
    w.cycleSupport[k.1]? = some (w.2.1.getVert k.1) := by
  rw [ClosedWalk.cycleSupport, List.getElem?_dropLast,
    if_pos (by simpa [SimpleGraph.Walk.length_support, w.2.2] using k.2)]
  exact (w.2.1.getVert_eq_support_getElem? (by rw [w.2.2]; exact k.2.le)).symm

lemma ClosedWalk.cycleSupport_rotate12 {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) (i : Fin 12) :
    (w.rotate12 i).cycleSupport = w.cycleSupport.rotate i.1 := by
  simp [ClosedWalk.cycleSupport, ClosedWalk.rotate12,
    SimpleGraph.Walk.support_append_eq_support_dropLast_append,
    List.rotate_eq_drop_append_take, w.2.2]
  rw [List.dropLast_drop_eq_drop_dropLast]
  rw [SimpleGraph.Walk.support_take, List.dropLast_take_eq_take_dropLast]
  simp

lemma ClosedWalk.rotate12_getVert {V : Type*} {G : SimpleGraph V}
    (w : ClosedWalk G 12) (i k : Fin 12) :
    (w.rotate12 i).2.1.getVert k.1 =
      w.2.1.getVert ((k.1 + i.1) % 12) := by
  let t : Fin 12 := ⟨(k.1 + i.1) % 12, Nat.mod_lt _ (by norm_num)⟩
  apply Option.some_injective
  calc
    some ((w.rotate12 i).2.1.getVert k.1) = (w.rotate12 i).cycleSupport[k.1]? :=
      ((w.rotate12 i).cycleSupport_getElem? k).symm
    _ = (w.cycleSupport.rotate i.1)[k.1]? := by rw [w.cycleSupport_rotate12]
    _ = w.cycleSupport[(k.1 + i.1) % 12]? := by
      simpa [w.cycleSupport_length] using
        (List.getElem?_rotate (l := w.cycleSupport) (n := i.1) (m := k.1)
          (by rw [w.cycleSupport_length]; exact k.2))
    _ = some (w.2.1.getVert ((k.1 + i.1) % 12)) := w.cycleSupport_getElem? t

lemma ClosedWalk.cycleSupport_injective {V : Type*} {G : SimpleGraph V} :
    Function.Injective (ClosedWalk.cycleSupport : ClosedWalk G 12 → List V) := by
  intro w z h
  rcases w with ⟨v, p, hp⟩
  rcases z with ⟨v', q, hq⟩
  have hv : v = v' := by
    have hh := congrArg List.head? h
    simp only [ClosedWalk.cycleSupport, List.dropLast_eq_take] at hh
    simp only [SimpleGraph.Walk.length_support, hp, hq, Nat.add_sub_cancel] at hh
    rw [← p.cons_tail_support, ← q.cons_tail_support] at hh
    simpa only [List.take_succ_cons, List.head?_cons, Option.some.injEq] using hh
  subst v'
  have hsupp : p.support = q.support := by
    calc
      p.support = p.support.dropLast ++ [v] := by
        symm
        simpa using (List.dropLast_append_getLast p.support_ne_nil)
      _ = q.support.dropLast ++ [v] := by
        simpa [ClosedWalk.cycleSupport] using congrArg (fun l : List V ↦ l ++ [v]) h
      _ = q.support := by
        simpa using (List.dropLast_append_getLast q.support_ne_nil)
  have hpq : p = q := SimpleGraph.Walk.ext_support hsupp
  subst q
  rfl

lemma ClosedWalk.rotate12_injective {V : Type*} {G : SimpleGraph V} (i : Fin 12) :
    Function.Injective (fun w : ClosedWalk G 12 ↦ w.rotate12 i) := by
  intro w z h
  apply ClosedWalk.cycleSupport_injective
  apply List.rotate_injective i.1
  change w.cycleSupport.rotate i.1 = z.cycleSupport.rotate i.1
  rw [← w.cycleSupport_rotate12 i, ← z.cycleSupport_rotate12 i]
  change w.rotate12 i = z.rotate12 i at h
  exact congrArg ClosedWalk.cycleSupport h

/-! ## Finite bipartite relations used by regularization -/

def bipartiteRelGraph {L R : Type*} (B : L → R → Prop) :
    SimpleGraph (L ⊕ R) where
  Adj x y := match x, y with
    | Sum.inl l, Sum.inr r => B l r
    | Sum.inr r, Sum.inl l => B l r
    | _, _ => False
  symm.symm := by
    rintro (l | r) (l' | r') <;> simp_all
  loopless.irrefl := by
    rintro (l | r) <;> simp

instance bipartiteRelGraph.instDecidableAdj
    {L R : Type*} (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    DecidableRel (bipartiteRelGraph B).Adj := by
  intro x y
  rcases x with l | r <;> rcases y with l' | r' <;>
    simp only [bipartiteRelGraph] <;> infer_instance

/-- The two sides of a graph constructed from a bipartite relation. -/
def bipartiteSide {L R : Type*} : L ⊕ R → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

lemma bipartiteSide_ne_of_adj
    {L R : Type*} {B : L → R → Prop} {x y : L ⊕ R}
    (hxy : (bipartiteRelGraph B).Adj x y) :
    bipartiteSide x ≠ bipartiteSide y := by
  rcases x with l | r <;> rcases y with l' | r' <;>
    simp [bipartiteRelGraph, bipartiteSide] at hxy ⊢

lemma bool_eq_of_ne_of_ne {a b c : Bool} (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma bipartiteWalk_length_five_side_ne
    {L R : Type*} {B : L → R → Prop} {x y : L ⊕ R}
    (p : (bipartiteRelGraph B).Walk x y) (hp : p.length = 5) :
    bipartiteSide x ≠ bipartiteSide y := by
  have h0 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 0) (by omega))
  have h1 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 1) (by omega))
  have h2 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 2) (by omega))
  have h3 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 3) (by omega))
  have h4 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 4) (by omega))
  have h02 : bipartiteSide x = bipartiteSide (p.getVert 2) := by
    simpa using bool_eq_of_ne_of_ne h0 h1
  have h24 : bipartiteSide (p.getVert 2) = bipartiteSide (p.getVert 4) :=
    bool_eq_of_ne_of_ne h2 h3
  have h4y : bipartiteSide (p.getVert 4) ≠ bipartiteSide y := by
    simpa [p.getVert_of_length_le (by omega : p.length ≤ 5), hp] using h4
  intro hxy
  exact h4y ((h02.trans h24).symm.trans hxy)

/-- A relation-preserving map on each side induces a graph homomorphism from
the associated bipartite-relation graph. -/
def bipartiteRelGraphHom
    {L R V : Type*} {B : L → R → Prop} (G : SimpleGraph V)
    (fL : L → V) (fR : R → V)
    (hmap : ∀ l r, B l r → G.Adj (fL l) (fR r)) :
    bipartiteRelGraph B →g G where
  toFun := Sum.elim fL fR
  map_rel' := by
    rintro (l | r) (l' | r') h
    · simp [bipartiteRelGraph] at h
    · exact hmap l r' h
    · exact G.adj_symm (hmap l' r h)
    · simp [bipartiteRelGraph] at h

end Erdos147
