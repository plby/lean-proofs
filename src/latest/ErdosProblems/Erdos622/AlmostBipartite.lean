/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.Core
import ErdosProblems.Erdos622.Assembly
import ErdosProblems.Erdos622.Regimes
import ErdosProblems.Erdos622.Covers
import ErdosProblems.Erdos622.GoodCut
import ErdosProblems.Erdos622.TailoredTrichotomy
import ErdosProblems.Erdos622.BinomialCLT
import ErdosProblems.Erdos622.Counting
import ErdosProblems.Erdos622.NormalWindow
import ErdosProblems.Erdos622.Concentration
import ErdosProblems.Erdos622.RandomCover
import ErdosProblems.Erdos622.AlonInduction
import ErdosProblems.Erdos622.LargeLinearForest

/-!
# Assembly of the almost-bipartite case for Erdős Problem 622

This file develops the almost-bipartite case of
Draganić--Keevash--Müyesser.  It contains unconditional finite reductions
from the exact tailored trichotomy witness to balanced minimum covers, the
Hall/random-cover matching estimate at square-root scale, a uniform
simultaneous concentration theorem for every numerical sampling condition,
and the compact-uniform binomial window estimate.  It also isolates the
final exact powerset-counting assembly, whose modular hypotheses are the
remaining graph-theoretic random-good-cut and deterministic Hamiltonicity
steps.

The definitions `restrictedPart` and `IsKGoodSample` remove a minor
type-theoretic ambiguity: the two parts of a sampled cut are finsets of the
subtype of selected vertices, which is the vertex type of the induced graph.
-/

open scoped SimpleGraph

namespace Erdos622

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The unconditional Alon input in precisely the one-large-linear-forest
form consumed by the DKM random-good-cut construction. -/
theorem alon_oneLargeLinearForest :
    LinearArboricity.OneLargeLinearForest.{0} :=
  AlonInduction.alon_asymptoticLinearArboricity.oneLargeLinearForest

/-- A smallest vertex cover of the edges internal to `A`. -/
def IsMinimumVertexCoverOn (G : SimpleGraph V) (A C : Finset V) : Prop :=
  IsVertexCoverOn G A C ∧
    ∀ D : Finset V, IsVertexCoverOn G A D → C.card ≤ D.card

/-- Every finite induced part admits a minimum internal vertex cover. -/
theorem exists_minimumVertexCoverOn (G : SimpleGraph V) (A : Finset V) :
    ∃ C : Finset V, IsMinimumVertexCoverOn G A C := by
  classical
  let candidates := A.powerset.filter (IsVertexCoverOn G A)
  have hAcover : IsVertexCoverOn G A A := by
    refine ⟨Finset.Subset.rfl, ?_⟩
    intro u huA v _hvA _huv
    exact Or.inl huA
  have hnonempty : candidates.Nonempty := by
    refine ⟨A, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.rfl, hAcover⟩
  obtain ⟨C, hC, hmin⟩ :=
    candidates.exists_min_image Finset.card hnonempty
  have hCcover : IsVertexCoverOn G A C :=
    (Finset.mem_filter.mp hC).2
  refine ⟨C, hCcover, ?_⟩
  intro D hD
  apply hmin D
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hD.1, hD⟩

/-- The finite family representing an event on the powerset of `U`. -/
noncomputable def almostBipartiteEvent {W : Type*} [DecidableEq W]
    (U : Finset W) (P : Finset W → Prop) : ℕ :=
  (U.powerset.filter P).card

/-- Number of samples from a finite coordinate set satisfying an event.  It
is defined locally so the final almost-bipartite assembly depends only on the
elementary powerset API. -/
noncomputable def almostBipartiteCount {W : Type*} [DecidableEq W]
    (U : Finset W) (P : Finset W → Prop) : ℕ :=
  almostBipartiteEvent U P

theorem almostBipartiteCount_mono {W : Type*} [DecidableEq W]
    {U : Finset W} {P Q : Finset W → Prop}
    (hPQ : ∀ S, S ⊆ U → P S → Q S) :
    almostBipartiteCount U P ≤ almostBipartiteCount U Q := by
  classical
  apply Finset.card_le_card
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  exact ⟨hS.1, hPQ S hS.1 hS.2⟩

theorem almostBipartiteCount_or_le {W : Type*} [DecidableEq W]
    (U : Finset W) (P Q : Finset W → Prop) :
    almostBipartiteCount U (fun S ↦ P S ∨ Q S) ≤
      almostBipartiteCount U P + almostBipartiteCount U Q := by
  classical
  unfold almostBipartiteCount almostBipartiteEvent
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union] at hS ⊢
  rcases hS with ⟨hSU, hP | hQ⟩
  · exact Or.inl ⟨hSU, hP⟩
  · exact Or.inr ⟨hSU, hQ⟩

/-- The vertices of `A` which occur in the sample `S`, regarded as vertices
of the induced graph on `S`. -/
def restrictedPart (S A : Finset V) : Finset (S : Set V) :=
  S.attach.filter fun v ↦ v.1 ∈ A

@[simp]
theorem mem_restrictedPart {S A : Finset V} {v : (S : Set V)} :
    v ∈ restrictedPart S A ↔ v.1 ∈ A := by
  simp [restrictedPart]

/-- A cut of the original vertex set restricts to a cut of every sampled
induced graph. -/
theorem restrictedParts_isCut {A B S : Finset V} (hAB : IsCut A B) :
    IsCut (restrictedPart S A) (restrictedPart S B) := by
  constructor
  · rw [Finset.disjoint_left]
    intro v hvA hvB
    exact Finset.disjoint_left.mp hAB.1
      (mem_restrictedPart.mp hvA) (mem_restrictedPart.mp hvB)
  · ext v
    have hv : v.1 ∈ A ∪ B := by
      rw [hAB.2]
      exact Finset.mem_univ _
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      simpa only [Finset.mem_union, mem_restrictedPart] using hv

theorem card_restrictedPart_of_subset {S A : Finset V} (hAS : A ⊆ S) :
    (restrictedPart S A).card = A.card := by
  classical
  apply Finset.card_bij (fun x _ ↦ x.1)
  · intro x hx
    exact mem_restrictedPart.mp hx
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro y hy
    exact ⟨⟨y, hAS hy⟩, mem_restrictedPart.mpr hy, rfl⟩

/-- The subtype presentation of a sampled part has the same cardinality as
the corresponding ambient intersection. -/
theorem card_restrictedPart (S A : Finset V) :
    (restrictedPart S A).card = (S ∩ A).card := by
  classical
  apply Finset.card_bij (fun x _ ↦ x.1)
  · intro x hx
    exact Finset.mem_inter.mpr ⟨x.property, mem_restrictedPart.mp hx⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro y hy
    exact ⟨⟨y, (Finset.mem_inter.mp hy).1⟩,
      mem_restrictedPart.mpr (Finset.mem_inter.mp hy).2, rfl⟩

/-- A minimum cover of edges internal to `A` becomes a minimum vertex cover
of the induced graph on the subtype `A`.  This is the exact bridge from the
cover-product reduction to the Hall/random-cover machinery. -/
theorem IsMinimumVertexCoverOn.induce
    (G : SimpleGraph V) {A C : Finset V}
    (hC : IsMinimumVertexCoverOn G A C) :
    RandomCover.IsMinimumVertexCover (G.induce (A : Set V))
      (restrictedPart A C) := by
  classical
  have hcard : (restrictedPart A C).card = C.card :=
    card_restrictedPart_of_subset hC.1.1
  constructor
  · intro u v huv
    rcases hC.1.2 u.property v.property huv with hu | hv
    · exact Or.inl (mem_restrictedPart.mpr hu)
    · exact Or.inr (mem_restrictedPart.mpr hv)
  · intro D hD
    let Dval : Finset V := D.image Subtype.val
    have hDcard : Dval.card = D.card := by
      apply Finset.card_image_iff.mpr
      intro x hx y hy hxy
      exact Subtype.ext hxy
    have hDcover : IsVertexCoverOn G A Dval := by
      constructor
      · intro x hx
        obtain ⟨v, hvD, rfl⟩ := Finset.mem_image.mp hx
        exact v.property
      · intro u hu v hv huv
        have huv' : (G.induce (A : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ := huv
        rcases hD huv' with huD | hvD
        · exact Or.inl (Finset.mem_image.mpr ⟨⟨u, hu⟩, huD, rfl⟩)
        · exact Or.inr (Finset.mem_image.mpr ⟨⟨v, hv⟩, hvD, rfl⟩)
    rw [hcard, ← hDcard]
    exact hC.2 Dval hDcover

/-- The graph of edges of `G` internal to `A`, extended by isolated
vertices to the original ambient type.  This presentation lets the uniform
random-cover theorem count subsets of the full vertex set rather than first
passing to the subtype `A`. -/
def internalGraph (G : SimpleGraph V) (A : Finset V) : SimpleGraph V :=
  (G.induce (A : Set V)).spanningCoe

@[simp]
theorem internalGraph_adj (G : SimpleGraph V) (A : Finset V) (u v : V) :
    (internalGraph G A).Adj u v ↔
      u ∈ A ∧ v ∈ A ∧ G.Adj u v := by
  simp only [internalGraph, SimpleGraph.Subgraph.spanningCoe_adj,
    SimpleGraph.induce_adj]
  aesop

theorem internalGraph_le (G : SimpleGraph V) (A : Finset V) :
    internalGraph G A ≤ G := by
  intro u v huv
  exact (internalGraph_adj G A u v).mp huv |>.2.2

/-- A minimum internal cover is literally a minimum vertex cover of the
ambient presentation `internalGraph G A`.  A competing cover may contain
vertices outside `A`; intersecting it with `A` can only decrease its size. -/
theorem IsMinimumVertexCoverOn.internalGraph
    (G : SimpleGraph V) {A C : Finset V}
    (hC : IsMinimumVertexCoverOn G A C) :
    RandomCover.IsMinimumVertexCover (internalGraph G A) C := by
  constructor
  · intro u v huv
    rw [internalGraph_adj] at huv
    exact hC.1.2 huv.1 huv.2.1 huv.2.2
  · intro D hD
    have hDAcover : IsVertexCoverOn G A (D ∩ A) := by
      constructor
      · exact Finset.inter_subset_right
      · intro u hu v hv huv
        have hi : (Erdos622.internalGraph G A).Adj u v :=
          (Erdos622.internalGraph_adj G A u v).2 ⟨hu, hv, huv⟩
        rcases hD hi with huD | hvD
        · exact Or.inl (Finset.mem_inter.mpr ⟨huD, hu⟩)
        · exact Or.inr (Finset.mem_inter.mpr ⟨hvD, hv⟩)
    exact (hC.2 (D ∩ A) hDAcover).trans
      (Finset.card_le_card Finset.inter_subset_left)

/-- At a vertex of `A`, degree in the ambient presentation of the internal
graph is exactly the number of `G`-neighbours lying in `A`. -/
theorem internalGraph_degree_eq_degreeInto_of_mem
    (G : SimpleGraph V) (A : Finset V) (v : V) (hv : v ∈ A) :
    (internalGraph G A).degree v = degreeInto G v A := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  unfold degreeInto
  congr 1
  ext w
  simp [internalGraph_adj, hv, and_comm]

/-- The tailored constant `gamma0 = 1/256` gives the stronger natural
internal-degree bound `n/128`; the coarser `n/16` conclusion is the form
used by the cover estimates below. -/
theorem internalGraph_degree_le_sixteenth_of_tailored
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    {A : Finset (Fin (2 * n))}
    (hmax : Trichotomy.InternalMaxDegree G A
      (TailoredTrichotomy.gamma0 * (2 * n : ℝ))) :
    ∀ v ∈ A, (internalGraph G A).degree v ≤ n / 16 := by
  intro v hv
  rw [internalGraph_degree_eq_degreeInto_of_mem G A v hv]
  have hr := hmax v hv
  have hr' : (degreeInto G v A : ℝ) * 128 ≤ n := by
    calc
      (degreeInto G v A : ℝ) * 128 ≤
          (TailoredTrichotomy.gamma0 * (2 * n : ℝ)) * 128 :=
        mul_le_mul_of_nonneg_right hr (by norm_num)
      _ = n := by rw [TailoredTrichotomy.gamma0]; ring
  have hnStrong : degreeInto G v A * 128 ≤ n := by exact_mod_cast hr'
  have hn : degreeInto G v A * 16 ≤ n := by omega
  exact (Nat.le_div_iff_mul_le (by omega : 0 < 16)).2 hn

/-- Deterministic cover lower bound in the large-imbalance regime.  If `A`
is the larger side of a cut in an `(n+1)`-regular graph, every vertex of `A`
has at least `|A|-n+1` internal neighbours.  Comparing the resulting
internal edge count with what a degree-`D` minimum cover can cover gives the
exact integral inequality used before the random matching argument. -/
theorem minimumCoverOn_large_side_bound
    {n D : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B C : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hnA : n ≤ A.card)
    (hmax : ∀ v ∈ A, (internalGraph G A).degree v ≤ D)
    (hC : IsMinimumVertexCoverOn G A C) :
    A.card * (A.card - n + 1) ≤ 2 * C.card * D := by
  let H := internalGraph G A
  have hdegLower : ∀ v ∈ A, A.card - n + 1 ≤ H.degree v := by
    intro v hv
    have hsplit := degreeInto_union_of_disjoint G v hcut.1
    rw [hcut.2, degreeInto_univ, hreg.degree_eq] at hsplit
    have hBle := degreeInto_le_card G v B
    have hcards := hcut.card_add_card
    simp only [Fintype.card_fin] at hcards
    rw [internalGraph_degree_eq_degreeInto_of_mem G A v hv]
    omega
  have hedgeCover : H.edgeFinset.card ≤ C.card * D := by
    apply card_edgeFinset_le_card_mul_of_vertexCover H C D hC.internalGraph.1
    intro v hvC
    exact hmax v (hC.1.1 hvC)
  calc
    A.card * (A.card - n + 1) =
        ∑ _v ∈ A, (A.card - n + 1) := by simp
    _ ≤ ∑ v ∈ A, H.degree v := by
      exact Finset.sum_le_sum fun v hv ↦ hdegLower v hv
    _ ≤ ∑ v, H.degree v := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ A)
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
    _ ≤ 2 * (C.card * D) := Nat.mul_le_mul_left 2 hedgeCover
    _ = 2 * C.card * D := by simp [Nat.mul_assoc]

/-- Quantitative cancellation form of
`minimumCoverOn_large_side_bound`.  If the internal maximum degree is at
most `n/(2Q)`, the minimum cover is at least `Q` times the cut imbalance
(with the harmless `+1` forced by regularity). -/
theorem minimumCoverOn_large_side_amplified
    {n D Q : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B C : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hnA : n ≤ A.card)
    (hmax : ∀ v ∈ A, (internalGraph G A).degree v ≤ D)
    (hC : IsMinimumVertexCoverOn G A C)
    (hD : 0 < D) (hQD : 2 * Q * D ≤ n) :
    Q * (A.card - n + 1) ≤ C.card := by
  let x := A.card - n + 1
  have hbase := minimumCoverOn_large_side_bound G hreg hcut hnA hmax hC
  have hmul : (2 * D) * (Q * x) ≤ (2 * D) * C.card := by
    calc
      (2 * D) * (Q * x) = (2 * Q * D) * x := by ring
      _ ≤ n * x := Nat.mul_le_mul_right x hQD
      _ ≤ A.card * x := Nat.mul_le_mul_right x hnA
      _ ≤ 2 * C.card * D := hbase
      _ = (2 * D) * C.card := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by positivity)

/-- Integer square-root scale used for minimum-cover thresholds.  A fixed
positive divisor represents a fixed positive multiple of `sqrt n` without
introducing rounding ambiguity into cover cardinalities. -/
def sqrtCoverThreshold (L n : ℕ) : ℕ := Nat.sqrt n / L

/-- An imbalance above the chosen integer square-root scale forces the
minimum internal cover above that same scale whenever the internal maximum
degree is at most `n/2`. -/
theorem minimumCoverOn_large_side_sqrtThreshold
    {n D L : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B C : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hnA : n ≤ A.card)
    (hmax : ∀ v ∈ A, (internalGraph G A).degree v ≤ D)
    (hC : IsMinimumVertexCoverOn G A C)
    (hD : 0 < D) (hDhalf : 2 * D ≤ n)
    (himbalance : sqrtCoverThreshold L n < A.card - n) :
    sqrtCoverThreshold L n ≤ C.card := by
  have hlarge := minimumCoverOn_large_side_amplified
    G hreg hcut hnA hmax hC hD (Q := 1) (by simpa using hDhalf)
  simp only [one_mul] at hlarge
  omega

theorem tendsto_sqrtCoverThreshold {L : ℕ} (hL : 0 < L) :
    Filter.Tendsto (sqrtCoverThreshold L) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro m
  apply Filter.eventually_atTop.mpr
  refine ⟨(m * L) ^ 2, ?_⟩
  intro n hn
  apply (Nat.le_div_iff_mul_le hL).2
  have hsqrt : m * L ≤ Nat.sqrt n := Nat.le_sqrt'.2 hn
  simpa [Nat.mul_comm] using hsqrt

/-- Uniform random-cover matching estimate for minimum internal covers of
size at least a fixed square-root scale.  It combines the subtype bridge
above with the fully uniform form of DKM's Hall/reveal lemma. -/
theorem eventually_minimumCoverOn_randomMatching_count_le
    {L : ℕ} (hL : 0 < L) {eps delta : ℝ}
    (heps : 0 < eps) (hepsHalf : eps < 1 / 2) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) (A C : Finset V),
        IsMinimumVertexCoverOn G A C → sqrtCoverThreshold L n ≤ C.card →
        ((((Finset.univ : Finset (A : Set V)).powerset.filter fun S ↦
            ¬ RandomCover.HasMatchingAtLeast (G.induce (A : Set V)) S
              ((1 / 4 - eps) * C.card)).card : ℝ)) ≤
          delta * (2 : ℝ) ^ A.card := by
  have hrandom := RandomCover.eventually_minimumCover_randomMatching_count_le
    heps hepsHalf hdelta
  have hscaled := (tendsto_sqrtCoverThreshold hL).eventually hrandom
  filter_upwards [hscaled] with n hn
  intro W instF instD G A C hC hsize
  let : Fintype W := instF
  let : DecidableEq W := instD
  have hCind := hC.induce G
  have hcoverCard : (restrictedPart A C).card = C.card :=
    card_restrictedPart_of_subset hC.1.1
  have hbound := hn (A : Set W) (G.induce (A : Set W))
    (restrictedPart A C) hCind (by simpa [hcoverCard] using hsize)
  have hAcard : Fintype.card (A : Set W) = A.card := by simp
  rw [hAcard, hcoverCard] at hbound
  exact hbound

/-- Ambient-coordinate form of the square-root-scale random-cover estimate.
The graph `internalGraph G A` has only the edges internal to `A`, but samples
range over all vertices of `V`; hence this already includes the exact
power-of-two multiplicity of coordinates outside `A`. -/
theorem eventually_minimumCoverOn_ambient_randomMatching_count_le
    {L : ℕ} (hL : 0 < L) {eps delta : ℝ}
    (heps : 0 < eps) (hepsHalf : eps < 1 / 2) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) (A C : Finset V),
        IsMinimumVertexCoverOn G A C → sqrtCoverThreshold L n ≤ C.card →
        ((((Finset.univ : Finset V).powerset.filter fun S ↦
            ¬ RandomCover.HasMatchingAtLeast (internalGraph G A) S
              ((1 / 4 - eps) * C.card)).card : ℝ)) ≤
          delta * (2 : ℝ) ^ Fintype.card V := by
  have hrandom := RandomCover.eventually_minimumCover_randomMatching_count_le
    heps hepsHalf hdelta
  have hscaled := (tendsto_sqrtCoverThreshold hL).eventually hrandom
  filter_upwards [hscaled] with n hn
  intro W instF instD G A C hC hsize
  let : Fintype W := instF
  let : DecidableEq W := instD
  exact hn W (internalGraph G A) C hC.internalGraph hsize

/-- Move exactly the excess vertices from the larger side of a cut to obtain
a balanced cut.  This is the finite bookkeeping step used before applying
the cover-product inequality in the DKM almost-bipartite argument. -/
theorem exists_balancingTransfer {n : ℕ} {A B : Finset V}
    (hV : Fintype.card V = 2 * n) (hcut : IsCut A B)
    (hA : n ≤ A.card) :
    ∃ T A₀ B₀ : Finset V,
      T ⊆ A ∧ T.card = A.card - n ∧
      A₀ = A \ T ∧ B₀ = B ∪ T ∧
      IsCut A₀ B₀ ∧ A₀.card = n ∧ B₀.card = n := by
  obtain ⟨T, hTA, hTcard⟩ :=
    Finset.exists_subset_card_eq (Nat.sub_le A.card n)
  let A₀ := A \ T
  let B₀ := B ∪ T
  have hBT : Disjoint B T := hcut.1.symm.mono_right hTA
  have hA₀card : A₀.card = n := by
    dsimp [A₀]
    rw [Finset.card_sdiff_of_subset hTA, hTcard]
    omega
  have hsum : A.card + B.card = 2 * n := by
    simpa [hV] using hcut.card_add_card
  have hB₀card : B₀.card = n := by
    dsimp [B₀]
    rw [Finset.card_union_of_disjoint hBT, hTcard]
    omega
  have hcut₀ : IsCut A₀ B₀ := by
    constructor
    · rw [Finset.disjoint_left]
      intro v hvA₀ hvB₀
      have hvA : v ∈ A := Finset.sdiff_subset hvA₀
      have hvT : v ∉ T := (Finset.mem_sdiff.mp hvA₀).2
      rcases Finset.mem_union.mp hvB₀ with hvB | hvT'
      · exact Finset.disjoint_left.mp hcut.1 hvA hvB
      · exact hvT hvT'
    · ext v
      constructor
      · intro _
        exact Finset.mem_univ _
      · intro _
        rcases Finset.mem_union.mp (by
            rw [hcut.2]
            exact Finset.mem_univ v) with hvA | hvB
        · by_cases hvT : v ∈ T
          · exact Finset.mem_union_right _
              (Finset.mem_union_right _ hvT)
          · exact Finset.mem_union_left _
              (Finset.mem_sdiff.mpr ⟨hvA, hvT⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_union_left _ hvB)
  exact ⟨T, A₀, B₀, hTA, hTcard, rfl, rfl, hcut₀,
    hA₀card, hB₀card⟩

/-- The DKM cover-product lower bound for the canonical minimum covers of a
balanced cut. -/
theorem minimumCovers_product {n : ℕ}
    (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B C D : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hAcard : A.card = n) (hBcard : B.card = n)
    (hC : IsMinimumVertexCoverOn G A C)
    (hD : IsMinimumVertexCoverOn G B D) :
    n + 1 ≤ (C.card + 1) * (D.card + 1) := by
  classical
  exact balancedCut_cover_product n G hreg hcut.1 hcut.2
    hAcard hBcard hC.1 hD.1

/-- Integer cover-size trichotomy.  If both minimum covers are not above the
chosen threshold `r`, the cover-product inequality forces the opposite cover
to be correspondingly large. -/
def CoverSizeRegime (n r c d : ℕ) : Prop :=
  (r ≤ c ∧ r ≤ d) ∨
    (c < r ∧ n + 1 ≤ r * (d + 1)) ∨
    (d < r ∧ n + 1 ≤ r * (c + 1))

theorem coverSize_regime_of_product {n r c d : ℕ}
    (hprod : n + 1 ≤ (c + 1) * (d + 1)) :
    CoverSizeRegime n r c d := by
  by_cases hc : r ≤ c
  · by_cases hd : r ≤ d
    · exact Or.inl ⟨hc, hd⟩
    · right
      right
      have hdr : d + 1 ≤ r := by omega
      refine ⟨Nat.lt_of_not_ge hd, ?_⟩
      calc
        n + 1 ≤ (c + 1) * (d + 1) := hprod
        _ ≤ r * (c + 1) := by
          simpa [Nat.mul_comm] using
            Nat.mul_le_mul_left (c + 1) hdr
  · right
    left
    have hcr : c + 1 ≤ r := by omega
    refine ⟨Nat.lt_of_not_ge hc, ?_⟩
    calc
      n + 1 ≤ (c + 1) * (d + 1) := hprod
      _ ≤ r * (d + 1) := Nat.mul_le_mul_right (d + 1) hcr

theorem minimumCovers_size_regime {n r : ℕ}
    (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B C D : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hAcard : A.card = n) (hBcard : B.card = n)
    (hC : IsMinimumVertexCoverOn G A C)
    (hD : IsMinimumVertexCoverOn G B D) :
    CoverSizeRegime n r C.card D.card :=
  coverSize_regime_of_product
    (minimumCovers_product G hreg hcut hAcard hBcard hC hD)

/-- A cut carrying exactly the quantitative conclusions of the tailored
almost-bipartite alternative.  Naming this package keeps the later cover and
probability reductions tied to the actual structural theorem rather than to
an abstract surrogate. -/
def IsAlmostBipartiteCut {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (A B : Finset (Fin (2 * n))) : Prop :=
  IsCut A B ∧
    (n : ℝ) ≤ A.card ∧
    (A.card : ℝ) ≤
      (1 / 2 + 16 * TailoredTrichotomy.epsilon0) * (2 * n : ℝ) ∧
    (1 / 4 - 14 * TailoredTrichotomy.epsilon0) * (2 * n : ℝ) ^ 2 ≤
      Trichotomy.edgeCount G A B ∧
    Trichotomy.CrossMinDegree G A B
      (TailoredTrichotomy.gamma0 * (2 * n : ℝ) / 2) ∧
    (A.card = n ∨
      Trichotomy.InternalMaxDegree G A
        (TailoredTrichotomy.gamma0 * (2 * n : ℝ)))

/-- The exact large-imbalance cover lower bound specialized to the cut
returned by the tailored trichotomy.  The constant `8` comes from
`2 * 8 * (n/16) ≤ n`. -/
theorem IsAlmostBipartiteCut.minimumCover_largeImbalance
    {n : ℕ} {G : SimpleGraph (Fin (2 * n))}
    {A B C : Finset (Fin (2 * n))}
    (hAB : IsAlmostBipartiteCut G A B)
    (hreg : G.IsRegularOfDegree (n + 1))
    (hC : IsMinimumVertexCoverOn G A C)
    (hn16 : 16 ≤ n) (himbalance : 0 < A.card - n) :
    8 * (A.card - n + 1) ≤ C.card := by
  have hnA : n ≤ A.card := by exact_mod_cast hAB.2.1
  have hmaxReal : Trichotomy.InternalMaxDegree G A
      (TailoredTrichotomy.gamma0 * (2 * n : ℝ)) := by
    rcases hAB.2.2.2.2.2 with hbalanced | hmax
    · rw [hbalanced] at himbalance
      simp at himbalance
    · exact hmax
  have hmax : ∀ v ∈ A, (internalGraph G A).degree v ≤ n / 16 :=
    internalGraph_degree_le_sixteenth_of_tailored G hmaxReal
  have hD : 0 < n / 16 := Nat.div_pos hn16 (by omega)
  have hQD : 2 * 8 * (n / 16) ≤ n := by
    simpa using Nat.mul_div_le n 16
  exact minimumCoverOn_large_side_amplified G hreg hAB.1 hnA hmax hC hD hQD

/-- Square-root-scale consequence of the preceding tailored bound, in the
form consumed by the uniform random-cover estimate. -/
theorem IsAlmostBipartiteCut.minimumCover_sqrtThreshold_of_largeImbalance
    {n L : ℕ} {G : SimpleGraph (Fin (2 * n))}
    {A B C : Finset (Fin (2 * n))}
    (hAB : IsAlmostBipartiteCut G A B)
    (hreg : G.IsRegularOfDegree (n + 1))
    (hC : IsMinimumVertexCoverOn G A C)
    (hn16 : 16 ≤ n)
    (himbalance : sqrtCoverThreshold L n < A.card - n) :
    sqrtCoverThreshold L n ≤ C.card := by
  have hlarge := hAB.minimumCover_largeImbalance hreg hC hn16
    (lt_of_le_of_lt (Nat.zero_le _) himbalance)
  omega

/-- Exact finite structural reduction of the almost-bipartite case.

If the original cut imbalance exceeds `t`, the first alternative holds.
Otherwise the excess is transferred to the smaller side, minimum internal
covers are chosen on the resulting balanced cut, and the cover-product
inequality gives `CoverSizeRegime`.  This theorem has no probabilistic or
asymptotic hypothesis. -/
theorem almostBipartite_cover_regime
    (n t r : ℕ) (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    (hab : AlmostBipartiteRegime n G) :
    ∃ A B : Finset (Fin (2 * n)),
      IsAlmostBipartiteCut G A B ∧
      (t < A.card - n ∨
        A.card - n ≤ t ∧
          ∃ A₀ B₀ C D : Finset (Fin (2 * n)),
            IsCut A₀ B₀ ∧ A₀.card = n ∧ B₀.card = n ∧
            IsMinimumVertexCoverOn G A₀ C ∧
            IsMinimumVertexCoverOn G B₀ D ∧
            CoverSizeRegime n r C.card D.card) := by
  classical
  obtain ⟨A, B, hAB, hpart, hAn, hAupper, hdense, hcross, hstop⟩ := hab
  have hcut : IsCut A B := ⟨hAB, hpart⟩
  refine ⟨A, B, ⟨hcut, hAn, hAupper, hdense, hcross, hstop⟩, ?_⟩
  by_cases himbalance : t < A.card - n
  · exact Or.inl himbalance
  · right
    have hnA : n ≤ A.card := by exact_mod_cast hAn
    obtain ⟨T, A₀, B₀, _hTA, _hTcard, _hA₀, _hB₀,
      hcut₀, hA₀card, hB₀card⟩ :=
      exists_balancingTransfer (V := Fin (2 * n)) (by simp) hcut hnA
    obtain ⟨C, hC⟩ := exists_minimumVertexCoverOn G A₀
    obtain ⟨D, hD⟩ := exists_minimumVertexCoverOn G B₀
    refine ⟨by omega, A₀, B₀, C, D, hcut₀, hA₀card, hB₀card,
      hC, hD, ?_⟩
    exact minimumCovers_size_regime G hreg hcut₀ hA₀card hB₀card hC hD

/-- Transfer-preserving form of `almostBipartite_cover_regime`.  The random
cover analysis is performed on the balanced parts `A₀,B₀`, but the final
Hamiltonicity lemma must use the original tailored cut `A,B`: a transferred
vertex can have very small crossing degree in the balanced cut.  Consequently
the transfer set and the exact identities of the balanced parts are retained
in this interface. -/
theorem almostBipartite_cover_regime_with_transfer
    (n t r : ℕ) (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    (hab : AlmostBipartiteRegime n G) :
    ∃ A B : Finset (Fin (2 * n)),
      IsAlmostBipartiteCut G A B ∧
      (t < A.card - n ∨
        A.card - n ≤ t ∧
          ∃ T A₀ B₀ C D : Finset (Fin (2 * n)),
            T ⊆ A ∧ T.card = A.card - n ∧
            A₀ = A \ T ∧ B₀ = B ∪ T ∧
            IsCut A₀ B₀ ∧ A₀.card = n ∧ B₀.card = n ∧
            IsMinimumVertexCoverOn G A₀ C ∧
            IsMinimumVertexCoverOn G B₀ D ∧
            CoverSizeRegime n r C.card D.card) := by
  classical
  obtain ⟨A, B, hAB, hpart, hAn, hAupper, hdense, hcross, hstop⟩ := hab
  have hcut : IsCut A B := ⟨hAB, hpart⟩
  refine ⟨A, B, ⟨hcut, hAn, hAupper, hdense, hcross, hstop⟩, ?_⟩
  by_cases himbalance : t < A.card - n
  · exact Or.inl himbalance
  · right
    have hnA : n ≤ A.card := by exact_mod_cast hAn
    obtain ⟨T, A₀, B₀, hTA, hTcard, hA₀, hB₀,
      hcut₀, hA₀card, hB₀card⟩ :=
      exists_balancingTransfer (V := Fin (2 * n)) (by simp) hcut hnA
    obtain ⟨C, hC⟩ := exists_minimumVertexCoverOn G A₀
    obtain ⟨D, hD⟩ := exists_minimumVertexCoverOn G B₀
    refine ⟨by omega, T, A₀, B₀, C, D, hTA, hTcard, hA₀, hB₀,
      hcut₀, hA₀card, hB₀card, hC, hD, ?_⟩
    exact minimumCovers_size_regime G hreg hcut₀ hA₀card hB₀card hC hD

/-- The sampled cut is `k`-good in the induced graph on the sample. -/
def IsKGoodSample (G : SimpleGraph V) (A B S : Finset V) (k : ℕ) : Prop :=
  IsKGoodCut (G.induce (S : Set V))
    (restrictedPart S A) (restrictedPart S B) k

/-- Every good-sample witness contains the expected restricted cut. -/
theorem IsKGoodSample.isCut {G : SimpleGraph V} {A B S : Finset V} {k : ℕ}
    (h : IsKGoodSample G A B S k) :
    IsCut (restrictedPart S A) (restrictedPart S B) :=
  h.1

/-- A positively buffered sampled good cut is, in particular, a good cut. -/
theorem IsKGoodSample.good {G : SimpleGraph V} {A B S : Finset V} {k : ℕ}
    (h : IsKGoodSample G A B S k) :
    IsKGoodSample G A B S 0 :=
  IsKGoodCut.good h

/-- A Mathlib subgraph-level matching supplied by the Hall/random-cover
argument is a supported linear forest in the graph-level `GoodCut` API.
The edge count is recovered exactly from the matching's vertex count by the
handshake identity. -/
theorem RandomCover.HasMatchingAtLeast.containsLinearForestWith
    {G : SimpleGraph V} {S : Finset V} {k : ℕ}
    (h : RandomCover.HasMatchingAtLeast G S (k : ℝ)) :
    ContainsLinearForestWith G S k := by
  obtain ⟨M, hM, hMS, hk⟩ := h
  let F : SimpleGraph V := M.spanningCoe
  have hFdegree : ∀ v, F.degree v ≤ 1 := by
    intro v
    change M.spanningCoe.degree v ≤ 1
    rw [M.degree_spanningCoe]
    by_cases hv : v ∈ M.verts
    · rw [(SimpleGraph.Subgraph.isMatching_iff_forall_degree.mp hM) v hv]
    · rw [M.degree_of_notMem_verts hv]
      omega
  have hFsupp : F.support ⊆ (S : Set V) := by
    intro v hv
    obtain ⟨w, hvw⟩ := hv
    exact hMS hvw.fst_mem
  refine ContainsLinearForestWith.of_degree_le_one
    M.spanningCoe_le hFdegree hFsupp ?_
  have hcard : M.verts.toFinset.card = 2 * F.edgeFinset.card := by
    rw [← F.sum_degrees_eq_twice_card_edges]
    have hdeg (v : V) :
        M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
      rw [M.degree_spanningCoe]
      split_ifs with hv
      · exact (SimpleGraph.Subgraph.isMatching_iff_forall_degree.mp hM) v hv
      · exact M.degree_of_notMem_verts hv
    change M.verts.toFinset.card = ∑ v, M.spanningCoe.degree v
    simp_rw [hdeg]
    simp
  have hk' : (k : ℝ) ≤ F.edgeFinset.card := by
    rw [hcard] at hk
    norm_num at hk ⊢
    linarith
  exact_mod_cast hk'

/-- A supported linear forest restricts to the sampled induced graph without
losing edges when its support already lies in the sample.  The proof uses
`Set.ncard` for the degree and edge-cardinality comparisons, making the
statement insensitive to the two definitionally different finite-type
instances carried by a finset subtype. -/
theorem ContainsLinearForestWith.induce
    {G : SimpleGraph V} {X S : Finset V} {k : ℕ}
    (h : ContainsLinearForestWith G X k) (hXS : X ⊆ S) :
    ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S X) k := by
  classical
  obtain ⟨F, hFG, hlin, hsupp, hcard⟩ := h
  refine ⟨F.induce (S : Set V), ?_, ?_, ?_, ?_⟩
  · intro u v huv
    exact hFG huv
  · refine ⟨hlin.1.induce _, ?_⟩
    intro u
    have himage : Subtype.val '' (F.induce (S : Set V)).neighborSet u ⊆
        F.neighborSet u.1 := by
      intro w hw
      obtain ⟨w', hw', rfl⟩ := hw
      exact hw'
    have hcardle := Set.ncard_le_ncard himage
    have hinj :
        (Subtype.val '' (F.induce (S : Set V)).neighborSet u).ncard =
          ((F.induce (S : Set V)).neighborSet u).ncard :=
      Set.ncard_image_of_injective _ Subtype.val_injective
    have hleft : ((F.induce (S : Set V)).neighborSet u).ncard =
        (F.induce (S : Set V)).degree u := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    have hright : (F.neighborSet u.1).ncard = F.degree u.1 := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    rw [hinj, hleft, hright] at hcardle
    exact hcardle.trans (hlin.2 u.1)
  · intro u hu
    obtain ⟨v, huv⟩ := hu
    apply mem_restrictedPart.mpr
    exact hsupp ⟨v.1, huv⟩
  · have hsuppS : F.support ⊆ (S : Set V) := by
      intro v hv
      exact hXS (hsupp hv)
    have hedgeNcard : (F.induce (S : Set V)).edgeSet.ncard =
        F.edgeSet.ncard := by
      have hraw := F.card_edgeFinset_induce_of_support_subset hsuppS
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset,
        ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at hraw
      exact hraw
    have hsource : F.edgeFinset.card = F.edgeSet.ncard := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset,
      hedgeNcard, ← hsource]
    exact hcard

/-- A linear forest found in the sampled restriction of an auxiliary graph
`J` lifts to the sampled restriction of `G`; if every non-isolated vertex of
`J` lies in `A`, the lifted forest is supported on the sampled part `A`.
This is the direct bridge consumed by the bounded-internal-graph/Alon stage. -/
theorem ContainsLinearForestWith.mono_induce_of_support
    {G J : SimpleGraph V} {A S : Finset V} {k : ℕ}
    (hJG : J ≤ G) (hsuppJ : J.support ⊆ (A : Set V))
    (h : ContainsLinearForestWith (J.induce (S : Set V))
      Finset.univ k) :
    ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) k := by
  obtain ⟨F, hFJ, hlin, _hsupp, hcard⟩ := h
  refine ⟨F, ?_, hlin, ?_, hcard⟩
  · intro u v huv
    exact hJG (hFJ huv)
  · intro u hu
    obtain ⟨v, huv⟩ := hu
    apply mem_restrictedPart.mpr
    apply hsuppJ
    exact (SimpleGraph.mem_support J).mpr ⟨v.1, hFJ huv⟩

/-- Ambient form of the preceding restriction lemma.  This is the exact
bridge from a Hall matching in `internalGraph G A` supported in the sample
to a linear forest in the induced sample graph, supported on the sampled
left part. -/
theorem RandomCover.HasMatchingAtLeast.induce_internalGraph
    {G : SimpleGraph V} {A S : Finset V} {k : ℕ}
    (h : RandomCover.HasMatchingAtLeast (internalGraph G A) S (k : ℝ)) :
    ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) k := by
  have hforest : ContainsLinearForestWith (internalGraph G A) S k :=
    h.containsLinearForestWith
  obtain ⟨F, hFH, hlin, hsupp, hcard⟩ := hforest
  have hsupportA : F.support ⊆ (A : Set V) := by
    intro v hv
    obtain ⟨w, hvw⟩ := hv
    exact (internalGraph_adj G A v w).mp (hFH hvw) |>.1
  have hsupportS : A ∩ S ⊆ S := Finset.inter_subset_right
  have hAS : ContainsLinearForestWith G (A ∩ S) k := by
    refine ⟨F, hFH.trans (internalGraph_le G A), hlin, ?_, hcard⟩
    intro v hv
    exact Finset.mem_inter.mpr ⟨hsupportA hv, hsupp hv⟩
  have hinduced := hAS.induce hsupportS
  have hpart : restrictedPart S (A ∩ S) = restrictedPart S A := by
    ext v
    simp only [mem_restrictedPart, Finset.mem_inter]
    exact and_iff_left v.property
  rw [hpart] at hinduced
  exact hinduced

/-- A sufficiently large matching inside the sampled left part is already
the exact good-cut witness required by the deterministic Hamiltonicity
stage. -/
theorem IsKGoodSample.of_matching_left
    {G : SimpleGraph V} {A B S : Finset V} {k : ℕ}
    (hcut : IsCut A B)
    (hcard : (restrictedPart S B).card ≤ (restrictedPart S A).card)
    (hmatching : RandomCover.HasMatchingAtLeast (G.induce (S : Set V))
      (restrictedPart S A)
      (k + ((restrictedPart S A).card - (restrictedPart S B).card) : ℕ)) :
    IsKGoodSample G A B S k := by
  refine ⟨restrictedParts_isCut hcut, Or.inl ⟨hcard, ?_⟩⟩
  exact hmatching.containsLinearForestWith

/-- Right-oriented counterpart of `IsKGoodSample.of_matching_left`. -/
theorem IsKGoodSample.of_matching_right
    {G : SimpleGraph V} {A B S : Finset V} {k : ℕ}
    (hcut : IsCut A B)
    (hcard : (restrictedPart S A).card ≤ (restrictedPart S B).card)
    (hmatching : RandomCover.HasMatchingAtLeast (G.induce (S : Set V))
      (restrictedPart S B)
      (k + ((restrictedPart S B).card - (restrictedPart S A).card) : ℕ)) :
    IsKGoodSample G A B S k := by
  refine ⟨restrictedParts_isCut hcut, Or.inr ⟨hcard, ?_⟩⟩
  exact hmatching.containsLinearForestWith

/-- Ambient Hall-matching form of `IsKGoodSample.of_matching_left`.  This is
the form directly produced by `RandomCover`, before passing to the sampled
induced vertex type. -/
theorem IsKGoodSample.of_ambient_matching_left
    {G : SimpleGraph V} {A B S : Finset V} {k : ℕ}
    (hcut : IsCut A B)
    (hcard : (restrictedPart S B).card ≤ (restrictedPart S A).card)
    (hmatching : RandomCover.HasMatchingAtLeast (internalGraph G A) S
      (k + ((restrictedPart S A).card - (restrictedPart S B).card) : ℕ)) :
    IsKGoodSample G A B S k := by
  refine ⟨restrictedParts_isCut hcut, Or.inl ⟨hcard, ?_⟩⟩
  exact hmatching.induce_internalGraph

/-- Right-oriented ambient Hall-matching form. -/
theorem IsKGoodSample.of_ambient_matching_right
    {G : SimpleGraph V} {A B S : Finset V} {k : ℕ}
    (hcut : IsCut A B)
    (hcard : (restrictedPart S A).card ≤ (restrictedPart S B).card)
    (hmatching : RandomCover.HasMatchingAtLeast (internalGraph G B) S
      (k + ((restrictedPart S B).card - (restrictedPart S A).card) : ℕ)) :
    IsKGoodSample G A B S k := by
  refine ⟨restrictedParts_isCut hcut, Or.inr ⟨hcard, ?_⟩⟩
  exact hmatching.induce_internalGraph

/-- The ambient random-cover estimate stated directly as a linear-forest
event.  Any integral target below the Hall threshold is met by all but a
`delta`-fraction of ambient subsets, uniformly over the graph and cover. -/
theorem eventually_minimumCoverOn_ambient_linearForest_count_le
    {L : ℕ} (hL : 0 < L) {eps delta : ℝ}
    (heps : 0 < eps) (hepsHalf : eps < 1 / 2) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) (A C : Finset V),
        IsMinimumVertexCoverOn G A C → sqrtCoverThreshold L n ≤ C.card →
        ∀ k : ℕ, (k : ℝ) ≤ (1 / 4 - eps) * C.card →
          ((((Finset.univ : Finset V).powerset.filter fun S ↦
              ¬ ContainsLinearForestWith (internalGraph G A) S k).card : ℝ)) ≤
            delta * (2 : ℝ) ^ Fintype.card V := by
  filter_upwards
      [eventually_minimumCoverOn_ambient_randomMatching_count_le
        hL heps hepsHalf hdelta] with n hn
  intro W instF instD G A C hC hsize k hk
  let : Fintype W := instF
  let : DecidableEq W := instD
  have hsub :
      ((Finset.univ : Finset W).powerset.filter fun S ↦
          ¬ ContainsLinearForestWith (internalGraph G A) S k) ⊆
        (Finset.univ : Finset W).powerset.filter fun S ↦
          ¬ RandomCover.HasMatchingAtLeast (internalGraph G A) S
            ((1 / 4 - eps) * C.card) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    refine ⟨hS.1, ?_⟩
    intro hmatching
    apply hS.2
    obtain ⟨M, hM, hMS, hMcard⟩ := hmatching
    exact (show RandomCover.HasMatchingAtLeast (internalGraph G A) S (k : ℝ)
      from ⟨M, hM, hMS, hk.trans hMcard⟩).containsLinearForestWith
  have hcardNat := Finset.card_le_card hsub
  have hcardReal :
      ((((Finset.univ : Finset W).powerset.filter fun S ↦
          ¬ ContainsLinearForestWith (internalGraph G A) S k).card : ℝ)) ≤
        (((Finset.univ : Finset W).powerset.filter fun S ↦
          ¬ RandomCover.HasMatchingAtLeast (internalGraph G A) S
            ((1 / 4 - eps) * C.card)).card : ℝ) := by
    exact_mod_cast hcardNat
  exact hcardReal.trans (hn W G A C hC hsize)

/-- The three regimes produced by the balance and cover-product argument in
the almost-bipartite case.  The propositions are kept abstract here because
their quantitative definitions belong to the cover and probability modules;
this file only assembles their proved consequences. -/
def AlmostBipartiteCoverRegime
    (largeImbalance twoLargeCovers oneSmallCover : Prop) : Prop :=
  largeImbalance ∨ twoLargeCovers ∨ oneSmallCover

/-- Exact finite-counting assembly of the DKM almost-bipartite argument.

`Suitable S` packages the high-probability degree, size, crossing-density,
and bipartite-minimum-degree conclusions.  The three good-cut hypotheses are
the large-imbalance matching argument, the DKM random-good-cut lemma in the
two-large-cover regime, and the one-small-cover matching argument.  The
cover-product input proves that at least one of those regimes applies.

The buffer `lambda` in the good-cut estimate is cancelled exactly by the
allowed concentration loss `lambda + epsilon`. -/
theorem almostBipartite_counting_assembly
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ)
    (Suitable : Finset V → Prop)
    (largeImbalance twoLargeCovers oneSmallCover : Prop)
    (ε lam : ℝ)
    (hcut : IsCut A B)
    (hcoverProduct :
      AlmostBipartiteCoverRegime
        largeImbalance twoLargeCovers oneSmallCover)
    (hlargeImbalanceGood : largeImbalance →
      ((1 / 2 : ℝ) + lam) * (2 : ℝ) ^ Fintype.card V ≤
        (almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsKGoodSample G A B S k) : ℝ))
    (hrandomGoodCut : twoLargeCovers →
      ((1 / 2 : ℝ) + lam) * (2 : ℝ) ^ Fintype.card V ≤
        (almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsKGoodSample G A B S k) : ℝ))
    (honeSmallCoverGood : oneSmallCover →
      ((1 / 2 : ℝ) + lam) * (2 : ℝ) ^ Fintype.card V ≤
        (almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsKGoodSample G A B S k) : ℝ))
    (hconcentration :
      (almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ ¬ Suitable S) : ℝ) ≤
        (lam + ε) * (2 : ℝ) ^ Fintype.card V)
    (hdeterministic : ∀ S : Finset V, S ⊆ Finset.univ →
      IsCut (restrictedPart S A) (restrictedPart S B) → Suitable S →
      IsKGoodSample G A B S k → IsSpannedByCycle G S) :
    ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ Fintype.card V ≤
      ((cycleSpannedSubsets G).card : ℝ) := by
  have hrestrictedCut (S : Finset V) :
      IsCut (restrictedPart S A) (restrictedPart S B) :=
    restrictedParts_isCut hcut
  have hgood :
      ((1 / 2 : ℝ) + lam) * (2 : ℝ) ^ Fintype.card V ≤
        (almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsKGoodSample G A B S k) : ℝ) := by
    rcases hcoverProduct with hlarge | htwo | hsmall
    · exact hlargeImbalanceGood hlarge
    · exact hrandomGoodCut htwo
    · exact honeSmallCoverGood hsmall
  have hsplitNat :
      almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsKGoodSample G A B S k) ≤
        almostBipartiteCount (Finset.univ : Finset V)
            (fun S ↦ IsSpannedByCycle G S) +
          almostBipartiteCount (Finset.univ : Finset V)
            (fun S ↦ ¬ Suitable S) := by
    calc
      almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsKGoodSample G A B S k) ≤
          almostBipartiteCount (Finset.univ : Finset V)
            (fun S ↦ IsSpannedByCycle G S ∨ ¬ Suitable S) := by
              apply almostBipartiteCount_mono
              intro S hSuniv hSgood
              by_cases hS : Suitable S
              · exact Or.inl
                  (hdeterministic S hSuniv (hrestrictedCut S) hS hSgood)
              · exact Or.inr hS
      _ ≤ almostBipartiteCount (Finset.univ : Finset V)
            (fun S ↦ IsSpannedByCycle G S) +
          almostBipartiteCount (Finset.univ : Finset V)
            (fun S ↦ ¬ Suitable S) :=
        almostBipartiteCount_or_le _ _ _
  have hsplit :
      (almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsKGoodSample G A B S k) : ℝ) ≤
        (almostBipartiteCount (Finset.univ : Finset V)
            (fun S ↦ IsSpannedByCycle G S) : ℝ) +
          (almostBipartiteCount (Finset.univ : Finset V)
            (fun S ↦ ¬ Suitable S) : ℝ) := by
    exact_mod_cast hsplitNat
  have hcount :
      ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ Fintype.card V ≤
        (almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsSpannedByCycle G S) : ℝ) := by
    calc
      ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ Fintype.card V =
          ((1 / 2 : ℝ) + lam) * (2 : ℝ) ^ Fintype.card V -
            (lam + ε) * (2 : ℝ) ^ Fintype.card V := by ring
      _ ≤ (almostBipartiteCount (Finset.univ : Finset V)
              (fun S ↦ IsKGoodSample G A B S k) : ℝ) -
            (almostBipartiteCount (Finset.univ : Finset V)
              (fun S ↦ ¬ Suitable S) : ℝ) :=
        sub_le_sub hgood hconcentration
      _ ≤ (almostBipartiteCount (Finset.univ : Finset V)
              (fun S ↦ IsSpannedByCycle G S) : ℝ) := by linarith
  have hfamily :
      (Finset.univ : Finset V).powerset.filter (IsSpannedByCycle G) =
        cycleSpannedSubsets G := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and, mem_cycleSpannedSubsets]
  have hcard :
      almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsSpannedByCycle G S) =
        (cycleSpannedSubsets G).card := by
    unfold almostBipartiteCount almostBipartiteEvent
    exact congrArg Finset.card hfamily
  rw [hcard] at hcount
  exact hcount

/-- Subtraction form of the finite almost-bipartite counting assembly.

If all but a `delta`-fraction of a family of good-cut samples are numerically
suitable, and the good-cut family itself has density at least
`1 / 2 - delta`, then cyclic samples have density at least
`1 / 2 - 2 * delta`.  This is the form used by the unconditional downstream
case theorem: its three cover regimes may each supply a half-minus-error
estimate, without first extracting a common positive buffer above one half. -/
theorem almostBipartite_counting_subtraction
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ)
    (Suitable : Finset V → Prop) (delta : ℝ)
    (hcut : IsCut A B)
    (hgood :
      ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ Fintype.card V ≤
        (almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsKGoodSample G A B S k) : ℝ))
    (hbad :
      (almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ ¬ Suitable S) : ℝ) ≤
        delta * (2 : ℝ) ^ Fintype.card V)
    (hdeterministic : ∀ S : Finset V, S ⊆ Finset.univ →
      IsCut (restrictedPart S A) (restrictedPart S B) → Suitable S →
      IsKGoodSample G A B S k → IsSpannedByCycle G S) :
    ((1 / 2 : ℝ) - 2 * delta) * (2 : ℝ) ^ Fintype.card V ≤
      ((cycleSpannedSubsets G).card : ℝ) := by
  apply almostBipartite_counting_assembly G A B k Suitable True False False
    (2 * delta) (-delta) hcut
  · exact Or.inl trivial
  · intro _
    convert hgood using 1 <;> ring
  · exact False.elim
  · exact False.elim
  · convert hbad using 1 <;> ring
  · exact hdeterministic

/-- The same assembly specialized to the canonical `2 * n`-vertex type used
by the public resolution statement. -/
theorem almostBipartite_cyclicDensity
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (A B : Finset (Fin (2 * n))) (k : ℕ)
    (Suitable : Finset (Fin (2 * n)) → Prop)
    (largeImbalance twoLargeCovers oneSmallCover : Prop)
    (ε lam : ℝ)
    (hcut : IsCut A B)
    (hcoverProduct :
      AlmostBipartiteCoverRegime
        largeImbalance twoLargeCovers oneSmallCover)
    (hlargeImbalanceGood : largeImbalance →
      ((1 / 2 : ℝ) + lam) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S k) : ℝ))
    (hrandomGoodCut : twoLargeCovers →
      ((1 / 2 : ℝ) + lam) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S k) : ℝ))
    (honeSmallCoverGood : oneSmallCover →
      ((1 / 2 : ℝ) + lam) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S k) : ℝ))
    (hconcentration :
      (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ ¬ Suitable S) : ℝ) ≤
        (lam + ε) * (2 : ℝ) ^ (2 * n))
    (hdeterministic : ∀ S : Finset (Fin (2 * n)),
      S ⊆ Finset.univ →
      IsCut (restrictedPart S A) (restrictedPart S B) → Suitable S →
      IsKGoodSample G A B S k → IsSpannedByCycle G S) :
    ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
      ((cycleSpannedSubsets G).card : ℝ) := by
  have hlargeImbalanceGood' : largeImbalance →
      ((1 / 2 : ℝ) + lam) * (2 : ℝ) ^ Fintype.card (Fin (2 * n)) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S k) : ℝ) := by
    simpa using hlargeImbalanceGood
  have hrandomGoodCut' : twoLargeCovers →
      ((1 / 2 : ℝ) + lam) * (2 : ℝ) ^ Fintype.card (Fin (2 * n)) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S k) : ℝ) := by
    simpa using hrandomGoodCut
  have honeSmallCoverGood' : oneSmallCover →
      ((1 / 2 : ℝ) + lam) * (2 : ℝ) ^ Fintype.card (Fin (2 * n)) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S k) : ℝ) := by
    simpa using honeSmallCoverGood
  have hconcentration' :
      (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ ¬ Suitable S) : ℝ) ≤
        (lam + ε) * (2 : ℝ) ^ Fintype.card (Fin (2 * n)) := by
    simpa using hconcentration
  simpa using almostBipartite_counting_assembly G A B k Suitable
    largeImbalance twoLargeCovers oneSmallCover ε lam hcut hcoverProduct
    hlargeImbalanceGood' hrandomGoodCut' honeSmallCoverGood' hconcentration'
    hdeterministic

end Erdos622


open Filter Finset Real
open scoped BigOperators Topology SimpleGraph

namespace Erdos622.SamplingSuitable

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type*} [Fintype E] [DecidableEq E]

private def halfProbability (_ : E) : ℝ := 1 / 2

/-- Number of selected elements belonging to a fixed test set. -/
def intersectionCount (C S : Finset E) : ℝ := ((S ∩ C).card : ℝ)

private lemma intersectionCount_sum_indicator (C S : Finset E) :
    intersectionCount C S = ∑ v ∈ C, if v ∈ S then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  simp [intersectionCount, Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- Exact mean of an intersection count. -/
lemma bernoulliExpectation_half_intersectionCount (C : Finset E) :
    Erdos76.FiniteNibble.bernoulliExpectation (univ : Finset E)
        halfProbability (intersectionCount C) = (C.card : ℝ) / 2 := by
  rw [Erdos76.FiniteNibble.bernoulliExpectation]
  simp_rw [intersectionCount_sum_indicator, mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ v ∈ C, ∑ S ∈ (univ : Finset E).powerset,
        Erdos76.FiniteNibble.bernoulliMass univ halfProbability S *
          (if v ∈ S then (1 : ℝ) else 0) =
        ∑ _v ∈ C, (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      calc
        ∑ S ∈ (univ : Finset E).powerset,
            Erdos76.FiniteNibble.bernoulliMass univ halfProbability S *
              (if v ∈ S then (1 : ℝ) else 0) =
            ∑ S ∈ (univ : Finset E).powerset with v ∈ S,
              Erdos76.FiniteNibble.bernoulliMass univ halfProbability S := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro S hS
          by_cases hvS : v ∈ S <;> simp [hvS]
        _ = 1 / 2 := by
          simpa [halfProbability] using
            (Erdos76.FiniteNibble.sum_bernoulliMass_filter_mem
              (U := (univ : Finset E)) (p := halfProbability)
              (e := v) (Finset.mem_univ v))
    _ = (C.card : ℝ) / 2 := by simp; ring

/-- A two-sided version of the finite-powerset bounded-difference bound. -/
theorem countEvent_twoSided_le
    {U : Finset E} {F : Finset E → ℝ} {c : E → ℝ} {t : ℝ}
    (hbd : Erdos76.FiniteNibble.HasBoundedDifferences U F c) (ht : 0 ≤ t) :
    ((U.powerset.filter fun S ↦
        t ≤ |F S -
          Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|).card : ℝ) ≤
      2 * (2 : ℝ) ^ U.card *
        exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) := by
  let A := U.powerset.filter fun S ↦
    Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S
  let B := U.powerset.filter fun S ↦
    F S ≤ Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t
  have hsub : U.powerset.filter (fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|) ⊆
      A ∪ B := by
    intro S hS
    simp only [mem_filter, mem_powerset, mem_union, A, B] at hS ⊢
    rcases le_abs.mp hS.2 with h | h
    · exact Or.inl ⟨hS.1, by linarith⟩
    · exact Or.inr ⟨hS.1, by linarith⟩
  have hcard : (U.powerset.filter fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|).card ≤
      A.card + B.card := (card_le_card hsub).trans (card_union_le A B)
  have hA := Concentration.countEvent_upperTail_le
    (U := U) (F := F) (c := c) (t := t) hbd ht
  have hB := Concentration.countEvent_lowerTail_le
    (U := U) (F := F) (c := c) (t := t) hbd ht
  change ((U.powerset.filter fun S ↦
      Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S).card : ℝ) ≤
      (2 : ℝ) ^ U.card * exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) at hA
  change ((U.powerset.filter fun S ↦
      F S ≤ Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t).card : ℝ) ≤
      (2 : ℝ) ^ U.card * exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) at hB
  have hcardR : ((U.powerset.filter fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|).card : ℝ) ≤
      (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcard
  dsimp [A, B] at hcardR hA hB ⊢
  linarith

/-- Intersections with a fixed test set have bounded differences one on the
whole ambient coordinate set.  This deliberately coarsens the optimal
test-set-sized variance proxy, making the estimate uniform even for an empty
test set. -/
theorem intersectionCount_hasBoundedDifferences_ambient (C : Finset E) :
    Erdos76.FiniteNibble.HasBoundedDifferences (univ : Finset E)
      (intersectionCount C) (fun _ ↦ 1) := by
  intro e he T hT
  have heT : e ∉ T := by
    intro heT
    exact (mem_erase.mp (hT heT)).1 rfl
  by_cases heC : e ∈ C
  · have hnot : e ∉ T ∩ C := fun h ↦ heT (Finset.mem_inter.mp h).1
    simp [intersectionCount, heC, heT, hnot]
  · have heq : insert e T ∩ C = T ∩ C := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hwT, hwC⟩
        · exact (heC hwC).elim
        · exact ⟨hwT, hwC⟩
      · rintro ⟨hwT, hwC⟩
        exact ⟨Or.inr hwT, hwC⟩
    simp [intersectionCount, heq]

/-- Uniform ambient-size Hoeffding bound for intersection with one fixed
test set. -/
theorem intersectionCount_twoSided_ambient (C : Finset E) {t : ℝ} (ht : 0 ≤ t) :
    ((((univ : Finset E).powerset.filter fun S ↦
        t ≤ |intersectionCount C S - (C.card : ℝ) / 2|).card : ℝ)) ≤
      2 * (2 : ℝ) ^ Fintype.card E *
        exp (-2 * t ^ 2 / Fintype.card E) := by
  have h := countEvent_twoSided_le
    (intersectionCount_hasBoundedDifferences_ambient C) ht
  rw [bernoulliExpectation_half_intersectionCount] at h
  simpa using h

/-- Union bound for simultaneous concentration over a finite family of test
sets, still with the ambient-size variance proxy. -/
theorem simultaneous_intersectionCount_twoSided_ambient
    {I : Type*} [Fintype I] [DecidableEq I] (C : I → Finset E)
    {t : ℝ} (ht : 0 ≤ t) :
    ((((univ : Finset E).powerset.filter fun S ↦
        ∃ i : I, t ≤
          |intersectionCount (C i) S - ((C i).card : ℝ) / 2|).card : ℝ)) ≤
      Fintype.card I *
        (2 * (2 : ℝ) ^ Fintype.card E *
          exp (-2 * t ^ 2 / Fintype.card E)) := by
  let bad : I → Finset (Finset E) := fun i ↦
    (univ : Finset E).powerset.filter fun S ↦
      t ≤ |intersectionCount (C i) S - ((C i).card : ℝ) / 2|
  have hsub : (univ : Finset E).powerset.filter (fun S ↦
      ∃ i : I, t ≤
        |intersectionCount (C i) S - ((C i).card : ℝ) / 2|) ⊆
      (univ : Finset I).biUnion bad := by
    intro S hS
    simp only [mem_filter, mem_powerset] at hS
    obtain ⟨i, hi⟩ := hS.2
    apply mem_biUnion.mpr
    exact ⟨i, mem_univ i, mem_filter.mpr ⟨mem_powerset.mpr hS.1, hi⟩⟩
  have hcard : ((univ : Finset E).powerset.filter (fun S ↦
      ∃ i : I, t ≤
        |intersectionCount (C i) S - ((C i).card : ℝ) / 2|)).card ≤
      ∑ i : I, (bad i).card := by
    exact (card_le_card hsub).trans (card_biUnion_le)
  have hcardR : ((((univ : Finset E).powerset.filter fun S ↦
      ∃ i : I, t ≤
        |intersectionCount (C i) S - ((C i).card : ℝ) / 2|).card : ℝ)) ≤
      ∑ i : I, ((bad i).card : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ ∑ i : I, ((bad i).card : ℝ) := hcardR
    _ ≤ ∑ _i : I, 2 * (2 : ℝ) ^ Fintype.card E *
          exp (-2 * t ^ 2 / Fintype.card E) := by
      apply sum_le_sum
      intro i _
      simpa [bad] using intersectionCount_twoSided_ambient (C i) ht
    _ = _ := by simp

section GraphSampling

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph retaining exactly the edges across the cut `A, Aᶜ`. -/
def crossingGraph (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A))
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.elim (fun h ↦ Or.inr ⟨h.2, h.1⟩)
      (fun h ↦ Or.inl ⟨h.2, h.1⟩)⟩
  loopless := by
    constructor
    intro x h
    exact G.loopless.irrefl x h.1

noncomputable instance crossingGraph.instDecidableRel
    (G : SimpleGraph V) (A : Finset V) : DecidableRel (crossingGraph G A).Adj :=
  Classical.decRel _

/-- Three global tests, all full neighborhoods, and all across-cut
neighborhoods. -/
abbrev TestIndex (V : Type*) := Sum (Fin 3) (Sum V V)

def testSet (G : SimpleGraph V) (A B : Finset V) : TestIndex V → Finset V
  | Sum.inl i =>
      if i = 0 then Finset.univ else if i = 1 then A else B
  | Sum.inr (Sum.inl v) => G.neighborFinset v
  | Sum.inr (Sum.inr v) =>
      if v ∈ A then G.neighborFinset v ∩ B else G.neighborFinset v ∩ A

/-- Primitive high-probability numerical conditions for the DKM
almost-bipartite Hamiltonicity argument.  The first conjunct simultaneously
controls sample size, both cut-part sizes, every induced degree, and every
crossing degree.  The second controls the number of sampled crossing edges. -/
def Suitable (G : SimpleGraph V) (A B : Finset V) (n : ℕ) (ρ : ℝ)
    (S : Finset V) : Prop :=
  (∀ i : TestIndex V,
    |intersectionCount (testSet G A B i) S -
        ((testSet G A B i).card : ℝ) / 2| < ρ * n) ∧
  |Concentration.inducedEdgeCount (crossingGraph G A) S -
      ((crossingGraph G A).edgeFinset.card : ℝ) / 4| < ρ * n ^ 2

theorem Suitable.sampleCard {G : SimpleGraph V} {A B S : Finset V}
    {n : ℕ} {ρ : ℝ} (h : Suitable G A B n ρ S) :
    |(S.card : ℝ) - (Fintype.card V : ℝ) / 2| < ρ * n := by
  simpa [testSet, intersectionCount] using h.1 (Sum.inl (0 : Fin 3))

/-- For the concrete `2 * n`-vertex ambient space, any suitable sample at
relative error at most `1/4` has enough vertices for the ordinary-cycle
Hamiltonicity bridge once `n ≥ 4`. -/
theorem Suitable.three_le_sampleCard_fin
    {n : ℕ} {G : SimpleGraph (Fin (2 * n))}
    {A B S : Finset (Fin (2 * n))} {ρ : ℝ}
    (h : Suitable G A B n ρ S) (hρ : ρ ≤ 1 / 4)
    (hn : 4 ≤ n) :
    3 ≤ S.card := by
  have hs := h.sampleCard
  simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at hs
  have hslow : - (ρ * (n : ℝ)) < (S.card : ℝ) - (2 * (n : ℝ)) / 2 :=
    (abs_lt.mp hs).1
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hsR : (3 : ℝ) < S.card := by
    nlinarith
  exact_mod_cast hsR.le

theorem Suitable.leftCard {G : SimpleGraph V} {A B S : Finset V}
    {n : ℕ} {ρ : ℝ} (h : Suitable G A B n ρ S) :
    |((S ∩ A).card : ℝ) - (A.card : ℝ) / 2| < ρ * n := by
  simpa [testSet, intersectionCount] using h.1 (Sum.inl (1 : Fin 3))

theorem Suitable.rightCard {G : SimpleGraph V} {A B S : Finset V}
    {n : ℕ} {ρ : ℝ} (h : Suitable G A B n ρ S) :
    |((S ∩ B).card : ℝ) - (B.card : ℝ) / 2| < ρ * n := by
  simpa [testSet, intersectionCount] using h.1 (Sum.inl (2 : Fin 3))

theorem Suitable.neighborCount {G : SimpleGraph V} {A B S : Finset V}
    {n : ℕ} {ρ : ℝ} (h : Suitable G A B n ρ S) (v : V) :
    |((S ∩ G.neighborFinset v).card : ℝ) - (G.degree v : ℝ) / 2| <
      ρ * n := by
  simpa [testSet, intersectionCount] using h.1 (Sum.inr (Sum.inl v))

theorem Suitable.crossNeighborCount_of_mem_left
    {G : SimpleGraph V} {A B S : Finset V} {n : ℕ} {ρ : ℝ}
    (h : Suitable G A B n ρ S) {v : V} (hv : v ∈ A) :
    |((S ∩ (G.neighborFinset v ∩ B)).card : ℝ) -
        ((G.neighborFinset v ∩ B).card : ℝ) / 2| < ρ * n := by
  simpa [testSet, intersectionCount, hv] using h.1 (Sum.inr (Sum.inr v))

theorem Suitable.crossNeighborCount_of_not_mem_left
    {G : SimpleGraph V} {A B S : Finset V} {n : ℕ} {ρ : ℝ}
    (h : Suitable G A B n ρ S) {v : V} (hv : v ∉ A) :
    |((S ∩ (G.neighborFinset v ∩ A)).card : ℝ) -
        ((G.neighborFinset v ∩ A).card : ℝ) / 2| < ρ * n := by
  simpa [testSet, intersectionCount, hv] using h.1 (Sum.inr (Sum.inr v))

theorem Suitable.crossingEdgeCount
    {G : SimpleGraph V} {A B S : Finset V} {n : ℕ} {ρ : ℝ}
    (h : Suitable G A B n ρ S) :
    |Concentration.inducedEdgeCount (crossingGraph G A) S -
        ((crossingGraph G A).edgeFinset.card : ℝ) / 4| < ρ * n ^ 2 :=
  h.2

theorem inducedEdgeCount_hasBoundedDifferences_ambient
    (J : SimpleGraph V) [DecidableRel J.Adj] :
    Erdos76.FiniteNibble.HasBoundedDifferences (univ : Finset V)
      (Concentration.inducedEdgeCount J) (fun _ ↦ (Fintype.card V : ℝ)) := by
  intro v hv T hT
  have h := Concentration.inducedEdgeCount_hasBoundedDifferences J v hv T hT
  have hdeg : (J.degree v : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Nat.le_of_lt (J.degree_lt_card_verts v)
  exact h.trans hdeg

/-- Uniform concentration for sampled crossing edges, with the deliberately
coarse ambient-cubed variance proxy. -/
theorem crossingEdgeCount_twoSided_ambient
    (J : SimpleGraph V) [DecidableRel J.Adj] {t : ℝ} (ht : 0 ≤ t) :
    ((((univ : Finset V).powerset.filter fun S ↦
        t ≤ |Concentration.inducedEdgeCount J S -
          (J.edgeFinset.card : ℝ) / 4|).card : ℝ)) ≤
      2 * (2 : ℝ) ^ Fintype.card V *
        exp (-2 * t ^ 2 /
          ((Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ 2)) := by
  have h := countEvent_twoSided_le
    (inducedEdgeCount_hasBoundedDifferences_ambient J) ht
  have hmean :
      Erdos76.FiniteNibble.bernoulliExpectation (univ : Finset V)
          halfProbability (Concentration.inducedEdgeCount J) =
        (J.edgeFinset.card : ℝ) / 4 := by
    change Erdos76.FiniteNibble.bernoulliExpectation (univ : Finset V)
          (fun _ ↦ (1 / 2 : ℝ)) (Concentration.inducedEdgeCount J) = _
    exact Concentration.bernoulliExpectation_half_inducedEdgeCount J
  rw [hmean] at h
  simpa using h

/-- Exact finite union bound for failure of any of the numerical sampling
conditions.  No graph hypothesis is needed; in particular this estimate is
uniform over all regular almost-bipartite graphs and all witness cuts. -/
theorem not_suitable_count_le
    (G : SimpleGraph V) (A B : Finset V) (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((((univ : Finset V).powerset.filter fun S ↦
        ¬ Suitable G A B n ρ S).card : ℝ)) ≤
      Fintype.card (TestIndex V) *
          (2 * (2 : ℝ) ^ Fintype.card V *
            exp (-2 * (ρ * n) ^ 2 / Fintype.card V)) +
        2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * (ρ * n ^ 2) ^ 2 /
            ((Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ 2)) := by
  let badTests := (univ : Finset V).powerset.filter fun S ↦
    ∃ i : TestIndex V, ρ * n ≤
      |intersectionCount (testSet G A B i) S -
        ((testSet G A B i).card : ℝ) / 2|
  let badEdges := (univ : Finset V).powerset.filter fun S ↦
    ρ * n ^ 2 ≤ |Concentration.inducedEdgeCount (crossingGraph G A) S -
      ((crossingGraph G A).edgeFinset.card : ℝ) / 4|
  have hsub : (univ : Finset V).powerset.filter (fun S ↦
      ¬ Suitable G A B n ρ S) ⊆ badTests ∪ badEdges := by
    intro S hS
    simp only [mem_filter, mem_powerset, mem_union] at hS ⊢
    simp only [Suitable, not_and_or, not_forall, not_lt] at hS
    rcases hS.2 with htest | hedge
    · exact Or.inl (mem_filter.mpr ⟨mem_powerset.mpr hS.1, htest⟩)
    · exact Or.inr (mem_filter.mpr ⟨mem_powerset.mpr hS.1, hedge⟩)
  have hcard : ((univ : Finset V).powerset.filter (fun S ↦
      ¬ Suitable G A B n ρ S)).card ≤ badTests.card + badEdges.card :=
    (card_le_card hsub).trans (card_union_le _ _)
  have hcardR : ((((univ : Finset V).powerset.filter fun S ↦
      ¬ Suitable G A B n ρ S).card : ℝ)) ≤
      (badTests.card : ℝ) + (badEdges.card : ℝ) := by exact_mod_cast hcard
  have htests := simultaneous_intersectionCount_twoSided_ambient
    (testSet G A B) (mul_nonneg hρ (Nat.cast_nonneg n))
  have hedges := crossingEdgeCount_twoSided_ambient (crossingGraph G A)
    (mul_nonneg hρ (sq_nonneg (n : ℝ)))
  calc
    _ ≤ (badTests.card : ℝ) + (badEdges.card : ℝ) := hcardR
    _ ≤ _ := by
      dsimp [badTests, badEdges] at htests hedges ⊢
      exact add_le_add htests hedges

/-- The graph-independent normalized error majorant after specializing the
ambient type to `Fin (2*n)`. -/
def failureMajorant (ρ : ℝ) (n : ℕ) : ℝ :=
  (3 + 4 * (n : ℝ)) * 2 * exp (-ρ ^ 2 * n) +
    2 * exp (-((ρ ^ 2) / 4) * n)

theorem not_suitable_count_le_failureMajorant
    {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin (2 * n)))
    (A B : Finset (Fin (2 * n))) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((((univ : Finset (Fin (2 * n))).powerset.filter fun S ↦
        ¬ Suitable G A B n ρ S).card : ℝ)) ≤
      failureMajorant ρ n * (2 : ℝ) ^ (2 * n) := by
  have h := not_suitable_count_le G A B n hρ
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have htestexp :
      -2 * (ρ * (n : ℝ)) ^ 2 / (2 * (n : ℝ)) =
        -ρ ^ 2 * (n : ℝ) := by
    field_simp
  have hedgeexp :
      -2 * (ρ * (n : ℝ) ^ 2) ^ 2 /
          ((2 * (n : ℝ)) * (2 * (n : ℝ)) ^ 2) =
        -(ρ ^ 2 / 4) * (n : ℝ) := by
    field_simp
    ring
  simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h
  rw [htestexp, hedgeexp] at h
  change _ ≤ failureMajorant ρ n * (2 : ℝ) ^ (2 * n)
  calc
    _ ≤
        (Fintype.card (TestIndex (Fin (2 * n))) : ℝ) *
            (2 * (2 : ℝ) ^ (2 * n) *
              exp (-ρ ^ 2 * (n : ℝ))) +
          2 * (2 : ℝ) ^ (2 * n) *
            exp (-(ρ ^ 2 / 4) * (n : ℝ)) := h
    _ = _ := by
      simp only [Fintype.card_sum, Fintype.card_fin, failureMajorant]
      push_cast
      ring

theorem failureMajorant_tendsto_zero {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (failureMajorant ρ) atTop (nhds 0) := by
  have hc1 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hc2 : 0 < ρ ^ 2 / 4 := div_pos hc1 (by norm_num)
  have hlin1 := Concentration.tendsto_linear_mul_exp_neg (ρ ^ 2) hc1
  have hlin2 := Concentration.tendsto_linear_mul_exp_neg (ρ ^ 2 / 4) hc2
  have hzero : Tendsto (fun n : ℕ ↦ exp (-ρ ^ 2 * (n : ℝ)))
      atTop (nhds 0) := by
    have htop : Tendsto (fun n : ℕ ↦ ρ ^ 2 * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hc1
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp htop using 1 <;>
      simp [Function.comp_def] <;> ring
  have hfirst : Tendsto
      (fun n : ℕ ↦ (3 + 4 * (n : ℝ)) * 2 * exp (-ρ ^ 2 * n))
      atTop (nhds 0) := by
    have hrewrite : (fun n : ℕ ↦
        (3 + 4 * (n : ℝ)) * 2 * exp (-ρ ^ 2 * n)) =
        (fun n : ℕ ↦
          6 * exp (-ρ ^ 2 * n) +
            8 * ((n : ℝ) * exp (-ρ ^ 2 * n))) := by
      funext n
      ring
    rw [hrewrite]
    convert (hzero.const_mul 6).add (hlin1.const_mul 8) using 1 <;>
      norm_num
  have hsecond : Tendsto
      (fun n : ℕ ↦ 2 * exp (-((ρ ^ 2) / 4) * n))
      atTop (nhds 0) := by
    have htop : Tendsto (fun n : ℕ ↦ (ρ ^ 2 / 4) * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hc2
    convert (Real.tendsto_exp_neg_atTop_nhds_zero.comp htop).const_mul 2 using 1 <;>
      simp [Function.comp_def] <;> ring
  unfold failureMajorant
  simpa only [add_zero] using hfirst.add hsecond

/-- Fully uniform eventual form: after one threshold depending only on
`ρ,ε`, every graph and every ordered pair of cut parts has at most an
`ε`-fraction of samples failing the DKM numerical conditions. -/
theorem eventually_not_suitable_count_le
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B : Finset (Fin (2 * n))),
        ((((univ : Finset (Fin (2 * n))).powerset.filter fun S ↦
            ¬ Suitable G A B n ρ S).card : ℝ)) ≤
          ε * (2 : ℝ) ^ (2 * n) := by
  have hmajor : ∀ᶠ n : ℕ in atTop, failureMajorant ρ n < ε :=
    (failureMajorant_tendsto_zero hρ).eventually (gt_mem_nhds hε)
  filter_upwards [eventually_ge_atTop 1, hmajor] with n hn hmaj
  intro G A B
  have hcount := not_suitable_count_le_failureMajorant hn G A B hρ.le
  have hpow : 0 < (2 : ℝ) ^ (2 * n) := by positivity
  exact hcount.trans (mul_le_mul_of_nonneg_right hmaj.le hpow.le)

/-- The preceding concentration theorem in the counting notation consumed
by `almostBipartite_counting_assembly`. -/
theorem eventually_not_suitable_almostBipartiteCount_le
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B : Finset (Fin (2 * n))),
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ ¬ Suitable G A B n ρ S) : ℝ) ≤
          ε * (2 : ℝ) ^ (2 * n) := by
  filter_upwards [eventually_not_suitable_count_le hρ hε] with n hn
  intro G A B
  have heq :
      almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ ¬ Suitable G A B n ρ S) =
        ((Finset.univ : Finset (Fin (2 * n))).powerset.filter
          fun S ↦ ¬ Suitable G A B n ρ S).card := by
    unfold almostBipartiteCount almostBipartiteEvent
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
  rw [heq]
  exact hn G A B

end GraphSampling

end

end Erdos622.SamplingSuitable

namespace Erdos622

/-- Eventual assembly interface used by the downstream unconditional
almost-bipartite case.  The probabilistic half-minus-error estimate and the
deterministic suitable-good-sample implication are kept separate; uniform
concentration and `almostBipartite_counting_subtraction` combine them into the
canonical case-density statement. -/
theorem uniformCaseDensityBound_almostBipartite_of_sample_bounds
    {ρ : ℝ} (hρ : 0 < ρ)
    (hgood : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin (2 * n))) [G.LocallyFinite],
          G.IsRegularOfDegree (n + 1) → AlmostBipartiteRegime n G →
            ∃ A B : Finset (Fin (2 * n)),
              IsAlmostBipartiteCut G A B ∧
              ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
                (almostBipartiteCount
                  (Finset.univ : Finset (Fin (2 * n)))
                  (fun S ↦ IsKGoodSample G A B S 0) : ℝ))
    (hdeterministic :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin (2 * n))) [G.LocallyFinite]
          (A B S : Finset (Fin (2 * n))),
          G.IsRegularOfDegree (n + 1) → IsAlmostBipartiteCut G A B →
          SamplingSuitable.Suitable G A B n ρ S →
          IsKGoodSample G A B S 0 → IsSpannedByCycle G S) :
    UniformCaseDensityBound AlmostBipartiteRegime := by
  intro epsilon hepsilon
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := div_pos hepsilon (by norm_num)
  filter_upwards [hgood delta hdelta,
    SamplingSuitable.eventually_not_suitable_almostBipartiteCount_le hρ hdelta,
    hdeterministic] with n hnGood hnBad hnDet
  intro G
  let : DecidableRel G.Adj := Classical.decRel _
  intro hreg hab
  obtain ⟨A, B, hAB, hgoodCount⟩ := hnGood G hreg hab
  have hgoodCount' :
      ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ Fintype.card (Fin (2 * n)) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
    simpa using hgoodCount
  have hbadCount' :
      (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ ¬ SamplingSuitable.Suitable G A B n ρ S) : ℝ) ≤
        delta * (2 : ℝ) ^ Fintype.card (Fin (2 * n)) := by
    simpa using hnBad G A B
  apply (cyclicSubsetDensity_lower_iff_count_lower G
    ((1 / 2 : ℝ) - epsilon)).mpr
  have hcount := almostBipartite_counting_subtraction
    G A B 0 (SamplingSuitable.Suitable G A B n ρ) delta hAB.1
    hgoodCount' hbadCount'
    (fun S _hSuniv _hcut hSuitable hGood ↦
      hnDet G A B S hreg hAB hSuitable hGood)
  convert hcount using 1 <;> simp only [Fintype.card_fin]
  · dsimp [delta]
    ring

end Erdos622

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval Interval

namespace Erdos622

noncomputable section

lemma gaussianPDFReal_zero_one_eq (x : ℝ) :
    gaussianPDFReal 0 1 x =
      gaussianKernel x / Real.sqrt (2 * Real.pi) := by
  simp [gaussianPDFReal, gaussianKernel, div_eq_mul_inv, mul_comm]

lemma integral_gaussianKernel_Icc_eq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∫ x in Icc (-u) v, gaussianKernel x =
      gaussianHalfInterval u + gaussianHalfInterval v := by
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith : -u ≤ v)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (gaussianKernel_intervalIntegrable (-u) 0)
    (gaussianKernel_intervalIntegrable 0 v)]
  have hneg : (∫ x in -u..0, gaussianKernel x) = gaussianHalfInterval u := by
    have hcomp : (∫ x in 0..u, gaussianKernel (-x)) =
        ∫ x in -u..0, gaussianKernel x := by
      simpa using
        (intervalIntegral.integral_comp_neg
          (f := gaussianKernel) (a := 0) (b := u))
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro x hx
    simp [gaussianKernel, gaussianHalfInterval]
  rw [hneg]
  rfl

lemma gaussianWindowMass_eq_gaussianWindow {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    BinomialCLT.gaussianWindowMass (-u) v = gaussianWindow u v := by
  unfold BinomialCLT.gaussianWindowMass BinomialCLT.standardGaussian
  change ENNReal.toReal (gaussianReal 0 1 (Icc (-u) v)) = gaussianWindow u v
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0) (Icc (-u) v)]
  rw [ENNReal.toReal_ofReal]
  · simp_rw [gaussianPDFReal_zero_one_eq]
    rw [MeasureTheory.integral_div]
    rw [integral_gaussianKernel_Icc_eq hu hv]
    rfl
  · exact integral_nonneg (fun x ↦ gaussianPDFReal_nonneg 0 1 x)

lemma gaussianWindowMass_dkm {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    BinomialCLT.gaussianWindowMass
        (-(dkmM1 α β * Real.sqrt 2))
        (dkmM2 α β * Real.sqrt 2) =
      dkmGaussianWindow α β := by
  apply gaussianWindowMass_eq_gaussianWindow
  · exact mul_nonneg (le_max_of_le_left (div_nonneg hα.le (by norm_num)))
      (Real.sqrt_nonneg _)
  · exact mul_nonneg (le_max_of_le_left (div_nonneg hβ.le (by norm_num)))
      (Real.sqrt_nonneg _)

lemma fairBinomialWindowCount_mono (N : ℕ) {a b c d : ℝ}
    (hac : a ≤ c) (hdb : d ≤ b) :
    BinomialCLT.fairBinomialWindowCount N c d ≤
      BinomialCLT.fairBinomialWindowCount N a b := by
  unfold BinomialCLT.fairBinomialWindowCount
  apply Finset.sum_le_sum
  intro k hk
  by_cases hinner : BinomialCLT.standardizedBinomialPoint N k ∈ Icc c d
  · have houter : BinomialCLT.standardizedBinomialPoint N k ∈ Icc a b :=
      ⟨hac.trans hinner.1, hinner.2.trans hdb⟩
    simp [hinner, houter]
  · simp [hinner]

/-- Complementing the second of two independent `n`-element samples turns
their cardinality difference into an ordinary fair binomial count on
`2 * n` coordinates.  This is the exact finite counting bridge between the
normal-window estimate and the two sides of a random cut. -/
lemma binomialDifference_window_count (n : ℕ) (a b : ℝ) :
    Counting.pairCount
        (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin n))
        (fun X Y ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
          (X.card + (n - Y.card)) ∈ Icc a b) =
      BinomialCLT.fairBinomialWindowCount (2 * n) a b := by
  calc
    Counting.pairCount
        (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin n))
        (fun X Y ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
          (X.card + (n - Y.card)) ∈ Icc a b) =
      Counting.binomialCount (n + n)
        (fun k ↦ BinomialCLT.standardizedBinomialPoint (2 * n) k ∈ Icc a b) :=
      by
        simpa using (Counting.binomialDifference_count n n
          (fun k : ℕ ↦ BinomialCLT.standardizedBinomialPoint (2 * n) k ∈ Icc a b))
    _ = BinomialCLT.fairBinomialWindowCount (2 * n) a b := by
      rw [Counting.binomialCount_eq_sum]
      unfold BinomialCLT.fairBinomialWindowCount
      rw [← Nat.range_succ_eq_Iic]
      simp only [two_mul]

theorem eventually_finite_windows_above (P : Finset (ℝ × ℝ)) (q : ℝ)
    (hP : ∀ z ∈ P, z.1 ≤ z.2 ∧
      q < BinomialCLT.gaussianWindowMass z.1 z.2) :
    ∀ᶠ N : ℕ in atTop, ∀ z ∈ P,
      q < (BinomialCLT.fairBinomialWindowCount N z.1 z.2 : ℝ) /
        (2 : ℝ) ^ N := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert z P hz ih =>
      have hzEventually :=
        BinomialCLT.eventually_lt_fairBinomialWindowCount_ratio
          (hP z (Finset.mem_insert_self z P)).1
          (hP z (Finset.mem_insert_self z P)).2
      have hrest : ∀ y ∈ P, y.1 ≤ y.2 ∧
          q < BinomialCLT.gaussianWindowMass y.1 y.2 := by
        intro y hy
        exact hP y (Finset.mem_insert_of_mem hy)
      filter_upwards [hzEventually, ih hrest] with N hzN hPN
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hzN
      · exact hPN y hy

/-- Finite-grid reduction for a compact-uniform binomial window estimate.
The only remaining work is to construct the finite family of fixed inner
windows, after which the fixed-window CLT applies uniformly. -/
theorem eventually_uniform_of_finite_inner_windows
    {Θ : Type*} (K : Set Θ) (a b : Θ → ℝ)
    (P : Finset (ℝ × ℝ)) (q : ℝ)
    (hcover : ∀ θ ∈ K, ∃ z ∈ P, a θ ≤ z.1 ∧ z.2 ≤ b θ)
    (hP : ∀ z ∈ P, z.1 ≤ z.2 ∧
      q < BinomialCLT.gaussianWindowMass z.1 z.2) :
    ∀ᶠ N : ℕ in atTop, ∀ θ ∈ K,
      q < (BinomialCLT.fairBinomialWindowCount N (a θ) (b θ) : ℝ) /
        (2 : ℝ) ^ N := by
  filter_upwards [eventually_finite_windows_above P q hP] with N hN
  intro θ hθ
  obtain ⟨z, hzP, haz, hzb⟩ := hcover θ hθ
  have hcount := fairBinomialWindowCount_mono N haz hzb
  have hcountReal :
      (BinomialCLT.fairBinomialWindowCount N z.1 z.2 : ℝ) ≤
        (BinomialCLT.fairBinomialWindowCount N (a θ) (b θ) : ℝ) := by
    exact_mod_cast hcount
  exact (hN z hzP).trans_le (div_le_div_of_nonneg_right hcountReal (by positivity))

/-- Compactness constructs the finite family needed by
`eventually_uniform_of_finite_inner_windows` once every parameter window has
a strictly internal fixed window retaining the desired Gaussian mass. -/
theorem exists_finite_inner_windows_of_compact
    {Θ : Type*} [TopologicalSpace Θ] {K : Set Θ}
    (hK : IsCompact K) (a b : Θ → ℝ) (q : ℝ)
    (ha : ContinuousOn a K) (hb : ContinuousOn b K)
    (hinner : ∀ θ ∈ K, ∃ z : ℝ × ℝ,
      a θ < z.1 ∧ z.2 < b θ ∧ z.1 ≤ z.2 ∧
        q < BinomialCLT.gaussianWindowMass z.1 z.2) :
    ∃ P : Finset (ℝ × ℝ),
      (∀ θ ∈ K, ∃ z ∈ P, a θ ≤ z.1 ∧ z.2 ≤ b θ) ∧
      ∀ z ∈ P, z.1 ≤ z.2 ∧
        q < BinomialCLT.gaussianWindowMass z.1 z.2 := by
  classical
  let z : K → ℝ × ℝ := fun x ↦ Classical.choose (hinner x.1 x.2)
  have hz (x : K) :
      a x.1 < (z x).1 ∧ (z x).2 < b x.1 ∧ (z x).1 ≤ (z x).2 ∧
        q < BinomialCLT.gaussianWindowMass (z x).1 (z x).2 :=
    Classical.choose_spec (hinner x.1 x.2)
  let U : K → Set K := fun x ↦
    {y | a y.1 < (z x).1 ∧ (z x).2 < b y.1}
  have hUopen (x : K) : IsOpen (U x) := by
    exact (isOpen_lt ha.restrict continuous_const).inter
      (isOpen_lt continuous_const hb.restrict)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hUcover : (Set.univ : Set K) ⊆ ⋃ x, U x := by
    intro x hx
    simp only [Set.mem_iUnion]
    exact ⟨x, (hz x).1, (hz x).2.1⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hUopen hUcover
  refine ⟨T.image z, ?_, ?_⟩
  · intro θ hθ
    let x : K := ⟨θ, hθ⟩
    have hx := hT (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hiT, hxi⟩ := hx
    refine ⟨z i, Finset.mem_image.mpr ⟨i, hiT, rfl⟩, ?_, ?_⟩
    · exact (show a x.1 < (z i).1 from hxi.1).le
    · exact (show (z i).2 < b x.1 from hxi.2).le
  · intro w hw
    obtain ⟨i, hiT, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨(hz i).2.2.1, (hz i).2.2.2⟩

theorem eventually_uniform_compact_windows
    {Θ : Type*} [TopologicalSpace Θ] {K : Set Θ}
    (hK : IsCompact K) (a b : Θ → ℝ) (q : ℝ)
    (ha : ContinuousOn a K) (hb : ContinuousOn b K)
    (hinner : ∀ θ ∈ K, ∃ z : ℝ × ℝ,
      a θ < z.1 ∧ z.2 < b θ ∧ z.1 ≤ z.2 ∧
        q < BinomialCLT.gaussianWindowMass z.1 z.2) :
    ∀ᶠ N : ℕ in atTop, ∀ θ ∈ K,
      q < (BinomialCLT.fairBinomialWindowCount N (a θ) (b θ) : ℝ) /
        (2 : ℝ) ^ N := by
  obtain ⟨P, hcover, hP⟩ :=
    exists_finite_inner_windows_of_compact hK a b q ha hb hinner
  exact eventually_uniform_of_finite_inner_windows K a b P q hcover hP

lemma exists_strict_inner_gaussian_window {u v q : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hq : q < gaussianWindow u v) :
    ∃ z : ℝ × ℝ,
      -u < z.1 ∧ z.2 < v ∧ z.1 ≤ z.2 ∧
        q < BinomialCLT.gaussianWindowMass z.1 z.2 := by
  have hhalf : Continuous gaussianHalfInterval :=
    intervalIntegral.continuous_primitive gaussianKernel_intervalIntegrable 0
  have hcont : ContinuousAt (fun t : ℝ ↦ gaussianWindow (u - t) (v - t)) 0 := by
    unfold gaussianWindow
    fun_prop
  have hev : ∀ᶠ t : ℝ in nhds 0, q < gaussianWindow (u - t) (v - t) :=
    hcont.eventually (by simpa using (lt_mem_nhds hq))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  let t : ℝ := min ε (min u v) / 2
  have hminpos : 0 < min ε (min u v) := by positivity
  have htpos : 0 < t := div_pos hminpos (by norm_num)
  have htε : t < ε := by
    dsimp [t]
    have hle : min ε (min u v) ≤ ε := min_le_left _ _
    nlinarith
  have htu : t < u := by
    dsimp [t]
    have hle : min ε (min u v) ≤ u :=
      (min_le_right ε (min u v)).trans (min_le_left u v)
    nlinarith
  have htv : t < v := by
    dsimp [t]
    have hle : min ε (min u v) ≤ v :=
      (min_le_right ε (min u v)).trans (min_le_right u v)
    nlinarith
  have htmem : q < gaussianWindow (u - t) (v - t) := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_of_pos htpos] using htε
  refine ⟨(-u + t, v - t), by linarith, by linarith, by linarith, ?_⟩
  rw [show -u + t = -(u - t) by ring]
  rw [gaussianWindowMass_eq_gaussianWindow (by linarith) (by linarith)]
  exact htmem

/-- Compact-uniform de Moivre--Laplace estimate for the one-parameter DKM
window.  Unlike the pointwise CLT in `BinomialCLT`, the eventual threshold is
uniform in `α ∈ [η,M]`. -/
theorem eventually_uniform_normal_window_above_half {η M : ℝ}
    (hη : 0 < η) (hηM : η ≤ M) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc η M,
        (1 / 2 : ℝ) + margin / 2 <
          (BinomialCLT.fairBinomialWindowCount N
            (-(α * Real.sqrt 2 / 4)) (Real.sqrt 2 / α) : ℝ) /
              (2 : ℝ) ^ N := by
  obtain ⟨margin, hmargin, hwindow⟩ := normalWindow_uniform_margin hη hηM
  refine ⟨margin, hmargin, ?_⟩
  let a : ℝ → ℝ := fun α ↦ -(α * Real.sqrt 2 / 4)
  let b : ℝ → ℝ := fun α ↦ Real.sqrt 2 / α
  have ha : ContinuousOn a (Icc η M) := by
    apply Continuous.continuousOn
    dsimp [a]
    fun_prop
  have hb : ContinuousOn b (Icc η M) := by
    intro α hα
    have hαne : α ≠ 0 := (hη.trans_le hα.1).ne'
    dsimp [b]
    fun_prop
  have hinner : ∀ α ∈ Icc η M, ∃ z : ℝ × ℝ,
      a α < z.1 ∧ z.2 < b α ∧ z.1 ≤ z.2 ∧
        (1 / 2 : ℝ) + margin / 2 <
          BinomialCLT.gaussianWindowMass z.1 z.2 := by
    intro α hα
    have hαpos : 0 < α := hη.trans_le hα.1
    have hu : 0 < α * Real.sqrt 2 / 4 := by positivity
    have hv : 0 < Real.sqrt 2 / α := by positivity
    have hq : (1 / 2 : ℝ) + margin / 2 <
        gaussianWindow (α * Real.sqrt 2 / 4) (Real.sqrt 2 / α) := by
      have hw := hwindow α hα
      change (1 / 2 : ℝ) + margin ≤
        gaussianWindow (α * Real.sqrt 2 / 4) (Real.sqrt 2 / α) at hw
      linarith
    simpa only [a, b] using exists_strict_inner_gaussian_window hu hv hq
  simpa only [a, b] using
    (eventually_uniform_compact_windows isCompact_Icc a b
      ((1 / 2 : ℝ) + margin / 2) ha hb hinner)

/-- The DKM two-cover window contains the one-parameter normal window.
Consequently the preceding compact estimate is uniform simultaneously in
`α ∈ [η,M]` and in every positive value of the second cover parameter `β`.
This is the triangular-array form needed when cover sizes vary with `n` and
with the input graph. -/
theorem eventually_uniform_dkm_window_above_half {η M : ℝ}
    (hη : 0 < η) (hηM : η ≤ M) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc η M, ∀ β : ℝ,
        (1 / 2 : ℝ) + margin / 2 <
          (BinomialCLT.fairBinomialWindowCount N
            (-(dkmM1 α β * Real.sqrt 2))
            (dkmM2 α β * Real.sqrt 2) : ℝ) / (2 : ℝ) ^ N := by
  obtain ⟨margin, hmargin, hnormal⟩ :=
    eventually_uniform_normal_window_above_half hη hηM
  refine ⟨margin, hmargin, ?_⟩
  filter_upwards [hnormal] with N hN
  intro α hα β
  have hαpos : 0 < α := hη.trans_le hα.1
  have hm1 : α / 4 ≤ dkmM1 α β := le_max_left _ _
  have hm2 : 1 / α ≤ dkmM2 α β := le_max_right _ _
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hleft : -(dkmM1 α β * Real.sqrt 2) ≤
      -(α * Real.sqrt 2 / 4) := by
    have := mul_le_mul_of_nonneg_right hm1 hsqrt
    nlinarith
  have hright : Real.sqrt 2 / α ≤ dkmM2 α β * Real.sqrt 2 := by
    calc
      Real.sqrt 2 / α = (1 / α) * Real.sqrt 2 := by ring
      _ ≤ dkmM2 α β * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right hm2 hsqrt
  have hcount := fairBinomialWindowCount_mono N hleft hright
  have hcountReal :
      (BinomialCLT.fairBinomialWindowCount N
          (-(α * Real.sqrt 2 / 4)) (Real.sqrt 2 / α) : ℝ) ≤
        (BinomialCLT.fairBinomialWindowCount N
          (-(dkmM1 α β * Real.sqrt 2))
          (dkmM2 α β * Real.sqrt 2) : ℝ) := by
    exact_mod_cast hcount
  exact (hN α hα).trans_le
    (div_le_div_of_nonneg_right hcountReal (by positivity))

/-- Exact two-block counting form of the compact-uniform DKM window.  The
two coordinates are independently chosen subsets of two `n`-vertex sides,
and the second cardinality is complemented.  The threshold is uniform in
both the graph-dependent compact parameter `α` and the unrestricted second
cover parameter `β`. -/
theorem eventually_uniform_dkm_difference_count {η M : ℝ}
    (hη : 0 < η) (hηM : η ≤ M) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ᶠ n : ℕ in atTop, ∀ α ∈ Icc η M, ∀ β : ℝ,
        (1 / 2 : ℝ) + margin / 2 <
          (Counting.pairCount
            (Finset.univ : Finset (Fin n))
            (Finset.univ : Finset (Fin n))
            (fun X Y ↦
              BinomialCLT.standardizedBinomialPoint (2 * n)
                (X.card + (n - Y.card)) ∈
              Icc (-(dkmM1 α β * Real.sqrt 2))
                (dkmM2 α β * Real.sqrt 2)) : ℝ) /
            (2 : ℝ) ^ (2 * n) := by
  obtain ⟨margin, hmargin, hwindow⟩ :=
    eventually_uniform_dkm_window_above_half hη hηM
  refine ⟨margin, hmargin, ?_⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hwindow
  apply Filter.eventually_atTop.mpr
  refine ⟨N, ?_⟩
  intro n hn α hα β
  have h2n : N ≤ 2 * n := by omega
  simpa only [binomialDifference_window_count] using
    hN (2 * n) h2n α hα β

theorem eventually_dkm_window_above_half
    {η M α β : ℝ} (hη : 0 < η) (hηM : η ≤ M)
    (hα : α ∈ Icc η M) (hβ : 0 < β) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ᶠ N : ℕ in atTop,
        (1 / 2 : ℝ) + margin / 2 <
          (BinomialCLT.fairBinomialWindowCount N
            (-(dkmM1 α β * Real.sqrt 2))
            (dkmM2 α β * Real.sqrt 2) : ℝ) / (2 : ℝ) ^ N := by
  obtain ⟨margin, hmargin, huniform⟩ := dkmGaussianWindow_uniform_margin hη hηM
  refine ⟨margin, hmargin, ?_⟩
  apply BinomialCLT.eventually_lt_fairBinomialWindowCount_ratio
  · have hm1 : 0 ≤ dkmM1 α β :=
      le_max_of_le_left (div_nonneg (hη.trans_le hα.1).le (by norm_num))
    have hm2 : 0 ≤ dkmM2 α β :=
      le_max_of_le_left (div_nonneg hβ.le (by norm_num))
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith
  · rw [gaussianWindowMass_dkm (hη.trans_le hα.1) hβ]
    have h := huniform α hα β
    linarith

end

end Erdos622
