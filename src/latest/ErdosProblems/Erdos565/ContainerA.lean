import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import ErdosProblems.Erdos565.FiniteAnalysis
import ErdosProblems.Erdos565.ContainerFuel
import ErdosProblems.Erdos565.ContainerInvariants
import ErdosProblems.Erdos565.ContainerWeight
import ErdosProblems.Erdos565.ContainerSelector
import ErdosProblems.Erdos565.Hypergraph
import ErdosProblems.Erdos565.JansonContainer

/-!
# The finite update kernel for the Campos--Samotij container algorithm

This file isolates the purely finite part of the container algorithm used in
the proof of Erdős problem 565.  A hypergraph is represented by a finite
family of finite subsets.  The central operation replaces every old edge
containing one of a family of new, smaller edges by that family.  We prove
that this operation preserves antichains and input-independence and strictly
increases the generated up-set.  The latter is the termination argument for
the algorithm.

The quantitative link-weight argument is layered on top of this kernel later;
the lemmas here deliberately have no analytic hypotheses.
-/

open scoped BigOperators

namespace Erdos565
namespace ContainerA

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite hypergraph on `V`.  This is definitionally the representation
used by `Erdos565.Hypergraph`. -/
abbrev Family (V : Type*) [DecidableEq V] := Hypergraph V

/-- No two distinct edges of the family contain one another. -/
def IsAntichain (H : Family V) : Prop :=
  ∀ ⦃A⦄, A ∈ H → ∀ ⦃B⦄, B ∈ H → A ⊆ B → A = B

/-- Every edge has the prescribed cardinality. -/
def IsUniform (H : Family V) (s : ℕ) : Prop :=
  ∀ ⦃E⦄, E ∈ H → E.card = s

/-- Every edge is nonempty. -/
def HasNonemptyEdges (H : Family V) : Prop :=
  ∀ ⦃E⦄, E ∈ H → E.Nonempty

/-- Every edge has size at most `s`. -/
def IsRankAtMost (H : Family V) (s : ℕ) : Prop :=
  ∀ ⦃E⦄, E ∈ H → E.card ≤ s

/-- The family of all vertex sets which contain an edge of `H`. -/
def upClosure (H : Family V) : Family V :=
  Finset.univ.filter fun A ↦ ∃ E ∈ H, E ⊆ A

/-- The cardinality of the generated up-set.  This is the termination rank. -/
def upRank (H : Family V) : ℕ := (upClosure H).card

/-- The edges of cardinality exactly `a`. -/
def layer (H : Family V) (a : ℕ) : Family V :=
  H.filter fun E ↦ E.card = a

/-- The edges of cardinality strictly less than `s`. -/
def below (H : Family V) (s : ℕ) : Family V :=
  H.filter fun E ↦ E.card < s

/-- The edges with at least two vertices. -/
def aboveOne (H : Family V) : Family V :=
  H.filter fun E ↦ 2 ≤ E.card

/-- The link at `L`, with `L` removed from each edge that contains it. -/
def link (H : Family V) (L : Finset V) : Family V :=
  (H.filter fun E ↦ L ⊆ E).image fun E ↦ E \ L

/-- A set is independent when it contains no edge of the hypergraph. -/
def Independent (H : Family V) (I : Finset V) : Prop :=
  ∀ ⦃E⦄, E ∈ H → ¬ E ⊆ I

/-- The vertices not forbidden by a singleton edge. -/
def containerVertices (H : Family V) : Finset V :=
  Finset.univ.filter fun v ↦ ({v} : Finset V) ∉ H

/-- `C` covers `H` if every edge of `H` contains an edge of `C`. -/
def Covers (C H : Family V) : Prop :=
  ∀ ⦃E⦄, E ∈ H → ∃ F ∈ C, F ⊆ E

/-- Delete all old edges lying above `F`, then insert `F`. -/
def update (H F : Family V) : Family V :=
  (H.filter fun E ↦ ¬ ∃ A ∈ F, A ⊆ E) ∪ F

/-- Bridge to the shared structural update API. -/
theorem update_eq_hypergraph_update (H F : Family V) :
    update H F = Hypergraph.update H F := by
  exact (Hypergraph.update_eq_filter_union H F).symm

@[simp] theorem mem_upClosure {H : Family V} {A : Finset V} :
    A ∈ upClosure H ↔ ∃ E ∈ H, E ⊆ A := by
  simp [upClosure]

@[simp] theorem mem_layer {H : Family V} {a : ℕ} {E : Finset V} :
    E ∈ layer H a ↔ E ∈ H ∧ E.card = a := by
  simp [layer]

@[simp] theorem mem_below {H : Family V} {s : ℕ} {E : Finset V} :
    E ∈ below H s ↔ E ∈ H ∧ E.card < s := by
  simp [below]

@[simp] theorem mem_aboveOne {H : Family V} {E : Finset V} :
    E ∈ aboveOne H ↔ E ∈ H ∧ 2 ≤ E.card := by
  simp [aboveOne]

@[simp] theorem mem_containerVertices {H : Family V} {v : V} :
    v ∈ containerVertices H ↔ ({v} : Finset V) ∉ H := by
  simp [containerVertices]

theorem mem_link {H : Family V} {L F : Finset V} :
    F ∈ link H L ↔ ∃ E ∈ H, L ⊆ E ∧ E \ L = F := by
  simp only [link, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨E, ⟨hEH, hLE⟩, rfl⟩
    exact ⟨E, hEH, hLE, rfl⟩
  · rintro ⟨E, hEH, hLE, hdiff⟩
    exact ⟨E, ⟨hEH, hLE⟩, hdiff⟩

@[simp] theorem mem_update {H F : Family V} {E : Finset V} :
    E ∈ update H F ↔
      (E ∈ H ∧ ¬ ∃ A ∈ F, A ⊆ E) ∨ E ∈ F := by
  simp [update]

theorem IsUniform.isAntichain {H : Family V} {s : ℕ}
    (hH : IsUniform H s) : IsAntichain H := by
  intro A hAH B hBH hAB
  exact Finset.eq_of_subset_of_card_le hAB (by simp [hH hAH, hH hBH])

theorem upClosure_mono {H K : Family V} (hHK : H ⊆ K) :
    upClosure H ⊆ upClosure K := by
  intro A hA
  rw [mem_upClosure] at hA ⊢
  obtain ⟨E, hEH, hEA⟩ := hA
  exact ⟨E, hHK hEH, hEA⟩

theorem upClosure_update_superset (H F : Family V) :
    upClosure H ⊆ upClosure (update H F) := by
  intro A hA
  rw [mem_upClosure] at hA ⊢
  obtain ⟨E, hEH, hEA⟩ := hA
  by_cases hdel : ∃ B ∈ F, B ⊆ E
  · obtain ⟨B, hBF, hBE⟩ := hdel
    exact ⟨B, (mem_update.mpr (Or.inr hBF)), hBE.trans hEA⟩
  · exact ⟨E, mem_update.mpr (Or.inl ⟨hEH, hdel⟩), hEA⟩

theorem replacement_mem_upClosure_update {H F : Family V} {A : Finset V}
    (hAF : A ∈ F) : A ∈ upClosure (update H F) := by
  rw [mem_upClosure]
  exact ⟨A, mem_update.mpr (Or.inr hAF), Finset.Subset.rfl⟩

theorem upClosure_update_ssubset {H F : Family V}
    (hF : ∃ A ∈ F, A ∉ upClosure H) :
    upClosure H ⊂ upClosure (update H F) := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨upClosure_update_superset H F, ?_⟩
  obtain ⟨A, hAF, hAold⟩ := hF
  intro heq
  exact hAold (heq ▸ replacement_mem_upClosure_update hAF)

theorem upRank_update_lt {H F : Family V}
    (hF : ∃ A ∈ F, A ∉ upClosure H) :
    upRank H < upRank (update H F) := by
  exact Finset.card_lt_card (upClosure_update_ssubset hF)

theorem upRank_le_univ (H : Family V) : upRank H ≤ Fintype.card (Finset V) := by
  exact Finset.card_le_card (Finset.subset_univ _)

theorem upRank_le_two_pow (H : Family V) : upRank H ≤ 2 ^ Fintype.card V := by
  simpa [Fintype.card_finset] using upRank_le_univ H

/-- A proper subset of an edge of an antichain cannot contain another edge
of that antichain. -/
theorem proper_subset_not_mem_upClosure {H : Family V} (hH : IsAntichain H)
    {A E : Finset V} (hEH : E ∈ H) (hAE : A ⊂ E) : A ∉ upClosure H := by
  intro hA
  obtain ⟨D, hDH, hDA⟩ := mem_upClosure.mp hA
  have hDE : D ⊆ E := hDA.trans hAE.1
  have hDEeq : D = E := hH hDH hEH hDE
  exact hAE.2 (hDEeq ▸ hDA)

theorem update_isAntichain {H F : Family V}
    (hH : IsAntichain H) (hF : IsAntichain F)
    (houtside : ∀ ⦃A⦄, A ∈ F → A ∉ upClosure H) :
    IsAntichain (update H F) := by
  intro A hA B hB hAB
  rw [mem_update] at hA hB
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact hH hA.1 hB.1 hAB
  · exfalso
    exact (houtside hB) (mem_upClosure.mpr ⟨A, hA.1, hAB⟩)
  · exfalso
    exact hB.2 ⟨A, hA, hAB⟩
  · exact hF hA hB hAB

theorem update_hasNonemptyEdges {H F : Family V}
    (hH : HasNonemptyEdges H) (hF : HasNonemptyEdges F) :
    HasNonemptyEdges (update H F) := by
  intro E hE
  rw [mem_update] at hE
  exact hE.elim (fun h ↦ hH h.1) (fun h ↦ hF h)

theorem update_isRankAtMost {H F : Family V} {s : ℕ}
    (hH : IsRankAtMost H s) (hF : IsRankAtMost F s) :
    IsRankAtMost (update H F) s := by
  intro E hE
  rw [mem_update] at hE
  exact hE.elim (fun h ↦ hH h.1) (fun h ↦ hF h)

theorem Independent.mono_family {H K : Family V} {I : Finset V}
    (hI : Independent K I) (hHK : H ⊆ K) : Independent H I := by
  intro E hEH
  exact hI (hHK hEH)

theorem independent_update {H F : Family V} {I : Finset V}
    (hH : Independent H I) (hF : Independent F I) :
    Independent (update H F) I := by
  intro E hE
  rw [mem_update] at hE
  exact hE.elim (fun h ↦ hH h.1) (fun h ↦ hF h)

theorem independent_singleton_family {L I : Finset V} (hLI : ¬ L ⊆ I) :
    Independent ({L} : Family V) I := by
  intro E hE
  simp only [Finset.mem_singleton] at hE
  subst E
  exact hLI

theorem independent_link_of_seed_subset {H : Family V} {I L : Finset V}
    (hI : Independent H I) (hLI : L ⊆ I) :
    Independent (link H L) I := by
  intro F hF hFI
  obtain ⟨E, hEH, hLE, rfl⟩ := mem_link.mp hF
  apply hI hEH
  intro x hxE
  by_cases hxL : x ∈ L
  · exact hLI hxL
  · exact hFI (Finset.mem_sdiff.mpr ⟨hxE, hxL⟩)

theorem independent_implies_subset_container {H : Family V} {I : Finset V}
    (hI : Independent H I) : I ⊆ containerVertices H := by
  intro v hvI
  rw [mem_containerVertices]
  intro hsv
  exact hI hsv (by simpa using hvI)

theorem aboveOne_subset_container {H : Family V} (hH : IsAntichain H) :
    ∀ ⦃E⦄, E ∈ aboveOne H → E ⊆ containerVertices H := by
  intro E hE v hvE
  obtain ⟨hEH, hEcard⟩ := mem_aboveOne.mp hE
  rw [mem_containerVertices]
  intro hsv
  have heq : ({v} : Finset V) = E := hH hsv hEH (by simpa using hvE)
  have : E.card = 1 := by simpa [← heq]
  omega

theorem cover_aboveOne_of_upClosure {H₀ H : Family V}
    (hup : upClosure H₀ ⊆ upClosure H) (hne : HasNonemptyEdges H) :
    Covers (aboveOne H)
      (H₀.filter fun E ↦ E ⊆ containerVertices H) := by
  intro E hE
  have hEH₀ : E ∈ H₀ := (Finset.mem_filter.mp hE).1
  have hEC : E ⊆ containerVertices H := (Finset.mem_filter.mp hE).2
  have hEup₀ : E ∈ upClosure H₀ := mem_upClosure.mpr ⟨E, hEH₀, Finset.Subset.rfl⟩
  obtain ⟨L, hLH, hLE⟩ := mem_upClosure.mp (hup hEup₀)
  have hLcard : 2 ≤ L.card := by
    have hpos : 0 < L.card := Finset.card_pos.mpr (hne hLH)
    have hneone : L.card ≠ 1 := by
      intro hcard
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      have hvE : v ∈ E := hLE (by simp)
      exact (mem_containerVertices.mp (hEC hvE)) hLH
    omega
  exact ⟨L, mem_aboveOne.mpr ⟨hLH, hLcard⟩, hLE⟩

theorem link_layer_isUniform (H : Family V) (a : ℕ) (L : Finset V) :
    IsUniform (link (layer H a) L) (a - L.card) := by
  intro F hF
  obtain ⟨E, hE, hLE, rfl⟩ := mem_link.mp hF
  rw [Finset.card_sdiff_of_subset hLE, (mem_layer.mp hE).2]

theorem link_layer_isAntichain (H : Family V) (a : ℕ) (L : Finset V) :
    IsAntichain (link (layer H a) L) :=
  (link_layer_isUniform H a L).isAntichain

theorem link_layer_hasNonemptyEdges {H : Family V} {a : ℕ} {L : Finset V}
    (hLnot : L ∉ H) : HasNonemptyEdges (link (layer H a) L) := by
  intro F hF
  obtain ⟨E, hE, hLE, hEF⟩ := mem_link.mp hF
  subst F
  rw [Finset.sdiff_nonempty]
  intro hEL
  have hEq : E = L := Finset.Subset.antisymm hEL hLE
  exact hLnot (hEq ▸ (mem_layer.mp hE).1)

theorem link_layer_edges_proper_old {H : Family V} {a : ℕ} {L F : Finset V}
    (hL : L.Nonempty) (hF : F ∈ link (layer H a) L) :
    ∃ E ∈ H, F ⊂ E := by
  obtain ⟨E, hE, hLE, rfl⟩ := mem_link.mp hF
  refine ⟨E, (mem_layer.mp hE).1, Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.sdiff_subset, ?_⟩⟩
  intro hEq
  obtain ⟨v, hvL⟩ := hL
  have hvE : v ∈ E := hLE hvL
  have hvDiff : v ∈ E \ L := hEq.symm ▸ hvE
  exact (Finset.mem_sdiff.mp hvDiff).2 hvL

theorem link_layer_outside_upClosure {H : Family V} {a : ℕ} {L : Finset V}
    (hH : IsAntichain H) (hL : L.Nonempty) :
    ∀ ⦃F⦄, F ∈ link (layer H a) L → F ∉ upClosure H := by
  intro F hF
  obtain ⟨E, hEH, hFE⟩ := link_layer_edges_proper_old hL hF
  exact proper_subset_not_mem_upClosure hH hEH hFE

theorem seed_outside_upClosure {H : Family V} {a : ℕ} {L : Finset V}
    (hH : IsAntichain H) (hLnot : L ∉ H)
    (hext : ∃ E ∈ layer H a, L ⊆ E) : L ∉ upClosure H := by
  obtain ⟨E, hE, hLE⟩ := hext
  have hne : L ≠ E := by
    intro hEq
    exact hLnot (hEq ▸ (mem_layer.mp hE).1)
  exact proper_subset_not_mem_upClosure hH (mem_layer.mp hE).1
    (Finset.ssubset_iff_subset_ne.mpr ⟨hLE, hne⟩)

theorem seed_rank_lt {H : Family V} {a : ℕ} {L : Finset V}
    (hext : ∃ E ∈ layer H a, L ⊆ E) (hLnot : L ∉ H) : L.card < a := by
  obtain ⟨E, hE, hLE⟩ := hext
  have hproper : L ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨hLE, by
    intro hEq
    exact hLnot (hEq ▸ (mem_layer.mp hE).1)⟩
  simpa [(mem_layer.mp hE).2] using Finset.card_lt_card hproper

/-- The two branches of a container-algorithm round. -/
inductive Branch where
  | accept
  | reject
  deriving DecidableEq

/-- A state records the current antichain and the accumulated fingerprint. -/
structure State (V : Type*) [DecidableEq V] where
  family : Family V
  fingerprint : Finset V
  acceptCount : ℕ

/-- The replacement family selected at a round. -/
def replacement (H : Family V) (a : ℕ) (L : Finset V) : Branch → Family V
  | .accept => link (layer H a) L
  | .reject => {L}

theorem replacement_isAntichain {H : Family V} {a : ℕ} {L : Finset V}
    (hH : IsAntichain H) (b : Branch) :
    IsAntichain (replacement H a L b) := by
  cases b with
  | accept => exact link_layer_isAntichain H a L
  | reject =>
      intro A hA B hB _
      simp only [replacement, Finset.mem_singleton] at hA hB
      subst A
      exact hB.symm

theorem replacement_hasNonemptyEdges {H : Family V} {a : ℕ} {L : Finset V}
    (hL : L.Nonempty) (hLnot : L ∉ H) (b : Branch) :
    HasNonemptyEdges (replacement H a L b) := by
  cases b with
  | accept => exact link_layer_hasNonemptyEdges hLnot
  | reject =>
      intro A hA
      simp only [replacement, Finset.mem_singleton] at hA
      simpa [hA] using hL

theorem replacement_outside_upClosure {H : Family V} {a : ℕ} {L : Finset V}
    (hH : IsAntichain H) (hL : L.Nonempty) (hLnot : L ∉ H)
    (hext : ∃ E ∈ layer H a, L ⊆ E) (b : Branch) :
    ∀ ⦃F⦄, F ∈ replacement H a L b → F ∉ upClosure H := by
  cases b with
  | accept => exact link_layer_outside_upClosure hH hL
  | reject =>
      intro F hF
      simp only [replacement, Finset.mem_singleton] at hF
      subst F
      exact seed_outside_upClosure hH hLnot hext

theorem replacement_nonempty {H : Family V} {a : ℕ} {L : Finset V}
    (hLnot : L ∉ H) (hext : ∃ E ∈ layer H a, L ⊆ E) (b : Branch) :
    (replacement H a L b).Nonempty := by
  cases b with
  | reject => simp [replacement]
  | accept =>
      obtain ⟨E, hE, hLE⟩ := hext
      refine ⟨E \ L, ?_⟩
      exact mem_link.mpr ⟨E, hE, hLE, rfl⟩

theorem replacement_isRankAtMost {H : Family V} {a s : ℕ} {L : Finset V}
    (has : a ≤ s) (hLnot : L ∉ H)
    (hext : ∃ E ∈ layer H a, L ⊆ E) (b : Branch) :
    IsRankAtMost (replacement H a L b) s := by
  cases b with
  | accept =>
      intro F hF
      rw [link_layer_isUniform H a L hF]
      exact (Nat.sub_le a L.card).trans has
  | reject =>
      intro F hF
      simp only [replacement, Finset.mem_singleton] at hF
      subst F
      exact (seed_rank_lt hext hLnot).le.trans has

/-- One explicit state update. -/
def State.next (st : State V) (a : ℕ) (L : Finset V) (b : Branch) : State V where
  family := update st.family (replacement st.family a L b)
  fingerprint := match b with
    | .accept => st.fingerprint ∪ L
    | .reject => st.fingerprint
  acceptCount := match b with
    | .accept => st.acceptCount + 1
    | .reject => st.acceptCount

/-- The combinatorial information attached to a nonterminal round.  The
weight threshold is used only to prove `extension`; all structural invariants
below need no real arithmetic. -/
structure Round (st : State V) (I : Finset V) (s : ℕ) where
  layerIndex : ℕ
  seed : Finset V
  branch : Branch
  two_le_layer : 2 ≤ layerIndex
  layer_le_rank : layerIndex ≤ s
  seed_nonempty : seed.Nonempty
  seed_not_edge : seed ∉ st.family
  extension : ∃ E ∈ layer st.family layerIndex, seed ⊆ E
  branch_spec : branch = .accept ↔ seed ⊆ I

/-- The layer and seed are selected from the current family alone; the input
`I` decides only whether the round is accepted. -/
structure SeedChoice (H : Family V) (s : ℕ) where
  layerIndex : ℕ
  seed : Finset V
  two_le_layer : 2 ≤ layerIndex
  layer_le_rank : layerIndex ≤ s
  seed_nonempty : seed.Nonempty
  seed_not_edge : seed ∉ H
  extension : ∃ E ∈ layer H layerIndex, seed ⊆ E

def linkWeight (p : ℝ) (H : Family V) (a : ℕ) (L : Finset V) : ℝ :=
  (Hypergraph.layer H a).link L |>.pWeight p

noncomputable def linkThreshold (s : ℕ) : ℝ := 1 / (4 * (s : ℝ))

/-- A layer/seed pair meeting the algorithm's link-weight threshold. -/
structure Candidate (H : Family V) (p : ℝ) (s : ℕ) extends SeedChoice H s where
  heavy : linkThreshold s ≤ linkWeight p H layerIndex seed

/-- A candidate with least layer and inclusion-maximal seed within that
layer.  Maximality is encoded in the precise numerical form used by the
low-link induction. -/
structure AlgorithmChoice (H : Family V) (p : ℝ) (s : ℕ)
    extends Candidate H p s where
  lower_layer : ∀ b, 2 ≤ b → b < layerIndex → ∀ K : Finset V,
    K.Nonempty → K ∉ H → (∃ E ∈ layer H b, K ⊆ E) →
      linkWeight p H b K < linkThreshold s
  maximal_seed : ∀ K : Finset V, seed ⊂ K → K ∉ H →
    (∃ E ∈ layer H layerIndex, K ⊆ E) →
      linkWeight p H layerIndex K < linkThreshold s

/-- Bridge the shared canonical-selector choice into the state-machine API. -/
def AlgorithmChoice.ofShared {H : Family V} {p : ℝ} {s : ℕ}
    (choice : ContainerSelector.Choice H p s) : AlgorithmChoice H p s where
  layerIndex := choice.layerIndex
  seed := choice.seed
  two_le_layer := choice.two_le_layer
  layer_le_rank := choice.layer_le_rank
  seed_nonempty := choice.seed_nonempty
  seed_not_edge := choice.seed_not_edge
  extension := choice.extension
  heavy := by
    simpa [linkThreshold, ContainerSelector.threshold, linkWeight,
      ContainerSelector.linkWeight] using choice.heavy
  lower_layer := by
    intro b hb hba K hK hKnot hKext
    simpa [linkThreshold, ContainerSelector.threshold, linkWeight,
      ContainerSelector.linkWeight] using
      choice.lower_layer b hb hba K hK hKnot hKext
  maximal_seed := by
    intro K hK hKnot hKext
    simpa [linkThreshold, ContainerSelector.threshold, linkWeight,
      ContainerSelector.linkWeight] using choice.maximal_seed K hK hKnot hKext

/-- From any heavy candidate, finite minimization in the layer and finite
maximization of seed cardinality produce the canonical structural choice
needed by the algorithm. -/
theorem exists_algorithmChoice_of_candidate {H : Family V} {p : ℝ} {s : ℕ}
    (hex : Nonempty (Candidate H p s)) :
    Nonempty (AlgorithmChoice H p s) := by
  classical
  let P : ℕ → Prop := fun a ↦ ∃ c : Candidate H p s, c.layerIndex = a
  have hP : ∃ a, P a := by
    obtain ⟨c⟩ := hex
    exact ⟨c.layerIndex, c, rfl⟩
  let a := Nat.find hP
  obtain ⟨c₀, hc₀a⟩ := Nat.find_spec hP
  let seeds : Finset (Finset V) :=
    Finset.univ.filter fun L ↦ ∃ c : Candidate H p s,
      c.layerIndex = a ∧ c.seed = L
  have hseeds : seeds.Nonempty := by
    refine ⟨c₀.seed, ?_⟩
    simp only [seeds, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c₀, hc₀a, rfl⟩
  obtain ⟨L, hLseed, hLmax⟩ := Finset.exists_max_image seeds Finset.card hseeds
  have hLcand : ∃ c : Candidate H p s,
      c.layerIndex = a ∧ c.seed = L := by
    simpa only [seeds, Finset.mem_filter, Finset.mem_univ, true_and] using hLseed
  obtain ⟨c, hca, hcL⟩ := hLcand
  refine ⟨{
    toCandidate := c
    lower_layer := ?_
    maximal_seed := ?_ }⟩
  · intro b hb2 hba K hKnon hKnot hKext
    by_contra hnotlt
    have hheavy : linkThreshold s ≤ linkWeight p H b K := le_of_not_gt hnotlt
    let d : Candidate H p s := {
      layerIndex := b
      seed := K
      two_le_layer := hb2
      layer_le_rank := hba.le.trans c.layer_le_rank
      seed_nonempty := hKnon
      seed_not_edge := hKnot
      extension := hKext
      heavy := hheavy }
    have hmin0 : Nat.find hP ≤ b := Nat.find_min' hP ⟨d, rfl⟩
    have hmin : c.layerIndex ≤ b := hca.trans_le hmin0
    omega
  · intro K hcK hKnot hKext
    by_contra hnotlt
    have hheavy : linkThreshold s ≤ linkWeight p H c.layerIndex K := le_of_not_gt hnotlt
    let d : Candidate H p s := {
      layerIndex := c.layerIndex
      seed := K
      two_le_layer := c.two_le_layer
      layer_le_rank := c.layer_le_rank
      seed_nonempty := c.seed_nonempty.mono hcK.1
      seed_not_edge := hKnot
      extension := hKext
      heavy := hheavy }
    have hKseed : K ∈ seeds := by
      simp only [seeds, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨d, hca, rfl⟩
    have hcardleL : K.card ≤ L.card := hLmax K hKseed
    have hcardle : K.card ≤ c.seed.card := by simpa [hcL] using hcardleL
    have hcardlt : c.seed.card < K.card := Finset.card_lt_card hcK
    omega

def branchFor (I L : Finset V) : Branch :=
  if L ⊆ I then .accept else .reject

@[simp] theorem branchFor_eq_accept_iff {I L : Finset V} :
    branchFor I L = .accept ↔ L ⊆ I := by
  simp [branchFor]

def SeedChoice.toRound {H : Family V} {s : ℕ} (choice : SeedChoice H s)
    (st : State V) (hfamily : st.family = H) (I : Finset V) : Round st I s where
  layerIndex := choice.layerIndex
  seed := choice.seed
  branch := branchFor I choice.seed
  two_le_layer := choice.two_le_layer
  layer_le_rank := choice.layer_le_rank
  seed_nonempty := choice.seed_nonempty
  seed_not_edge := hfamily ▸ choice.seed_not_edge
  extension := hfamily ▸ choice.extension
  branch_spec := branchFor_eq_accept_iff

/-- State invariants maintained throughout the execution on input `I`. -/
structure Invariant (H₀ : Family V) (I : Finset V) (s : ℕ) (st : State V) : Prop where
  family_antichain : IsAntichain st.family
  family_nonempty : HasNonemptyEdges st.family
  family_bounded : IsRankAtMost st.family s
  fingerprint_subset : st.fingerprint ⊆ I
  fingerprint_card_le : st.fingerprint.card ≤ s * st.acceptCount
  input_independent : Independent st.family I
  initial_upClosure : upClosure H₀ ⊆ upClosure st.family

/-- Initial state for the algorithm. -/
def initialState (H : Family V) : State V where
  family := H
  fingerprint := ∅
  acceptCount := 0

theorem initial_invariant {H : Family V} {I : Finset V} {s : ℕ}
    (hs : 0 < s) (huniform : IsUniform H s) (hI : Independent H I) :
    Invariant H I s (initialState H) := by
  refine ⟨huniform.isAntichain, ?_, ?_, by simp [initialState], by simp [initialState], hI,
    Finset.Subset.rfl⟩
  · intro E hE
    exact Finset.card_pos.mp (by simpa [huniform hE] using hs)
  · intro E hE
    exact (huniform hE).le

theorem Invariant.input_subset_container {H₀ : Family V} {I : Finset V}
    {s : ℕ} {st : State V} (hinv : Invariant H₀ I s st) :
    I ⊆ containerVertices st.family :=
  independent_implies_subset_container hinv.input_independent

theorem Invariant.output_cover {H₀ : Family V} {I : Finset V}
    {s : ℕ} {st : State V} (hinv : Invariant H₀ I s st) :
    Covers (aboveOne st.family)
      (H₀.filter fun E ↦ E ⊆ containerVertices st.family) :=
  cover_aboveOne_of_upClosure hinv.initial_upClosure hinv.family_nonempty

theorem Invariant.cover_edges_in_container {H₀ : Family V} {I : Finset V}
    {s : ℕ} {st : State V} (hinv : Invariant H₀ I s st) :
    ∀ ⦃E⦄, E ∈ aboveOne st.family → E ⊆ containerVertices st.family :=
  aboveOne_subset_container hinv.family_antichain

theorem Round.next_rank_gt {st : State V} {I : Finset V} {s : ℕ}
    (hinv : Invariant H₀ I s st) (rd : Round st I s) :
    upRank st.family <
      upRank (st.next rd.layerIndex rd.seed rd.branch).family := by
  apply upRank_update_lt
  obtain ⟨F, hF⟩ := replacement_nonempty rd.seed_not_edge rd.extension rd.branch
  exact ⟨F, hF,
    replacement_outside_upClosure hinv.family_antichain rd.seed_nonempty
      rd.seed_not_edge rd.extension rd.branch hF⟩

theorem fingerprint_subset_next_of_accept {st : State V} {a : ℕ} {L I : Finset V}
    (hS : st.fingerprint ⊆ I) (hL : L ⊆ I) :
    (st.next a L .accept).fingerprint ⊆ I := by
  intro v hv
  simp only [State.next, Finset.mem_union] at hv
  exact hv.elim (fun h ↦ hS h) (fun h ↦ hL h)

@[simp] theorem fingerprint_next_reject (st : State V) (a : ℕ) (L : Finset V) :
    (st.next a L .reject).fingerprint = st.fingerprint := rfl

theorem fingerprint_mono_next (st : State V) (a : ℕ) (L : Finset V) (b : Branch) :
    st.fingerprint ⊆ (st.next a L b).fingerprint := by
  cases b <;> simp [State.next]

theorem independent_next_accept {st : State V} {a : ℕ} {L I : Finset V}
    (hI : Independent st.family I) (hLI : L ⊆ I) :
    Independent (st.next a L .accept).family I := by
  apply independent_update hI
  apply independent_link_of_seed_subset
    (hI.mono_family (by intro E hE; exact (mem_layer.mp hE).1)) hLI

theorem independent_next_reject {st : State V} {a : ℕ} {L I : Finset V}
    (hI : Independent st.family I) (hLI : ¬ L ⊆ I) :
    Independent (st.next a L .reject).family I := by
  exact independent_update hI (independent_singleton_family hLI)

theorem Round.next_invariant {st : State V} {I : Finset V} {s : ℕ}
    (hinv : Invariant H₀ I s st) (rd : Round st I s) :
    Invariant H₀ I s (st.next rd.layerIndex rd.seed rd.branch) := by
  have hout := replacement_outside_upClosure hinv.family_antichain rd.seed_nonempty
    rd.seed_not_edge rd.extension rd.branch
  have hrepanti := replacement_isAntichain (a := rd.layerIndex) (L := rd.seed)
    hinv.family_antichain rd.branch
  have hrepnonempty := replacement_hasNonemptyEdges (a := rd.layerIndex)
    rd.seed_nonempty rd.seed_not_edge rd.branch
  have hrepbounded := replacement_isRankAtMost rd.layer_le_rank rd.seed_not_edge
    rd.extension rd.branch
  refine ⟨update_isAntichain hinv.family_antichain hrepanti hout,
    update_hasNonemptyEdges hinv.family_nonempty hrepnonempty,
    update_isRankAtMost hinv.family_bounded hrepbounded, ?_, ?_, ?_,
    hinv.initial_upClosure.trans (upClosure_update_superset _ _)⟩
  · cases hb : rd.branch with
    | accept =>
        exact fingerprint_subset_next_of_accept hinv.fingerprint_subset
          (rd.branch_spec.mp hb)
    | reject => simpa [State.next, hb] using hinv.fingerprint_subset
  · cases hb : rd.branch with
    | accept =>
        have hseed : rd.seed.card ≤ s :=
          (seed_rank_lt rd.extension rd.seed_not_edge).le.trans rd.layer_le_rank
        have hunion : (st.fingerprint ∪ rd.seed).card ≤
            st.fingerprint.card + rd.seed.card :=
          Finset.card_union_le st.fingerprint rd.seed
        simp only [State.next, hb]
        calc
          (st.fingerprint ∪ rd.seed).card ≤
              st.fingerprint.card + rd.seed.card := hunion
          _ ≤ s * st.acceptCount + s := Nat.add_le_add hinv.fingerprint_card_le hseed
          _ = s * (st.acceptCount + 1) := by rw [Nat.mul_add]; simp
    | reject => simpa [State.next, hb] using hinv.fingerprint_card_le
  · cases hb : rd.branch with
    | accept =>
        exact independent_next_accept hinv.input_independent (rd.branch_spec.mp hb)
    | reject =>
        apply independent_next_reject hinv.input_independent
        intro hseed
        have : rd.branch = .accept := rd.branch_spec.mpr hseed
        simp [hb] at this

/-- Every strictly rank-increasing chain has at most `2 ^ |V|` updates. -/
theorem upRank_add_length_le {f : ℕ → Family V} {k : ℕ}
    (hstep : ∀ i < k, upRank (f i) < upRank (f (i + 1))) :
    upRank (f 0) + k ≤ upRank (f k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have ih' : upRank (f 0) + k ≤ upRank (f k) :=
        ih (fun i hi ↦ hstep i (hi.trans (Nat.lt_succ_self k)))
      have hk : upRank (f k) < upRank (f (k + 1)) := hstep k (Nat.lt_succ_self k)
      omega

theorem strict_upRank_chain_length_le {f : ℕ → Family V} {k : ℕ}
    (hstep : ∀ i < k, upRank (f i) < upRank (f (i + 1))) :
    k ≤ 2 ^ Fintype.card V := by
  have hsum := upRank_add_length_le hstep
  have hbound := upRank_le_two_pow (f k)
  omega

/-- A deterministic choice of a legal round at every nonterminal state. -/
structure Oracle (I : Finset V) (s : ℕ) where
  terminal : State V → Prop
  decision : ∀ st, Decidable (terminal st)
  choose : ∀ st, ¬ terminal st → Round st I s

/-- A canonical selector: terminality and the chosen `(layer, seed)` depend
only on the current family, never on the input independent set or the current
fingerprint. -/
structure Selector (s : ℕ) where
  terminal : Family V → Prop
  decision : ∀ H, Decidable (terminal H)
  choose : ∀ H, ¬ terminal H → SeedChoice H s

/-- Terminality for the concrete weighted algorithm.  The two defensive
disjuncts make the selector total on arbitrary families; on states satisfying
`Invariant` they are impossible, so this is exactly the stopping inequality. -/
def algorithmTerminal (p : ℝ) (s : ℕ) (H : Family V) : Prop :=
  ContainerSelector.Stop p H ∨ ¬ IsAntichain H ∨ ¬ IsRankAtMost H s

noncomputable instance algorithmTerminalDecidable (p : ℝ) (s : ℕ) (H : Family V) :
    Decidable (algorithmTerminal p s H) := Classical.propDecidable _

/-- The shared least-layer, maximal-seed choice at a concrete nonterminal
family. -/
noncomputable def selectedSharedChoice (p : ℝ) (s : ℕ) (hs : 0 < s)
    (hp : 0 < p)
    (H : Family V) (hterminal : ¬ algorithmTerminal p s H) :
    ContainerSelector.Choice H p s := by
  have hstop : ¬ ContainerSelector.Stop p H := fun h => hterminal (Or.inl h)
  have hanti : IsAntichain H := by
    by_contra h
    exact hterminal (Or.inr (Or.inl h))
  have hbounded : IsRankAtMost H s := by
    by_contra h
    exact hterminal (Or.inr (Or.inr h))
  exact (ContainerSelector.canonicalSelector (V := V) p s hs hp).choose H
    hanti hbounded hstop

/-- The same choice transported to the local state-machine structures. -/
noncomputable def selectedChoice (p : ℝ) (s : ℕ) (hs : 0 < s) (hp : 0 < p)
    (H : Family V) (hterminal : ¬ algorithmTerminal p s H) :
    AlgorithmChoice H p s :=
  AlgorithmChoice.ofShared (selectedSharedChoice p s hs hp H hterminal)

/-- The concrete deterministic selector.  Its layer and seed depend only on
the current family; the independent input is consulted later only to choose
the accept/reject branch. -/
noncomputable def algorithmSelector (p : ℝ) (s : ℕ) (hs : 0 < s) (hp : 0 < p) :
    Selector (V := V) s where
  terminal := algorithmTerminal p s
  decision := fun H => algorithmTerminalDecidable p s H
  choose H h := (selectedChoice p s hs hp H h).toSeedChoice

theorem algorithmTerminal_iff_stop_of_invariant {H₀ : Family V} {I : Finset V}
    {s : ℕ} {st : State V} (hinv : Invariant H₀ I s st) (p : ℝ) :
    algorithmTerminal p s st.family ↔ ContainerSelector.Stop p st.family := by
  simp [algorithmTerminal, hinv.family_antichain, hinv.family_bounded]

/-- Finite/classical choice turns an existence proof for a legal seed into a
canonical selector depending only on the current family. -/
noncomputable def Selector.ofExists {s : ℕ} (terminal : Family V → Prop)
    (decision : ∀ H, Decidable (terminal H))
    (exists_choice : ∀ H, ¬ terminal H → Nonempty (SeedChoice H s)) :
    Selector (V := V) s where
  terminal := terminal
  decision := decision
  choose H h := Classical.choice (exists_choice H h)

def Selector.toOracle {s : ℕ} (selector : Selector (V := V) s)
    (I : Finset V) : Oracle I s where
  terminal st := selector.terminal st.family
  decision st := selector.decision st.family
  choose st h := (selector.choose st.family h).toRound st rfl I

/-- Apply the oracle's chosen round, fixing terminal states. -/
def Oracle.next {I : Finset V} {s : ℕ} (O : Oracle I s) (st : State V) : State V :=
  letI : Decidable (O.terminal st) := O.decision st
  if h : O.terminal st then st
  else
    let rd := O.choose st h
    st.next rd.layerIndex rd.seed rd.branch

theorem Oracle.next_eq_of_terminal {I : Finset V} {s : ℕ} (O : Oracle I s)
    {st : State V} (hst : O.terminal st) : O.next st = st := by
  simp [Oracle.next, hst]

theorem Oracle.next_eq_round_of_not_terminal {I : Finset V} {s : ℕ}
    (O : Oracle I s) {st : State V} (hst : ¬ O.terminal st) :
    O.next st =
      st.next (O.choose st hst).layerIndex (O.choose st hst).seed
        (O.choose st hst).branch := by
  simp [Oracle.next, hst]

theorem Oracle.next_rank_gt {I : Finset V} {s : ℕ} (O : Oracle I s)
    {H₀ : Family V} {st : State V} (hinv : Invariant H₀ I s st)
    (hst : ¬ O.terminal st) : upRank st.family < upRank (O.next st).family := by
  rw [O.next_eq_round_of_not_terminal hst]
  exact (O.choose st hst).next_rank_gt hinv

theorem Oracle.next_invariant {I : Finset V} {s : ℕ} (O : Oracle I s)
    {H₀ : Family V} {st : State V} (hinv : Invariant H₀ I s st) :
    Invariant H₀ I s (O.next st) := by
  by_cases hst : O.terminal st
  · rwa [O.next_eq_of_terminal hst]
  · rw [O.next_eq_round_of_not_terminal hst]
    exact (O.choose st hst).next_invariant hinv

theorem Oracle.fingerprint_mono_next {I : Finset V} {s : ℕ}
    (O : Oracle I s) (st : State V) : st.fingerprint ⊆ (O.next st).fingerprint := by
  by_cases hst : O.terminal st
  · rw [O.next_eq_of_terminal hst]
  · rw [O.next_eq_round_of_not_terminal hst]
    exact ContainerA.fingerprint_mono_next _ _ _ _

theorem Oracle.fingerprint_subset_run {I : Finset V} {s : ℕ}
    (O : Oracle I s) : ∀ (fuel : ℕ) (st : State V),
    st.fingerprint ⊆
      (@ContainerFuel.run (State V) O.terminal O.decision O.next fuel st).fingerprint := by
  letI : DecidablePred O.terminal := O.decision
  intro fuel
  induction fuel with
  | zero => intro st; exact Finset.Subset.rfl
  | succ fuel ih =>
      intro st
      by_cases hst : O.terminal st
      · rw [ContainerFuel.run_succ_of_terminal O.terminal O.next hst]
      · rw [ContainerFuel.run_succ_of_not_terminal O.terminal O.next hst]
        exact (O.fingerprint_mono_next st).trans (ih (O.next st))

theorem Oracle.invariant_run {I : Finset V} {s : ℕ} (O : Oracle I s)
    {H₀ : Family V} {st : State V} (hinv : Invariant H₀ I s st) :
    ∀ fuel, Invariant H₀ I s
      (@ContainerFuel.run (State V) O.terminal O.decision O.next fuel st) := by
  letI : DecidablePred O.terminal := O.decision
  intro fuel
  induction fuel generalizing st with
  | zero => simpa using hinv
  | succ fuel ih =>
      by_cases hst : O.terminal st
      · rw [ContainerFuel.run_succ_of_terminal O.terminal O.next hst]
        exact hinv
      · rw [ContainerFuel.run_succ_of_not_terminal O.terminal O.next hst]
        exact ih (O.next_invariant hinv)

/-- States equipped with the proof that all algorithm invariants hold. -/
abbrev GoodState (H₀ : Family V) (I : Finset V) (s : ℕ) :=
  {st : State V // Invariant H₀ I s st}

def Oracle.goodNext {I : Finset V} {s : ℕ} (O : Oracle I s)
    {H₀ : Family V} (x : GoodState H₀ I s) : GoodState H₀ I s :=
  ⟨O.next x.1, O.next_invariant x.2⟩

/-- The deterministic container execution reaches a terminal state within
`2 ^ |V| + 1` rounds.  Running on `GoodState` makes preservation of all
invariants part of the transition type. -/
theorem Oracle.terminates {I : Finset V} {s : ℕ} (O : Oracle I s)
    {H₀ : Family V} (x : GoodState H₀ I s) :
    let terminalGood : GoodState H₀ I s → Prop := fun y ↦ O.terminal y.1
    terminalGood
      (@ContainerFuel.run (GoodState H₀ I s) terminalGood
        (fun y ↦ O.decision y.1) O.goodNext
        (2 ^ Fintype.card V + 1) x) := by
  dsimp only
  let terminalGood : GoodState H₀ I s → Prop := fun y ↦ O.terminal y.1
  letI : DecidablePred terminalGood := fun y ↦ O.decision y.1
  apply ContainerFuel.terminal_run_of_strict_bounded_rank terminalGood O.goodNext
    (fun y ↦ upRank y.1.family) (2 ^ Fintype.card V)
  · intro state
    exact upRank_le_two_pow state.1.family
  · intro state hstate
    exact O.next_rank_gt state.2 hstate

/-! ## Quantitative invariants for the concrete selector -/

/-- An `s`-uniform initial family has no lower layers, hence satisfies the
low-link invariant. -/
theorem lowLinks_initial {H : Family V} {p : ℝ} {s : ℕ} (hs : 0 < s)
    (huniform : IsUniform H s) : ContainerSelector.LowLinks H p s := by
  intro a has L hL hLa
  have hlayer : Hypergraph.layer H a = ∅ := by
    ext E
    simp only [Hypergraph.mem_layer, Finset.notMem_empty, iff_false]
    rintro ⟨hEH, hcard⟩
    have := huniform hEH
    omega
  rw [ContainerSelector.linkWeight, hlayer]
  have hlink : Hypergraph.link (∅ : Hypergraph V) L = ∅ := by
    ext E
    simp [Hypergraph.link]
  rw [hlink, Hypergraph.pWeight_empty]
  positivity

/-- A strict link of an `a`-uniform layer is empty unless the seed has
cardinality strictly below `a`. -/
theorem strictLink_layer_eq_empty_of_not_card_lt (H : Family V) (a : ℕ)
    (L : Finset V) (hLa : ¬ L.card < a) :
    (Hypergraph.layer H a).strictLink L = ∅ := by
  ext F
  simp only [Finset.notMem_empty, iff_false]
  intro hF
  obtain ⟨hne, E, hE, hLE, hdiff⟩ := Hypergraph.mem_strictLink.mp hF
  have hproper : L ⊂ E := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hLE, ?_⟩
    intro hEq
    have : E \ L = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr
      (hEq ▸ Finset.Subset.rfl)
    exact hne (hdiff ▸ this)
  have hcard := Finset.card_lt_card hproper
  have hEa : E.card = a := (Hypergraph.mem_layer.mp hE).2
  omega

/-- Summing the layerwise low-link invariant gives the half-weight bound
needed by the deletion charging argument. -/
theorem lowLinks_strictBelow_le_half {H : Family V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 ≤ p) (hlow : ContainerSelector.LowLinks H p s)
    {L : Finset V} (hL : L.Nonempty) :
    ((ContainerWeight.belowRank H s).strictLink L).pWeight p ≤ 1 / 2 := by
  apply ContainerWeight.pWeight_strictLink_belowRank_le_half H L hs hp
  intro a ha
  have has : a < s := Finset.mem_range.mp ha
  by_cases hLa : L.card < a
  · rw [ContainerWeight.strictLink_layer_eq_link_of_card_lt hLa]
    exact hlow a has L hL hLa
  · rw [strictLink_layer_eq_empty_of_not_card_lt H a L hLa,
      Hypergraph.pWeight_empty]
    positivity

/-- Every inserted edge has rank strictly below the selected layer. -/
theorem replacement_card_lt_layer {H : Family V} {p : ℝ} {s : ℕ}
    (choice : AlgorithmChoice H p s) (b : Branch) {E : Finset V}
    (hE : E ∈ replacement H choice.layerIndex choice.seed b) :
    E.card < choice.layerIndex := by
  cases b with
  | accept =>
      rw [link_layer_isUniform H choice.layerIndex choice.seed hE]
      have hpos : 0 < choice.seed.card := Finset.card_pos.mpr choice.seed_nonempty
      have hseedlt : choice.seed.card < choice.layerIndex :=
        seed_rank_lt choice.extension choice.seed_not_edge
      omega
  | reject =>
      simp only [replacement, Finset.mem_singleton] at hE
      subst E
      exact seed_rank_lt choice.extension choice.seed_not_edge

/-- The below-rank weight inequality for one concrete round.  Rejecting a
seed is nondecreasing; accepting it gains at least `1/(8s)`. -/
theorem below_step_gain {H : Family V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 ≤ p) (hanti : IsAntichain H)
    (hlow : ContainerSelector.LowLinks H p s)
    (choice : ContainerSelector.Choice H p s) (b : Branch) :
    (ContainerWeight.belowRank H s).pWeight p +
        (if b = .accept then 1 / (8 * (s : ℝ)) else 0) ≤
      (ContainerWeight.belowRank
        (update H (replacement H choice.layerIndex choice.seed b)) s).pWeight p := by
  let localChoice : AlgorithmChoice H p s := AlgorithmChoice.ofShared choice
  let C : Family V := replacement H choice.layerIndex choice.seed b
  let HB : Family V := ContainerWeight.belowRank H s
  let D : Family V := ContainerWeight.removedBy HB C
  let K : Family V := ContainerWeight.belowRank (update H C) s
  have houtside : ∀ F ∈ C, F ∉ upClosure H := by
    intro F hF
    exact replacement_outside_upClosure hanti localChoice.seed_nonempty
      localChoice.seed_not_edge localChoice.extension b hF
  have hCcard : ∀ F ∈ C, F.card < s := by
    intro F hF
    exact (replacement_card_lt_layer localChoice b hF).trans_le choice.layer_le_rank
  have hDH : D ⊆ HB := by
    intro E hE
    exact (ContainerWeight.mem_removedBy.mp hE).1
  have hkeep : HB \ D ⊆ K := by
    intro E hE
    obtain ⟨hEHB, hEnD⟩ := Finset.mem_sdiff.mp hE
    obtain ⟨hEH, hEcard⟩ := ContainerWeight.mem_belowRank.mp hEHB
    have hnorem : ¬ ∃ F ∈ C, F ⊆ E := by
      intro hex
      exact hEnD (ContainerWeight.mem_removedBy.mpr ⟨hEHB, hex⟩)
    exact ContainerWeight.mem_belowRank.mpr
      ⟨mem_update.mpr (Or.inl ⟨hEH, hnorem⟩), hEcard⟩
  have hinsert : C ⊆ K := by
    intro F hF
    exact ContainerWeight.mem_belowRank.mpr
      ⟨mem_update.mpr (Or.inr hF), hCcard F hF⟩
  have hdis : Disjoint (HB \ D) C := by
    rw [Finset.disjoint_left]
    intro F hFold hFC
    have hFH : F ∈ H :=
      (ContainerWeight.mem_belowRank.mp (Finset.mem_sdiff.mp hFold).1).1
    exact (houtside F hFC) (mem_upClosure.mpr ⟨F, hFH, Finset.Subset.rfl⟩)
  have hout : ∀ F ∈ C, F ∉ HB := by
    intro F hFC hFHB
    have hFH := (ContainerWeight.mem_belowRank.mp hFHB).1
    exact (houtside F hFC) (mem_upClosure.mpr ⟨F, hFH, Finset.Subset.rfl⟩)
  have hremoved : D.pWeight p ≤ (1 / 2 : ℝ) * C.pWeight p := by
    apply ContainerWeight.pWeight_removedBy_le_half_mul hp hout
    intro F hFC
    exact lowLinks_strictBelow_le_half hs hp hlow
      (replacement_hasNonemptyEdges localChoice.seed_nonempty
        localChoice.seed_not_edge b hFC)
  have hbase : HB.pWeight p + C.pWeight p - D.pWeight p ≤ K.pWeight p :=
    ContainerWeight.pWeight_retained_inserted_le hp hDH hkeep hinsert hdis
  cases b with
  | reject =>
      rw [if_neg (by decide : Branch.reject ≠ Branch.accept)]
      have hCnonneg : 0 ≤ C.pWeight p := Hypergraph.pWeight_nonneg C hp
      nlinarith
  | accept =>
      rw [if_pos rfl]
      apply ContainerWeight.accepting_step_gain hs hp hDH hkeep hinsert hdis hremoved
      simpa [C, replacement, ContainerSelector.threshold,
        ContainerSelector.linkWeight, link, layer, Hypergraph.link,
        Hypergraph.layer] using choice.heavy

theorem p_le_one_of_le_container_bound {p : ℝ} {s : ℕ} (hs : 0 < s)
    (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2)) : p ≤ 1 := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hden : (1 : ℝ) ≤ 8 * (s : ℝ) ^ 2 := by nlinarith [sq_nonneg (s : ℝ)]
  calc
    p ≤ 1 / (8 * (s : ℝ) ^ 2) := hpmax
    _ ≤ 1 / 1 := one_div_le_one_div_of_le (by norm_num) hden
    _ = 1 := by norm_num

theorem p_le_threshold_of_le_container_bound {p : ℝ} {s : ℕ} (hs : 0 < s)
    (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2)) :
    p ≤ ContainerSelector.threshold s := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hpos : (0 : ℝ) < 4 * s := by positivity
  have hden : (4 : ℝ) * s ≤ 8 * s ^ 2 := by nlinarith [sq_nonneg ((s : ℝ) - 1)]
  calc
    p ≤ 1 / (8 * (s : ℝ) ^ 2) := hpmax
    _ ≤ 1 / (4 * (s : ℝ)) := one_div_le_one_div_of_le hpos hden
    _ = ContainerSelector.threshold s := by rw [ContainerSelector.threshold]

/-- One executable step of the concrete algorithm. -/
noncomputable def algorithmStep (p : ℝ) (s : ℕ) (hs : 0 < s) (hp : 0 < p)
    (I : Finset V) (st : State V) : State V :=
  if h : algorithmTerminal p s st.family then st
  else
    let choice := selectedSharedChoice p s hs hp st.family h
    st.next choice.layerIndex choice.seed (branchFor I choice.seed)

theorem algorithmStep_eq_self {p : ℝ} {s : ℕ} {hs : 0 < s} {hp : 0 < p}
    {I : Finset V} {st : State V} (h : algorithmTerminal p s st.family) :
    algorithmStep p s hs hp I st = st := by
  simp [algorithmStep, h]

theorem algorithmStep_eq_next {p : ℝ} {s : ℕ} {hs : 0 < s} {hp : 0 < p}
    {I : Finset V} {st : State V} (h : ¬ algorithmTerminal p s st.family) :
    algorithmStep p s hs hp I st =
      st.next (selectedSharedChoice p s hs hp st.family h).layerIndex
        (selectedSharedChoice p s hs hp st.family h).seed
        (branchFor I (selectedSharedChoice p s hs hp st.family h).seed) := by
    simp [algorithmStep, h]

/-- The executable presentation of a round is exactly the next-state map of
the canonical selector.  This identification is important: the quantitative
run below uses `algorithmStep`, while fingerprint consistency is most
naturally proved for the input-independent `Selector` interface. -/
theorem algorithmStep_eq_algorithmSelector_next (p : ℝ) (s : ℕ)
    (hs : 0 < s) (hp : 0 < p) (I : Finset V) (st : State V) :
    algorithmStep p s hs hp I st =
      ((algorithmSelector (V := V) p s hs hp).toOracle I).next st := by
  by_cases hterminal : algorithmTerminal p s st.family
  · simp [algorithmStep, Oracle.next, Selector.toOracle, algorithmSelector,
      selectedChoice, AlgorithmChoice.ofShared, SeedChoice.toRound, hterminal]
  · simp [algorithmStep, Oracle.next, Selector.toOracle, algorithmSelector,
      selectedChoice, AlgorithmChoice.ofShared, SeedChoice.toRound, hterminal]

/-- Structural, low-link, and accumulated-gain invariants packaged together. -/
structure QuantInvariant (H₀ : Family V) (I : Finset V) (p : ℝ) (s : ℕ)
    (st : State V) : Prop extends Invariant H₀ I s st where
  lowLinks : ContainerSelector.LowLinks st.family p s
  accepting_gain :
    (st.acceptCount : ℝ) * (1 / (8 * (s : ℝ))) ≤
      (ContainerWeight.belowRank st.family s).pWeight p

theorem initial_quantInvariant {H : Family V} {I : Finset V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (huniform : IsUniform H s) (hI : Independent H I) :
    QuantInvariant H I p s (initialState H) := by
  refine ⟨initial_invariant hs huniform hI, lowLinks_initial hs huniform, ?_⟩
  have hbelow : ContainerWeight.belowRank H s = ∅ := by
    ext E
    simp only [ContainerWeight.mem_belowRank, Finset.notMem_empty, iff_false]
    rintro ⟨hEH, hcard⟩
    have := huniform hEH
    omega
  simp [initialState, hbelow]

theorem algorithmStep_quantInvariant {H₀ : Family V} {I : Finset V}
    {p : ℝ} {s : ℕ} (hs : 0 < s) (hp : 0 < p)
    (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2)) {st : State V}
    (hinv : QuantInvariant H₀ I p s st) :
    QuantInvariant H₀ I p s (algorithmStep p s hs hp I st) := by
  by_cases hterm : algorithmTerminal p s st.family
  · rwa [algorithmStep_eq_self hterm]
  · let choice := selectedSharedChoice p s hs hp st.family hterm
    let b := branchFor I choice.seed
    rw [algorithmStep_eq_next hterm]
    change QuantInvariant H₀ I p s (st.next choice.layerIndex choice.seed b)
    have hbase : Invariant H₀ I s (st.next choice.layerIndex choice.seed b) := by
      exact ((AlgorithmChoice.ofShared choice).toSeedChoice.toRound st rfl I).next_invariant
        hinv.toInvariant
    have hlow : ContainerSelector.LowLinks
        (st.next choice.layerIndex choice.seed b).family p s := by
      cases hb : b with
      | reject =>
          have h := ContainerSelector.lowLinks_update_reject hs hp.le
            (p_le_one_of_le_container_bound hs hpmax)
            (p_le_threshold_of_le_container_bound hs hpmax)
            hinv.family_antichain hinv.lowLinks choice
          simpa [State.next, b, hb, replacement, update_eq_hypergraph_update,
            link, layer, Hypergraph.link, Hypergraph.layer] using h
      | accept =>
          have h := ContainerSelector.lowLinks_update_accept hs hp.le
            hinv.family_antichain hinv.lowLinks choice
          simpa [State.next, b, hb, replacement, update_eq_hypergraph_update,
            link, layer, Hypergraph.link, Hypergraph.layer] using h
    refine ⟨hbase, hlow, ?_⟩
    have hstep := below_step_gain hs hp.le hinv.family_antichain hinv.lowLinks choice b
    cases hb : b with
    | reject =>
        have hstep' : (ContainerWeight.belowRank st.family s).pWeight p ≤
            (ContainerWeight.belowRank
              (update st.family
                (replacement st.family choice.layerIndex choice.seed b)) s).pWeight p := by
          simpa [hb] using hstep
        rw [hb] at hstep'
        simpa [State.next, b, hb] using hinv.accepting_gain.trans hstep'
    | accept =>
        have hstep' : (ContainerWeight.belowRank st.family s).pWeight p +
              1 / (8 * (s : ℝ)) ≤
            (ContainerWeight.belowRank
              (update st.family
                (replacement st.family choice.layerIndex choice.seed b)) s).pWeight p := by
          simpa [hb] using hstep
        rw [hb] at hstep'
        simp only [State.next, b, hb, Nat.cast_add, Nat.cast_one]
        calc
          ((st.acceptCount : ℝ) + 1) * (1 / (8 * (s : ℝ))) =
              (st.acceptCount : ℝ) * (1 / (8 * (s : ℝ))) +
                1 / (8 * (s : ℝ)) := by ring
          _ ≤ (ContainerWeight.belowRank st.family s).pWeight p +
                1 / (8 * (s : ℝ)) :=
            add_le_add hinv.accepting_gain le_rfl
          _ ≤ _ := hstep'

/-- Quantitatively valid states, used as the terminating state space. -/
abbrev QuantState (H₀ : Family V) (I : Finset V) (p : ℝ) (s : ℕ) :=
  {st : State V // QuantInvariant H₀ I p s st}

noncomputable def quantNext {H₀ : Family V} {I : Finset V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (x : QuantState H₀ I p s) : QuantState H₀ I p s :=
  ⟨algorithmStep p s hs hp I x.1, algorithmStep_quantInvariant hs hp hpmax x.2⟩

def quantTerminal {H₀ : Family V} {I : Finset V} {p : ℝ} {s : ℕ}
    (x : QuantState H₀ I p s) : Prop :=
  algorithmTerminal p s x.1.family

noncomputable def quantTerminalDecision {H₀ : Family V} {I : Finset V}
    {p : ℝ} {s : ℕ} (x : QuantState H₀ I p s) :
    Decidable (quantTerminal x) := Classical.propDecidable _

theorem algorithmStep_rank_gt {H₀ : Family V} {I : Finset V}
    {p : ℝ} {s : ℕ} {hs : 0 < s} {hp : 0 < p} {st : State V}
    (hinv : QuantInvariant H₀ I p s st)
    (hterm : ¬ algorithmTerminal p s st.family) :
    upRank st.family < upRank (algorithmStep p s hs hp I st).family := by
  rw [algorithmStep_eq_next hterm]
  exact ((AlgorithmChoice.ofShared
    (selectedSharedChoice p s hs hp st.family hterm)).toSeedChoice.toRound st rfl I).next_rank_gt
      hinv.toInvariant

theorem quantRun_terminal {H₀ : Family V} {I : Finset V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (x : QuantState H₀ I p s) :
    quantTerminal
      (@ContainerFuel.run (QuantState H₀ I p s) quantTerminal quantTerminalDecision
        (quantNext hs hp hpmax) (2 ^ Fintype.card V + 1) x) := by
  letI : DecidablePred (@quantTerminal V _ _ H₀ I p s) := quantTerminalDecision
  apply ContainerFuel.terminal_run_of_strict_bounded_rank quantTerminal
    (quantNext hs hp hpmax) (fun y ↦ upRank y.1.family) (2 ^ Fintype.card V)
  · intro y
    exact upRank_le_two_pow y.1.family
  · intro y hy
    exact algorithmStep_rank_gt y.2 hy

noncomputable def finalQuantState (H : Family V) (I : Finset V) (p : ℝ) (s : ℕ)
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (hI : Independent H I) : QuantState H I p s :=
  @ContainerFuel.run (QuantState H I p s) quantTerminal quantTerminalDecision
    (quantNext hs hp hpmax) (2 ^ Fintype.card V + 1)
    ⟨initialState H, initial_quantInvariant hs huniform hI⟩

/-- The ordinary-state run of the canonical selector, with the uniform fuel
used throughout the finite container theorem. -/
noncomputable def algorithmRun (H : Family V) (I : Finset V) (p : ℝ) (s : ℕ)
    (hs : 0 < s) (hp : 0 < p) : State V :=
  let O := (algorithmSelector (V := V) p s hs hp).toOracle I
  @ContainerFuel.run (State V) O.terminal O.decision O.next
    (2 ^ Fintype.card V + 1) (initialState H)

/-- Forgetting the quantitative invariant from a quantitative execution gives
exactly the canonical selector execution. -/
theorem quantRun_val_eq_algorithmRunAux {H : Family V} {I : Finset V}
    {p : ℝ} {s : ℕ} (hs : 0 < s) (hp : 0 < p)
    (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2)) :
    ∀ (fuel : ℕ) (x : QuantState H I p s),
      (@ContainerFuel.run (QuantState H I p s) quantTerminal
          quantTerminalDecision (quantNext hs hp hpmax) fuel x).1 =
        @ContainerFuel.run (State V)
          ((algorithmSelector (V := V) p s hs hp).toOracle I).terminal
          ((algorithmSelector (V := V) p s hs hp).toOracle I).decision
          ((algorithmSelector (V := V) p s hs hp).toOracle I).next fuel x.1 := by
  letI : DecidablePred (@quantTerminal V _ _ H I p s) := quantTerminalDecision
  intro fuel
  induction fuel with
  | zero =>
      intro x
      rfl
  | succ fuel ih =>
      intro x
      let O := (algorithmSelector (V := V) p s hs hp).toOracle I
      letI : DecidablePred O.terminal := O.decision
      by_cases hterminal : quantTerminal x
      · rw [ContainerFuel.run_succ_of_terminal quantTerminal
          (quantNext hs hp hpmax) hterminal]
        rw [ContainerFuel.run_succ_of_terminal O.terminal O.next hterminal]
      · rw [ContainerFuel.run_succ_of_not_terminal quantTerminal
          (quantNext hs hp hpmax) hterminal]
        rw [ContainerFuel.run_succ_of_not_terminal O.terminal O.next hterminal]
        rw [ih]
        apply congrArg (fun st : State V =>
          @ContainerFuel.run (State V) O.terminal O.decision O.next fuel st)
        exact algorithmStep_eq_algorithmSelector_next p s hs hp I x.1

/-- The final quantitative state projects to `algorithmRun`. -/
theorem finalQuantState_val_eq_algorithmRun (H : Family V) (I : Finset V)
    (p : ℝ) (s : ℕ) (hs : 0 < s) (hp : 0 < p)
    (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (hI : Independent H I) :
    (finalQuantState H I p s hs hp hpmax huniform hI).1 =
      algorithmRun H I p s hs hp := by
  simpa [finalQuantState, algorithmRun] using
    quantRun_val_eq_algorithmRunAux (V := V) hs hp hpmax
      (2 ^ Fintype.card V + 1)
      (⟨initialState H, initial_quantInvariant hs huniform hI⟩ : QuantState H I p s)

theorem finalQuantState_terminal (H : Family V) (I : Finset V) (p : ℝ) (s : ℕ)
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (hI : Independent H I) :
    algorithmTerminal p s (finalQuantState H I p s hs hp hpmax huniform hI).1.family := by
  exact quantRun_terminal hs hp hpmax
    (⟨initialState H, initial_quantInvariant hs huniform hI⟩ : QuantState H I p s)

theorem QuantInvariant.fingerprint_card_bound {H₀ : Family V} {I : Finset V}
    {p : ℝ} {s : ℕ} {st : State V} (hinv : QuantInvariant H₀ I p s st)
    (hs : 0 < s) (hp : 0 ≤ p) (hstop : ContainerSelector.Stop p st.family) :
    (st.fingerprint.card : ℝ) ≤
      8 * (s : ℝ) ^ 2 * p * Fintype.card V := by
  have htotal : st.family.pWeight p ≤ p * Fintype.card V :=
    ContainerWeight.terminal_pWeight_le st.family hp hinv.family_nonempty hstop
  have hbelow : (ContainerWeight.belowRank st.family s).pWeight p ≤
      st.family.pWeight p := by
    exact Hypergraph.pWeight_mono (by
      intro E hE
      exact (ContainerWeight.mem_belowRank.mp hE).1) hp
  have hgain : (st.acceptCount : ℝ) * (1 / (8 * (s : ℝ))) ≤
      p * Fintype.card V := hinv.accepting_gain.trans (hbelow.trans htotal)
  have hden : (0 : ℝ) < 8 * s := by positivity
  have hgain' : (st.acceptCount : ℝ) / (8 * (s : ℝ)) ≤
      p * Fintype.card V := by
    simpa [div_eq_mul_inv] using hgain
  have hacc : (st.acceptCount : ℝ) ≤
      8 * (s : ℝ) * (p * Fintype.card V) := by
    have := (div_le_iff₀ hden).mp hgain'
    nlinarith
  have hfpNat := hinv.fingerprint_card_le
  have hfp : (st.fingerprint.card : ℝ) ≤
      (s : ℝ) * st.acceptCount := by exact_mod_cast hfpNat
  calc
    (st.fingerprint.card : ℝ) ≤ (s : ℝ) * st.acceptCount := hfp
    _ ≤ (s : ℝ) * (8 * (s : ℝ) * (p * Fintype.card V)) :=
      mul_le_mul_of_nonneg_left hacc (by positivity)
    _ = 8 * (s : ℝ) ^ 2 * p * Fintype.card V := by ring

/-- Rich deterministic output of the finite Campos--Samotij algorithm. -/
structure FiniteContainerOutput (H : Family V) (I : Finset V) (p : ℝ) (s : ℕ) where
  fingerprint : Finset V
  container : Finset V
  cover : Family V
  fingerprint_subset : fingerprint ⊆ I
  input_subset : I ⊆ container
  fingerprint_card : (fingerprint.card : ℝ) ≤
    8 * (s : ℝ) ^ 2 * p * Fintype.card V
  covers : cover.Covers (H.restrict container)
  edge_card : ∀ c ∈ cover, 2 ≤ c.card
  cover_supported : ∀ c ∈ cover, c ⊆ container
  weight_le : cover.pWeight p ≤ p * container.card

/-- The complete finite container theorem, with its exact `8s²pn` fingerprint
bound and a cover of the induced hypergraph on the returned container. -/
noncomputable def finiteContainer (H : Family V) (s : ℕ) (p : ℝ)
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (I : Finset V) (hI : Independent H I) :
    FiniteContainerOutput H I p s := by
  let out := finalQuantState H I p s hs hp hpmax huniform hI
  have hterm := finalQuantState_terminal H I p s hs hp hpmax huniform hI
  have hstop : ContainerSelector.Stop p out.1.family :=
    (algorithmTerminal_iff_stop_of_invariant out.2.toInvariant p).mp hterm
  refine {
    fingerprint := out.1.fingerprint
    container := containerVertices out.1.family
    cover := aboveOne out.1.family
    fingerprint_subset := out.2.fingerprint_subset
    input_subset := out.2.input_subset_container
    fingerprint_card := out.2.fingerprint_card_bound hs hp.le hstop
    covers := ?_
    edge_card := ?_
    cover_supported := ?_
    weight_le := ?_ }
  · simpa [Hypergraph.Covers, Covers, Hypergraph.restrict, aboveOne,
      Hypergraph.aboveOne, containerVertices, Hypergraph.containerVertices] using
      out.2.output_cover
  · intro c hc
    exact (mem_aboveOne.mp hc).2
  · intro c hc
    exact out.2.cover_edges_in_container hc
  · simpa [ContainerSelector.Stop, aboveOne, Hypergraph.aboveOne,
      containerVertices, Hypergraph.containerVertices] using hstop

/-- The fingerprint exposed by `finiteContainer` is the fingerprint of the
canonical selector run. -/
theorem finiteContainer_fingerprint_eq_algorithmRun (H : Family V) (s : ℕ)
    (p : ℝ) (hs : 0 < s) (hp : 0 < p)
    (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2)) (huniform : IsUniform H s)
    (I : Finset V) (hI : Independent H I) :
    (finiteContainer H s p hs hp hpmax huniform I hI).fingerprint =
      (algorithmRun H I p s hs hp).fingerprint := by
  change (finalQuantState H I p s hs hp hpmax huniform hI).1.fingerprint = _
  rw [finalQuantState_val_eq_algorithmRun]

/-- The vertex set exposed by `finiteContainer` is the vertex container of
the same canonical selector run. -/
theorem finiteContainer_container_eq_algorithmRun (H : Family V) (s : ℕ)
    (p : ℝ) (hs : 0 < s) (hp : 0 < p)
    (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2)) (huniform : IsUniform H s)
    (I : Finset V) (hI : Independent H I) :
    (finiteContainer H s p hs hp hpmax huniform I hI).container =
      containerVertices (algorithmRun H I p s hs hp).family := by
  change containerVertices
      (finalQuantState H I p s hs hp hpmax huniform hI).1.family = _
  rw [finalQuantState_val_eq_algorithmRun]

/-- Adapter consumed by the Janson conversion layer. -/
noncomputable def finiteCoverOutput (H : Family V) (s : ℕ) (p : ℝ)
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (I : Finset V) (hI : Independent H I) :
    Hypergraph.FiniteCoverOutput H I p := by
  let out := finiteContainer H s p hs hp hpmax huniform I hI
  exact {
    container := out.container
    cover := out.cover
    input_subset := out.input_subset
    covers := out.covers
    edge_card := out.edge_card
    weight_le := out.weight_le }

end ContainerA
end Erdos565
