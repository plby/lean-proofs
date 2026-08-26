/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Partite
import ErdosProblems.Erdos547b.EC2
import ErdosProblems.Erdos547b.EC1
import ErdosProblems.Erdos547b.Fact72
import ErdosProblems.Erdos547b.Proposition73Discrete
import ErdosProblems.Erdos547b.Lemma77Full
import ErdosProblems.Erdos547b.Lemma78Full
import ErdosProblems.Erdos547b.Lemma710Full
import ErdosProblems.Erdos547b.TreePadding
import ErdosProblems.Erdos547b.LeafImbalance
import ErdosProblems.Erdos547b.Lemma710
import ErdosProblems.Erdos547b.Lemma78
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic
import Lean.Elab.Tactic.Omega

namespace Erdos547b

open Finset SimpleGraph

/-- Removing degree-one vertices preserves connectedness when a vertex
remains.  This is the simultaneous deletion fact used by the near-ideal
terminal-path construction. -/
theorem connected_induce_compl_of_leaves {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (R : Set W)
    (hG : G.Connected) (hR : ∀ v ∈ R, IsLeaf G v) (hne : Rᶜ.Nonempty) :
    (G.induce Rᶜ).Connected := by
  rw [connected_iff]
  refine ⟨?_, hne.to_subtype⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨p, hp⟩ := hG.exists_isPath u v
  refine ⟨p.induce Rᶜ ?_⟩
  intro z hz
  simp only [Set.mem_compl_iff]
  intro hzR
  obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hz
  have hi0 : i ≠ 0 := by
    intro hi0
    subst i
    have huget : p.getVert 0 ∉ R := by simpa using hu
    apply huget
    rw [hiz]
    exact hzR
  have hilt : i < p.length := by
    by_contra hnot
    have hieq : i = p.length := by omega
    subst i
    have hvget : p.getVert p.length ∉ R := by simpa using hv
    apply hvget
    rw [hiz]
    exact hzR
  have hleftSub : p.toSubgraph.Adj (p.getVert i) (p.getVert (i - 1)) := by
    rw [← Subgraph.mem_neighborSet, hp.neighborSet_toSubgraph_internal hi0 hilt]
    simp
  have hrightSub : p.toSubgraph.Adj (p.getVert i) (p.getVert (i + 1)) := by
    rw [← Subgraph.mem_neighborSet, hp.neighborSet_toSubgraph_internal hi0 hilt]
    simp
  have hleft : G.Adj z (p.getVert (i - 1)) := by
    rw [← hiz]
    exact hleftSub.adj_sub
  have hright : G.Adj z (p.getVert (i + 1)) := by
    rw [← hiz]
    exact hrightSub.adj_sub
  obtain ⟨w, hzw, hw⟩ := degree_eq_one_iff_existsUnique_adj.mp (hR z hzR)
  have hsame : p.getVert (i - 1) = p.getVert (i + 1) :=
    (hw _ hleft).trans (hw _ hright).symm
  have hind := hp.getVert_injOn
    (show i - 1 ∈ Set.Iic p.length by simp; omega)
    (show i + 1 ∈ Set.Iic p.length by simp; omega) hsame
  omega

end Erdos547b

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547EC2

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Endpoints used by an indexed family of two-edge paths. -/
def twoPathEnds {k : ℕ} (left right : Fin k → V) : Finset V :=
  Finset.univ.image left ∪ Finset.univ.image right

/-- Midpoints belonging to a selected subfamily of an indexed family of two-edge paths. -/
def selectedTwoPathMiddles {k : ℕ} (middle : Fin k → V) (J : Finset (Fin k)) : Finset V :=
  J.image middle

/-- All midpoints in an indexed family of two-edge paths. -/
def allTwoPathMiddles {k : ℕ} (middle : Fin k → V) : Finset V :=
  Finset.univ.image middle

lemma card_twoPathEnds {k : ℕ} {left right : Fin k → V}
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hdisj : Disjoint (Finset.univ.image left) (Finset.univ.image right)) :
    (twoPathEnds left right).card = 2 * k := by
  rw [twoPathEnds, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hleft, Finset.card_image_of_injective _ hright]
  simp [two_mul]

lemma card_selectedTwoPathMiddles {k : ℕ} {middle : Fin k → V}
    (J : Finset (Fin k)) (hmiddle : Function.Injective middle) :
    (selectedTwoPathMiddles middle J).card = J.card := by
  exact Finset.card_image_of_injective J hmiddle

/--
The maximal-disjoint-two-path counting step on page 49 of Zhao's proof of
Lemma 7.4.

The family is indexed by `Fin k`: its `i`th member is
`left i -- middle i -- right i`.  The injectivity and disjointness hypotheses
say that its vertices are pairwise disjoint (membership of every midpoint
outside `A` already separates midpoints from endpoints).  `hmax` is precisely
the consequence of inclusion-maximality used in the paper: two unused
endpoints in `A` cannot have a common unused neighbor outside `A ∪ B₁`.

The set `J` selects `min k (n - |A| - |B₁|)` paths, exactly as in Zhao, and
only their midpoints are added.  The numerical hypothesis `14q < n` is the
integer form of the paper's estimate `7q < n/2`.
-/
theorem card_union_selectedTwoPathMiddles_ge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B₁ : Finset V} {n q k : ℕ}
    {left middle right : Fin k → V} (J : Finset (Fin k))
    (hVcard : Fintype.card V = 2 * n)
    (hAB₁ : Disjoint A B₁)
    (hAcard : n ≤ 2 * A.card)
    (hlarge : ∀ v ∈ A, n ≤ degreeInto G v Finset.univ)
    (hAB₁large : n ≤ A.card + B₁.card + q)
    (hq : 14 * q < n)
    (hleftA : ∀ i, left i ∈ A)
    (hrightA : ∀ i, right i ∈ A)
    (hmiddleOut : ∀ i, middle i ∉ A ∪ B₁)
    (hleftInj : Function.Injective left)
    (hmiddleInj : Function.Injective middle)
    (hrightInj : Function.Injective right)
    (hendsDisj : Disjoint (Finset.univ.image left) (Finset.univ.image right))
    (hpathLeft : ∀ i, G.Adj (left i) (middle i))
    (hpathRight : ∀ i, G.Adj (middle i) (right i))
    (hJcard : J.card = min k (n - A.card - B₁.card))
    (hmax : ∀ x ∈ A \ twoPathEnds left right,
      ∀ z ∈ A \ twoPathEnds left right, x ≠ z →
      ∀ y ∉ A ∪ B₁ ∪ allTwoPathMiddles middle,
        ¬(G.Adj x y ∧ G.Adj y z)) :
    n - 1 ≤ (A ∪ B₁ ∪ selectedTwoPathMiddles middle J).card := by
  classical
  let E : Finset V := twoPathEnds left right
  let M : Finset V := allTwoPathMiddles middle
  let B₂ : Finset V := selectedTwoPathMiddles middle J
  let U : Finset V := A ∪ B₁ ∪ B₂
  let C : Finset V := Finset.univ \ U
  let A' : Finset V := A \ E

  have hB₂card : B₂.card = J.card := by
    exact card_selectedTwoPathMiddles J hmiddleInj
  have hAB₁B₂ : Disjoint (A ∪ B₁) B₂ := by
    rw [Finset.disjoint_left]
    intro v hvAB hvB₂
    rcases Finset.mem_image.mp hvB₂ with ⟨i, hiJ, rfl⟩
    exact hmiddleOut i hvAB
  have hUcard : U.card = A.card + B₁.card + J.card := by
    simp only [U]
    rw [Finset.card_union_of_disjoint hAB₁B₂,
      Finset.card_union_of_disjoint hAB₁, hB₂card]
  have hAB₁subU : A ∪ B₁ ⊆ U := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvA | hvB
    · simp [U, hvA]
    · simp [U, hvB]
  have hAsubU : A ⊆ U := by
    intro v hv
    simp [U, hv]

  by_contra hgoal
  change ¬n - 1 ≤ U.card at hgoal
  have hUsmall : U.card ≤ n - 2 := by
    omega
  have hsum_le : A.card + B₁.card ≤ n - 2 := by omega
  have hJltcap : J.card < n - A.card - B₁.card := by omega
  have hkltcap : k < n - A.card - B₁.card := by
    have : min k (n - A.card - B₁.card) < n - A.card - B₁.card := by
      rwa [← hJcard]
    rw [min_lt_iff] at this
    exact this.resolve_right (lt_irrefl _)
  have hJcardk : J.card = k := by
    rw [hJcard, min_eq_left hkltcap.le]
  have hJuniv : J = (Finset.univ : Finset (Fin k)) := by
    exact Finset.eq_univ_of_card J (by simpa using hJcardk)
  have hB₂M : B₂ = M := by
    simp [B₂, M, selectedTwoPathMiddles, allTwoPathMiddles, hJuniv]

  have hcap_le_q : n - A.card - B₁.card ≤ q := by omega
  have hk_le_q : k ≤ q := hkltcap.le.trans hcap_le_q
  have hEsubA : E ⊆ A := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_image.mp hv with ⟨i, -, rfl⟩
      exact hleftA i
    · rcases Finset.mem_image.mp hv with ⟨i, -, rfl⟩
      exact hrightA i
  have hEcard : E.card = 2 * k := by
    exact card_twoPathEnds hleftInj hrightInj hendsDisj
  have hA'card : A'.card = A.card - 2 * k := by
    simp only [A']
    rw [Finset.card_sdiff_of_subset hEsubA, hEcard]
  have htwokA : 2 * k ≤ A.card := by omega
  have hA'large : n + q < 3 * A'.card := by omega

  have hCcard : C.card = 2 * n - U.card := by
    simp only [C]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U),
      Finset.card_univ, hVcard]
  have hClargeBound : C.card ≤ n + q := by omega
  have hdisjUC : Disjoint U C := by
    simpa only [C] using (Finset.disjoint_sdiff : Disjoint U (Finset.univ \ U))
  have hcoverUC : U ∪ C = Finset.univ := by
    exact Finset.union_sdiff_of_subset (Finset.subset_univ U)

  have hdegC : ∀ v ∈ A', 3 ≤ degreeInto G v C := by
    intro v hvA'
    have hvA : v ∈ A := (Finset.mem_sdiff.mp hvA').1
    have hvU : v ∈ U := hAsubU hvA
    have hdegU : degreeInto G v U ≤ U.card - 1 := by
      unfold degreeInto
      calc
        (U.filter fun w ↦ G.Adj v w).card ≤ (U.erase v).card := by
          apply Finset.card_le_card
          intro w hw
          rw [Finset.mem_erase]
          exact ⟨by
            intro hwv
            subst w
            exact G.loopless.irrefl v (Finset.mem_filter.mp hw).2,
            (Finset.mem_filter.mp hw).1⟩
        _ = U.card - 1 := by rw [Finset.card_erase_of_mem hvU]
    have hsplit := degreeInto_partition G v hdisjUC hcoverUC
    have hvlarge := hlarge v hvA
    omega

  have hedgeUpper : (G.interedges A' C).card ≤ C.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      exact (Rel.mem_interedges_iff.mp hp).2.1
    · intro p hp r hr hpr
      apply Prod.ext
      · by_contra hfirst
        have hpdata := Rel.mem_interedges_iff.mp hp
        have hrdata := Rel.mem_interedges_iff.mp hr
        have hpC : p.2 ∈ C := hpdata.2.1
        have hpnotU : p.2 ∉ U := (Finset.mem_sdiff.mp hpC).2
        have hpnotAll : p.2 ∉ A ∪ B₁ ∪ M := by
          rw [← hB₂M]
          intro hpbad
          exact hpnotU hpbad
        have hforbid := hmax p.1 (by simpa [A', E] using hpdata.1)
          r.1 (by simpa [A', E] using hrdata.1) hfirst p.2
          (by simpa [M] using hpnotAll)
        apply hforbid
        exact ⟨hpdata.2.2, by simpa [hpr] using hrdata.2.2.symm⟩
      · exact hpr

  have hedgeLower : A'.card * 3 ≤ (G.interedges A' C).card := by
    exact card_mul_le_card_interedges_of_subset_of_degreeInto G
      (Finset.Subset.rfl) hdegC
  omega

/-- The page-49 statement with Zhao's literal floor/ceiling cardinalities.
Here `(n + 1) / 2` is `⌈n/2⌉` and `n / 2` is `⌊n/2⌋`. -/
theorem zhao_lemma74_maximal_two_path_count
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B₁ : Finset V} {n q k : ℕ}
    {left middle right : Fin k → V} (J : Finset (Fin k))
    (hVcard : Fintype.card V = 2 * n)
    (hAB₁ : Disjoint A B₁)
    (hAcard : A.card = (n + 1) / 2)
    (hlarge : ∀ v ∈ A, n ≤ degreeInto G v Finset.univ)
    (hB₁card : n / 2 - q ≤ B₁.card)
    (hq : 7 * q < n / 2)
    (hleftA : ∀ i, left i ∈ A)
    (hrightA : ∀ i, right i ∈ A)
    (hmiddleOut : ∀ i, middle i ∉ A ∪ B₁)
    (hleftInj : Function.Injective left)
    (hmiddleInj : Function.Injective middle)
    (hrightInj : Function.Injective right)
    (hendsDisj : Disjoint (Finset.univ.image left) (Finset.univ.image right))
    (hpathLeft : ∀ i, G.Adj (left i) (middle i))
    (hpathRight : ∀ i, G.Adj (middle i) (right i))
    (hJcard : J.card = min k (n - A.card - B₁.card))
    (hmax : ∀ x ∈ A \ twoPathEnds left right,
      ∀ z ∈ A \ twoPathEnds left right, x ≠ z →
      ∀ y ∉ A ∪ B₁ ∪ allTwoPathMiddles middle,
        ¬(G.Adj x y ∧ G.Adj y z)) :
    n - 1 ≤ (A ∪ B₁ ∪ selectedTwoPathMiddles middle J).card := by
  have hhalves : (n + 1) / 2 + n / 2 = n := by omega
  have hqfloor : q ≤ n / 2 := by omega
  apply card_union_selectedTwoPathMiddles_ge (n := n) (q := q) (k := k)
    (A := A) (B₁ := B₁) (left := left) (middle := middle) (right := right)
    G J hVcard hAB₁
  · rw [hAcard]
    omega
  · exact hlarge
  · rw [hAcard]
    omega
  · omega
  · exact hleftA
  · exact hrightA
  · exact hmiddleOut
  · exact hleftInj
  · exact hmiddleInj
  · exact hrightInj
  · exact hendsDisj
  · exact hpathLeft
  · exact hpathRight
  · exact hJcard
  · exact hmax


end Erdos547EC2

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547EC2

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A labelled path with two edges. -/
structure TwoPath where
  left : V
  middle : V
  right : V
deriving DecidableEq

private def twoPathEquiv : TwoPath (V := V) ≃ V × V × V where
  toFun p := (p.left, p.middle, p.right)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨x, y, z⟩; rfl

instance : Fintype (TwoPath (V := V)) :=
  Fintype.ofEquiv (V × V × V) twoPathEquiv.symm

/-- The three vertices of a labelled two-edge path. -/
def TwoPath.vertices (p : TwoPath (V := V)) : Set V :=
  {p.left, p.middle, p.right}

/-- A path is admissible when its endpoints are distinct vertices of `A`, its
midpoint is outside `A ∪ B₁`, and its two required graph edges are present. -/
def TwoPath.IsAdmissible (G : SimpleGraph V) (A B₁ : Finset V)
    (p : TwoPath (V := V)) : Prop :=
  p.left ∈ A ∧ p.right ∈ A ∧ p.left ≠ p.right ∧
    p.middle ∉ A ∪ B₁ ∧ G.Adj p.left p.middle ∧ G.Adj p.middle p.right

/-- A finite family of admissible paths whose three-vertex supports are
pairwise disjoint. -/
def IsDisjointTwoPathFamily (G : SimpleGraph V) (A B₁ : Finset V)
    (F : Finset (TwoPath (V := V))) : Prop :=
  (∀ p ∈ F, p.IsAdmissible G A B₁) ∧
    ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint p.vertices q.vertices

lemma isDisjointTwoPathFamily_empty (G : SimpleGraph V) (A B₁ : Finset V) :
    IsDisjointTwoPathFamily G A B₁ ∅ := by
  simp [IsDisjointTwoPathFamily]

/-- Among the finitely many disjoint admissible two-path families, one has
maximum cardinality. -/
lemma exists_max_card_disjointTwoPathFamily
    (G : SimpleGraph V) (A B₁ : Finset V) :
    ∃ F : Finset (TwoPath (V := V)),
      IsDisjointTwoPathFamily G A B₁ F ∧
      ∀ F' : Finset (TwoPath (V := V)),
        IsDisjointTwoPathFamily G A B₁ F' → F'.card ≤ F.card := by
  classical
  let families : Finset (Finset (TwoPath (V := V))) :=
    Finset.univ.filter (IsDisjointTwoPathFamily G A B₁)
  have hne : families.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [families, isDisjointTwoPathFamily_empty]
  obtain ⟨F, hFmem, hFmax⟩ := Finset.exists_max_image families Finset.card hne
  refine ⟨F, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hFmem).2
  · intro F' hF'
    apply hFmax F'
    simp [families, hF']

private lemma newPath_disjoint
    (G : SimpleGraph V) (A B₁ : Finset V)
    {F : Finset (TwoPath (V := V))}
    (hF : IsDisjointTwoPathFamily G A B₁ F)
    {x y z : V}
    (hxA : x ∈ A) (hzA : z ∈ A)
    (hxUnused : ∀ p ∈ F, x ≠ p.left ∧ x ≠ p.right)
    (hzUnused : ∀ p ∈ F, z ≠ p.left ∧ z ≠ p.right)
    (hyOut : y ∉ A ∪ B₁)
    (hyUnused : ∀ p ∈ F, y ≠ p.middle) :
    ∀ p ∈ F, Disjoint ({x, y, z} : Set V) p.vertices := by
  intro p hp
  rw [Set.disjoint_left]
  intro v hvnew hvp
  have hpAdm := hF.1 p hp
  rcases hpAdm with ⟨hplA, hprA, -, hpmOut, -, -⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvnew hvp
  rcases hvnew with hvx | hvy | hvz
  · rw [hvx] at hvp
    rcases hvp with h | h | h
    · exact (hxUnused p hp).1 h
    · apply hpmOut
      exact Finset.mem_union_left _ (h ▸ hxA)
    · exact (hxUnused p hp).2 h
  · rw [hvy] at hvp
    rcases hvp with h | h | h
    · apply hyOut
      exact Finset.mem_union_left _ (h.symm ▸ hplA)
    · exact hyUnused p hp h
    · apply hyOut
      exact Finset.mem_union_left _ (h.symm ▸ hprA)
  · rw [hvz] at hvp
    rcases hvp with h | h | h
    · exact (hzUnused p hp).1 h
    · apply hpmOut
      exact Finset.mem_union_left _ (h ▸ hzA)
    · exact (hzUnused p hp).2 h

private lemma insert_newPath_family
    (G : SimpleGraph V) (A B₁ : Finset V)
    {F : Finset (TwoPath (V := V))}
    (hF : IsDisjointTwoPathFamily G A B₁ F)
    {x y z : V}
    (hxA : x ∈ A) (hzA : z ∈ A) (hxz : x ≠ z)
    (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hxUnused : ∀ p ∈ F, x ≠ p.left ∧ x ≠ p.right)
    (hzUnused : ∀ p ∈ F, z ≠ p.left ∧ z ≠ p.right)
    (hyOut : y ∉ A ∪ B₁)
    (hyUnused : ∀ p ∈ F, y ≠ p.middle) :
    IsDisjointTwoPathFamily G A B₁
      (insert ⟨x, y, z⟩ F) := by
  let t : TwoPath (V := V) := ⟨x, y, z⟩
  have htAdm : t.IsAdmissible G A B₁ := by
    exact ⟨hxA, hzA, hxz, hyOut, hxy, hyz⟩
  have htDisj : ∀ p ∈ F, Disjoint t.vertices p.vertices := by
    simpa [t, TwoPath.vertices] using
      newPath_disjoint G A B₁ hF hxA hzA hxUnused hzUnused hyOut hyUnused
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact htAdm
    · exact hF.1 p hp
  · intro p hp q hq hpq
    rcases Finset.mem_insert.mp hp with rfl | hpF
    · rcases Finset.mem_insert.mp hq with rfl | hqF
      · exact (hpq rfl).elim
      · exact htDisj q hqF
    · rcases Finset.mem_insert.mp hq with rfl | hqF
      · exact (htDisj p hpF).symm
      · exact hF.2 p hpF q hqF hpq

/-- An indexed, inclusion-maximal family of vertex-disjoint
`A`--outside-`(A ∪ B₁)`--`A` two-paths exists.  The final conjunct is exactly
the maximality premise consumed by `zhao_lemma74_maximal_two_path_count`.
The selected index set `J` has Zhao's required cardinality. -/
theorem exists_indexed_maximal_two_path_family
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B₁ : Finset V) (n : ℕ) :
    ∃ (k : ℕ) (left middle right : Fin k → V) (J : Finset (Fin k)),
      (∀ i, left i ∈ A) ∧
      (∀ i, right i ∈ A) ∧
      (∀ i, middle i ∉ A ∪ B₁) ∧
      Function.Injective left ∧
      Function.Injective middle ∧
      Function.Injective right ∧
      Disjoint (Finset.univ.image left) (Finset.univ.image right) ∧
      (∀ i, G.Adj (left i) (middle i)) ∧
      (∀ i, G.Adj (middle i) (right i)) ∧
      J.card = min k (n - A.card - B₁.card) ∧
      (∀ x ∈ A \ twoPathEnds left right,
        ∀ z ∈ A \ twoPathEnds left right, x ≠ z →
        ∀ y ∉ A ∪ B₁ ∪ allTwoPathMiddles middle,
          ¬(G.Adj x y ∧ G.Adj y z)) := by
  classical
  obtain ⟨F, hF, hFmax⟩ := exists_max_card_disjointTwoPathFamily G A B₁
  let e : Fin F.card ≃ {p // p ∈ F} := F.equivFin.symm
  let left : Fin F.card → V := fun i ↦ (e i).1.left
  let middle : Fin F.card → V := fun i ↦ (e i).1.middle
  let right : Fin F.card → V := fun i ↦ (e i).1.right
  obtain ⟨J, -, hJcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin F.card)))
    (n := min F.card (n - A.card - B₁.card))
    (by simpa using min_le_left F.card (n - A.card - B₁.card))
  refine ⟨F.card, left, middle, right, J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hJcard, ?_⟩
  · intro i
    exact (hF.1 (e i).1 (e i).2).1
  · intro i
    exact (hF.1 (e i).1 (e i).2).2.1
  · intro i
    exact (hF.1 (e i).1 (e i).2).2.2.2.1
  · intro i j hij
    by_contra hne
    have hpne : (e i).1 ≠ (e j).1 := by
      intro hp
      apply hne
      exact e.injective (Subtype.ext hp)
    have hd := hF.2 (e i).1 (e i).2 (e j).1 (e j).2 hpne
    have hiMem : left i ∈ (e i).1.vertices := by
      simp [TwoPath.vertices, left]
    have hjMem : left i ∈ (e j).1.vertices := by
      rw [hij]
      simp [TwoPath.vertices, left]
    exact (Set.disjoint_left.mp hd) hiMem hjMem
  · intro i j hij
    by_contra hne
    have hpne : (e i).1 ≠ (e j).1 := by
      intro hp
      apply hne
      exact e.injective (Subtype.ext hp)
    have hd := hF.2 (e i).1 (e i).2 (e j).1 (e j).2 hpne
    have hiMem : middle i ∈ (e i).1.vertices := by
      simp [TwoPath.vertices, middle]
    have hjMem : middle i ∈ (e j).1.vertices := by
      rw [hij]
      simp [TwoPath.vertices, middle]
    exact (Set.disjoint_left.mp hd) hiMem hjMem
  · intro i j hij
    by_contra hne
    have hpne : (e i).1 ≠ (e j).1 := by
      intro hp
      apply hne
      exact e.injective (Subtype.ext hp)
    have hd := hF.2 (e i).1 (e i).2 (e j).1 (e j).2 hpne
    have hiMem : right i ∈ (e i).1.vertices := by
      simp [TwoPath.vertices, right]
    have hjMem : right i ∈ (e j).1.vertices := by
      rw [hij]
      simp [TwoPath.vertices, right]
    exact (Set.disjoint_left.mp hd) hiMem hjMem
  · rw [Finset.disjoint_left]
    intro v hvleft hvright
    rcases Finset.mem_image.mp hvleft with ⟨i, -, rfl⟩
    rcases Finset.mem_image.mp hvright with ⟨j, -, hij⟩
    by_cases hidx : i = j
    · subst j
      exact (hF.1 (e i).1 (e i).2).2.2.1 hij.symm
    · have hpne : (e i).1 ≠ (e j).1 := by
        intro hp
        exact hidx (e.injective (Subtype.ext hp))
      have hd := hF.2 (e i).1 (e i).2 (e j).1 (e j).2 hpne
      have hiMem : left i ∈ (e i).1.vertices := by
        simp [TwoPath.vertices, left]
      have hjMem : left i ∈ (e j).1.vertices := by
        rw [← hij]
        simp [TwoPath.vertices, right]
      exact (Set.disjoint_left.mp hd) hiMem hjMem
  · intro i
    exact (hF.1 (e i).1 (e i).2).2.2.2.2.1
  · intro i
    exact (hF.1 (e i).1 (e i).2).2.2.2.2.2
  · intro x hx z hz hxz y hy hpaths
    have hnotmem : (⟨x, y, z⟩ : TwoPath (V := V)) ∉ F := by
      intro ht
      have hxused : x ∈ twoPathEnds left right := by
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        let i : Fin F.card := e.symm ⟨⟨x, y, z⟩, ht⟩
        refine ⟨i, Finset.mem_univ _, ?_⟩
        change (e i).1.left = x
        simp [i]
      exact (Finset.mem_sdiff.mp hx).2 hxused
    have hvalidInsert :
        IsDisjointTwoPathFamily G A B₁
          (insert (⟨x, y, z⟩ : TwoPath (V := V)) F) := by
      apply insert_newPath_family G A B₁ hF
      · exact (Finset.mem_sdiff.mp hx).1
      · exact (Finset.mem_sdiff.mp hz).1
      · exact hxz
      · exact hpaths.1
      · exact hpaths.2
      · intro p hp
        have hi : ∃ i : Fin F.card, (e i).1 = p := by
          refine ⟨e.symm ⟨p, hp⟩, ?_⟩
          simp
        obtain ⟨i, hi⟩ := hi
        have hxunused := (Finset.mem_sdiff.mp hx).2
        constructor
        · intro hxp
          apply hxunused
          apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          refine ⟨i, Finset.mem_univ _, ?_⟩
          simpa [left, hi] using hxp.symm
        · intro hxp
          apply hxunused
          apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨i, Finset.mem_univ _, ?_⟩
          simpa [right, hi] using hxp.symm
      · intro p hp
        have hi : ∃ i : Fin F.card, (e i).1 = p := by
          refine ⟨e.symm ⟨p, hp⟩, ?_⟩
          simp
        obtain ⟨i, hi⟩ := hi
        have hzunused := (Finset.mem_sdiff.mp hz).2
        constructor
        · intro hzp
          apply hzunused
          apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          refine ⟨i, Finset.mem_univ _, ?_⟩
          simpa [left, hi] using hzp.symm
        · intro hzp
          apply hzunused
          apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨i, Finset.mem_univ _, ?_⟩
          simpa [right, hi] using hzp.symm
      · exact fun hyAB ↦ hy (Finset.mem_union_left _ hyAB)
      · intro p hp hyp
        have hi : ∃ i : Fin F.card, (e i).1 = p := by
          refine ⟨e.symm ⟨p, hp⟩, ?_⟩
          simp
        obtain ⟨i, hi⟩ := hi
        apply hy
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        simpa [middle, hi] using hyp.symm
    have hle := hFmax (insert (⟨x, y, z⟩ : TwoPath (V := V)) F) hvalidInsert
    rw [Finset.card_insert_of_notMem hnotmem] at hle
    omega


end Erdos547EC2
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547EC2

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The bipartite restriction of `G` to the indicated two finite sides. -/
def lowLeafHostGraph (G : SimpleGraph V) (A B : Finset V) : SimpleGraph V :=
  G.between (A : Set V) (B : Set V)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    DecidableRel (lowLeafHostGraph G A B).Adj :=
  fun _ _ ↦ Classical.propDecidable _

/-- The complete host package passed from Zhao's Lemma 7.4 to Lemma 7.10. -/
structure LowLeafHostPackage
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B₁ : Finset V) (n l : ℕ) where
  k : ℕ
  left : Fin k → V
  middle : Fin k → V
  right : Fin k → V
  J : Finset (Fin k)
  B₂ : Finset V
  B : Finset V
  B₂_eq : B₂ = selectedTwoPathMiddles middle J
  B_eq : B = B₁ ∪ B₂
  left_mem : ∀ i, left i ∈ A
  right_mem : ∀ i, right i ∈ A
  middle_out : ∀ i, middle i ∉ A ∪ B₁
  left_injective : Function.Injective left
  middle_injective : Function.Injective middle
  right_injective : Function.Injective right
  ends_disjoint : Disjoint (Finset.univ.image left) (Finset.univ.image right)
  adj_left : ∀ i, G.Adj (left i) (middle i)
  adj_right : ∀ i, G.Adj (middle i) (right i)
  J_card : J.card = min k (n - A.card - B₁.card)
  maximal : ∀ x ∈ A \ twoPathEnds left right,
    ∀ z ∈ A \ twoPathEnds left right, x ≠ z →
    ∀ y ∉ A ∪ B₁ ∪ allTwoPathMiddles middle,
      ¬(G.Adj x y ∧ G.Adj y z)
  B₁_B₂_disjoint : Disjoint B₁ B₂
  B_split : B₁ ∪ B₂ = B
  card_B_lower : n / 2 - 1 ≤ B.card
  card_B_upper : B.card ≤ n / 2
  card_B₂_le : B₂.card ≤ l
  restricted_le : lowLeafHostGraph G A B ≤ G
  restricted_bipartite :
    (lowLeafHostGraph G A B).IsBipartiteWith (A : Set V) (B : Set V)
  paths : Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem
    (lowLeafHostGraph G A B) A B₂
  left_inter_eq : ∀ a ∈ A,
    ((lowLeafHostGraph G A B).neighborFinset a ∩ B₁) =
      (G.neighborFinset a ∩ B₁)
  right_inter_eq : ∀ b ∈ B₁,
    ((lowLeafHostGraph G A B).neighborFinset b ∩ A) =
      (G.neighborFinset b ∩ A)
  left_degree_bound : ∀ a ∈ A,
    B₁.card - l ≤ ((lowLeafHostGraph G A B).neighborFinset a ∩ B₁).card
  right_degree_bound : ∀ b ∈ B₁,
    A.card - l ≤ ((lowLeafHostGraph G A B).neighborFinset b ∩ A).card

private def selectedIndex {k : ℕ} (middle : Fin k → V) (J : Finset (Fin k))
    (y : selectedTwoPathMiddles middle J) : Fin k :=
  Classical.choose (Finset.mem_image.mp y.property)

private theorem selectedIndex_mem {k : ℕ} (middle : Fin k → V) (J : Finset (Fin k))
    (y : selectedTwoPathMiddles middle J) : selectedIndex middle J y ∈ J :=
  (Classical.choose_spec (Finset.mem_image.mp y.property)).1

private theorem middle_selectedIndex {k : ℕ} (middle : Fin k → V)
    (J : Finset (Fin k)) (y : selectedTwoPathMiddles middle J) :
    middle (selectedIndex middle J y) = y :=
  (Classical.choose_spec (Finset.mem_image.mp y.property)).2

private theorem neighborFinset_lowLeafHostGraph_inter_right
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B C : Finset V} (hCB : C ⊆ B) {a : V} (ha : a ∈ A) :
    (lowLeafHostGraph G A B).neighborFinset a ∩ C = G.neighborFinset a ∩ C := by
  ext x
  simp only [Finset.mem_inter, G.mem_neighborFinset,
    (lowLeafHostGraph G A B).mem_neighborFinset]
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, Or.inl ⟨ha, hCB h.2⟩⟩, h.2⟩

private theorem neighborFinset_lowLeafHostGraph_inter_left
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B C : Finset V} (hCA : C ⊆ A) {b : V} (hb : b ∈ B) :
    (lowLeafHostGraph G A B).neighborFinset b ∩ C = G.neighborFinset b ∩ C := by
  ext x
  simp only [Finset.mem_inter, G.mem_neighborFinset,
    (lowLeafHostGraph G A B).mem_neighborFinset]
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, Or.inr ⟨hb, hCA h.2⟩⟩, h.2⟩

/-- The EC3 host construction, packaged end-to-end for the low-leaf branch.
The hypotheses are exactly the normalized/pruned estimates produced before
the invocation of Lemma 7.10. -/
theorem exists_lowLeafHostPackage
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B₁ : Finset V) (n s q l : ℕ)
    (hVcard : Fintype.card V = 2 * n)
    (hAB₁ : Disjoint A B₁)
    (hAcard : A.card = (n + 1) / 2)
    (hlarge : ∀ a ∈ A, n ≤ degreeInto G a Finset.univ)
    (hB₁lower : n / 2 - s ≤ B₁.card)
    (hB₁upper : B₁.card ≤ n / 2)
    (_hAA : ∀ a ∈ A, A.card - l ≤ (G.neighborFinset a ∩ A).card)
    (hB₁A : ∀ b ∈ B₁, A.card - l ≤ (G.neighborFinset b ∩ A).card)
    (hAB₁deg : ∀ a ∈ A, B₁.card - l ≤ (G.neighborFinset a ∩ B₁).card)
    (hsq : s ≤ q) (hql : q ≤ l) (hq : 7 * q < n / 2) :
    Nonempty (LowLeafHostPackage G A B₁ n l) := by
  classical
  obtain ⟨k, left, middle, right, J,
      hleftA, hrightA, hmiddleOut,
      hleftInj, hmiddleInj, hrightInj, hendsDisj,
      hpathLeft, hpathRight, hJcard, hmax⟩ :=
    exists_indexed_maximal_two_path_family G A B₁ n
  let B₂ : Finset V := selectedTwoPathMiddles middle J
  let B : Finset V := B₁ ∪ B₂
  let H : SimpleGraph V := lowLeafHostGraph G A B

  have hB₂card : B₂.card = J.card := by
    exact card_selectedTwoPathMiddles J hmiddleInj
  have hB₁B₂ : Disjoint B₁ B₂ := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    rcases Finset.mem_image.mp hv₂ with ⟨i, hiJ, rfl⟩
    exact hmiddleOut i (Finset.mem_union_right A hv₁)
  have hAB₂ : Disjoint A B₂ := by
    rw [Finset.disjoint_left]
    intro v hvA hv₂
    rcases Finset.mem_image.mp hv₂ with ⟨i, hiJ, rfl⟩
    exact hmiddleOut i (Finset.mem_union_left B₁ hvA)
  have hAB : Disjoint A B := by
    change Disjoint A (B₁ ∪ B₂)
    rw [Finset.disjoint_union_right]
    exact ⟨hAB₁, hAB₂⟩
  have hBcard : B.card = B₁.card + J.card := by
    change (B₁ ∪ B₂).card = B₁.card + J.card
    rw [Finset.card_union_of_disjoint hB₁B₂, hB₂card]
  have hhalves : (n + 1) / 2 + n / 2 = n := by omega
  have hcap_le_s : n - A.card - B₁.card ≤ s := by omega
  have hB₂le : B₂.card ≤ l := by
    rw [hB₂card, hJcard]
    exact (min_le_right _ _).trans (hcap_le_s.trans (hsq.trans hql))
  have hBupper : B.card ≤ n / 2 := by
    rw [hBcard, hJcard]
    have hmin := min_le_right k (n - A.card - B₁.card)
    omega
  have hB₁q : n / 2 - q ≤ B₁.card := by omega
  have hcount : n - 1 ≤ (A ∪ B₁ ∪ B₂).card := by
    apply zhao_lemma74_maximal_two_path_count G J hVcard hAB₁ hAcard hlarge hB₁q hq
      hleftA hrightA hmiddleOut hleftInj hmiddleInj hrightInj hendsDisj
      hpathLeft hpathRight hJcard hmax
  have hABcard : (A ∪ B).card = A.card + B.card :=
    Finset.card_union_of_disjoint hAB
  have hsameUnion : A ∪ B₁ ∪ B₂ = A ∪ B := by
    simp [B, Finset.union_assoc]
  have hBlower : n / 2 - 1 ≤ B.card := by
    rw [hsameUnion, hABcard] at hcount
    omega

  have hB₁subB : B₁ ⊆ B := by
    intro b hb
    exact Finset.mem_union_left B₂ hb
  have hB₂subB : B₂ ⊆ B := by
    intro b hb
    exact Finset.mem_union_right B₁ hb

  let idx : B₂ → Fin k := selectedIndex middle J
  have hidxMem : ∀ y : B₂, idx y ∈ J := selectedIndex_mem middle J
  have hidxMiddle : ∀ y : B₂, middle (idx y) = y := middle_selectedIndex middle J
  have hidxInj : Function.Injective idx := by
    intro y z h
    have h' : idx y = idx z := hmiddleInj (congrArg middle h)
    apply Subtype.ext
    rw [← hidxMiddle y, ← hidxMiddle z, h']
  have hleftRight : ∀ i j, left i ≠ right j := by
    intro i j hij
    apply (Finset.disjoint_left.mp hendsDisj)
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hij.symm⟩
  let paths : Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem H A B₂ :=
    { left := fun y ↦ left (idx y)
      right := fun y ↦ right (idx y)
      left_mem := fun y ↦ hleftA (idx y)
      right_mem := fun y ↦ hrightA (idx y)
      adj_left := fun y ↦ by
        have hmidB : middle (idx y) ∈ B₂ := by
          simpa only [hidxMiddle y] using y.property
        rw [show (y : V) = middle (idx y) from (hidxMiddle y).symm]
        rw [show H = G.between (A : Set V) (B : Set V) by rfl,
          SimpleGraph.between_adj]
        exact ⟨hpathLeft (idx y), Or.inl ⟨hleftA (idx y),
          hB₂subB hmidB⟩⟩
      adj_right := fun y ↦ by
        have hmidB : middle (idx y) ∈ B₂ := by
          simpa only [hidxMiddle y] using y.property
        rw [show (y : V) = middle (idx y) from (hidxMiddle y).symm]
        rw [show H = G.between (A : Set V) (B : Set V) by rfl,
          SimpleGraph.between_adj]
        exact ⟨hpathRight (idx y), Or.inr ⟨hB₂subB hmidB,
          hrightA (idx y)⟩⟩
      endpointInjective := by
        rintro ⟨y, a⟩ ⟨z, b⟩ heq
        fin_cases a <;> fin_cases b
        · simp only [Fin.isValue, if_pos] at heq
          have hi : idx y = idx z := hleftInj heq
          simp [hidxInj hi]
        · simp only [Fin.isValue, if_pos, OfNat.zero_ne_ofNat, if_false] at heq
          exact (hleftRight (idx y) (idx z) heq).elim
        · simp only [Fin.isValue, OfNat.one_ne_ofNat, if_false, if_pos] at heq
          exact (hleftRight (idx z) (idx y) heq.symm).elim
        · simp only [Fin.isValue, OfNat.one_ne_ofNat, if_false] at heq
          have hi : idx y = idx z := hrightInj heq
          simp [hidxInj hi] }

  have hleftEq : ∀ a ∈ A,
      (H.neighborFinset a ∩ B₁) = (G.neighborFinset a ∩ B₁) := by
    intro a ha
    exact neighborFinset_lowLeafHostGraph_inter_right G hB₁subB ha
  have hrightEq : ∀ b ∈ B₁,
      (H.neighborFinset b ∩ A) = (G.neighborFinset b ∩ A) := by
    intro b hb
    exact neighborFinset_lowLeafHostGraph_inter_left G (Finset.Subset.rfl) (hB₁subB hb)

  let P : LowLeafHostPackage G A B₁ n l :=
    { k := k
      left := left
      middle := middle
      right := right
      J := J
      B₂ := B₂
      B := B
      B₂_eq := rfl
      B_eq := rfl
      left_mem := hleftA
      right_mem := hrightA
      middle_out := hmiddleOut
      left_injective := hleftInj
      middle_injective := hmiddleInj
      right_injective := hrightInj
      ends_disjoint := hendsDisj
      adj_left := hpathLeft
      adj_right := hpathRight
      J_card := hJcard
      maximal := hmax
      B₁_B₂_disjoint := hB₁B₂
      B_split := rfl
      card_B_lower := hBlower
      card_B_upper := hBupper
      card_B₂_le := hB₂le
      restricted_le := SimpleGraph.between_le
      restricted_bipartite := SimpleGraph.between_isBipartiteWith (by
        rw [Set.disjoint_left]
        intro x hxA hxB
        exact (Finset.disjoint_left.mp hAB) hxA hxB)
      paths := paths
      left_inter_eq := hleftEq
      right_inter_eq := hrightEq
      left_degree_bound := fun a ha ↦ by rw [hleftEq a ha]; exact hAB₁deg a ha
      right_degree_bound := fun b hb ↦ by rw [hrightEq b hb]; exact hB₁A b hb }
  exact ⟨P⟩


end Erdos547EC2
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Global greedy extension by a set of leaves

This file isolates the elementary global-degree leaf-extension step used in
Zhao's Lemma 7.8.  A copy of the graph induced on the nonleaves is already
fixed.  Every selected leaf has a parent in that core, and every such parent
image has host degree at least one less than the total number of target
vertices.  Hall's theorem then chooses pairwise distinct unused neighbours
for all selected leaves simultaneously.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoGlobalLeafExtension74

open Finset Function SimpleGraph

/-- The core left after deleting the selected leaves. -/
abbrev LeafCore {A : Type*} [DecidableEq A] (D : Finset A) :=
  {a : A // a ∉ D}

/-- Assemble a copy of the whole graph from a copy on the complement of a
set of leaves and distinct new images for those leaves. -/
theorem extend_copy_by_leaf_images
    {A V : Type*} [Fintype A] [Fintype V]
    [DecidableEq A] [DecidableEq V]
    (T : SimpleGraph A) (G : SimpleGraph V)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (D : Finset A)
    (hleaf : ∀ d : D, T.degree d.1 = 1)
    (parent : D → LeafCore D)
    (hparent : ∀ d, T.Adj d.1 (parent d).1)
    (core : Copy (T.induce ({a : A | a ∉ D} : Set A)) G)
    (leafImage : D → V)
    (hleafImage_inj : Injective leafImage)
    (hdisjoint : ∀ c d, core c ≠ leafImage d)
    (hadj : ∀ d, G.Adj (core (parent d)) (leafImage d)) :
    ∃ full : Copy T G,
      (∀ c : LeafCore D, full c.1 = core c) ∧
      ∀ d : D, full d.1 = leafImage d := by
  classical
  let F : A → V := fun a =>
    if ha : a ∈ D then leafImage ⟨a, ha⟩ else core ⟨a, ha⟩
  have hparent_unique (d : D) :
      ∀ a, T.Adj d.1 a → a = (parent d).1 := by
    obtain ⟨p, hdp, hp⟩ := degree_eq_one_iff_existsUnique_adj.mp (hleaf d)
    intro a hda
    exact (hp a hda).trans (hp (parent d).1 (hparent d)).symm
  have hF_inj : Injective F := by
    intro a b hab
    by_cases ha : a ∈ D
    · by_cases hb : b ∈ D
      · have : (⟨a, ha⟩ : D) = ⟨b, hb⟩ := by
          apply hleafImage_inj
          simpa [F, ha, hb] using hab
        exact congrArg Subtype.val this
      · have hcross : core (⟨b, hb⟩ : LeafCore D) =
            leafImage (⟨a, ha⟩ : D) := by
          simpa [F, ha, hb] using hab.symm
        exact (hdisjoint ⟨b, hb⟩ ⟨a, ha⟩ hcross).elim
    · by_cases hb : b ∈ D
      · have hcross : core (⟨a, ha⟩ : LeafCore D) =
            leafImage (⟨b, hb⟩ : D) := by
          simpa [F, ha, hb] using hab
        exact (hdisjoint ⟨a, ha⟩ ⟨b, hb⟩ hcross).elim
      · have : (⟨a, ha⟩ : LeafCore D) = ⟨b, hb⟩ := by
          apply core.injective
          simpa [F, ha, hb] using hab
        exact congrArg Subtype.val this
  have hF_adj : ∀ ⦃a b⦄, T.Adj a b → G.Adj (F a) (F b) := by
    intro a b hab
    by_cases ha : a ∈ D
    · let d : D := ⟨a, ha⟩
      have hbval : b = (parent d).1 := hparent_unique d b hab
      have hb : b ∉ D := by simpa [hbval] using (parent d).property
      have hpa : (⟨b, hb⟩ : LeafCore D) = parent d := by
        apply Subtype.ext
        exact hbval
      simpa [F, ha, hb, d, hpa] using (hadj d).symm
    · by_cases hb : b ∈ D
      · let d : D := ⟨b, hb⟩
        have haval : a = (parent d).1 := hparent_unique d a hab.symm
        have hpa : (⟨a, ha⟩ : LeafCore D) = parent d := by
          apply Subtype.ext
          exact haval
        simpa [F, ha, hb, d, hpa] using hadj d
      · have habCore :
            (T.induce ({a : A | a ∉ D} : Set A)).Adj
              (⟨a, ha⟩ : LeafCore D) ⟨b, hb⟩ := by
          simpa using hab
        simpa [F, ha, hb] using core.toHom.map_adj habCore
  let full : Copy T G :=
    ⟨⟨F, fun {_ _} hab => hF_adj hab⟩, hF_inj⟩
  refine ⟨full, ?_, ?_⟩
  · intro c
    simp [full, F, c.property]
  · intro d
    simp [full, F, d.property]

/-- A copy on the complement of a selected set of leaves extends to the
whole tree if every embedded parent has host degree at least `|T|-1`. -/
theorem exists_copy_extending_core_of_parent_degree
    {A V : Type*} [Fintype A] [Fintype V]
    [DecidableEq A] [DecidableEq V]
    (T : SimpleGraph A) (G : SimpleGraph V)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (D : Finset A)
    (hleaf : ∀ d : D, T.degree d.1 = 1)
    (parent : D → LeafCore D)
    (hparent : ∀ d, T.Adj d.1 (parent d).1)
    (core : Copy (T.induce ({a : A | a ∉ D} : Set A)) G)
    (hdegree : ∀ d : D,
      Fintype.card A - 1 ≤ G.degree (core (parent d))) :
    ∃ full : Copy T G,
      ∀ c : LeafCore D, full c.1 = core c := by
  classical
  let usedCore : Finset V := univ.image core
  let candidate : D → Finset V := fun d =>
    G.neighborFinset (core (parent d)) \ usedCore
  have hused_card : #usedCore = Fintype.card (LeafCore D) := by
    dsimp only [usedCore]
    exact card_image_iff.mpr fun _ _ _ _ h => core.injective h
  have hcore_card : Fintype.card (LeafCore D) = Fintype.card A - #D := by
    rw [Fintype.card_subtype_compl]
    congr 1
    rw [Fintype.card_subtype (fun a : A => a ∈ D)]
    simp
  have hcandidate : ∀ d, #D ≤ #(candidate d) := by
    intro d
    let p : V := core (parent d)
    have hp_used : p ∈ usedCore := by
      exact mem_image.mpr ⟨parent d, mem_univ _, rfl⟩
    have hinter_subset :
        G.neighborFinset p ∩ usedCore ⊆ usedCore.erase p := by
      intro x hx
      rw [mem_inter] at hx
      rw [mem_erase]
      exact ⟨(G.ne_of_adj ((G.mem_neighborFinset p x).mp hx.1)).symm, hx.2⟩
    have hinter_card : #(G.neighborFinset p ∩ usedCore) ≤ #usedCore - 1 := by
      calc
        #(G.neighborFinset p ∩ usedCore) ≤ #(usedCore.erase p) :=
          card_le_card hinter_subset
        _ = #usedCore - 1 := by rw [card_erase_of_mem hp_used]
    have hsplit := card_sdiff_add_card_inter (G.neighborFinset p) usedCore
    have hdeg : Fintype.card A - 1 ≤ #(G.neighborFinset p) := by
      simpa [p, G.card_neighborFinset_eq_degree] using hdegree d
    dsimp only [candidate]
    rw [show core (parent d) = p by rfl]
    rw [hused_card, hcore_card] at hinter_card
    have hcore_pos : 0 < Fintype.card (LeafCore D) :=
      Fintype.card_pos_iff.mpr ⟨parent d⟩
    rw [hcore_card] at hcore_pos
    have hDcard : #D ≤ Fintype.card A := by
      simpa using card_le_univ D
    omega
  have hHall : ∀ S : Finset D, #S ≤ #(S.biUnion candidate) := by
    intro S
    by_cases hS : S = ∅
    · simp [hS]
    · obtain ⟨d, hd⟩ := nonempty_iff_ne_empty.mpr hS
      calc
        #S ≤ Fintype.card D := card_le_univ S
        _ = #D := Fintype.card_coe D
        _ ≤ #(candidate d) := hcandidate d
        _ ≤ #(S.biUnion candidate) := card_le_card (subset_biUnion_of_mem candidate hd)
  obtain ⟨leafImage, hleafImage_inj, hleafImage_mem⟩ :=
    (all_card_le_biUnion_card_iff_exists_injective candidate).mp hHall
  have hdisjoint : ∀ c d, core c ≠ leafImage d := by
    intro c d heq
    have hmem := hleafImage_mem d
    rw [mem_sdiff] at hmem
    exact hmem.2 (mem_image.mpr ⟨c, mem_univ _, heq⟩)
  have hadj : ∀ d, G.Adj (core (parent d)) (leafImage d) := by
    intro d
    exact (G.mem_neighborFinset (core (parent d)) (leafImage d)).mp
      (mem_sdiff.mp (hleafImage_mem d)).1
  obtain ⟨full, hcore, _⟩ :=
    extend_copy_by_leaf_images T G D hleaf parent hparent core leafImage
      hleafImage_inj hdisjoint hadj
  exact ⟨full, hcore⟩

/-- Convenient specialization when the degree bound is known for every
embedded core vertex (as in Zhao's global high-degree set). -/
theorem exists_copy_extending_core_of_degree
    {A V : Type*} [Fintype A] [Fintype V]
    [DecidableEq A] [DecidableEq V]
    (T : SimpleGraph A) (G : SimpleGraph V)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (D : Finset A)
    (hleaf : ∀ d : D, T.degree d.1 = 1)
    (parent : D → LeafCore D)
    (hparent : ∀ d, T.Adj d.1 (parent d).1)
    (core : Copy (T.induce ({a : A | a ∉ D} : Set A)) G)
    (hdegree : ∀ c : LeafCore D,
      Fintype.card A - 1 ≤ G.degree (core c)) :
    ∃ full : Copy T G,
      ∀ c : LeafCore D, full c.1 = core c := by
  exact exists_copy_extending_core_of_parent_degree T G D hleaf parent hparent core
    (fun d => hdegree (parent d))

/-- Source-shaped global-degree leaf extension used in the low-leaf branch of
Zhao's Lemma 7.4.  If `T` has `n + 1` vertices, a copy of the complement of
the chosen leaves extends to a copy of all of `T` as soon as every embedded
parent has host degree at least `n`.

The proof above only needs the local pendant-vertex data; the tree hypothesis
is retained here because this is the interface used by Lemma 7.4. -/
theorem global_degree_leaf_extension
    {A V : Type*} [Fintype A] [Fintype V]
    [DecidableEq A] [DecidableEq V]
    (T : SimpleGraph A) (G : SimpleGraph V)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card A = n + 1) (_hT : T.IsTree)
    (W : Finset A)
    (hleaf : ∀ w : W, T.degree w.1 = 1)
    (parent : W → LeafCore W)
    (hparent : ∀ w, T.Adj w.1 (parent w).1)
    (core : Copy (T.induce ({a : A | a ∉ W} : Set A)) G)
    (hdegree : ∀ w : W, n ≤ G.degree (core (parent w))) :
    T.IsContained G := by
  have hdegree' : ∀ w : W,
      Fintype.card A - 1 ≤ G.degree (core (parent w)) := by
    intro w
    rw [hcard]
    simpa using hdegree w
  obtain ⟨full, _⟩ := exists_copy_extending_core_of_parent_degree
    T G W hleaf parent hparent core hdegree'
  exact ⟨full⟩

end Erdos547b.ZhaoGlobalLeafExtension74


open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLowLeafCore74

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The leaves of `T` lying in the displayed right bipartition class. -/
def deletedLeaves (T : SimpleGraph V) [DecidableRel T.Adj] (O : Finset V) : Finset V :=
  O.filter fun v => T.degree v = 1

/-- The target tree after deleting all right-side leaves. -/
abbrev core (T : SimpleGraph V) [DecidableRel T.Adj] (O : Finset V) :
    SimpleGraph {v : V // v ∉ deletedLeaves T O} :=
  T.induce {v : V | v ∉ deletedLeaves T O}

/-- A retained part, regarded as a finset in the core vertex type. -/
def retainedPart (T : SimpleGraph V) [DecidableRel T.Adj]
    (O A : Finset V) : Finset {v : V // v ∉ deletedLeaves T O} :=
  Finset.univ.filter fun v => v.1 ∈ A

@[simp] theorem mem_deletedLeaves {T : SimpleGraph V} [DecidableRel T.Adj]
    {O : Finset V} {v : V} :
    v ∈ deletedLeaves T O ↔ v ∈ O ∧ T.degree v = 1 := by
  simp [deletedLeaves]

@[simp] theorem mem_retainedPart {T : SimpleGraph V} [DecidableRel T.Adj]
    {O A : Finset V} {v : {v : V // v ∉ deletedLeaves T O}} :
    v ∈ retainedPart T O A ↔ v.1 ∈ A := by
  simp [retainedPart]

theorem card_retainedPart_eq {T : SimpleGraph V} [DecidableRel T.Adj]
    {O A : Finset V} (hdisj : Disjoint A (deletedLeaves T O)) :
    #(retainedPart T O A) = #A := by
  classical
  let q : (v : {x : V // x ∉ deletedLeaves T O}) →
      v ∈ retainedPart T O A → V := fun v _ => v.1
  apply Finset.card_bij q
  · intro v hv
    exact (mem_retainedPart.mp hv)
  · intro v hv w hw heq
    exact Subtype.ext heq
  · intro v hv
    have hvnot : v ∉ deletedLeaves T O := fun hvdel =>
      Finset.disjoint_left.mp hdisj hv hvdel
    exact ⟨⟨v, hvnot⟩, mem_retainedPart.mpr hv, rfl⟩

theorem deletedLeaves_subset_right {T : SimpleGraph V} [DecidableRel T.Adj]
    (O : Finset V) : deletedLeaves T O ⊆ O := by
  intro v hv
  exact (mem_deletedLeaves.mp hv).1

theorem deletedLeaves_subset_allLeaves {T : SimpleGraph V} [DecidableRel T.Adj]
    (O : Finset V) :
    deletedLeaves T O ⊆ Erdos547b.ZhaoLemma710.leafVertices T := by
  intro v hv
  simpa [Erdos547b.ZhaoLemma710.leafVertices] using (mem_deletedLeaves.mp hv).2

/-- Deleting any collection of degree-one vertices from a connected graph,
provided at least one vertex remains, preserves connectedness. -/
theorem connected_induce_compl_leaves
    (T : SimpleGraph V) [DecidableRel T.Adj] (W : Finset V)
    (hconn : T.Connected) (hleaf : ∀ w ∈ W, T.degree w = 1)
    (hremain : ({v : V | v ∉ W} : Set V).Nonempty) :
    (T.induce {v : V | v ∉ W}).Connected := by
  classical
  rw [connected_iff]
  refine ⟨?_, hremain.to_subtype⟩
  intro x y
  obtain ⟨p, hp⟩ := hconn.exists_isPath x.1 y.1
  have hav : ∀ z ∈ p.support, z ∉ W := by
    intro z hz hzW
    have hzdeg := hleaf z hzW
    obtain ⟨a, hza, hauniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hzdeg
    obtain ⟨pxz, pzy, hpxz, hpzy, hpEq⟩ := p.mem_support_iff_exists_append.mp hz
    have hxz : x.1 ≠ z := fun heq => x.property (heq ▸ hzW)
    have hzy : z ≠ y.1 := fun heq => y.property (heq ▸ hzW)
    have hpxzNotNil : ¬pxz.Nil := SimpleGraph.Walk.not_nil_of_ne hxz
    have hpzyNotNil : ¬pzy.Nil := SimpleGraph.Walk.not_nil_of_ne hzy
    refine List.nodup_iff_forall_not_duplicate.mp
      ((SimpleGraph.Walk.isPath_def (pxz.append pzy)).mp hp) a ?_
    rw [SimpleGraph.Walk.support_append, List.duplicate_iff_two_le_count,
      List.count_append]
    have hleft := List.one_le_count_iff.mpr
      (pxz.getVert_mem_support (pxz.length - 1))
    simp only [hauniq _ (pxz.adj_penultimate hpxzNotNil).symm] at hleft
    have hright := List.one_le_count_iff.mpr
      (pzy.snd_mem_tail_support hpzyNotNil)
    rw [hauniq _ (pzy.adj_snd hpzyNotNil)] at hright
    omega
  exact ⟨(p.induce {v : V | v ∉ W} hav).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

/-- The induced graph obtained by deleting all right-side leaves is a tree. -/
theorem core_isTree
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V)
    (hT : T.IsTree) (hpart : IsProperBipartition T E O) :
    (core T O).IsTree := by
  classical
  have hdisj : Disjoint E (deletedLeaves T O) :=
    (Finset.disjoint_coe.mp hpart.bipartite.disjoint).mono_right
      (deletedLeaves_subset_right O)
  have hremain : ({v : V | v ∉ deletedLeaves T O} : Set V).Nonempty := by
    obtain ⟨e, heE⟩ := hpart.left_nonempty
    exact ⟨e, fun heW => Finset.disjoint_left.mp hdisj heE heW⟩
  refine ⟨?_, hT.isAcyclic.induce _⟩
  exact connected_induce_compl_leaves T (deletedLeaves T O) hT.connected
    (fun w hw => (mem_deletedLeaves.mp hw).2) hremain

/-- The retained left class is all of `E`; the retained right class is
`O` with the deleted leaves removed. -/
def coreLeft (T : SimpleGraph V) [DecidableRel T.Adj]
    (E O : Finset V) := retainedPart T O E

def coreRight (T : SimpleGraph V) [DecidableRel T.Adj]
    (O : Finset V) := retainedPart T O (O \ deletedLeaves T O)

theorem core_parts_bipartite
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V)
    (hpart : IsProperBipartition T E O) :
    (core T O).IsBipartiteWith (coreLeft T E O : Set _)
      (coreRight T O : Set _) := by
  classical
  constructor
  · rw [Set.disjoint_left]
    intro x hxE hxO
    have hxE' : x.1 ∈ E := by simpa [coreLeft] using hxE
    have hxO' : x.1 ∈ O := by
      have : x.1 ∈ O \ deletedLeaves T O := by simpa [coreRight] using hxO
      exact (Finset.mem_sdiff.mp this).1
    exact Set.disjoint_left.mp hpart.bipartite.disjoint hxE' hxO'
  · intro x y hxy
    have hxyT : T.Adj x.1 y.1 := hxy
    rcases hpart.bipartite.mem_of_adj hxyT with h | h
    · left
      constructor
      · simpa [coreLeft] using h.1
      · have hy : y.1 ∈ O \ deletedLeaves T O :=
          Finset.mem_sdiff.mpr ⟨h.2, y.property⟩
        simpa [coreRight] using hy
    · right
      constructor
      · have hx : x.1 ∈ O \ deletedLeaves T O :=
          Finset.mem_sdiff.mpr ⟨h.1, x.property⟩
        simpa [coreRight] using hx
      · simpa [coreLeft] using h.2

theorem core_parts_cover
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V)
    (hpart : IsProperBipartition T E O) :
    coreLeft T E O ∪ coreRight T O = Finset.univ := by
  classical
  ext x
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  have hxcover : x.1 ∈ E ∨ x.1 ∈ O := by
    have hx := Set.ext_iff.mp hpart.cover x.1
    simpa using hx
  rcases hxcover with hxE | hxO
  · exact Or.inl (by simpa [coreLeft] using hxE)
  · exact Or.inr (by
      have : x.1 ∈ O \ deletedLeaves T O :=
        Finset.mem_sdiff.mpr ⟨hxO, x.property⟩
      simpa [coreRight] using this)

theorem card_coreLeft
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V)
    (hpart : IsProperBipartition T E O) :
    #(coreLeft T E O) = #E := by
  apply card_retainedPart_eq
  exact (Finset.disjoint_coe.mp hpart.bipartite.disjoint).mono_right
    (deletedLeaves_subset_right O)

theorem card_coreRight
    (T : SimpleGraph V) [DecidableRel T.Adj] (O : Finset V) :
    #(coreRight T O) = #(O \ deletedLeaves T O) := by
  apply card_retainedPart_eq
  exact Finset.sdiff_disjoint

theorem deletedLeaves_eq_leavesIn
    (T : SimpleGraph V) [DecidableRel T.Adj] (O : Finset V) :
    deletedLeaves T O = Erdos547b.leavesIn T O := by
  ext v
  simp [deletedLeaves, Erdos547b.leavesIn, Erdos547b.IsLeaf]

/-- Zhao Fact 6.9 supplies the strict right-side loss: after deleting all
right-side leaves, the retained right side has at most `#E - 1` vertices. -/
theorem card_coreRight_le_card_left_sub_one
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V)
    (hT : T.IsTree) (hpart : IsProperBipartition T E O)
    (hEO : #E ≤ #O) :
    #(coreRight T O) ≤ #E - 1 := by
  have hfact := Erdos547b.card_leavesIn_larger_part T E O hT hpart hEO
  rw [← deletedLeaves_eq_leavesIn T O] at hfact
  have hWsub : deletedLeaves T O ⊆ O := deletedLeaves_subset_right O
  rw [card_coreRight, Finset.card_sdiff_of_subset hWsub]
  omega

/-- The structural package for the pruned low-leaf core. -/
structure CoreWitness
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V) : Prop where
  isTree : (core T O).IsTree
  bipartite : (core T O).IsBipartiteWith (coreLeft T E O : Set _)
    (coreRight T O : Set _)
  cover : coreLeft T E O ∪ coreRight T O = Finset.univ
  card_left : #(coreLeft T E O) = #E
  card_right : #(coreRight T O) = #(O \ deletedLeaves T O)
  card_right_le : #(coreRight T O) ≤ #E - 1

theorem coreWitness
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V)
    (hT : T.IsTree) (hpart : IsProperBipartition T E O)
    (hEO : #E ≤ #O) : CoreWitness T E O where
  isTree := core_isTree T E O hT hpart
  bipartite := core_parts_bipartite T E O hpart
  cover := core_parts_cover T E O hpart
  card_left := card_coreLeft T E O hpart
  card_right := card_coreRight T O
  card_right_le := card_coreRight_le_card_left_sub_one T E O hT hpart hEO

theorem degree_core_le
    (T : SimpleGraph V) [DecidableRel T.Adj] (O : Finset V)
    (x : {v : V // v ∉ deletedLeaves T O}) :
    (core T O).degree x ≤ T.degree x.1 := by
  classical
  let e : (core T O).neighborSet x ↪ T.neighborSet x.1 :=
    { toFun := fun y => ⟨y.1.1, y.property⟩
      inj' := by
        intro y z hyz
        have hv : y.1.1 = z.1.1 :=
          congrArg (fun q : T.neighborSet x.1 => (q.1 : V)) hyz
        exact Subtype.ext (Subtype.ext hv) }
  calc
    (core T O).degree x = Fintype.card ((core T O).neighborSet x) :=
      ((core T O).card_neighborSet_eq_degree x).symm
    _ ≤ Fintype.card (T.neighborSet x.1) := Fintype.card_le_of_embedding e
    _ = T.degree x.1 := T.card_neighborSet_eq_degree x.1

theorem branchExcess_core_le
    (T : SimpleGraph V) [DecidableRel T.Adj] (O : Finset V) :
    Erdos547b.ZhaoLemma710.branchExcess (core T O) ≤
      Erdos547b.ZhaoLemma710.branchExcess T := by
  classical
  let e : {v : V // v ∉ deletedLeaves T O} ↪ V :=
    Function.Embedding.subtype _
  have hsubset :
      (Erdos547b.ZhaoLemma710.branchVertices (core T O)).map e ⊆
        Erdos547b.ZhaoLemma710.branchVertices T := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hv
    have hx3 : 3 ≤ (core T O).degree x := by
      exact (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hx3.trans (degree_core_le T O x)⟩
  rw [Erdos547b.ZhaoLemma710.branchExcess,
    Erdos547b.ZhaoLemma710.branchExcess]
  calc
    (∑ x ∈ Erdos547b.ZhaoLemma710.branchVertices (core T O),
        ((core T O).degree x - 2)) ≤
        ∑ x ∈ Erdos547b.ZhaoLemma710.branchVertices (core T O),
          (T.degree x.1 - 2) := by
      exact Finset.sum_le_sum fun x _ => Nat.sub_le_sub_right (degree_core_le T O x) 2
    _ = ∑ v ∈ (Erdos547b.ZhaoLemma710.branchVertices (core T O)).map e,
        (T.degree v - 2) := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ v ∈ Erdos547b.ZhaoLemma710.branchVertices T, (T.degree v - 2) :=
      Finset.sum_le_sum_of_subset hsubset

/-- Pruning leaves cannot increase the number of leaves of the remaining
tree.  In the nontrivial-core case this follows by monotonicity of total
degree excess; a subsingleton core has no degree-one vertex. -/
theorem card_leafVertices_core_le [Nontrivial V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V)
    (hT : T.IsTree) (hpart : IsProperBipartition T E O) :
    #(Erdos547b.ZhaoLemma710.leafVertices (core T O)) ≤
      #(Erdos547b.ZhaoLemma710.leafVertices T) := by
  classical
  let S := {v : V // v ∉ deletedLeaves T O}
  by_cases hsub : Subsingleton S
  · have hzero : ∀ x : S, (core T O).degree x = 0 := by
      intro x
      rw [SimpleGraph.degree_eq_zero]
      intro y hxy
      exact hxy.ne (Subsingleton.elim x y)
    have hempty : Erdos547b.ZhaoLemma710.leafVertices (core T O) = ∅ := by
      ext x
      simp [Erdos547b.ZhaoLemma710.leafVertices, hzero x]
    rw [hempty]
    simp
  · letI : Nontrivial S := not_subsingleton_iff_nontrivial.mp hsub
    have hcore := Erdos547b.ZhaoLemma710.branchExcess_add_two_eq_card_leaves
      (core T O) (core_isTree T E O hT hpart)
    have horig := Erdos547b.ZhaoLemma710.branchExcess_add_two_eq_card_leaves T hT
    have hmono := branchExcess_core_le T O
    omega

theorem ec2_leafVertices_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Erdos547EC2.leafVertices G = Erdos547b.ZhaoLemma710.leafVertices G := by
  rfl

theorem card_ec2_leafVertices_core_le [Nontrivial V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V)
    (hT : T.IsTree) (hpart : IsProperBipartition T E O) :
    #(Erdos547EC2.leafVertices (core T O)) ≤
      #(Erdos547EC2.leafVertices T) := by
  rw [ec2_leafVertices_eq, ec2_leafVertices_eq]
  exact card_leafVertices_core_le T E O hT hpart

/-- The complete adapter needed by Zhao's low-leaf embedding lemma. -/
structure BoundedCoreWitness [Nontrivial V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (E O : Finset V) (l : ℕ) : Prop extends CoreWitness T E O where
  leaf_card_le : #(Erdos547EC2.leafVertices (core T O)) ≤
    #(Erdos547EC2.leafVertices T)
  left_large : 26 * l ≤ #(coreLeft T E O)
  right_large : 26 * l ≤ #(coreRight T O)

theorem boundedCoreWitness_of_explicit_bounds [Nontrivial V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V) (l : ℕ)
    (hT : T.IsTree) (hpart : IsProperBipartition T E O)
    (hEO : #E ≤ #O) (hleft : 26 * l ≤ #E)
    (hright : 26 * l + #(deletedLeaves T O) ≤ #O) :
    BoundedCoreWitness T E O l := by
  have hbase := coreWitness T E O hT hpart hEO
  refine
    { hbase with
      leaf_card_le := card_ec2_leafVertices_core_le T E O hT hpart
      left_large := by simpa [hbase.card_left]
      right_large := ?_ }
  rw [hbase.card_right, Finset.card_sdiff_of_subset (deletedLeaves_subset_right O)]
  omega

/-- Zhao's numerical hypotheses imply the explicit side-capacity estimates.
Here `#E > n/2-r` is written as a strict inequality in the convenient order. -/
theorem boundedCoreWitness_of_zhao_numbers [Nontrivial V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V)
    (n r l : ℕ) (hT : T.IsTree) (hpart : IsProperBipartition T E O)
    (hEO : #E ≤ #O) (hcard : Fintype.card V = n + 1)
    (hleaves : #(Erdos547EC2.leafVertices T) ≤ l)
    (hElarge : n / 2 - r < #E) (hscale : 1782 * r ≤ n)
    (hl : l = 33 * r) :
    BoundedCoreWitness T E O l := by
  have hdisj : Disjoint E O := Finset.disjoint_coe.mp hpart.bipartite.disjoint
  have hcover : E ∪ O = Finset.univ := by
    ext v
    have hv := Set.ext_iff.mp hpart.cover v
    simpa using hv
  have hsum : #E + #O = n + 1 := by
    rw [← hcard, ← Finset.card_univ, ← hcover,
      Finset.card_union_of_disjoint hdisj]
  have hW : #(deletedLeaves T O) ≤ l := by
    exact (Finset.card_le_card (deletedLeaves_subset_allLeaves O)).trans hleaves
  apply boundedCoreWitness_of_explicit_bounds T E O l hT hpart hEO
  · omega
  · omega


end Erdos547b.ZhaoLowLeafCore74

open scoped SimpleGraph

noncomputable section

namespace Erdos547b

open SimpleGraph

/-- Vertices retained after a finite set `L` is removed. -/
abbrev LeafCore {V : Type*} [DecidableEq V] (L : Finset V) :=
  {x : V // x ∉ L}

/-- The vertices in the designated finite leaf set. -/
abbrev ChosenLeaves {V : Type*} [DecidableEq V] (L : Finset V) :=
  {x : V // x ∈ L}

/-- A simultaneous extension lemma for a copy of the graph obtained by deleting
a set of leaves.  The chosen parent of each leaf is required to lie in the
core.  The new leaf images must be injective, disjoint from the core image,
and adjacent to the corresponding parent images. -/
def Copy.extendChosenLeaves {V W : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq W]
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel T.Adj]
    (L : Finset V)
    (hleaf : ∀ l : ChosenLeaves L, T.degree l.1 = 1)
    (parent : ChosenLeaves L → LeafCore L)
    (hparent : ∀ l, T.Adj l.1 (parent l).1)
    (f : Copy (T.induce {x | x ∉ L}) G)
    (g : ChosenLeaves L → W)
    (hg : Function.Injective g)
    (hdisj : ∀ c l, f c ≠ g l)
    (hadj : ∀ l, G.Adj (f (parent l)) (g l)) :
    Copy T G := by
  classical
  let F : V → W := fun x ↦
    if hx : x ∈ L then g ⟨x, hx⟩ else f ⟨x, hx⟩
  have hparent_unique (l : ChosenLeaves L) :
      ∀ v, T.Adj l.1 v → v = (parent l).1 := by
    obtain ⟨p, hlp, hp⟩ := degree_eq_one_iff_existsUnique_adj.mp (hleaf l)
    intro v hlv
    exact (hp v hlv).trans (hp (parent l).1 (hparent l)).symm
  have hF_inj : Function.Injective F := by
    intro x y hxy
    by_cases hx : x ∈ L
    · by_cases hy : y ∈ L
      · have hgg : g (⟨x, hx⟩ : ChosenLeaves L) =
            g (⟨y, hy⟩ : ChosenLeaves L) := by
          simpa only [F, dif_pos hx, dif_pos hy] using hxy
        exact congrArg Subtype.val (hg hgg)
      · have hcross : f (⟨y, hy⟩ : LeafCore L) =
            g (⟨x, hx⟩ : ChosenLeaves L) := by
          dsimp only [F] at hxy
          rw [dif_pos hx, dif_neg hy] at hxy
          exact hxy.symm
        exact False.elim (hdisj ⟨y, hy⟩ ⟨x, hx⟩ hcross)
    · by_cases hy : y ∈ L
      · have hcross : f (⟨x, hx⟩ : LeafCore L) =
            g (⟨y, hy⟩ : ChosenLeaves L) := by
          dsimp only [F] at hxy
          rw [dif_neg hx, dif_pos hy] at hxy
          exact hxy
        exact False.elim (hdisj ⟨x, hx⟩ ⟨y, hy⟩ hcross)
      · have hff : f (⟨x, hx⟩ : LeafCore L) =
            f (⟨y, hy⟩ : LeafCore L) := by
          simpa only [F, dif_neg hx, dif_neg hy] using hxy
        exact congrArg Subtype.val (f.injective hff)
  refine ⟨⟨F, ?_⟩, hF_inj⟩
  intro x y hxy
  by_cases hx : x ∈ L
  · let l : ChosenLeaves L := ⟨x, hx⟩
    by_cases hy : y ∈ L
    · have hyeq : y = (parent l).1 := hparent_unique l y hxy
      exact False.elim ((parent l).2 (hyeq ▸ hy))
    · let c : LeafCore L := ⟨y, hy⟩
      have hcp : c = parent l := by
        apply Subtype.ext
        exact hparent_unique l y hxy
      change G.Adj (F x) (F y)
      dsimp only [F]
      rw [dif_pos hx, dif_neg hy]
      change G.Adj (g l) (f c)
      rw [hcp]
      exact (hadj l).symm
  · let c : LeafCore L := ⟨x, hx⟩
    by_cases hy : y ∈ L
    · let l : ChosenLeaves L := ⟨y, hy⟩
      have hcp : c = parent l := by
        apply Subtype.ext
        exact hparent_unique l x hxy.symm
      change G.Adj (F x) (F y)
      dsimp only [F]
      rw [dif_neg hx, dif_pos hy]
      change G.Adj (f c) (g l)
      rw [hcp]
      exact hadj l
    · let d : LeafCore L := ⟨y, hy⟩
      have hcd : (T.induce {z | z ∉ L}).Adj c d := hxy
      change G.Adj (F x) (F y)
      dsimp only [F]
      rw [dif_neg hx, dif_neg hy]
      exact f.toHom.map_rel hcd

/-- Proposition-valued version of `Copy.extendChosenLeaves`. -/
theorem isContained_of_copy_induce_compl_leaves {V W : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq W]
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel T.Adj]
    (L : Finset V)
    (hleaf : ∀ l : ChosenLeaves L, T.degree l.1 = 1)
    (parent : ChosenLeaves L → LeafCore L)
    (hparent : ∀ l, T.Adj l.1 (parent l).1)
    (f : Copy (T.induce {x | x ∉ L}) G)
    (g : ChosenLeaves L → W)
    (hg : Function.Injective g)
    (hdisj : ∀ c l, f c ≠ g l)
    (hadj : ∀ l, G.Adj (f (parent l)) (g l)) :
    T ⊑ G :=
  ⟨Copy.extendChosenLeaves T G L hleaf parent hparent f g hg hdisj hadj⟩


end Erdos547b
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma74

open SimpleGraph

variable {A V : Type*} [Fintype A] [DecidableEq A]
  [Fintype V] [DecidableEq V]

/-- Vertices of degree one.  Zhao calls these the leaves of a nontrivial
tree.  We keep the degree-one definition because every tree in Lemma 7.4 has
at least two vertices. -/
def leaves (T : SimpleGraph A) [DecidableRel T.Adj] : Finset A :=
  Finset.univ.filter fun x => T.degree x = 1

@[simp] theorem mem_leaves {T : SimpleGraph A} [DecidableRel T.Adj] {x : A} :
    x ∈ leaves T ↔ T.degree x = 1 := by
  simp [leaves]

/-- The absolute difference between the two color-class sizes. -/
def colorGap {T : SimpleGraph A} (c : T.Coloring (Fin 2)) : ℕ :=
  max (Coloring.partCard c 0) (Coloring.partCard c 1) -
    min (Coloring.partCard c 0) (Coloring.partCard c 1)

/-- The elementary parity-free estimate used in Zhao's large-gap case. -/
theorem min_partCard_le_floor_sub_of_gap
    {T : SimpleGraph A} (c : T.Coloring (Fin 2))
    {n r : ℕ} (hcard : Fintype.card A = n + 1)
    (hgap : 2 * r + 1 ≤ colorGap c) :
    min (Coloring.partCard c 0) (Coloring.partCard c 1) ≤ n / 2 - r := by
  have hsum := Erdos547b.EC1Scratch.partCard_zero_add_one c
  rw [hcard] at hsum
  unfold colorGap at hgap
  by_cases hab : Coloring.partCard c 0 ≤ Coloring.partCard c 1
  · rw [max_eq_right hab] at hgap
    rw [min_eq_left hab] at hgap ⊢
    omega
  · have hba : Coloring.partCard c 1 ≤ Coloring.partCard c 0 := by omega
    rw [max_eq_left hba] at hgap
    rw [min_eq_right hba] at hgap ⊢
    omega

/-- The two fibers of a proper two-coloring of a nontrivial tree form a
proper bipartition in the sense used by Fact 6.9 and Lemma 7.7. -/
theorem properBipartition_colorClasses
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (c : T.Coloring (Fin 2)) :
    IsProperBipartition T
      (Erdos547b.EC1Scratch.colorClassFinset c 0)
      (Erdos547b.EC1Scratch.colorClassFinset c 1) := by
  classical
  let u : A := Classical.choice (inferInstance : Nonempty A)
  obtain ⟨v, huv⟩ := hT.connected.preconnected.exists_adj_of_nontrivial u
  have hcne : c u ≠ c v := c.valid huv
  have hzero : ∃ x, c x = 0 := by
    rcases Erdos547b.EC1Scratch.fin_two_eq_zero_or_one (c u) with hu | hu
    · exact ⟨u, hu⟩
    · have hv : c v = 0 :=
        (Erdos547b.EC1Scratch.fin_two_eq_zero_or_one (c v)).resolve_right
          (fun hv ↦ hcne (hu.trans hv.symm))
      exact ⟨v, hv⟩
  have hone : ∃ x, c x = 1 := by
    rcases Erdos547b.EC1Scratch.fin_two_eq_zero_or_one (c u) with hu | hu
    · have hv : c v = 1 :=
        (Erdos547b.EC1Scratch.fin_two_eq_zero_or_one (c v)).resolve_left
          (fun hv ↦ hcne (hu.trans hv.symm))
      exact ⟨v, hv⟩
    · exact ⟨u, hu⟩
  refine
    { bipartite := Erdos547b.EC1Scratch.coloring_isBipartiteWith_zero_one c
      cover := ?_
      left_nonempty := ?_
      right_nonempty := ?_ }
  · ext x
    simp only [Erdos547b.EC1Scratch.colorClassFinset, Finset.coe_union,
      Finset.coe_filter, Finset.coe_univ, Set.mem_union, Set.mem_setOf_eq,
      Set.mem_univ, true_and, iff_true]
    rcases Erdos547b.EC1Scratch.fin_two_eq_zero_or_one (c x) with hx | hx
    · exact Or.inl ⟨Finset.mem_univ x, hx⟩
    · exact Or.inr ⟨Finset.mem_univ x, hx⟩
  · obtain ⟨x, hx⟩ := hzero
    exact ⟨x, by simp [Erdos547b.EC1Scratch.colorClassFinset, hx]⟩
  · obtain ⟨x, hx⟩ := hone
    exact ⟨x, by simp [Erdos547b.EC1Scratch.colorClassFinset, hx]⟩

/-- The high-degree set occurring in Zhao's statement. -/
def highVertices (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Finset V :=
  Finset.univ.filter fun v => n ≤ G.degree v

@[simp] theorem mem_highVertices {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} {v : V} : v ∈ highVertices G n ↔ n ≤ G.degree v := by
  simp [highVertices]

/-- A discrete version of Zhao's extremal case EC3.  The integer `q` is the
rounding-safe upper bound for the real defect `θ n`. -/
structure EC3Witness (G : SimpleGraph V) [DecidableRel G.Adj] (n q : ℕ) where
  V₁ : Finset V
  V₂ : Finset V
  A₀ : Finset V
  cut_disjoint : Disjoint V₁ V₂
  cut_cover : V₁ ∪ V₂ = Finset.univ
  card_V₁ : V₁.card = n
  card_V₂ : V₂.card = n
  A₀_subset : A₀ ⊆ V₁
  card_A₀ : A₀.card = (n + 1) / 2
  high_count : n / 2 + 1 ≤ (highVertices G n).card
  high_A₀ : ∀ a ∈ A₀, n ≤ G.degree a
  dense_A₀_V₁ : ∀ a ∈ A₀,
    n - q ≤ Erdos547EC2.degreeInto G a V₁

/-- EC3 as it is stated in Zhao's paper, before shrinking `A` to have
exactly `ceil(n/2)` vertices. -/
structure RawEC3Witness (G : SimpleGraph V) [DecidableRel G.Adj] (n q : ℕ) where
  V₁ : Finset V
  V₂ : Finset V
  A : Finset V
  cut_disjoint : Disjoint V₁ V₂
  cut_cover : V₁ ∪ V₂ = Finset.univ
  card_V₁ : V₁.card = n
  card_V₂ : V₂.card = n
  A_subset : A ⊆ V₁
  card_A : (n + 1) / 2 ≤ A.card
  high_count : n / 2 + 1 ≤ (highVertices G n).card
  high_A : ∀ a ∈ A, n ≤ G.degree a
  dense_A_V₁ : ∀ a ∈ A,
    n - q ≤ Erdos547EC2.degreeInto G a V₁

/-- Zhao's harmless normalization `|A|=ceil(n/2)` is a genuine finite
selection step; all degree hypotheses are inherited by the subset. -/
noncomputable def RawEC3Witness.normalize
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q : ℕ}
    (h : RawEC3Witness G n q) : EC3Witness G n q :=
  let hex := Finset.exists_subset_card_eq h.card_A
  let A₀ := Classical.choose hex
  let hA₀A := (Classical.choose_spec hex).1
  let hA₀card := (Classical.choose_spec hex).2
  by
    exact
    { V₁ := h.V₁
      V₂ := h.V₂
      A₀ := A₀
      cut_disjoint := h.cut_disjoint
      cut_cover := h.cut_cover
      card_V₁ := h.card_V₁
      card_V₂ := h.card_V₂
      A₀_subset := hA₀A.trans h.A_subset
      card_A₀ := hA₀card
      high_count := h.high_count
      high_A₀ := fun a ha => h.high_A a (hA₀A ha)
      dense_A₀_V₁ := fun a ha => h.dense_A_V₁ a (hA₀A ha) }

/-- Exact integer hypotheses corresponding to `θ ≤ (1/1782)^2`: `q` bounds
`θ n`, `s` bounds `sqrt θ n`, and the two product inequalities retain all
rounding information instead of silently appealing to real arithmetic. -/
structure SourceHierarchy (n q s : ℕ) : Prop where
  defect_square : q * n ≤ s * s
  theta_zero_bound : 1782 * s ≤ n
  q_pos : 0 < q
  n_large : 100 ≤ n

theorem EC3Witness.card_host
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q : ℕ}
    (h : EC3Witness G n q) : Fintype.card V = 2 * n := by
  have hcardUnion := Finset.card_union_of_disjoint h.cut_disjoint
  rw [h.cut_cover, Finset.card_univ, h.card_V₁, h.card_V₂] at hcardUnion
  omega

theorem EC3Witness.A₀_subset_highVertices
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q : ℕ}
    (h : EC3Witness G n q) : h.A₀ ⊆ highVertices G n := by
  intro a ha
  exact mem_highVertices.mpr (h.high_A₀ a ha)

/-- In the only parity in which Zhao's near-ideal case occurs, the global
high-degree hypothesis supplies a high vertex outside the normalized set
`A₀`. -/
theorem EC3Witness.exists_high_outside_A₀_of_even
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q : ℕ}
    (h : EC3Witness G n q) (hn : n % 2 = 0) :
    ∃ v ∈ highVertices G n, v ∉ h.A₀ := by
  have hceil : (n + 1) / 2 = n / 2 := by omega
  have hlt : h.A₀.card < (highVertices G n).card := by
    rw [h.card_A₀, hceil]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) h.high_count
  exact Finset.exists_mem_notMem_of_card_lt_card hlt

/-- A convenient form of the degree hypothesis after restricting to a set:
at most `q` vertices of `S` fail to be neighbors of `v`. -/
def MissesAtMost (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) (q : ℕ) : Prop :=
  S.card ≤ Erdos547EC2.degreeInto G v S + q

/-- The vertices of `S` not adjacent to `v` (including `v` itself when it
belongs to `S`). -/
def missingVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) : Finset V :=
  S.filter fun w => ¬G.Adj v w

theorem degreeInto_add_missingVertices
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) :
    Erdos547EC2.degreeInto G v S + (missingVertices G v S).card = S.card := by
  classical
  unfold Erdos547EC2.degreeInto missingVertices
  exact Finset.card_filter_add_card_filter_not _

theorem missesAtMost_iff_card_missing_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) (q : ℕ) :
    MissesAtMost G v S q ↔ (missingVertices G v S).card ≤ q := by
  unfold MissesAtMost
  have hpart := degreeInto_add_missingVertices G v S
  omega

theorem MissesAtMost.mono_set
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v : V} {R S : Finset V} {q : ℕ}
    (h : MissesAtMost G v S q) (hRS : R ⊆ S) :
    MissesAtMost G v R q := by
  rw [missesAtMost_iff_card_missing_le] at h ⊢
  apply (Finset.card_le_card ?_).trans h
  intro w hw
  simp only [missingVertices, Finset.mem_filter] at hw ⊢
  exact ⟨hRS hw.1, hw.2⟩

theorem missesAtMost_of_degreeInto_sub
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) (q : ℕ)
    (h : S.card - q ≤ Erdos547EC2.degreeInto G v S) :
    MissesAtMost G v S q := by
  unfold MissesAtMost
  omega

theorem degreeInto_sdiff_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S R : Finset V) :
    Erdos547EC2.degreeInto G v S - R.card ≤
      Erdos547EC2.degreeInto G v (S \ R) := by
  classical
  unfold Erdos547EC2.degreeInto
  have hsub :
      (S.filter fun w => G.Adj v w) \ R ⊆
        ((S \ R).filter fun w => G.Adj v w) := by
    intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_filter] at hw ⊢
    exact ⟨⟨hw.1.1, hw.2⟩, hw.1.2⟩
  have hc := Finset.card_le_card hsub
  have hcard :
      (S.filter fun w => G.Adj v w).card - R.card ≤
        ((S.filter fun w => G.Adj v w) \ R).card := by
    rw [Finset.card_sdiff]
    have hinter : (R ∩ (S.filter fun w => G.Adj v w)).card ≤ R.card :=
      Finset.card_le_card Finset.inter_subset_left
    omega
  exact hcard.trans hc

/-- Removing a set of host vertices worsens a defect bound by at most the
number removed. -/
theorem MissesAtMost.sdiff
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v : V} {S R : Finset V} {q : ℕ}
    (h : MissesAtMost G v S q) :
    MissesAtMost G v (S \ R) (q + R.card) := by
  unfold MissesAtMost at h ⊢
  rw [Finset.card_sdiff]
  have hd := degreeInto_sdiff_lower G v S R
  omega

theorem degreeInto_eq_neighborFinset_inter
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S : Finset V) :
    Erdos547EC2.degreeInto G v S = (G.neighborFinset v ∩ S).card := by
  classical
  unfold Erdos547EC2.degreeInto
  apply congrArg Finset.card
  ext w
  simp [G.mem_neighborFinset, and_comm]

/-- Proposition 7.3 applied to the normalized EC3 witness.  This is exactly
the pair `A,B₁` and estimates (7.5), with all square-root rounding retained
in `q*n ≤ s(s+1)`. -/
theorem EC3Witness.exists_prunedSide
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1)) :
    ∃ B₁ : Finset V,
      B₁ ⊆ h.V₁ \ h.A₀ ∧
      (h.V₁ \ h.A₀).card ≤ B₁.card + s ∧
      (∀ a ∈ h.A₀, B₁.card - q ≤ Erdos547EC2.degreeInto G a B₁) ∧
      ∀ b ∈ B₁, h.A₀.card - s ≤ Erdos547EC2.degreeInto G b h.A₀ := by
  classical
  have hAB : Disjoint h.A₀ (h.V₁ \ h.A₀) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp hxB).2 hxA
  have hXtoB : ∀ a ∈ h.A₀,
      (h.V₁ \ h.A₀).card - q ≤
        Erdos547EC2.degreeInto G a (h.V₁ \ h.A₀) := by
    intro a ha
    have hmissV₁ : MissesAtMost G a h.V₁ q := by
      apply missesAtMost_of_degreeInto_sub
      simpa [h.card_V₁] using h.dense_A₀_V₁ a ha
    have hmissB := hmissV₁.mono_set (Finset.sdiff_subset : h.V₁ \ h.A₀ ⊆ h.V₁)
    unfold MissesAtMost at hmissB
    omega
  have hAcard : h.A₀.card ≤ n := by
    calc
      h.A₀.card ≤ h.V₁.card := Finset.card_le_card h.A₀_subset
      _ = n := h.card_V₁
  obtain ⟨B₁, hB₁, _hdiscardProduct, _hdiscard, hBcard, hleft, hright⟩ :=
    Erdos547EC2.zhao_proposition_7_3_discrete74 G hAB hXtoB hAcard hscale
  exact ⟨B₁, hB₁, hBcard, hleft, hright⟩

/-- The exact package of estimates (7.4)--(7.5) used by Lemmas 7.8 and
7.10, with a common enlarged defect `r`. -/
theorem EC3Witness.exists_prunedPair
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s r : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (hqr : q ≤ r) (hsr : s ≤ r) :
    ∃ B₁ : Finset V,
      B₁ ⊆ h.V₁ \ h.A₀ ∧ Disjoint h.A₀ B₁ ∧
      n / 2 - s ≤ B₁.card ∧ B₁.card ≤ n / 2 ∧
      (∀ a ∈ h.A₀, h.A₀.card - r ≤ (G.neighborFinset a ∩ h.A₀).card) ∧
      (∀ b ∈ B₁, h.A₀.card - r ≤ (G.neighborFinset b ∩ h.A₀).card) ∧
      (∀ a ∈ h.A₀, B₁.card - q ≤ (G.neighborFinset a ∩ B₁).card) := by
  classical
  obtain ⟨B₁, hBsub, hBcard, hAB, hBA⟩ := h.exists_prunedSide hscale
  have hcomp : (h.V₁ \ h.A₀).card = n / 2 := by
    rw [Finset.card_sdiff_of_subset h.A₀_subset, h.card_V₁, h.card_A₀]
    omega
  have hdisj : Disjoint h.A₀ B₁ := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp (hBsub hxB)).2 hxA
  have hupper : B₁.card ≤ n / 2 := by
    rw [← hcomp]
    exact Finset.card_le_card hBsub
  have hlower : n / 2 - s ≤ B₁.card := by
    rw [← hcomp]
    omega
  have hAA : ∀ a ∈ h.A₀,
      h.A₀.card - r ≤ (G.neighborFinset a ∩ h.A₀).card := by
    intro a ha
    have hmissV₁ : MissesAtMost G a h.V₁ q := by
      apply missesAtMost_of_degreeInto_sub
      simpa [h.card_V₁] using h.dense_A₀_V₁ a ha
    have hmissA := hmissV₁.mono_set h.A₀_subset
    unfold MissesAtMost at hmissA
    rw [degreeInto_eq_neighborFinset_inter] at hmissA
    omega
  have hBA' : ∀ b ∈ B₁,
      h.A₀.card - r ≤ (G.neighborFinset b ∩ h.A₀).card := by
    intro b hb
    rw [← degreeInto_eq_neighborFinset_inter]
    exact le_trans (by omega) (hBA b hb)
  have hAB' : ∀ a ∈ h.A₀,
      B₁.card - q ≤ (G.neighborFinset a ∩ B₁).card := by
    intro a ha
    rw [← degreeInto_eq_neighborFinset_inter]
    exact hAB a ha
  exact ⟨B₁, hBsub, hdisj, hlower, hupper, hAA, hBA', hAB'⟩

@[simp] theorem EC3Witness.card_V₁_sdiff_A₀
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q : ℕ}
    (h : EC3Witness G n q) :
    (h.V₁ \ h.A₀).card = n / 2 := by
  rw [Finset.card_sdiff_of_subset h.A₀_subset, h.card_V₁, h.card_A₀]
  omega

/-- The ideal-partition branch of Zhao Lemma 7.4, obtained by applying the
full finite Lemma 7.8 to the pruned host pair. -/
theorem EC3Witness.contains_of_idealPartition
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s r : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (hqr : q ≤ r) (hsr : s ≤ r) (hsq : s + q ≤ r)
    (hrsource : 1782 * r ≤ n)
    (hrpos : 0 < r)
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (U₁ U₂ : Finset A)
    (hU : Erdos547b.ZhaoLemma77.IsIdealPartition r T U₁ U₂) :
    T ⊑ G := by
  classical
  obtain ⟨B₁, hBsub, hABdisj, hBlower, hBupper, hAA, hBA, hAB⟩ :=
    h.exists_prunedPair hscale hqr hsr
  let W₂ := Erdos547b.ZhaoLemma77.leavesIn T U₂
  let active := U₂ \ W₂
  let side : A → Fin 2 := fun x ↦ if x ∈ U₂ then 1 else 0
  have hUdisj : Disjoint U₁ U₂ := hU.partition.1
  have hcoverMem (x : A) : x ∈ U₁ ∨ x ∈ U₂ := by
    have hxold := (Finset.ext_iff.mp hU.partition.2 x).mpr (Finset.mem_univ x)
    exact (@Finset.mem_union A (fun a b ↦ Classical.propDecidable (a = b)) U₁ U₂ x).mp hxold
  have hUcover : U₁ ∪ U₂ = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact hcoverMem x
  have hsideZero : (Finset.univ.filter fun x ↦ side x = 0) = U₁ := by
    ext x
    by_cases hx₂ : x ∈ U₂
    · have hx₁ : x ∉ U₁ := fun hx₁ ↦ Finset.disjoint_left.mp hUdisj hx₁ hx₂
      simp [side, hx₂, hx₁]
    · have hx₁ : x ∈ U₁ := by
        exact (hcoverMem x).resolve_right hx₂
      simp [side, hx₂, hx₁]
  have hsideOne : (Finset.univ.filter fun x ↦ side x = 1) = U₂ := by
    ext x
    simp [side]
  have hpartZero : Erdos547b.ZhaoFact72.partCount side 0 = U₁.card := by
    simpa [Erdos547b.ZhaoFact72.partCount] using congrArg Finset.card hsideZero
  have hpartOne : Erdos547b.ZhaoFact72.partCount side 1 = U₂.card := by
    simpa [Erdos547b.ZhaoFact72.partCount] using congrArg Finset.card hsideOne
  have hsumU : U₁.card + U₂.card = n + 1 := by
    have hc := Finset.card_union_of_disjoint hUdisj
    rw [hUcover, Finset.card_univ, hcardT] at hc
    exact hc.symm
  have hU₁cap : U₁.card ≤ h.A₀.card := by
    rw [h.card_A₀]
    have horder := hU.card_le
    omega
  have hleafIff (x : A) :
      Erdos547b.ZhaoLemma77.IsLeaf T x ↔ T.degree x = 1 := by
    unfold Erdos547b.ZhaoLemma77.IsLeaf
    apply iff_of_eq
    apply congrArg (fun d : ℕ ↦ d = 1)
    apply Erdos547b.ZhaoLemma77Full74.degree_instance_eq
  have hindep : ∀ ⦃u v⦄, T.Adj u v → side u = 1 → side v ≠ 1 := by
    intro u v huv hu hv
    have hu₂ : u ∈ U₂ := by simpa [side] using hu
    have hv₂ : v ∈ U₂ := by simpa [side] using hv
    exact hU.right_independent hu₂ hv₂ (T.ne_of_adj huv) huv
  have hactive : ∀ x ∈ active, side x = 1 := by
    intro x hx
    simp [side, active, (Finset.mem_sdiff.mp hx).1]
  have hdeferred : ∀ x, side x = 1 → x ∉ active → T.degree x = 1 := by
    intro x hxside hxactive
    have hx₂ : x ∈ U₂ := by simpa [side] using hxside
    by_contra hxdeg
    apply hxactive
    apply Finset.mem_sdiff.mpr
    refine ⟨hx₂, ?_⟩
    simp [W₂, Erdos547b.ZhaoLemma77.leavesIn, Erdos547b.ZhaoLemma77.IsLeaf, hxdeg]
  have hleafZero :
      (Finset.univ.filter fun x ↦ side x = 0 ∧ T.degree x = 1) =
        Erdos547b.ZhaoLemma77.leavesIn T U₁ := by
    ext x
    simp only [Erdos547b.ZhaoLemma77.leavesIn, Finset.mem_filter,
      Finset.mem_univ, true_and, Erdos547b.ZhaoLemma77.IsLeaf]
    constructor
    · intro hx
      have hxU₁ : x ∈ U₁ := by
        rw [← hsideZero]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hx.1
      exact ⟨hxU₁, hx.2⟩
    · intro hx
      have hxzero : side x = 0 := by
        rw [show x ∈ U₁ ↔ x ∈ Finset.univ.filter (fun y ↦ side y = 0) by rw [hsideZero]] at hx
        exact (Finset.mem_filter.mp hx.1).2
      exact ⟨hxzero, hx.2⟩
  have hWsub : W₂ ⊆ U₂ := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hWcard : 2 * r ≤ W₂.card := by
    have heq : W₂ = U₂.filter fun x ↦ T.degree x = 1 := by
      ext x
      simp only [W₂, Erdos547b.ZhaoLemma77.leavesIn, Finset.mem_filter]
      exact and_congr_right (fun _ ↦ hleafIff x)
    rw [heq]
    convert hU.right_leaves using 1
    apply congrArg Finset.card
    ext x
    simp only [Erdos547b.ZhaoLemma77.leavesIn, Finset.mem_filter]
    apply and_congr_right
    intro _
    unfold Erdos547b.ZhaoLemma77.IsLeaf
    apply iff_of_eq
    apply congrArg (fun d : ℕ ↦ d = 1)
    apply Erdos547b.ZhaoLemma77Full74.degree_instance_eq
  have hactiveNonleaf : ∀ x ∈ active, T.degree x ≠ 1 := by
    intro x hx hxdeg
    exact (Finset.mem_sdiff.mp hx).2 (by
      simp [W₂, Erdos547b.ZhaoLemma77.leavesIn,
        Erdos547b.ZhaoLemma77.IsLeaf, (Finset.mem_sdiff.mp hx).1, hxdeg])
  have hactiveLt : active.card < U₁.card := by
    have ht := Erdos547b.ZhaoFact72.card_nonleaves_second_lt_first
      T hT side hindep active hactive hactiveNonleaf
    simpa [hpartZero] using ht
  have hactiveCard : active.card ≤ n / 2 - r := by
    have hac : active.card = U₂.card - W₂.card := by
      simp [active, Finset.card_sdiff_of_subset hWsub]
    omega
  have hrn : r < n := by omega
  have hedge : T.edgeFinset.card = n := by
    have ht := hT.card_edgeFinset
    omega
  have hleftLeaves :
      5 * r ≤ (Finset.univ.filter fun x ↦ side x = 0 ∧ T.degree x = 1).card := by
    rw [hleafZero]
    convert hU.left_leaves using 1
    apply congrArg Finset.card
    ext x
    simp only [Erdos547b.ZhaoLemma77.leavesIn, Finset.mem_filter]
    apply and_congr_right
    intro _
    unfold Erdos547b.ZhaoLemma77.IsLeaf
    apply iff_of_eq
    apply congrArg (fun d : ℕ ↦ d = 1)
    apply Erdos547b.ZhaoLemma77Full74.degree_instance_eq
  have hXYdeg : ∀ a ∈ h.A₀,
      max (B₁.card - r) active.card ≤ (G.neighborFinset a ∩ B₁).card := by
    intro a ha
    apply max_le
    · exact le_trans (by omega) (hAB a ha)
    · exact le_trans (by omega) (hAB a ha)
  have hglobal : ∀ a ∈ h.A₀, T.edgeFinset.card ≤ G.degree a := by
    intro a ha
    simpa [hedge] using h.high_A₀ a ha
  have hfirst : ∃ root, side root = 0 := by
    have hleftPos : 0 < U₁.card := by
      have hleafPos : 0 <
          (Finset.univ.filter fun x ↦ side x = 0 ∧ T.degree x = 1).card := by
        omega
      have hsub : (Finset.univ.filter fun x ↦ side x = 0 ∧ T.degree x = 1) ⊆ U₁ := by
        intro x hx
        rw [← hsideZero]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2.1⟩
      exact hleafPos.trans_le (Finset.card_le_card hsub)
    obtain ⟨root, hroot⟩ := Finset.card_pos.mp hleftPos
    refine ⟨root, ?_⟩
    rw [← hsideZero] at hroot
    exact (Finset.mem_filter.mp hroot).2
  exact Erdos547b.ZhaoLemma78Full74.lemma7_8_unrooted
    T G n r hrn hT (by omega) side hindep active hactive hdeferred hleftLeaves
    h.A₀ B₁ hABdisj (by simpa [hpartZero] using hU₁cap) hAA hBA hXYdeg hglobal hfirst

/-- The large-bipartition-gap branch of Zhao Lemma 7.4.  It is precisely the
application of Fact 7.2(1) after Proposition 7.3. -/
theorem EC3Witness.contains_of_small_colorClass
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (c : T.Coloring (Fin 2))
    (hsmall : min (Coloring.partCard c 0) (Coloring.partCard c 1) ≤
      min ((h.V₁ \ h.A₀).card - s - q) (h.A₀.card - s)) :
    T ⊑ G := by
  classical
  obtain ⟨B₁, hB₁B, hBcard, hcrossA, hcrossB⟩ := h.exists_prunedSide hscale
  let m := min (Coloring.partCard c 0) (Coloring.partCard c 1)
  have hmBminus : m ≤ B₁.card - q := by
    have h₁ : m ≤ (h.V₁ \ h.A₀).card - s - q := hsmall.trans (min_le_left _ _)
    omega
  have hmAminus : m ≤ h.A₀.card - s :=
    hsmall.trans (min_le_right _ _)
  have hmA : m ≤ h.A₀.card := hmAminus.trans (Nat.sub_le _ _)
  have hmB : m ≤ B₁.card := hmBminus.trans (Nat.sub_le _ _)
  apply Erdos547b.EC1Scratch.fact72_part1 T G hT c h.A₀ B₁
  · exact (by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      exact (Finset.mem_sdiff.mp (hB₁B hxB)).2 hxA)
  · exact hmA
  · exact hmB
  · intro a ha
    exact hmBminus.trans (hcrossA a ha)
  · intro b hb
    exact hmAminus.trans (hcrossB b hb)
  · intro a ha
    simpa [hcardT] using h.high_A₀ a ha

/-- Source-style numerical corollary of the preceding branch: a color class
of size at most `floor(n/2)-s-q` is small enough for the pruned pair. -/
theorem EC3Witness.contains_of_small_colorClass_floor
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (c : T.Coloring (Fin 2))
    (hsmall : min (Coloring.partCard c 0) (Coloring.partCard c 1) ≤
      n / 2 - s - q) :
    T ⊑ G := by
  apply h.contains_of_small_colorClass hscale T hT hcardT c
  rw [h.card_V₁_sdiff_A₀, h.card_A₀]
  apply le_min
  · exact hsmall
  · omega

/-- The literal large-gap subcase of Zhao Lemma 7.4. -/
theorem EC3Witness.contains_of_colorGap
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (c : T.Coloring (Fin 2))
    (hgap : 2 * (s + q) + 1 ≤ colorGap c) :
    T ⊑ G := by
  apply h.contains_of_small_colorClass_floor hscale T hT hcardT c
  have hsmall := min_partCard_le_floor_sub_of_gap c hcardT hgap
  omega

/-- All integral estimates needed in the low-leaf branch follow from the
rounding-safe source hierarchy.  The leaf budget there is `33 * (s + q)`;
`1782 = 2 * 27 * 33` leaves enough room for both color classes after the
leaf deletion, while also implying Zhao's `7q < floor(n/2)` packing bound. -/
theorem source_numeric_estimates {n q s : ℕ}
    (hsource : 1782 * (s + q) ≤ n) (hrpos : 0 < s + q) :
    q ≤ 33 * (s + q) ∧
    s ≤ 33 * (s + q) ∧
    7 * q < n / 2 ∧
    26 * (33 * (s + q)) ≤ n / 2 - s ∧
    26 * (33 * (s + q)) ≤ (n + 1) / 2 := by
  omega

/-- Arithmetic used in the ideal-partition branch.  If `w` leaves are
deleted from the larger side, Fact 6.9 and the additional `2r` leaf reserve
together put the active remainder below `floor(n/2)-r`. -/
theorem ideal_active_card_bound
    {n r u₁ u₂ w : ℕ}
    (hsum : u₁ + u₂ = n + 1) (horder : u₁ ≤ u₂)
    (hwle : w ≤ u₂) (hreserve : 2 * r ≤ w)
    (himbalance : u₂ - u₁ + 1 ≤ w) :
    u₁ ≤ (n + 1) / 2 ∧ u₂ - w ≤ n / 2 - r := by
  omega

/-- The set of selected midpoints in the maximal two-path construction has
the same cardinality as its index set and is disjoint from both `A` and
`B₁`. -/
theorem selected_middles_card_and_disjoint
    {k : ℕ} {middle : Fin k → V} (J : Finset (Fin k))
    (hmiddleInj : Function.Injective middle)
    {A B₁ : Finset V} (hmiddleOut : ∀ i, middle i ∉ A ∪ B₁) :
    (Erdos547EC2.selectedTwoPathMiddles middle J).card = J.card ∧
      Disjoint A (Erdos547EC2.selectedTwoPathMiddles middle J) ∧
      Disjoint B₁ (Erdos547EC2.selectedTwoPathMiddles middle J) := by
  classical
  constructor
  · exact Erdos547EC2.card_selectedTwoPathMiddles J hmiddleInj
  constructor <;> rw [Finset.disjoint_left] <;> intro x hx hxm
  · obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.mp hxm
    exact (hmiddleOut i) (Finset.mem_union_left _ hx)
  · obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.mp hxm
    exact (hmiddleOut i) (Finset.mem_union_right _ hx)

/-- The cardinal range for Zhao's augmented side `B = B₁ ∪ B₂`.
The upper bound is built into the choice of `B₂`; the lower bound is the
maximal-two-path counting claim. -/
theorem augmented_side_card_bounds
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {n q k : ℕ} {A B₁ : Finset V}
    {left middle right : Fin k → V} (J : Finset (Fin k))
    (hVcard : Fintype.card V = 2 * n)
    (hAB₁ : Disjoint A B₁)
    (hAcard : A.card = (n + 1) / 2)
    (hlarge : ∀ v ∈ A, n ≤ Erdos547EC2.degreeInto G v Finset.univ)
    (hB₁card : n / 2 - q ≤ B₁.card)
    (hB₁upper : B₁.card ≤ n / 2)
    (hq : 7 * q < n / 2)
    (hleftA : ∀ i, left i ∈ A)
    (hrightA : ∀ i, right i ∈ A)
    (hmiddleOut : ∀ i, middle i ∉ A ∪ B₁)
    (hleftInj : Function.Injective left)
    (hmiddleInj : Function.Injective middle)
    (hrightInj : Function.Injective right)
    (hendsDisj : Disjoint (Finset.univ.image left) (Finset.univ.image right))
    (hpathLeft : ∀ i, G.Adj (left i) (middle i))
    (hpathRight : ∀ i, G.Adj (middle i) (right i))
    (hJcard : J.card = min k (n - A.card - B₁.card))
    (hmax : ∀ x ∈ A \ Erdos547EC2.twoPathEnds left right,
      ∀ z ∈ A \ Erdos547EC2.twoPathEnds left right, x ≠ z →
      ∀ y ∉ A ∪ B₁ ∪ Erdos547EC2.allTwoPathMiddles middle,
        ¬(G.Adj x y ∧ G.Adj y z)) :
    n / 2 - 1 ≤
        (B₁ ∪ Erdos547EC2.selectedTwoPathMiddles middle J).card ∧
      (B₁ ∪ Erdos547EC2.selectedTwoPathMiddles middle J).card ≤ n / 2 := by
  classical
  let B₂ := Erdos547EC2.selectedTwoPathMiddles middle J
  have hcount := Erdos547EC2.zhao_lemma74_maximal_two_path_count G J hVcard
    hAB₁ hAcard hlarge hB₁card hq hleftA hrightA hmiddleOut hleftInj
    hmiddleInj hrightInj hendsDisj hpathLeft hpathRight hJcard hmax
  obtain ⟨hB₂card, hAB₂, hB₁B₂⟩ :=
    selected_middles_card_and_disjoint J hmiddleInj hmiddleOut
  have hAunionB : (A ∪ B₁ ∪ B₂).card = A.card + (B₁ ∪ B₂).card := by
    rw [Finset.union_assoc,
      Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hAB₁, hAB₂⟩)]
  have hBcard : (B₁ ∪ B₂).card = B₁.card + B₂.card :=
    Finset.card_union_of_disjoint hB₁B₂
  have hJle : J.card ≤ n - A.card - B₁.card := by
    rw [hJcard]
    exact min_le_right _ _
  change n / 2 - 1 ≤ (B₁ ∪ B₂).card ∧ (B₁ ∪ B₂).card ≤ n / 2
  have hhalf : (n + 1) / 2 + n / 2 = n := by omega
  change n - 1 ≤ (A ∪ B₁ ∪ B₂).card at hcount
  rw [hAunionB, hAcard, hBcard, hB₂card] at hcount
  constructor
  · rw [hBcard, hB₂card]
    omega
  · rw [hBcard, hB₂card]
    have hABcard : A.card + B₁.card ≤ n := by
      have hAhalf : A.card = n - n / 2 := by omega
      rw [hAhalf]
      omega
    omega

/-- Zhao's noncomputable leaf finset and the explicit degree-one finset used
in this file have the same cardinality; this also transports across the two
extensionally equal local-finiteness instances that arise in the imported
development of Lemma 7.7. -/
theorem leaves_card_eq_zhaoLeaves
    (T : SimpleGraph A) [DecidableRel T.Adj] :
    (leaves T).card = (Erdos547b.ZhaoLemma77.leaves T).card := by
  classical
  apply congrArg Finset.card
  ext x
  simp only [leaves, Erdos547b.ZhaoLemma77.leaves, Finset.mem_filter,
    Finset.mem_univ, true_and]
  unfold Erdos547b.ZhaoLemma77.IsLeaf
  apply iff_of_eq
  apply congrArg (fun d : ℕ ↦ d = 1)
  apply Erdos547b.ZhaoLemma77Full74.degree_instance_eq

/-- The large-leaf part of Lemma 7.4 reduced to its final near-ideal branch.
All other alternatives of Lemma 7.7 are discharged by the already checked
large-gap and ideal-partition embedding theorems. -/
theorem EC3Witness.contains_of_manyLeaves_or_nearIdeal
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (hsource : 1782 * (s + q) ≤ n) (hrpos : 0 < s + q)
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (hmany : 33 * (s + q) ≤ (leaves T).card) :
    T ⊑ G ∨ ∃ U₁ U₂,
      Erdos547b.ZhaoLemma77.IsNearIdealPartition (s + q) n T U₁ U₂ := by
  classical
  letI : DecidableRel T.Adj := fun a b ↦ Classical.propDecidable (T.Adj a b)
  let c : T.Coloring (Fin 2) := Classical.choice hT.isBipartite
  let C₀ := Erdos547b.EC1Scratch.colorClassFinset c 0
  let C₁ := Erdos547b.EC1Scratch.colorClassFinset c 1
  have hproper : IsProperBipartition T C₀ C₁ :=
    properBipartition_colorClasses T hT c
  have hedge : T.edgeFinset.card = n := by
    have ht := hT.card_edgeFinset
    omega
  have hmanyC : 33 * (s + q) ≤ (leaves T).card := by
    convert hmany using 1
    apply congrArg Finset.card
    ext x
    simp only [leaves, Finset.mem_filter, Finset.mem_univ, true_and]
    apply iff_of_eq
    apply congrArg (fun d : ℕ ↦ d = 1)
    apply Erdos547b.ZhaoLemma77Full74.degree_instance_eq
  have hmanyZ :
      33 * (s + q) ≤ (Erdos547b.ZhaoLemma77.leaves T).card := by
    rw [← leaves_card_eq_zhaoLeaves T]
    exact hmanyC
  by_cases h01 : C₀.card ≤ C₁.card
  · rcases Erdos547b.ZhaoLemma77Full74.lemma7_7
      (s + q) n T hT C₀ C₁ hproper h01 (by
        have ht := hT.card_edgeFinset
        omega) hmanyZ with
      hgap | hideal | hnear
    · left
      apply h.contains_of_colorGap hscale T hT hcardT c
      have hp01 : Coloring.partCard c 0 ≤ Coloring.partCard c 1 := by
        simpa [C₀, C₁, Erdos547b.EC1Scratch.colorClassFinset_card] using h01
      rw [Erdos547b.ZhaoLemma77.bipartitionGap,
        Nat.dist_eq_sub_of_le h01] at hgap
      simpa [colorGap, max_eq_right hp01, min_eq_left hp01,
        C₀, C₁, Erdos547b.EC1Scratch.colorClassFinset_card] using hgap
    · left
      obtain ⟨U₁, U₂, hU⟩ := hideal
      exact h.contains_of_idealPartition hscale (by omega) (by omega)
        (by omega) hsource hrpos T hT hcardT U₁ U₂ hU
    · exact Or.inr hnear
  · have h10 : C₁.card ≤ C₀.card := by omega
    have hproper' : IsProperBipartition T C₁ C₀ :=
      { bipartite := hproper.bipartite.symm
        cover := by rw [Set.union_comm, hproper.cover]
        left_nonempty := hproper.right_nonempty
        right_nonempty := hproper.left_nonempty }
    rcases Erdos547b.ZhaoLemma77Full74.lemma7_7
      (s + q) n T hT C₁ C₀ hproper' h10 (by
        have ht := hT.card_edgeFinset
        omega) hmanyZ with
      hgap | hideal | hnear
    · left
      apply h.contains_of_colorGap hscale T hT hcardT c
      have hp10 : Coloring.partCard c 1 ≤ Coloring.partCard c 0 := by
        simpa [C₀, C₁, Erdos547b.EC1Scratch.colorClassFinset_card] using h10
      rw [Erdos547b.ZhaoLemma77.bipartitionGap,
        Nat.dist_eq_sub_of_le h10] at hgap
      simpa [colorGap, max_eq_left hp10, min_eq_right hp10,
        C₀, C₁, Erdos547b.EC1Scratch.colorClassFinset_card] using hgap
    · left
      obtain ⟨U₁, U₂, hU⟩ := hideal
      exact h.contains_of_idealPartition hscale (by omega) (by omega)
        (by omega) hsource hrpos T hT hcardT U₁ U₂ hU
    · exact Or.inr hnear

/-- A low-leaf host package embeds any sufficiently balanced source core.
The root and its host image are selected outside the reserved two-path
endpoints, after which Lemma 7.10 applies verbatim. -/
theorem lowLeafHostPackage_coreCopy
    {C : Type*} [Fintype C] [DecidableEq C]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B₁ : Finset V} {n l : ℕ}
    (P : Erdos547EC2.LowLeafHostPackage G A B₁ n l)
    (Tc : SimpleGraph C) [DecidableRel Tc.Adj]
    (U₁ U₂ : Finset C)
    (hTc : Tc.IsTree)
    (hTU : Tc.IsBipartiteWith (U₁ : Set C) (U₂ : Set C))
    (hcover : U₁ ∪ U₂ = Finset.univ)
    (hleaves : (Erdos547EC2.leafVertices Tc).card ≤ l)
    (hU₁large : 26 * l ≤ U₁.card)
    (hU₂large : 26 * l ≤ U₂.card)
    (hU₁cap : U₁.card ≤ A.card)
    (hU₂cap : U₂.card ≤ P.B.card)
    (hlpos : 0 < l) :
    ∃ f : Tc.Copy G,
      (∀ x ∈ U₁, f x ∈ A) ∧ (∀ x ∈ U₂, f x ∈ P.B) := by
  classical
  have hU₁pos : 0 < U₁.card := by omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hU₁pos
  have hendcard := P.paths.card_endpoints
  have hendslt : P.paths.endpoints.card < A.card := by
    rw [hendcard]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 P.card_B₂_le) (by omega)
  have hdiffpos : 0 < (A \ P.paths.endpoints).card := by
    rw [Finset.card_sdiff_of_subset P.paths.endpoints_subset]
    omega
  obtain ⟨a, haDiff⟩ := Finset.card_pos.mp hdiffpos
  have haA : a ∈ A := (Finset.mem_sdiff.mp haDiff).1
  have haAvoid : a ∉ P.paths.endpoints := (Finset.mem_sdiff.mp haDiff).2
  obtain ⟨fH, _, hfU₁, hfU₂⟩ :=
    Erdos547b.ZhaoLemma710ApplicationAlt.zhao_lemma_7_10
      U₁ U₂ A P.B B₁ P.B₂ l z a hTc hTU hcover hz hleaves
      hU₁large hU₂large P.restricted_bipartite P.B_split P.B₁_B₂_disjoint
      hU₁cap hU₂cap P.left_degree_bound P.right_degree_bound P.card_B₂_le
      P.paths haA haAvoid
  let f : Tc.Copy G := (SimpleGraph.Copy.ofLE _ _ P.restricted_le).comp fH
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    simpa [f] using hfU₁ x hx
  · intro x hx
    simpa [f] using hfU₂ x hx

/-- Select the unique parents of a finite family of leaves and invoke the
global-degree extension theorem.  The cardinality-three hypothesis excludes
the only case in which two degree-one vertices can be adjacent. -/
theorem extend_leafStrip_coreCopy
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} (T : SimpleGraph A) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (hcard3 : 3 ≤ Fintype.card A)
    (E D : Finset A) (hleaf : ∀ d : D, T.degree d.1 = 1)
    (hparentSide : ∀ d : D, ∀ a, T.Adj d.1 a → a ∈ E)
    (core : (T.induce ({a : A | a ∉ D} : Set A)).Copy G)
    (hdegree : ∀ c : Erdos547b.ZhaoGlobalLeafExtension74.LeafCore D,
      c.1 ∈ E → n ≤ G.degree (core c)) :
    T ⊑ G := by
  classical
  let parentVertex : D → A := fun d ↦
    Classical.choose (degree_eq_one_iff_existsUnique_adj.mp (hleaf d))
  have hparentAdj : ∀ d : D, T.Adj d.1 (parentVertex d) := by
    intro d
    exact (Classical.choose_spec
      (degree_eq_one_iff_existsUnique_adj.mp (hleaf d))).1
  have hparentNot : ∀ d : D, parentVertex d ∉ D := by
    intro d hd
    have hpLeaf : T.degree (parentVertex d) = 1 := hleaf ⟨parentVertex d, hd⟩
    exact (Erdos547b.ZhaoLemma78Full74.not_adj_of_both_degree_one_of_three_le_card
      T hT (hleaf d) hpLeaf hcard3) (hparentAdj d)
  let parent : D → Erdos547b.ZhaoGlobalLeafExtension74.LeafCore D :=
    fun d ↦ ⟨parentVertex d, hparentNot d⟩
  exact Erdos547b.ZhaoGlobalLeafExtension74.global_degree_leaf_extension
    T G n hcardT hT D hleaf parent (fun d ↦ hparentAdj d) core
      (fun d ↦ hdegree (parent d) (hparentSide d _ (hparentAdj d)))

/-- Apply Lemma 7.10 to the tree obtained by deleting all leaves of the
right source class, then restore those leaves using the degree-`n` vertices
of the host's distinguished side. -/
theorem lowLeafHostPackage_contains_after_leafStrip
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A₀ B₁ : Finset V} {n l : ℕ}
    (P : Erdos547EC2.LowLeafHostPackage G A₀ B₁ n l)
    (hhigh : ∀ a ∈ A₀, n ≤ G.degree a)
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (E O : Finset A) (hpart : IsProperBipartition T E O)
    (hEO : E.card ≤ O.card)
    (hleaves : (Erdos547EC2.leafVertices T).card ≤ l)
    (hElarge : 26 * l ≤ E.card)
    (hOcoreLarge : 26 * l ≤
      (Erdos547b.ZhaoLowLeafCore74.coreRight T O).card)
    (hEcap : E.card ≤ A₀.card)
    (hOcap : (Erdos547b.ZhaoLowLeafCore74.coreRight T O).card ≤ P.B.card)
    (hlpos : 0 < l) (hcard3 : 3 ≤ Fintype.card A) :
    T ⊑ G := by
  classical
  let D := Erdos547b.ZhaoLowLeafCore74.deletedLeaves T O
  let Tc := Erdos547b.ZhaoLowLeafCore74.core T O
  let U₁ := Erdos547b.ZhaoLowLeafCore74.coreLeft T E O
  let U₂ := Erdos547b.ZhaoLowLeafCore74.coreRight T O
  have hC := Erdos547b.ZhaoLowLeafCore74.coreWitness T E O hT hpart hEO
  have hcoreLeavesZ :=
    Erdos547b.ZhaoLowLeafCore74.card_leafVertices_core_le T E O hT hpart
  have hcoreLeaves : (Erdos547EC2.leafVertices Tc).card ≤ l := by
    have hle : (Erdos547b.ZhaoLemma710.leafVertices Tc).card ≤ l :=
      hcoreLeavesZ.trans (by
        simpa [Erdos547b.ZhaoLemma710.leafVertices,
          Erdos547EC2.leafVertices] using hleaves)
    simpa [Erdos547b.ZhaoLemma710.leafVertices,
      Erdos547EC2.leafVertices] using hle
  obtain ⟨coreCopy, hfU₁, _hfU₂⟩ :=
    lowLeafHostPackage_coreCopy P Tc U₁ U₂ hC.isTree hC.bipartite hC.cover
      hcoreLeaves (by simpa [U₁, hC.card_left] using hElarge)
      (by simpa [U₂] using hOcoreLarge)
      (by simpa [U₁, hC.card_left] using hEcap)
      (by simpa [U₂] using hOcap) hlpos
  let core : (T.induce ({a : A | a ∉ D} : Set A)).Copy G := by
    simpa [Tc, D, Erdos547b.ZhaoLowLeafCore74.core] using coreCopy
  refine extend_leafStrip_coreCopy T hT hcardT hcard3 E D ?_ ?_ core ?_
  · intro d
    exact (Erdos547b.ZhaoLowLeafCore74.mem_deletedLeaves.mp d.property).2
  · intro d a hda
    have hdO : d.1 ∈ O :=
      (Erdos547b.ZhaoLowLeafCore74.mem_deletedLeaves.mp d.property).1
    rcases hpart.bipartite.mem_of_adj hda with hEA | hOE
    · exact False.elim (Set.disjoint_left.mp hpart.bipartite.disjoint hEA.1 hdO)
    · exact hOE.2
  · intro c hcE
    apply hhigh (core c)
    change coreCopy c ∈ A₀
    apply hfU₁ c
    simpa [U₁, Erdos547b.ZhaoLowLeafCore74.coreLeft,
      Erdos547b.ZhaoLowLeafCore74.retainedPart] using hcE

/-- The EC3 inequalities construct the complete host package used in the
low-leaf branch.  The maximal two-path defect is `s+q`, while the source
leaf budget is Zhao's `33(s+q)`. -/
theorem EC3Witness.exists_lowLeafHostPackage
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (hsource : 1782 * (s + q) ≤ n) (hrpos : 0 < s + q) :
    ∃ B₁ : Finset V,
      Nonempty (Erdos547EC2.LowLeafHostPackage
        G h.A₀ B₁ n (33 * (s + q))) := by
  classical
  let r := s + q
  let l := 33 * r
  have hqr : q ≤ l := by simp [l, r]; omega
  have hsr : s ≤ l := by simp [l, r]; omega
  obtain ⟨B₁, _hBsub, hdisj, hBlower, hBupper, hAA, hBA, hAB⟩ :=
    h.exists_prunedPair hscale hqr hsr
  refine ⟨B₁, Erdos547EC2.exists_lowLeafHostPackage
    G h.A₀ B₁ n s r l h.card_host hdisj h.card_A₀ ?_
      hBlower hBupper hAA hBA ?_ ?_ ?_ ?_⟩
  · intro a ha
    change n ≤ Erdos547EC2.degreeInto G a Finset.univ
    rw [degreeInto_eq_neighborFinset_inter, Finset.inter_univ,
      G.card_neighborFinset_eq_degree]
    exact h.high_A₀ a ha
  · intro a ha
    exact le_trans (by simp [l, r]; omega) (hAB a ha)
  · simp [r]
  · simp [l, r]
    omega
  · simp [r]
    omega

/-- The regular low-leaf branch of Zhao's Lemma 7.4.  The only information
about the augmented host side used here is its proved lower bound
`floor(n/2)-1`; hence the exceptional path case is isolated precisely by the
failure of `hcoreFit`. -/
theorem EC3Witness.contains_of_lowLeaves_core_fits
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (hsource : 1782 * (s + q) ≤ n) (hrpos : 0 < s + q)
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (E O : Finset A) (hpart : IsProperBipartition T E O)
    (hEO : E.card ≤ O.card)
    (hleaves : (Erdos547EC2.leafVertices T).card ≤ 33 * (s + q))
    (hElarge : n / 2 - (s + q) < E.card)
    (hcoreFit : (Erdos547b.ZhaoLowLeafCore74.coreRight T O).card ≤ n / 2 - 1) :
    T ⊑ G := by
  classical
  obtain ⟨B₁, ⟨P⟩⟩ := h.exists_lowLeafHostPackage hscale hsource hrpos
  have hbounded :=
    Erdos547b.ZhaoLowLeafCore74.boundedCoreWitness_of_zhao_numbers
      T E O n (s + q) (33 * (s + q)) hT hpart hEO hcardT hleaves
        hElarge hsource rfl
  have hsum : E.card + O.card = n + 1 := by
    have hdisj : Disjoint E O :=
      Finset.disjoint_coe.mp hpart.bipartite.disjoint
    have hcover : E ∪ O = Finset.univ := by
      ext x
      have hx := Set.ext_iff.mp hpart.cover x
      simpa using hx
    rw [← Finset.card_union_of_disjoint hdisj, hcover,
      Finset.card_univ, hcardT]
  have hEcap : E.card ≤ h.A₀.card := by
    rw [h.card_A₀]
    omega
  have hElarge' : 26 * (33 * (s + q)) ≤ E.card := by
    rw [← hbounded.card_left]
    exact hbounded.left_large
  apply lowLeafHostPackage_contains_after_leafStrip P h.high_A₀ T hT hcardT
    E O hpart hEO hleaves hElarge' hbounded.right_large hEcap
  · exact hcoreFit.trans P.card_B_lower
  · omega
  · omega

theorem deletedLeaves_union_of_bipartition
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (E O : Finset A) (hpart : IsProperBipartition T E O) :
    Erdos547b.ZhaoLowLeafCore74.deletedLeaves T E ∪
      Erdos547b.ZhaoLowLeafCore74.deletedLeaves T O =
        Erdos547EC2.leafVertices T := by
  classical
  ext x
  have hx : x ∈ E ∨ x ∈ O := by
    have hx' := Set.ext_iff.mp hpart.cover x
    simpa using hx'
  simp only [Finset.mem_union,
    Erdos547b.ZhaoLowLeafCore74.mem_deletedLeaves, Finset.mem_filter,
    Finset.mem_univ, true_and, Erdos547EC2.leafVertices]
  constructor
  · rintro (⟨_, hd⟩ | ⟨_, hd⟩) <;> exact hd
  · intro hd
    exact hx.elim (fun hxE ↦ Or.inl ⟨hxE, hd⟩) (fun hxO ↦ Or.inr ⟨hxO, hd⟩)

theorem card_deletedLeaves_add_of_bipartition
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (E O : Finset A) (hpart : IsProperBipartition T E O) :
    (Erdos547b.ZhaoLowLeafCore74.deletedLeaves T E).card +
      (Erdos547b.ZhaoLowLeafCore74.deletedLeaves T O).card =
        (Erdos547EC2.leafVertices T).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · exact congrArg Finset.card (deletedLeaves_union_of_bipartition T E O hpart)
  · exact (Finset.disjoint_coe.mp hpart.bipartite.disjoint).mono
      (Erdos547b.ZhaoLowLeafCore74.deletedLeaves_subset_right E)
      (Erdos547b.ZhaoLowLeafCore74.deletedLeaves_subset_right O)

/-- Apart from the unique odd balanced exception in Zhao's low-leaf proof,
one orientation of the leaf-pruned source core fits the augmented host side.
The conclusion records the exceptional source invariant exactly: at most two
degree-one vertices. -/
theorem EC3Witness.contains_of_lowLeaves_or_atMostTwoLeaves
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (hsource : 1782 * (s + q) ≤ n) (hrpos : 0 < s + q)
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (E O : Finset A) (hpart : IsProperBipartition T E O)
    (hEO : E.card ≤ O.card)
    (hleaves : (Erdos547EC2.leafVertices T).card ≤ 33 * (s + q))
    (hElarge : n / 2 - (s + q) < E.card) :
    T ⊑ G ∨
      (Erdos547EC2.leafVertices T).card ≤ 2 ∧ n % 2 = 1 := by
  classical
  have hdisj : Disjoint E O :=
    Finset.disjoint_coe.mp hpart.bipartite.disjoint
  have hcover : E ∪ O = Finset.univ := by
    ext x
    have hx := Set.ext_iff.mp hpart.cover x
    simpa using hx
  have hsum : E.card + O.card = n + 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover,
      Finset.card_univ, hcardT]
  let DE := Erdos547b.ZhaoLowLeafCore74.deletedLeaves T E
  let DO := Erdos547b.ZhaoLowLeafCore74.deletedLeaves T O
  have hdelSum : DE.card + DO.card =
      (Erdos547EC2.leafVertices T).card := by
    simpa [DE, DO] using card_deletedLeaves_add_of_bipartition T E O hpart
  have hright :=
    Erdos547b.ZhaoLowLeafCore74.card_coreRight_le_card_left_sub_one
      T E O hT hpart hEO
  by_cases hfit :
      (Erdos547b.ZhaoLowLeafCore74.coreRight T O).card ≤ n / 2 - 1
  · exact Or.inl (h.contains_of_lowLeaves_core_fits hscale hsource hrpos
      T hT hcardT E O hpart hEO hleaves hElarge hfit)
  have hEeq : E.card = O.card := by omega
  have hEcard : E.card = n / 2 + 1 := by omega
  have hOcard : O.card = n / 2 + 1 := by omega
  have hnodd : n % 2 = 1 := by omega
  have hcoreO :
      (Erdos547b.ZhaoLowLeafCore74.coreRight T O).card = n / 2 := by
    omega
  have hDO : DO.card = 1 := by
    rw [Erdos547b.ZhaoLowLeafCore74.card_coreRight,
      Finset.card_sdiff_of_subset
        (Erdos547b.ZhaoLowLeafCore74.deletedLeaves_subset_right O)] at hcoreO
    simp [DO]
    omega
  by_cases hDE : 2 ≤ DE.card
  · have hpart' : IsProperBipartition T O E :=
      { bipartite := hpart.bipartite.symm
        cover := by rw [Set.union_comm, hpart.cover]
        left_nonempty := hpart.right_nonempty
        right_nonempty := hpart.left_nonempty }
    have hfit' :
        (Erdos547b.ZhaoLowLeafCore74.coreRight T E).card ≤ n / 2 - 1 := by
      rw [Erdos547b.ZhaoLowLeafCore74.card_coreRight,
        Finset.card_sdiff_of_subset
          (Erdos547b.ZhaoLowLeafCore74.deletedLeaves_subset_right E)]
      change E.card - DE.card ≤ n / 2 - 1
      omega
    exact Or.inl (h.contains_of_lowLeaves_core_fits hscale hsource hrpos
      T hT hcardT O E hpart' (by omega) hleaves (by omega) hfit')
  · right
    exact ⟨by omega, hnodd⟩

/-- The complete few-leaf reduction, including the small-color-class branch.
Only the path exception (a tree with at most two leaves) remains in the
right disjunct. -/
theorem EC3Witness.contains_of_fewLeaves_or_atMostTwoLeaves
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (hsource : 1782 * (s + q) ≤ n) (hrpos : 0 < s + q)
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (hfew : (leaves T).card < 33 * (s + q)) :
    T ⊑ G ∨
      (Erdos547EC2.leafVertices T).card ≤ 2 ∧ n % 2 = 1 := by
  classical
  let c : T.Coloring (Fin 2) := Classical.choice hT.isBipartite
  let C₀ := Erdos547b.EC1Scratch.colorClassFinset c 0
  let C₁ := Erdos547b.EC1Scratch.colorClassFinset c 1
  have hproper : IsProperBipartition T C₀ C₁ :=
    properBipartition_colorClasses T hT c
  have hleaves : (Erdos547EC2.leafVertices T).card ≤ 33 * (s + q) := by
    change (leaves T).card ≤ 33 * (s + q)
    omega
  by_cases hsmall : min (Coloring.partCard c 0) (Coloring.partCard c 1) ≤
      n / 2 - (s + q)
  · apply Or.inl
    apply h.contains_of_small_colorClass_floor hscale T hT hcardT c
    omega
  · have hlargeBoth :
        n / 2 - (s + q) < Coloring.partCard c 0 ∧
          n / 2 - (s + q) < Coloring.partCard c 1 := by
      simpa only [not_le, lt_min_iff] using hsmall
    by_cases h01 : C₀.card ≤ C₁.card
    · apply h.contains_of_lowLeaves_or_atMostTwoLeaves hscale hsource hrpos
        T hT hcardT C₀ C₁ hproper h01 hleaves
      simpa [C₀, Erdos547b.EC1Scratch.colorClassFinset_card] using hlargeBoth.1
    · have h10 : C₁.card ≤ C₀.card := by omega
      have hproper' : IsProperBipartition T C₁ C₀ :=
        { bipartite := hproper.bipartite.symm
          cover := by rw [Set.union_comm, hproper.cover]
          left_nonempty := hproper.right_nonempty
          right_nonempty := hproper.left_nonempty }
      apply h.contains_of_lowLeaves_or_atMostTwoLeaves hscale hsource hrpos
        T hT hcardT C₁ C₀ hproper' h10 hleaves
      simpa [C₁, Erdos547b.EC1Scratch.colorClassFinset_card] using hlargeBoth.2

/-- All already-formalized branches of Zhao's Lemma 7.4, with the two
specialized source configurations exposed for their dedicated reinsertion
arguments. -/
theorem EC3Witness.contains_or_nearIdeal_or_atMostTwoLeaves
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (hsource : 1782 * (s + q) ≤ n) (hrpos : 0 < s + q)
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1) :
    T ⊑ G ∨
      (∃ U₁ U₂, Erdos547b.ZhaoLemma77.IsNearIdealPartition
        (s + q) n T U₁ U₂) ∨
      ((Erdos547EC2.leafVertices T).card ≤ 2 ∧ n % 2 = 1) := by
  classical
  by_cases hmany : 33 * (s + q) ≤ (leaves T).card
  · rcases h.contains_of_manyLeaves_or_nearIdeal hscale hsource hrpos
      T hT hcardT hmany with hcopy | hnear
    · exact Or.inl hcopy
    · exact Or.inr (Or.inl hnear)
  · rcases h.contains_of_fewLeaves_or_atMostTwoLeaves hscale hsource hrpos
      T hT hcardT (by omega) with hcopy | hpath
    · exact Or.inl hcopy
    · exact Or.inr (Or.inr hpath)

end Erdos547b.ZhaoLemma74

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoNearIdealEC374

open Finset SimpleGraph

variable {V A : Type*} [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A]

def liftFinset (H S : Finset V) : Finset {v // v ∈ H} :=
  Finset.univ.filter fun v => v.1 ∈ S

@[simp] theorem mem_liftFinset {H S : Finset V} {v : {v // v ∈ H}} :
    v ∈ liftFinset H S ↔ v.1 ∈ S := by
  simp [liftFinset]

theorem card_liftFinset (H S : Finset V) (hSH : S ⊆ H) :
    (liftFinset H S).card = S.card := by
  classical
  let e : (v : {v // v ∈ H}) → v ∈ liftFinset H S → V :=
    fun v _ => v.1
  apply Finset.card_bij e
  · intro v hv
    exact mem_liftFinset.mp hv
  · intro v hv w hw heq
    exact Subtype.ext heq
  · intro v hv
    exact ⟨⟨v, hSH hv⟩, mem_liftFinset.mpr hv, rfl⟩

theorem card_neighbor_inter_liftFinset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H S : Finset V) (hSH : S ⊆ H) (v : {v // v ∈ H}) :
    (((G.induce (H : Set V)).neighborFinset v) ∩ liftFinset H S).card =
      (G.neighborFinset v.1 ∩ S).card := by
  classical
  let e : (w : {v // v ∈ H}) →
      w ∈ ((G.induce (H : Set V)).neighborFinset v ∩ liftFinset H S) → V :=
    fun w _ => w.1
  apply Finset.card_bij e
  · intro w hw
    have hw' := Finset.mem_inter.mp hw
    exact Finset.mem_inter.mpr ⟨by simpa using hw'.1, mem_liftFinset.mp hw'.2⟩
  · intro u hu w hw heq
    exact Subtype.ext heq
  · intro w hw
    refine ⟨⟨w, hSH (Finset.mem_inter.mp hw).2⟩, ?_, rfl⟩
    exact Finset.mem_inter.mpr ⟨by simpa using (Finset.mem_inter.mp hw).1,
      mem_liftFinset.mpr (Finset.mem_inter.mp hw).2⟩

/- Two nonadjacent vertices of degree at least half the order have a common
neighbor.  The two forbidden endpoints provide the two units of slack. -/
theorem exists_common_neighbor_of_half_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card V = 2 * n)
    {a v : V} (hav : a ≠ v) (hnot : ¬G.Adj a v)
    (ha : n ≤ G.degree a) (hv : n ≤ G.degree v) :
    ∃ b, G.Adj a b ∧ G.Adj b v ∧ b ≠ a ∧ b ≠ v := by
  classical
  let Na := G.neighborFinset a
  let Nv := G.neighborFinset v
  have haNa : a ∉ Na := by simp [Na]
  have haNv : a ∉ Nv := by simpa [Nv, G.adj_comm] using hnot
  have hvNa : v ∉ Na := by simpa [Na] using hnot
  have hvNv : v ∉ Nv := by simp [Nv]
  have hunion : Na ∪ Nv ⊆ (Finset.univ.erase a).erase v := by
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase]
    constructor
    · intro hxv
      subst x
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hvNa hx
      · exact hvNv hx
    constructor
    · intro hxa
      subst x
      rcases Finset.mem_union.mp hx with hx | hx
      · exact haNa hx
      · exact haNv hx
    · simp
  have hnpos : 0 < n := by
    have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
    rw [hcard] at hVpos
    omega
  have heraseCard : ((Finset.univ.erase a).erase v).card = 2 * n - 2 := by
    rw [Finset.card_erase_of_mem (by simp [hav.symm]), Finset.card_erase_of_mem (by simp),
      Finset.card_univ, hcard]
    omega
  have hunionCard : (Na ∪ Nv).card ≤ 2 * n - 2 := by
    rw [← heraseCard]
    exact Finset.card_le_card hunion
  have hNa : n ≤ Na.card := by
    simpa [Na] using ha
  have hNv : n ≤ Nv.card := by
    simpa [Nv] using hv
  have hsum := Finset.card_union_add_card_inter Na Nv
  have hinter : 2 ≤ (Na ∩ Nv).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (Na ∩ Nv).card)
  have hbNa := (Finset.mem_inter.mp hb).1
  have hbNv := (Finset.mem_inter.mp hb).2
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · exact (G.mem_neighborFinset _ _).mp hbNa
  · exact ((G.mem_neighborFinset _ _).mp hbNv).symm
  · intro h
    subst b
    exact haNa hbNa
  · intro h
    subst b
    exact hvNv hbNv

/- A high vertex outside the normalized EC3 set can always be connected to
`A₀` by a path of length one or two whose internal vertex also lies outside
`A₀`.  This replaces the switching argument in the paper and is the host
dichotomy used by all near-ideal branches. -/
theorem EC3Witness.exists_reserved_path_from_A₀
    (G : SimpleGraph V) [DecidableRel G.Adj] {n q : ℕ}
    (h : Erdos547b.ZhaoLemma74.EC3Witness G n q)
    (hneven : Even n) :
    ∃ a ∈ h.A₀, ∃ v₀ ∉ h.A₀,
      n ≤ G.degree v₀ ∧
      (G.Adj a v₀ ∨ ∃ b ∉ h.A₀, b ≠ v₀ ∧ G.Adj a b ∧ G.Adj b v₀) := by
  classical
  have hnmod : n % 2 = 0 := Nat.even_iff.mp hneven
  obtain ⟨v₀, hv₀high, hv₀A⟩ := h.exists_high_outside_A₀_of_even hnmod
  have hAcard : 0 < h.A₀.card := by
    rw [h.card_A₀]
    have hnlarge : 1 ≤ n := by
      have hhighle : (Erdos547b.ZhaoLemma74.highVertices G n).card ≤
          Fintype.card V := by
        exact Finset.card_le_card (Finset.subset_univ _)
      rw [h.card_host] at hhighle
      have hc := h.high_count
      omega
    omega
  obtain ⟨a, haA⟩ := Finset.card_pos.mp hAcard
  have hvdeg : n ≤ G.degree v₀ :=
    Erdos547b.ZhaoLemma74.mem_highVertices.mp hv₀high
  by_cases hav : G.Adj a v₀
  · exact ⟨a, haA, v₀, hv₀A, hvdeg, Or.inl hav⟩
  ·
    obtain ⟨b, hab, hbv, hba, hbvne⟩ :=
      exists_common_neighbor_of_half_degree G n h.card_host
        (by intro hEq; subst v₀; exact hv₀A haA) hav (h.high_A₀ a haA)
        hvdeg
    by_cases hbA : b ∈ h.A₀
    · exact ⟨b, hbA, v₀, hv₀A, hvdeg, Or.inl hbv⟩
    · exact ⟨a, haA, v₀, hv₀A, hvdeg,
        Or.inr ⟨b, hbA, hbvne, hab, hbv⟩⟩

/- Deleting the leaf `z` makes its degree-two parent `y` a leaf; deleting
that new leaf therefore leaves a tree. -/
theorem terminal_two_path_core_isTree
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (hT : T.IsTree) (z y x : A)
    (hz : T.degree z = 1) (hyz : T.Adj y z) (hy : T.degree y = 2)
    (hyx : T.Adj y x) (hxz : x ≠ z) :
    let Tz := T.induce {w | w ∉ ({z} : Finset A)}
    let y' : Erdos547b.LeafCore ({z} : Finset A) := ⟨y, by
      simpa using hyz.ne⟩
    (Tz.induce {w | w ∉ ({y'} : Finset _)}).IsTree := by
  classical
  let Tz := T.induce {w | w ∉ ({z} : Finset A)}
  let y' : Erdos547b.LeafCore ({z} : Finset A) := ⟨y, by
    simpa using hyz.ne⟩
  let x' : Erdos547b.LeafCore ({z} : Finset A) := ⟨x, by simpa using hxz⟩
  have hTz : Tz.IsTree := by
    constructor
    · exact Erdos547b.connected_induce_compl_of_leaves T
        (↑({z} : Finset A) : Set A) hT.connected
        (by
          intro v hv
          have hvz : v = z := by simpa using hv
          subst v
          exact hz)
        ⟨y, by simpa using hyz.ne⟩
    · exact hT.isAcyclic.induce _
  have hdegY : Tz.degree y' = 1 := by
    have hset : T.neighborFinset y ∩ ({w | w ∉ ({z} : Finset A)} : Set A).toFinset =
        (T.neighborFinset y).erase z := by
      ext w
      simp [and_comm]
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_map (f := Function.Embedding.subtype _),
      T.map_neighborFinset_induce]
    change #(T.neighborFinset y ∩
      ({w | w ∉ ({z} : Finset A)} : Set A).toFinset) = 1
    rw [hset, Finset.card_erase_of_mem, SimpleGraph.card_neighborFinset_eq_degree, hy]
    simpa using hyz
  constructor
  · exact Erdos547b.connected_induce_compl_of_leaves Tz
      (↑({y'} : Finset (Erdos547b.LeafCore ({z} : Finset A))) :
        Set (Erdos547b.LeafCore ({z} : Finset A))) hTz.connected
      (by
        intro v hv
        have hvy : v = y' := by simpa using hv
        subst v
        exact hdegY)
      ⟨x', by
        simp only [Set.mem_compl_iff]
        intro hxmem
        have hxy' : x' = y' := by simpa using hxmem
        exact hyx.ne.symm (congrArg Subtype.val hxy')⟩
  · exact hTz.isAcyclic.induce _

/- The other neighbour of a degree-two vertex after one specified neighbour
is removed. -/
theorem exists_other_neighbor_of_degree_two
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (y z : A) (hy : T.degree y = 2) (hyz : T.Adj y z) :
    ∃ x, T.Adj y x ∧ x ≠ z ∧ ∀ w, T.Adj y w → w = z ∨ w = x := by
  classical
  have hzmem : z ∈ T.neighborFinset y := by simpa using hyz
  have hcard : ((T.neighborFinset y).erase z).card = 1 := by
    rw [Finset.card_erase_of_mem hzmem,
      SimpleGraph.card_neighborFinset_eq_degree, hy]
  obtain ⟨x, hxerase⟩ := Finset.card_eq_one.mp hcard
  have hxmem : x ∈ T.neighborFinset y := by
    have : x ∈ (T.neighborFinset y).erase z := by simp [hxerase]
    exact (Finset.mem_erase.mp this).2
  have hxz : x ≠ z := by
    have : x ∈ (T.neighborFinset y).erase z := by simp [hxerase]
    exact (Finset.mem_erase.mp this).1
  refine ⟨x, by simpa using hxmem, hxz, ?_⟩
  intro w hyw
  by_cases hwz : w = z
  · exact Or.inl hwz
  · right
    have hwmem : w ∈ (T.neighborFinset y).erase z := by
      exact Finset.mem_erase.mpr ⟨hwz, by simpa using hyw⟩
    simpa [hxerase] using hwmem

/- Source-side package for the twice-deleted near-ideal core.  The loss of
the distinguished leaf is absorbed by running Lemma 7.8 at `r-1`. -/
theorem nearIdeal_core_left_data
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (n r : ℕ) (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (U₁ U₂ : Finset A)
    (hU : Erdos547b.ZhaoLemma77.IsNearIdealPartition r n T U₁ U₂)
    (z y x : A) (hzU : z ∈ U₁)
    (hz : T.degree z = 1) (hyU : y ∈ U₂)
    (hyz : T.Adj y z) (hy : T.degree y = 2)
    (hyx : T.Adj y x) (hxz : x ≠ z)
    (hother : ∀ w, T.Adj y w → w = z ∨ w = x)
    (hr : 1 ≤ r) :
    let Tz := T.induce {w | w ∉ ({z} : Finset A)}
    let y' : Erdos547b.LeafCore ({z} : Finset A) := ⟨y, by simpa using hyz.ne⟩
    let Tzy := Tz.induce {w | w ∉ ({y'} : Finset _)}
    let side : (Erdos547b.LeafCore ({y'} : Finset _)) → Fin 2 :=
      fun w => if w.1.1 ∈ U₂ then 1 else 0
    Tzy.IsTree ∧
      Erdos547b.ZhaoFact72.partCount side 0 = n / 2 ∧
      5 * (r - 1) ≤
        #(Finset.univ.filter fun w => side w = 0 ∧ Tzy.degree w = 1) := by
  classical
  let Tz := T.induce {w | w ∉ ({z} : Finset A)}
  let y' : Erdos547b.LeafCore ({z} : Finset A) := ⟨y, by simpa using hyz.ne⟩
  let Tzy := Tz.induce {w | w ∉ ({y'} : Finset _)}
  let side : (Erdos547b.LeafCore ({y'} : Finset _)) → Fin 2 :=
    fun w => if w.1.1 ∈ U₂ then 1 else 0
  have hcoreTree : Tzy.IsTree :=
    terminal_two_path_core_isTree T hT z y x hz hyz hy hyx hxz
  have hdisj := hU.partition.1
  have hcover := hU.partition.2
  have hxU₁ : x ∈ U₁ := by
    have hxnotU₂ : x ∉ U₂ := by
      intro hxU₂
      exact hU.right_independent hyU hxU₂ hyx.ne hyx
    have hxall : x ∈ U₁ ∨ x ∈ U₂ := by
      have hx := (Finset.ext_iff.mp hcover x).mpr (Finset.mem_univ x)
      exact (@Finset.mem_union A (fun a b => Classical.propDecidable (a = b))
        U₁ U₂ x).mp hx
    exact hxall.resolve_right hxnotU₂
  have hyNotU₁ : y ∉ U₁ := fun hyU₁ =>
    Finset.disjoint_left.mp hdisj hyU₁ hyU
  let P₀ : Finset (Erdos547b.LeafCore ({y'} : Finset _)) :=
    Finset.univ.filter fun w => side w = 0
  have hP₀card : P₀.card = U₁.card - 1 := by
    let toU : (w : Erdos547b.LeafCore ({y'} : Finset _)) →
        w ∈ P₀ → A := fun w _ => w.1.1
    have heq : P₀.card = (U₁.erase z).card := by
      apply Finset.card_bij toU
      · intro w hw
        have hw0 : side w = 0 := (Finset.mem_filter.mp hw).2
        have hwNotU₂ : w.1.1 ∉ U₂ := by
          simpa [side] using hw0
        have hwAll : w.1.1 ∈ U₁ ∨ w.1.1 ∈ U₂ := by
          have hx := (Finset.ext_iff.mp hcover w.1.1).mpr (Finset.mem_univ _)
          exact (@Finset.mem_union A (fun a b => Classical.propDecidable (a = b))
            U₁ U₂ w.1.1).mp hx
        have hwU₁ := hwAll.resolve_right hwNotU₂
        exact Finset.mem_erase.mpr ⟨by
          intro hwz
          exact w.1.2 (by simpa using hwz), hwU₁⟩
      · intro u hu v hv huv
        exact Subtype.ext (Subtype.ext huv)
      · intro w hw
        have hwU₁ : w ∈ U₁ := (Finset.mem_erase.mp hw).2
        have hwz : w ≠ z := (Finset.mem_erase.mp hw).1
        have hwy : w ≠ y := by
          intro hwy
          subst w
          exact hyNotU₁ hwU₁
        let wz : Erdos547b.LeafCore ({z} : Finset A) := ⟨w, by simpa using hwz⟩
        let wc : Erdos547b.LeafCore ({y'} : Finset _) := ⟨wz, by
          simp only [Finset.mem_singleton, Subtype.ext_iff]
          exact hwy⟩
        refine ⟨wc, ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hwNotU₂ : w ∉ U₂ := fun hwU₂ =>
          Finset.disjoint_left.mp hdisj hwU₁ hwU₂
        change (if w ∈ U₂ then (1 : Fin 2) else 0) = 0
        simp [hwNotU₂]
    rw [heq, Finset.card_erase_of_mem hzU]
  have hP₀ : Erdos547b.ZhaoFact72.partCount side 0 = n / 2 := by
    change P₀.card = n / 2
    rw [hP₀card, hU.left_card]
    omega
  let W := ((Erdos547b.ZhaoLemma77.leavesIn T U₁).erase z).erase x
  have hWcard : 5 * (r - 1) ≤ W.card := by
    have hzloss : (Erdos547b.ZhaoLemma77.leavesIn T U₁).card ≤
        ((Erdos547b.ZhaoLemma77.leavesIn T U₁).erase z).card + 1 := by
      by_cases hzmem : z ∈ Erdos547b.ZhaoLemma77.leavesIn T U₁
      · rw [Finset.card_erase_add_one hzmem]
      · simp [hzmem]
    have hxloss : ((Erdos547b.ZhaoLemma77.leavesIn T U₁).erase z).card ≤
        W.card + 1 := by
      by_cases hxmem : x ∈ (Erdos547b.ZhaoLemma77.leavesIn T U₁).erase z
      · rw [show W = ((Erdos547b.ZhaoLemma77.leavesIn T U₁).erase z).erase x by rfl,
          Finset.card_erase_add_one hxmem]
      · simp [W, hxmem]
    have hleft : 5 * r ≤ (Erdos547b.ZhaoLemma77.leavesIn T U₁).card := by
      convert hU.left_leaves using 1
      apply congrArg Finset.card
      ext w
      simp only [Erdos547b.ZhaoLemma77.mem_leavesIn]
      apply and_congr_right
      intro _
      unfold Erdos547b.ZhaoLemma77.IsLeaf
      apply iff_of_eq
      apply congrArg (fun d : ℕ => d = 1)
      exact Erdos547b.ZhaoLemma77Full74.degree_instance_eq T w _ _
    have hrEq : r = (r - 1) + 1 := by omega
    rw [hrEq, Nat.mul_add] at hleft
    omega
  have hWsub : W.card ≤
      #(Finset.univ.filter fun w => side w = 0 ∧ Tzy.degree w = 1) := by
    let e : {w // w ∈ W} → Erdos547b.LeafCore ({y'} : Finset _) :=
      fun w =>
        ⟨⟨w, by
          have := (Finset.mem_erase.mp (Finset.mem_erase.mp w.2).2).1
          simpa using this⟩, by
          simp only [Finset.mem_singleton, Subtype.ext_iff]
          have hwU₁ := (Erdos547b.ZhaoLemma77.mem_leavesIn.mp
            (Finset.mem_erase.mp (Finset.mem_erase.mp w.2).2).2).1
          exact fun hwy => hyNotU₁ (by simpa [hwy] using hwU₁)⟩
    let WI := (Finset.univ : Finset {w // w ∈ W}).image e
    have hWIcard : WI.card = W.card := by
      have heinj : Set.InjOn e (↑(Finset.univ : Finset {w // w ∈ W}) : Set _) := by
        intro u hu v hv huv
        exact Subtype.ext (congrArg (fun c => c.1.1) huv)
      rw [(Finset.card_image_iff.mpr heinj), Finset.card_univ,
        Fintype.card_coe]
    have hWIsub : WI ⊆
        (Finset.univ.filter fun w => side w = 0 ∧ Tzy.degree w = 1) := by
      intro c hc
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hc
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · have hwU₁ := (Erdos547b.ZhaoLemma77.mem_leavesIn.mp
          (Finset.mem_erase.mp (Finset.mem_erase.mp w.2).2).2).1
        have hwNotU₂ : (w : A) ∉ U₂ := fun hwU₂ =>
          Finset.disjoint_left.mp hdisj hwU₁ hwU₂
        change (if (w : A) ∈ U₂ then (1 : Fin 2) else 0) = 0
        simp [hwNotU₂]
      · have hwLeaf := (Erdos547b.ZhaoLemma77.mem_leavesIn.mp
          (Finset.mem_erase.mp (Finset.mem_erase.mp w.2).2).2).2
        have hwdeg : T.degree w = 1 := by
          unfold Erdos547b.ZhaoLemma77.IsLeaf at hwLeaf
          simpa only [Erdos547b.ZhaoLemma77Full74.degree_instance_eq] using hwLeaf
        have hdegZ : Tz.degree (e w).1 = T.degree w := by
          apply T.degree_induce_of_neighborSet_subset
          intro v hwv
          have hvz : v ≠ z := by
            intro hvz
            subst v
            obtain ⟨p, hzp, hp⟩ := degree_eq_one_iff_existsUnique_adj.mp hz
            have hwy : (w : A) = y :=
              (hp w hwv.symm).trans (hp y hyz.symm).symm
            have hwU₁ := (Erdos547b.ZhaoLemma77.mem_leavesIn.mp
              (Finset.mem_erase.mp (Finset.mem_erase.mp w.2).2).2).1
            exact hyNotU₁ (hwy ▸ hwU₁)
          simpa using hvz
        have hdegY : Tzy.degree (e w) = Tz.degree (e w).1 := by
          apply Tz.degree_induce_of_neighborSet_subset
          intro v hwv
          have hvy : v ≠ y' := by
            intro hvy
            subst v
            have hadjwy : T.Adj y (w : A) := by
              have : T.Adj (w : A) y := hwv
              exact this.symm
            rcases hother w hadjwy with hwz | hwx
            · exact (Finset.mem_erase.mp
                (Finset.mem_erase.mp w.2).2).1 hwz
            · exact (Finset.mem_erase.mp w.2).1 hwx
          change v ∉ ({y'} : Finset _)
          simpa only [Finset.mem_singleton] using hvy
        rw [hdegY, hdegZ, hwdeg]
    rw [← hWIcard]
    exact Finset.card_le_card hWIsub
  exact ⟨hcoreTree, hP₀, hWcard.trans hWsub⟩

theorem nearIdeal_core_right_data
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (n r : ℕ) (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (U₁ U₂ : Finset A)
    (hU : Erdos547b.ZhaoLemma77.IsNearIdealPartition r n T U₁ U₂)
    (z y x : A) (hzU : z ∈ U₁)
    (hz : T.degree z = 1) (hyU : y ∈ U₂)
    (hyz : T.Adj y z) (hy : T.degree y = 2)
    (hyx : T.Adj y x) (hxz : x ≠ z)
    (hother : ∀ w, T.Adj y w → w = z ∨ w = x)
    (hr : 1 ≤ r) :
    let Tz := T.induce {w | w ∉ ({z} : Finset A)}
    let y' : Erdos547b.LeafCore ({z} : Finset A) := ⟨y, by simpa using hyz.ne⟩
    let Tzy := Tz.induce {w | w ∉ ({y'} : Finset _)}
    let side : (Erdos547b.LeafCore ({y'} : Finset _)) → Fin 2 :=
      fun w => if w.1.1 ∈ U₂ then 1 else 0
    let active : Finset (Erdos547b.LeafCore
        ({y'} : Finset (Erdos547b.LeafCore ({z} : Finset A)))) :=
      (Finset.univ : Finset (Erdos547b.LeafCore
        ({y'} : Finset (Erdos547b.LeafCore ({z} : Finset A))))).filter
          fun w => side w = 1 ∧ Tzy.degree w ≠ 1
    (∀ ⦃u v⦄, Tzy.Adj u v → side u = 1 → side v ≠ 1) ∧
      (∀ w ∈ active, side w = 1) ∧
      (∀ w, side w = 1 → w ∉ active → Tzy.degree w = 1) ∧
      active.card ≤ n / 2 - 1 - 2 * r := by
  classical
  let Tz := T.induce {w | w ∉ ({z} : Finset A)}
  let y' : Erdos547b.LeafCore ({z} : Finset A) := ⟨y, by simpa using hyz.ne⟩
  let Tzy := Tz.induce {w | w ∉ ({y'} : Finset _)}
  let side : (Erdos547b.LeafCore ({y'} : Finset _)) → Fin 2 :=
    fun w => if w.1.1 ∈ U₂ then 1 else 0
  let active : Finset (Erdos547b.LeafCore
      ({y'} : Finset (Erdos547b.LeafCore ({z} : Finset A)))) :=
    (Finset.univ : Finset (Erdos547b.LeafCore
      ({y'} : Finset (Erdos547b.LeafCore ({z} : Finset A))))).filter
        fun w => side w = 1 ∧ Tzy.degree w ≠ 1
  have hdisj := hU.partition.1
  have hcover := hU.partition.2
  have hxU₁ : x ∈ U₁ := by
    have hxnotU₂ : x ∉ U₂ := by
      intro hxU₂
      exact hU.right_independent hyU hxU₂ hyx.ne hyx
    have hxold := (Finset.ext_iff.mp hcover x).mpr (Finset.mem_univ x)
    have hxall := (@Finset.mem_union A (fun a b => Classical.propDecidable (a = b))
      U₁ U₂ x).mp hxold
    exact hxall.resolve_right hxnotU₂
  have hindep : ∀ ⦃u v⦄, Tzy.Adj u v → side u = 1 → side v ≠ 1 := by
    intro u v huv hu hv
    have huU₂ : u.1.1 ∈ U₂ := by
      by_contra h
      simp [side, h] at hu
    have hvU₂ : v.1.1 ∈ U₂ := by
      by_contra h
      simp [side, h] at hv
    have hne : u.1.1 ≠ v.1.1 := by
      intro heq
      exact huv.ne (Subtype.ext (Subtype.ext heq))
    exact hU.right_independent huU₂ hvU₂ hne huv
  have hactive : ∀ w ∈ active, side w = 1 := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2.1
  have hdeferred : ∀ w, side w = 1 → w ∉ active → Tzy.degree w = 1 := by
    intro w hw hwa
    by_contra hd
    exact hwa (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hd⟩)
  let P₀ := Finset.univ.filter fun w => side w = 0
  let P₁ := Finset.univ.filter fun w => side w = 1
  have hP₀ : P₀.card = n / 2 := by
    have hleft := nearIdeal_core_left_data T n r hT hcardT U₁ U₂ hU
      z y x hzU hz hyU hyz hy hyx hxz hother hr
    exact hleft.2.1
  have hcoreCard : Fintype.card (Erdos547b.LeafCore ({y'} : Finset _)) = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe,
      Finset.card_singleton, Fintype.card_subtype_compl, Fintype.card_coe,
      Finset.card_singleton, hcardT]
    omega
  have hparts : P₀.card + P₁.card = n - 1 := by
    have hdisjP : Disjoint P₀ P₁ := by
      rw [Finset.disjoint_left]
      intro w hw0 hw1
      have h0 := (Finset.mem_filter.mp hw0).2
      have h1 := (Finset.mem_filter.mp hw1).2
      exact Fin.zero_ne_one (h0.symm.trans h1)
    have hcoverP : P₀ ∪ P₁ = Finset.univ := by
      ext w
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      rcases Erdos547b.EC1Scratch.fin_two_eq_zero_or_one (side w) with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [← Finset.card_union_of_disjoint hdisjP, hcoverP, Finset.card_univ,
      hcoreCard]
  have hP₁ : P₁.card = n / 2 - 1 := by
    have heven := Nat.even_iff.mp hU.n_even
    omega
  let R := Erdos547b.ZhaoLemma77.leavesIn T U₂
  let e : {w // w ∈ R} → Erdos547b.LeafCore ({y'} : Finset _) := fun w =>
    ⟨⟨w, by
      have hwU₂ := (Erdos547b.ZhaoLemma77.mem_leavesIn.mp w.2).1
      intro hwz
      have hwEq : (w : A) = z := by simpa using hwz
      exact Finset.disjoint_left.mp hdisj hzU (hwEq ▸ hwU₂)⟩,
      by
        simp only [Finset.mem_singleton, Subtype.ext_iff]
        intro hwy
        have hwLeaf := (Erdos547b.ZhaoLemma77.mem_leavesIn.mp w.2).2
        unfold Erdos547b.ZhaoLemma77.IsLeaf at hwLeaf
        have hwdeg : T.degree w = 1 := by
          simpa only [Erdos547b.ZhaoLemma77Full74.degree_instance_eq] using hwLeaf
        have hwEq : (w : A) = y := by simpa using hwy
        have hwdegY : T.degree y = 1 := hwEq ▸ hwdeg
        omega⟩
  let RI := (Finset.univ : Finset {w // w ∈ R}).image e
  have hRIcard : RI.card = R.card := by
    have heinj : Set.InjOn e (↑(Finset.univ : Finset {w // w ∈ R}) : Set _) := by
      intro u hu v hv huv
      exact Subtype.ext (congrArg (fun c => c.1.1) huv)
    rw [(Finset.card_image_iff.mpr heinj), Finset.card_univ, Fintype.card_coe]
  have hRIsubP₁ : RI ⊆ P₁ := by
    intro c hc
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hwU₂ := (Erdos547b.ZhaoLemma77.mem_leavesIn.mp w.2).1
    change (if (w : A) ∈ U₂ then (1 : Fin 2) else 0) = 1
    simp [hwU₂]
  have hRIsubLeaf : ∀ c ∈ RI, Tzy.degree c = 1 := by
    intro c hc
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hc
    have hwLeaf := (Erdos547b.ZhaoLemma77.mem_leavesIn.mp w.2).2
    have hwdeg : T.degree w = 1 := by
      unfold Erdos547b.ZhaoLemma77.IsLeaf at hwLeaf
      simpa only [Erdos547b.ZhaoLemma77Full74.degree_instance_eq] using hwLeaf
    have hdegZ : Tz.degree (e w).1 = T.degree w := by
      apply T.degree_induce_of_neighborSet_subset
      intro v hwv
      have hvz : v ≠ z := by
        intro hvz
        subst v
        obtain ⟨p, hzp, hp⟩ := degree_eq_one_iff_existsUnique_adj.mp hz
        have hwy : (w : A) = y := (hp w hwv.symm).trans (hp y hyz.symm).symm
        have hwdegY : T.degree y = 1 := hwy ▸ hwdeg
        omega
      simpa using hvz
    have hdegY : Tzy.degree (e w) = Tz.degree (e w).1 := by
      apply Tz.degree_induce_of_neighborSet_subset
      intro v hwv
      have hvy : v ≠ y' := by
        intro hvy
        subst v
        have hadj : T.Adj y (w : A) := hwv.symm
        rcases hother w hadj with hwz | hwx
        · have hwU₂ := (Erdos547b.ZhaoLemma77.mem_leavesIn.mp w.2).1
          exact Finset.disjoint_left.mp hdisj hzU (by simpa [hwz] using hwU₂)
        · have hwU₂ := (Erdos547b.ZhaoLemma77.mem_leavesIn.mp w.2).1
          exact Finset.disjoint_left.mp hdisj hxU₁ (by simpa [hwx] using hwU₂)
      change v ∉ ({y'} : Finset _)
      simpa only [Finset.mem_singleton] using hvy
    rw [hdegY, hdegZ, hwdeg]
  have hactiveSub : active ⊆ P₁ \ RI := by
    intro w hw
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2.1⟩, ?_⟩
    intro hwRI
    exact (Finset.mem_filter.mp hw).2.2 (hRIsubLeaf w hwRI)
  have hactiveCard : active.card ≤ n / 2 - 1 - 2 * r := by
    have hRIin := Finset.card_le_card hRIsubP₁
    have hsdiff : (P₁ \ RI).card = P₁.card - RI.card :=
      Finset.card_sdiff_of_subset hRIsubP₁
    have hleft : 2 * r ≤ R.card := by
      change 2 * r ≤ (Erdos547b.ZhaoLemma77.leavesIn T U₂).card
      convert hU.right_leaves using 1
      apply congrArg Finset.card
      ext w
      simp only [Erdos547b.ZhaoLemma77.mem_leavesIn]
      apply and_congr_right
      intro _
      unfold Erdos547b.ZhaoLemma77.IsLeaf
      apply iff_of_eq
      apply congrArg (fun d : ℕ => d = 1)
      exact Erdos547b.ZhaoLemma77Full74.degree_instance_eq T w _ _
    have hc := Finset.card_le_card hactiveSub
    rw [hsdiff, hP₁, hRIcard] at hc
    omega
  exact ⟨hindep, hactive, hdeferred, hactiveCard⟩

/- Reinsert the terminal path `x-y-z` after a copy of the twice-deleted
core has been found in an induced host set.  This is the exact gluing step
needed in the near-ideal branch; using `extendChosenLeaves` twice keeps the
proof independent of the particular construction of the core copy. -/
theorem extend_copy_over_terminal_two_path
    (T : SimpleGraph A) (G : SimpleGraph V)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (z y x : A) (H : Finset V) (a p zImage : V)
    (hz : T.degree z = 1) (hyz : T.Adj y z)
    (hy : T.degree y = 2) (hyx : T.Adj y x) (hxz : x ≠ z)
    (haH : a ∈ H) (hpH : p ∉ H) (hzImageH : zImage ∉ H)
    (hpz : p ≠ zImage) (hap : G.Adj a p) (hpzAdj : G.Adj p zImage)
    (hcore :
      let Tz := T.induce {w | w ∉ ({z} : Finset A)}
      let y' : Erdos547b.LeafCore ({z} : Finset A) := ⟨y, by
        simpa using hyz.ne⟩
      let Tzy := Tz.induce {w | w ∉ ({y'} : Finset _)}
      let x' : Erdos547b.LeafCore ({y'} : Finset _) :=
        ⟨⟨x, by simpa using hxz⟩, by
          simp only [Finset.mem_singleton, Subtype.ext_iff]
          exact hyx.ne.symm⟩
      ∃ f : Tzy.Copy (G.induce (H : Set V)), f x' = ⟨a, haH⟩) :
    T ⊑ G := by
  classical
  let Tz := T.induce {w | w ∉ ({z} : Finset A)}
  let y' : Erdos547b.LeafCore ({z} : Finset A) := ⟨y, by
    simpa using hyz.ne⟩
  let xz : Erdos547b.LeafCore ({z} : Finset A) := ⟨x, by simpa using hxz⟩
  have hyx' : Tz.Adj y' xz := hyx
  have hdegY : Tz.degree y' = 1 := by
    have hset : T.neighborFinset y ∩ ({w | w ∉ ({z} : Finset A)} : Set A).toFinset =
        (T.neighborFinset y).erase z := by
      ext w
      simp [and_comm]
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_map (f := Function.Embedding.subtype _),
      T.map_neighborFinset_induce]
    change #(T.neighborFinset y ∩
      ({w | w ∉ ({z} : Finset A)} : Set A).toFinset) = 1
    rw [hset, Finset.card_erase_of_mem, SimpleGraph.card_neighborFinset_eq_degree, hy]
    simpa using hyz
  let Tzy := Tz.induce {w | w ∉ ({y'} : Finset _)}
  let x' : Erdos547b.LeafCore ({y'} : Finset _) :=
    ⟨xz, by
      simp only [Finset.mem_singleton, Subtype.ext_iff]
      exact hyx.ne.symm⟩
  obtain ⟨f, hfx⟩ := hcore
  let fcore : Tzy.Copy G := (SimpleGraph.Copy.induce G (H : Set V)).comp f
  have hfxcore : fcore x' = a := by
    change (f x' : V) = a
    simpa using congrArg Subtype.val hfx
  let parentY : Erdos547b.ChosenLeaves ({y'} : Finset _) →
      Erdos547b.LeafCore ({y'} : Finset _) := fun _ =>
        x'
  have hparentY : ∀ l, Tz.Adj l.1 (parentY l).1 := by
    intro l
    have hl : l.1 = y' := Finset.mem_singleton.mp l.2
    rw [hl]
    exact hyx'
  let imageY : Erdos547b.ChosenLeaves ({y'} : Finset _) → V := fun _ => p
  have himageYinj : Function.Injective imageY := by
    intro u v _
    apply Subtype.ext
    exact (Finset.mem_singleton.mp u.2).trans
      (Finset.mem_singleton.mp v.2).symm
  have hcoreDisjY : ∀ c l, fcore c ≠ imageY l := by
    intro c l heq
    have hcH : fcore c ∈ H := by
      change (f c : V) ∈ H
      exact (f c).2
    rw [heq] at hcH
    exact hpH (by simpa [imageY] using hcH)
  have hparentImageY : ∀ l, G.Adj (fcore (parentY l)) (imageY l) := by
    intro l
    have hl : l.1 = y' := Finset.mem_singleton.mp l.2
    have hparentEq : parentY l = x' := rfl
    rw [hparentEq, hfxcore]
    exact hap
  let fz : Tz.Copy G := Erdos547b.Copy.extendChosenLeaves Tz G ({y'} : Finset _)
    (fun l => by
      have hl : l.1 = y' := Finset.mem_singleton.mp l.2
      rw [hl]
      exact hdegY) parentY hparentY fcore imageY
    himageYinj hcoreDisjY hparentImageY
  have hfzY : fz y' = p := by
    simp [fz, Erdos547b.Copy.extendChosenLeaves, imageY]
  let parentZ : Erdos547b.ChosenLeaves ({z} : Finset A) →
      Erdos547b.LeafCore ({z} : Finset A) := fun _ =>
        ⟨y, by simpa using hyz.ne⟩
  have hparentZ : ∀ l, T.Adj l.1 (parentZ l).1 := by
    intro l
    have hl : l.1 = z := Finset.mem_singleton.mp l.2
    rw [hl]
    exact hyz.symm
  let imageZ : Erdos547b.ChosenLeaves ({z} : Finset A) → V := fun _ => zImage
  have himageZinj : Function.Injective imageZ := by
    intro u v _
    apply Subtype.ext
    exact (Finset.mem_singleton.mp u.2).trans
      (Finset.mem_singleton.mp v.2).symm
  have hfzDisjZ : ∀ c l, fz c ≠ imageZ l := by
    intro c l heq
    by_cases hcy : c = y'
    · subst c
      have heq' := heq
      rw [hfzY] at heq'
      exact hpz (by simpa [imageZ] using heq')
    · have hcnot : c ∉ ({y'} : Finset _) := by
        simpa using hcy
      have hfzc : fz c = fcore ⟨c, hcnot⟩ := by
        simp [fz, Erdos547b.Copy.extendChosenLeaves, hcy]
      have hcH : fz c ∈ H := by
        rw [hfzc]
        change (f ⟨c, hcnot⟩ : V) ∈ H
        exact (f ⟨c, hcnot⟩).2
      rw [heq] at hcH
      exact hzImageH (by simpa [imageZ] using hcH)
  have hparentImageZ : ∀ l, G.Adj (fz (parentZ l)) (imageZ l) := by
    intro l
    change G.Adj (fz y') zImage
    rw [hfzY]
    exact hpzAdj
  exact ⟨Erdos547b.Copy.extendChosenLeaves T G ({z} : Finset A)
    (fun l => by
      have hl : l.1 = z := Finset.mem_singleton.mp l.2
      rw [hl]
      exact hz) parentZ hparentZ fz imageZ
    himageZinj hfzDisjZ hparentImageZ⟩

/- The rooted core copy used in the near-ideal branch.  The finite set `R`
contains the one or two host vertices reserved for reinserting the terminal
path.  Removing it from the pruned right side costs at most two vertices. -/
theorem nearIdeal_core_copy_avoiding
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n q s sp l : ℕ)
    (h : Erdos547b.ZhaoLemma74.EC3Witness G n q)
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (U₁ U₂ : Finset A)
    (hU : Erdos547b.ZhaoLemma77.IsNearIdealPartition (s + q) n T U₁ U₂)
    (z y x : A) (hzU : z ∈ U₁)
    (hz : T.degree z = 1) (hyU : y ∈ U₂)
    (hyz : T.Adj y z) (hy : T.degree y = 2)
    (hyx : T.Adj y x) (hxz : x ≠ z)
    (hother : ∀ w, T.Adj y w → w = z ∨ w = x)
    (hpos : 0 < s + q)
    (hsource : 1782 * (s + q) ≤ n)
    (hsp : sp ≤ s) (hql : q ≤ l) (hl : l = s + q - 1)
    (B₁ : Finset V)
    (hBsub : B₁ ⊆ h.V₁ \ h.A₀)
    (hBlower : n / 2 - sp ≤ B₁.card)
    (hAA : ∀ a ∈ h.A₀,
      h.A₀.card - l ≤ (G.neighborFinset a ∩ h.A₀).card)
    (hBA : ∀ b ∈ B₁,
      h.A₀.card - l ≤ (G.neighborFinset b ∩ h.A₀).card)
    (hAB : ∀ a ∈ h.A₀,
      B₁.card - q ≤ (G.neighborFinset a ∩ B₁).card)
    (R : Finset V) (hRcard : R.card ≤ 2)
    (hRdisj : Disjoint h.A₀ R)
    (a : V) (haA : a ∈ h.A₀) :
    let Tz := T.induce {w | w ∉ ({z} : Finset A)}
    let y' : Erdos547b.LeafCore ({z} : Finset A) := ⟨y, by
      simpa using hyz.ne⟩
    let Tzy := Tz.induce {w | w ∉ ({y'} : Finset _)}
    let x' : Erdos547b.LeafCore ({y'} : Finset _) :=
      ⟨⟨x, by simpa using hxz⟩, by
        simp only [Finset.mem_singleton, Subtype.ext_iff]
        exact hyx.ne.symm⟩
    let B := B₁ \ R
    let H := Finset.univ \ R
    ∃ f : Tzy.Copy (G.induce (H : Set V)),
      f x' = ⟨a, by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
          fun haR => Finset.disjoint_left.mp hRdisj haA haR⟩⟩ := by
  classical
  subst l
  let Tz := T.induce {w | w ∉ ({z} : Finset A)}
  let y' : Erdos547b.LeafCore ({z} : Finset A) := ⟨y, by
    simpa using hyz.ne⟩
  let Tzy := Tz.induce {w | w ∉ ({y'} : Finset _)}
  let x' : Erdos547b.LeafCore ({y'} : Finset _) :=
    ⟨⟨x, by simpa using hxz⟩, by
      simp only [Finset.mem_singleton, Subtype.ext_iff]
      exact hyx.ne.symm⟩
  let side : Erdos547b.LeafCore ({y'} : Finset _) → Fin 2 :=
    fun w => if w.1.1 ∈ U₂ then 1 else 0
  let active : Finset (Erdos547b.LeafCore ({y'} : Finset _)) :=
    Finset.univ.filter fun w => side w = 1 ∧ Tzy.degree w ≠ 1
  let B := B₁ \ R
  let H := Finset.univ \ R
  let X := liftFinset H h.A₀
  let Y := liftFinset H B
  have hleft := nearIdeal_core_left_data T n (s + q) hT hcardT U₁ U₂ hU
    z y x hzU hz hyU hyz hy hyx hxz hother (by omega)
  have hright := nearIdeal_core_right_data T n (s + q) hT hcardT U₁ U₂ hU
    z y x hzU hz hyU hyz hy hyx hxz hother (by omega)
  have hAsubH : h.A₀ ⊆ H := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hvR => Finset.disjoint_left.mp hRdisj hv hvR⟩
  have hBsubH : B ⊆ H := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hv).2⟩
  have hABdisj : Disjoint h.A₀ B := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    have hvB₁ : v ∈ B₁ := (Finset.mem_sdiff.mp hvB).1
    have hvBsub : v ∈ h.V₁ \ h.A₀ := hBsub hvB₁
    exact (Finset.mem_sdiff.mp hvBsub).2 hvA
  have hXY : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro u huX huY
    exact Finset.disjoint_left.mp hABdisj
      (mem_liftFinset.mp huX) (mem_liftFinset.mp huY)
  have hXcard : X.card = h.A₀.card := card_liftFinset H h.A₀ hAsubH
  have hYcard : Y.card = B.card := card_liftFinset H B hBsubH
  have hBLower : n / 2 - sp - 2 ≤ B.card := by
    rw [Finset.card_sdiff]
    have hi : (R ∩ B₁).card ≤ R.card :=
      Finset.card_le_card Finset.inter_subset_left
    omega
  have hroom : sp + 2 ≤ n / 2 := by omega
  have hAB' : ∀ a ∈ h.A₀,
      B.card - q ≤ (G.neighborFinset a ∩ B).card := by
    intro v hv
    have hm : Erdos547b.ZhaoLemma74.MissesAtMost G v B₁ q := by
      unfold Erdos547b.ZhaoLemma74.MissesAtMost
      rw [Erdos547b.ZhaoLemma74.degreeInto_eq_neighborFinset_inter]
      have := hAB v hv
      omega
    have hmB := hm.mono_set (Finset.sdiff_subset : B₁ \ R ⊆ B₁)
    unfold Erdos547b.ZhaoLemma74.MissesAtMost at hmB
    rw [Erdos547b.ZhaoLemma74.degreeInto_eq_neighborFinset_inter] at hmB
    change (B₁ \ R).card - q ≤
      (G.neighborFinset v ∩ (B₁ \ R)).card
    omega
  have hactiveNumeric : n / 2 - 1 - 2 * (s + q) ≤
      (n / 2 - sp - 2) - q := by
    have hspq : sp + q ≤ s + q := Nat.add_le_add_right hsp q
    omega
  have hcoreCard : Fintype.card (Erdos547b.LeafCore ({y'} : Finset _)) = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe,
      Finset.card_singleton, Fintype.card_subtype_compl, Fintype.card_coe,
      Finset.card_singleton, hcardT]
    omega
  have hedgeStrong : Tzy.edgeFinset.card + 2 ≤ n := by
    have he : Tzy.edgeFinset.card + 1 =
        Fintype.card (Erdos547b.LeafCore ({y'} : Finset _)) :=
      hleft.1.card_edgeFinset
    rw [hcoreCard] at he
    omega
  have hedge : Tzy.edgeFinset.card ≤ n := by omega
  have hXX : ∀ u ∈ X,
      X.card - (s + q - 1) ≤
        ((G.induce (H : Set V)).neighborFinset u ∩ X).card := by
    intro u hu
    rw [hXcard, card_neighbor_inter_liftFinset G H h.A₀ hAsubH]
    exact hAA u.1 (mem_liftFinset.mp hu)
  have hYX : ∀ u ∈ Y,
      X.card - (s + q - 1) ≤
        ((G.induce (H : Set V)).neighborFinset u ∩ X).card := by
    intro u hu
    rw [hXcard, card_neighbor_inter_liftFinset G H h.A₀ hAsubH]
    exact hBA u.1 (Finset.mem_sdiff.mp (mem_liftFinset.mp hu)).1
  have hXYdeg : ∀ u ∈ X,
      max (Y.card - (s + q - 1)) active.card ≤
        ((G.induce (H : Set V)).neighborFinset u ∩ Y).card := by
    intro u hu
    rw [hYcard, card_neighbor_inter_liftFinset G H B hBsubH]
    apply max_le
    · exact le_trans (by omega) (hAB' u.1 (mem_liftFinset.mp hu))
    · calc
        active.card ≤ n / 2 - 1 - 2 * (s + q) := hright.2.2.2
        _ ≤ (n / 2 - sp - 2) - q := hactiveNumeric
        _ ≤ B.card - q := Nat.sub_le_sub_right hBLower q
        _ ≤ (G.neighborFinset u.1 ∩ B).card :=
          hAB' u.1 (mem_liftFinset.mp hu)
  have hglobal : ∀ u ∈ X, Tzy.edgeFinset.card ≤
      (G.induce (H : Set V)).degree u := by
    intro u hu
    have hh := h.high_A₀ u.1 (mem_liftFinset.mp hu)
    have hd := Erdos547b.ZhaoLemma74.degreeInto_sdiff_lower G u.1 Finset.univ R
    have hallDegree : Erdos547EC2.degreeInto G u.1 Finset.univ = G.degree u.1 := by
      rw [Erdos547b.ZhaoLemma74.degreeInto_eq_neighborFinset_inter]
      simp
    have hd' : G.degree u.1 - R.card ≤
        (G.neighborFinset u.1 ∩ H).card := by
      rw [hallDegree] at hd
      rw [Erdos547b.ZhaoLemma74.degreeInto_eq_neighborFinset_inter] at hd
      simpa [H] using hd
    have hindDegree : (G.induce (H : Set V)).degree u =
        (G.neighborFinset u.1 ∩ H).card := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      have hc := card_neighbor_inter_liftFinset G H H
        (by exact Finset.Subset.rfl) u
      have hall : liftFinset H H = Finset.univ := by
        ext w
        simp [liftFinset]
      rw [hall, Finset.inter_univ] at hc
      exact hc
    have hdH : G.degree u.1 - R.card ≤
        (G.induce (H : Set V)).degree u := by
      rw [hindDegree]
      exact hd'
    omega
  have hxNotU₂ : x ∉ U₂ := by
    intro hxU₂
    exact hU.right_independent hyU hxU₂ hyx.ne hyx
  have hxSide : side x' = 0 := by simp [side, x', hxNotU₂]
  have haH : a ∈ H := hAsubH haA
  have hleaves : 5 * (s + q - 1) ≤
      (Finset.univ.filter fun w => side w = 0 ∧ Tzy.degree w = 1).card :=
    hleft.2.2
  exact Erdos547b.ZhaoLemma78Full74.lemma7_8 Tzy (G.induce (H : Set V))
    n (s + q - 1) (by omega) hleft.1 hedge side hright.1 active hright.2.1
    hright.2.2.1 hleaves
    X Y hXY (by rw [hleft.2.1, hXcard, h.card_A₀]; omega)
    hXX hYX hXYdeg hglobal x' hxSide ⟨a, haH⟩ (mem_liftFinset.mpr haA)

/- The exceptional near-ideal branch of Zhao's Lemma 7.4.  The two deleted
source vertices are put back along a one- or two-edge path reserved outside
the core image. -/
theorem EC3Witness.contains_of_nearIdealPartition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n q s : ℕ)
    (h : Erdos547b.ZhaoLemma74.EC3Witness G n q)
    (hscale : q * n ≤ s * (s + 1))
    (hsource : 1782 * (s + q) ≤ n)
    (hrpos : 0 < s + q)
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (U₁ U₂ : Finset A)
    (hU : Erdos547b.ZhaoLemma77.IsNearIdealPartition (s + q) n T U₁ U₂) :
    T ⊑ G := by
  classical
  have hnpos : 0 < n := by omega
  have hnlarge : 2 ≤ n := by omega
  let sp : ℕ := if q = 0 then 0 else s
  let l : ℕ := s + q - 1
  have hsp_le : sp ≤ s := by
    simp only [sp]
    split <;> omega
  have hspos_of_qpos (hq : q ≠ 0) : 0 < s := by
    by_contra hs
    have hs0 : s = 0 := by omega
    subst s
    simp at hscale
    exact hq (by
      have : q * n = 0 := by omega
      exact (Nat.mul_eq_zero.mp this).resolve_right (by omega))
  have hspScale : q * n ≤ sp * (sp + 1) := by
    by_cases hq : q = 0
    · simp [hq]
    · simpa [sp, hq] using hscale
  have hql : q ≤ l := by
    by_cases hq : q = 0
    · simp [hq, l]
    · have hs := hspos_of_qpos hq
      simp only [l]
      omega
  have hspl : sp ≤ l := by
    by_cases hq : q = 0
    · simp [sp, hq, l]
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      simp only [sp, hq, if_false, l]
      omega
  obtain ⟨B₁, hBsub, _hABdisj, hBlower, _hBupper, hAA, hBA, hAB⟩ :=
    h.exists_prunedPair hspScale hql hspl
  obtain ⟨z, hzU, hzLeaf, y, hyU, hyz, hy⟩ := hU.special_leaf
  have hz : T.degree z = 1 := by
    unfold Erdos547b.ZhaoLemma77.IsLeaf at hzLeaf
    exact Eq.trans (Erdos547b.ZhaoLemma77Full74.degree_instance_eq T z _ _) hzLeaf
  have hy' : T.degree y = 2 := by
    exact Eq.trans (Erdos547b.ZhaoLemma77Full74.degree_instance_eq T y _ _) hy
  obtain ⟨x, hyx, hxz, hother⟩ :=
    exists_other_neighbor_of_degree_two T y z hy' hyz
  obtain ⟨a, haA, v₀, hv₀A, hvdeg, hpath⟩ :=
    Erdos547b.ZhaoNearIdealEC374.EC3Witness.exists_reserved_path_from_A₀
      G h hU.n_even
  have hcoreFor (R : Finset V) (hRcard : R.card ≤ 2)
      (hRdisj : Disjoint h.A₀ R) :
      let Tz := T.induce {w | w ∉ ({z} : Finset A)}
      let y' : Erdos547b.LeafCore ({z} : Finset A) := ⟨y, by
        simpa using hyz.ne⟩
      let Tzy := Tz.induce {w | w ∉ ({y'} : Finset _)}
      let x' : Erdos547b.LeafCore ({y'} : Finset _) :=
        ⟨⟨x, by simpa using hxz⟩, by
          simp only [Finset.mem_singleton, Subtype.ext_iff]
          exact hyx.ne.symm⟩
      let H := Finset.univ \ R
      ∃ f : Tzy.Copy (G.induce (H : Set V)),
        f x' = ⟨a, by
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
            fun haR => Finset.disjoint_left.mp hRdisj haA haR⟩⟩ := by
    simpa [sp, l] using nearIdeal_core_copy_avoiding G n q s sp l h T hT hcardT
      U₁ U₂ hU z y x hzU hz hyU hyz hy' hyx hxz hother hrpos hsource
      hsp_le hql rfl B₁ hBsub hBlower hAA hBA hAB R hRcard hRdisj a haA
  rcases hpath with hav | ⟨b, hbA, hbv, hab, hbvAdj⟩
  · have hlt : h.A₀.card < (G.neighborFinset v₀).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, h.card_A₀]
      omega
    obtain ⟨zImage, hzN, hzA⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hlt
    have hvz : G.Adj v₀ zImage := (G.mem_neighborFinset _ _).mp hzN
    let R : Finset V := {v₀, zImage}
    let H : Finset V := Finset.univ \ R
    have hRcard : R.card ≤ 2 := by
      calc
        R.card ≤ ({zImage} : Finset V).card + 1 := by
          simpa [R] using Finset.card_insert_le v₀ ({zImage} : Finset V)
        _ = 2 := by simp
    have hRdisj : Disjoint h.A₀ R := by
      rw [Finset.disjoint_left]
      intro w hwA hwR
      simp only [R, Finset.mem_insert, Finset.mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · exact hv₀A hwA
      · exact hzA hwA
    have hcore := hcoreFor R hRcard hRdisj
    refine extend_copy_over_terminal_two_path T G z y x H a v₀ zImage
      hz hyz hy' hyx hxz ?_ ?_ ?_ hvz.ne hav hvz ?_
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        intro haR
        exact Finset.disjoint_left.mp hRdisj haA haR⟩
    · simp [H, R]
    · simp [H, R]
    · simpa [H, R] using hcore
  · let R : Finset V := {b, v₀}
    let H : Finset V := Finset.univ \ R
    have hRcard : R.card ≤ 2 := by
      calc
        R.card ≤ ({v₀} : Finset V).card + 1 := by
          simpa [R] using Finset.card_insert_le b ({v₀} : Finset V)
        _ = 2 := by simp
    have hRdisj : Disjoint h.A₀ R := by
      rw [Finset.disjoint_left]
      intro w hwA hwR
      simp only [R, Finset.mem_insert, Finset.mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · exact hbA hwA
      · exact hv₀A hwA
    have hcore := hcoreFor R hRcard hRdisj
    refine extend_copy_over_terminal_two_path T G z y x H a b v₀
      hz hyz hy' hyx hxz ?_ ?_ ?_ hbv hab hbvAdj ?_
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        intro haR
        exact Finset.disjoint_left.mp hRdisj haA haR⟩
    · simp [H, R]
    · simp [H, R]
    · simpa [H, R] using hcore

end Erdos547b.ZhaoNearIdealEC374


/-!
# Zhao's odd path exception in Lemma 7.4

The odd case deletes three vertices from a Hamiltonian ordering: the first
two consecutive vertices and the opposite endpoint.  This file isolates the
exact gluing operation and the host restriction needed before invoking
Lemma 7.10.
-/

namespace Erdos547b.ZhaoOddPathException74

open Finset SimpleGraph

universe u v

variable {S : Type u} {V : Type v}

theorem card_even_indices_two_mul_sub_one (m : ℕ) (hm : 1 ≤ m) :
    #((Finset.univ : Finset (Fin (2 * m - 1))).filter
      fun i => i.1 % 2 = 0) = m := by
  classical
  let E := (Finset.univ : Finset (Fin (2 * m - 1))).filter
    fun i => i.1 % 2 = 0
  calc
    E.card = (Finset.univ : Finset (Fin m)).card := by
      apply Finset.card_bij (fun i _ => ⟨i.1 / 2, by
        have hi := i.2
        have he : i.1 % 2 = 0 := (Finset.mem_filter.mp ‹i ∈ E›).2
        omega⟩)
      · intro i hi
        simp
      · intro i hi j hj hij
        apply Fin.ext
        have hiEven : i.1 % 2 = 0 := (Finset.mem_filter.mp hi).2
        have hjEven : j.1 % 2 = 0 := (Finset.mem_filter.mp hj).2
        have hv := congrArg Fin.val hij
        dsimp at hv
        omega
      · intro j hj
        let i : Fin (2 * m - 1) := ⟨2 * j.1, by omega⟩
        refine ⟨i, ?_, ?_⟩
        · simp [E, i]
        · apply Fin.ext
          simp [i]
    _ = m := by simp

theorem card_odd_indices_two_mul_sub_one (m : ℕ) (hm : 1 ≤ m) :
    #((Finset.univ : Finset (Fin (2 * m - 1))).filter
      fun i => i.1 % 2 = 1) = m - 1 := by
  classical
  let O := (Finset.univ : Finset (Fin (2 * m - 1))).filter
    fun i => i.1 % 2 = 1
  calc
    O.card = (Finset.univ : Finset (Fin (m - 1))).card := by
      apply Finset.card_bij (fun i _ => ⟨i.1 / 2, by
        have hi := i.2
        have ho : i.1 % 2 = 1 := (Finset.mem_filter.mp ‹i ∈ O›).2
        omega⟩)
      · intro i hi
        simp
      · intro i hi j hj hij
        apply Fin.ext
        have hiOdd : i.1 % 2 = 1 := (Finset.mem_filter.mp hi).2
        have hjOdd : j.1 % 2 = 1 := (Finset.mem_filter.mp hj).2
        have hv := congrArg Fin.val hij
        dsimp at hv
        omega
      · intro j hj
        let i : Fin (2 * m - 1) := ⟨2 * j.1 + 1, by omega⟩
        refine ⟨i, ?_, ?_⟩
        · simp [O, i]
        · apply Fin.ext
          change (2 * j.1 + 1) / 2 = j.1
          omega
    _ = m - 1 := by simp

/-- A Hamiltonian path in a finite tree uses every edge of the tree. -/
theorem hamiltonian_toSubgraph_eq_top
    [Fintype S] [DecidableEq S]
    (T : SimpleGraph S) {u w : S} (p : T.Walk u w)
    (hT : T.IsTree) (hp : p.IsHamiltonian) : p.toSubgraph = ⊤ := by
  classical
  have hpath : p.IsPath := hp.isPath
  have hcardP : p.edges.toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hpath.isTrail.edges_nodup,
      p.length_edges]
  have hsub : p.edges.toFinset ⊆ T.edgeFinset := by
    intro e he
    rw [T.mem_edgeFinset]
    apply p.edges_subset_edgeSet
    simpa using he
  have hcardT := hT.card_edgeFinset
  have hlen := hp.length_eq
  have hcardle : T.edgeFinset.card ≤ p.edges.toFinset.card := by
    rw [hcardP, hlen]
    omega
  have hedge : p.edges.toFinset = T.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcardle
  apply SimpleGraph.Subgraph.ext
  · ext z
    simp [hp.mem_support]
  · funext a b
    apply propext
    constructor
    · exact fun h => h.adj_sub
    · intro hab
      rw [← SimpleGraph.Subgraph.mem_edgeSet, p.mem_edges_toSubgraph]
      have he : s(a, b) ∈ T.edgeFinset := by
        rw [T.mem_edgeFinset, T.mem_edgeSet]
        exact hab
      rw [← hedge] at he
      simpa using he

theorem hamiltonian_tree_first_neighbor
    [Fintype S] [DecidableEq S]
    (T : SimpleGraph S) {u w : S} (p : T.Walk u w)
    (hT : T.IsTree) (hp : p.IsHamiltonian) (hlen : 1 ≤ p.length) :
    ∀ z, T.Adj (p.getVert 0) z → z = p.getVert 1 := by
  intro z hz
  have hz' : p.toSubgraph.Adj (p.getVert 0) z := by
    rw [hamiltonian_toSubgraph_eq_top T p hT hp]
    exact hz
  rw [p.toSubgraph_adj_iff] at hz'
  obtain ⟨i, hi, hil⟩ := hz'
  have hget : ∀ i j, i ≤ p.length → j ≤ p.length →
      p.getVert i = p.getVert j → i = j := by
    intro i j hii hjj hij
    exact hp.isPath.getVert_injOn (by simpa) (by simpa) hij
  grind [Sym2.eq]

theorem hamiltonian_tree_second_neighbors
    [Fintype S] [DecidableEq S]
    (T : SimpleGraph S) {u w : S} (p : T.Walk u w)
    (hT : T.IsTree) (hp : p.IsHamiltonian) (hlen : 2 ≤ p.length) :
    ∀ z, T.Adj (p.getVert 1) z →
      z = p.getVert 0 ∨ z = p.getVert 2 := by
  intro z hz
  have hz' : p.toSubgraph.Adj (p.getVert 1) z := by
    rw [hamiltonian_toSubgraph_eq_top T p hT hp]
    exact hz
  rw [p.toSubgraph_adj_iff] at hz'
  obtain ⟨i, hi, hil⟩ := hz'
  have hget : ∀ i j, i ≤ p.length → j ≤ p.length →
      p.getVert i = p.getVert j → i = j := by
    intro i j hii hjj hij
    exact hp.isPath.getVert_injOn (by simpa) (by simpa) hij
  grind [Sym2.eq]

theorem hamiltonian_tree_last_neighbor
    [Fintype S] [DecidableEq S]
    (T : SimpleGraph S) {u w : S} (p : T.Walk u w)
    (hT : T.IsTree) (hp : p.IsHamiltonian) (hlen : 1 ≤ p.length) :
    ∀ z, T.Adj (p.getVert p.length) z →
      z = p.getVert (p.length - 1) := by
  intro z hz
  have hz' : p.toSubgraph.Adj (p.getVert p.length) z := by
    rw [hamiltonian_toSubgraph_eq_top T p hT hp]
    exact hz
  rw [p.toSubgraph_adj_iff] at hz'
  obtain ⟨i, hi, hil⟩ := hz'
  have hget : ∀ i j, i ≤ p.length → j ≤ p.length →
      p.getVert i = p.getVert j → i = j := by
    intro i j hii hjj hij
    exact hp.isPath.getVert_injOn (by simpa) (by simpa) hij
  grind [Sym2.eq]

/-- The three-vertex deletion of a Hamiltonian tree is canonically a path
graph: index `i` corresponds to old Hamiltonian position `i+2`. -/
theorem exists_triply_trimmed_path_iso
    [Fintype S] [DecidableEq S]
    (T : SimpleGraph S) {u w : S} (p : T.Walk u w)
    (hT : T.IsTree) (hp : p.IsHamiltonian)
    (n k : ℕ) (hk : k = n - 2)
    (hcard : Fintype.card S = n + 1) (hn : 4 ≤ n) :
    ∃ e : SimpleGraph.pathGraph k ≃g
        T.induce ((({p.getVert 0, p.getVert 1, p.getVert n} : Finset S) : Set S)ᶜ),
      ∀ i, (e i).1 = p.getVert (i.1 + 2) := by
  classical
  have hlen : p.length = n := by
    have hpLen := hp.length_eq
    rw [hcard] at hpLen
    omega
  have hget : ∀ i j, i ≤ n → j ≤ n →
      p.getVert i = p.getVert j → i = j := by
    intro i j hi hj hij
    apply hp.isPath.getVert_injOn (by simpa [hlen]) (by simpa [hlen]) hij
  let f : Fin k →
      ↥((((({p.getVert 0, p.getVert 1, p.getVert n} : Finset S) : Set S)ᶜ))) :=
    fun i => ⟨p.getVert (i.1 + 2), by
      simp only [Set.mem_compl_iff, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨?_, ?_, ?_⟩
      · intro hi
        have := hget (i.1 + 2) 0 (by omega) (by omega) hi
        omega
      · intro hi
        have := hget (i.1 + 2) 1 (by omega) (by omega) hi
        omega
      · intro hi
        have := hget (i.1 + 2) n (by omega) (by omega) hi
        omega⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Subtype.val hij
    have := hget (i.1 + 2) (j.1 + 2) (by omega) (by omega) hv
    omega
  have htriple : ({p.getVert 0, p.getVert 1, p.getVert n} : Finset S).card = 3 := by
    have h01 : p.getVert 0 ≠ p.getVert 1 := by
      intro h; have := hget 0 1 (by omega) (by omega) h; omega
    have h0n : p.getVert 0 ≠ p.getVert n := by
      intro h; have := hget 0 n (by omega) (by omega) h; omega
    have h1n : p.getVert 1 ≠ p.getVert n := by
      intro h; have := hget 1 n (by omega) (by omega) h; omega
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa only [Finset.mem_singleton] using h1n
    · simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
        (And.intro h01 h0n)
  have hcoreCard : Fintype.card
      ↥((((({p.getVert 0, p.getVert 1, p.getVert n} : Finset S) : Set S)ᶜ))) = n - 2 := by
    change Fintype.card {z : S //
      z ∉ ({p.getVert 0, p.getVert 1, p.getVert n} : Finset S)} = _
    rw [Fintype.card_subtype_compl (fun z : S =>
      z ∈ ({p.getVert 0, p.getVert 1, p.getVert n} : Finset S))]
    rw [Fintype.card_coe, htriple, hcard]
    omega
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, by
      rw [Fintype.card_fin, hcoreCard, hk]⟩
  let eqv : Fin k ≃
      ↥((((({p.getVert 0, p.getVert 1, p.getVert n} : Finset S) : Set S)ᶜ))) :=
    Equiv.ofBijective f hfbij
  have htop := hamiltonian_toSubgraph_eq_top T p hT hp
  let e : SimpleGraph.pathGraph k ≃g
      T.induce ((({p.getVert 0, p.getVert 1, p.getVert n} : Finset S) : Set S)ᶜ) :=
    { eqv with
      map_rel_iff' := by
        intro i j
        change T.Adj (p.getVert (i.1 + 2)) (p.getVert (j.1 + 2)) ↔ _
        rw [SimpleGraph.pathGraph_adj]
        constructor
        · intro hij
          have hij' : p.toSubgraph.Adj
              (p.getVert (i.1 + 2)) (p.getVert (j.1 + 2)) := by
            rw [htop]
            exact hij
          rw [p.toSubgraph_adj_iff] at hij'
          obtain ⟨k, hk, hklt⟩ := hij'
          have hkBound : k + 1 ≤ n := by omega
          grind [Sym2.eq]
        · intro hij
          rcases hij with hij | hij
          · have hadj := p.adj_getVert_succ (i := i.1 + 2) (by omega : i.1 + 2 < p.length)
            have heq : i.1 + 2 + 1 = j.1 + 2 := by omega
            rwa [heq] at hadj
          · have hadj := p.adj_getVert_succ (i := j.1 + 2) (by omega : j.1 + 2 < p.length)
            have heq : j.1 + 2 + 1 = i.1 + 2 := by omega
            rw [heq] at hadj
            exact hadj.symm }
  refine ⟨e, ?_⟩
  intro i
  rfl

/-- The canonical bipartition and leaf bound on an odd path, transported
through a graph isomorphism. -/
theorem path_iso_odd_core_data
    {C : Type*} [Fintype C] [DecidableEq C]
    (H : SimpleGraph C) [DecidableRel H.Adj]
    (m : ℕ) (hm : 1 ≤ m)
    (e : SimpleGraph.pathGraph (2 * m - 1) ≃g H)
    (hacyclic : H.IsAcyclic) :
    ∃ U₁ U₂ : Finset C,
      H.IsTree ∧ H.IsBipartiteWith (U₁ : Set C) (U₂ : Set C) ∧
      U₁ ∪ U₂ = Finset.univ ∧ U₁.card = m ∧ U₂.card = m - 1 ∧
      e ⟨0, by omega⟩ ∈ U₁ ∧ e ⟨2 * m - 2, by omega⟩ ∈ U₁ ∧
      #(Erdos547EC2.leafVertices H) ≤ 2 := by
  classical
  let U₁ : Finset C := Finset.univ.filter fun z => (e.symm z).1 % 2 = 0
  let U₂ : Finset C := Finset.univ.filter fun z => (e.symm z).1 % 2 = 1
  have hU₁card : U₁.card = m := by
    let E := (Finset.univ : Finset (Fin (2 * m - 1))).filter
      fun i => i.1 % 2 = 0
    calc
      U₁.card = E.card := by
        apply Finset.card_bij (fun z _ => e.symm z)
        · intro z hz
          simpa [E, U₁] using (Finset.mem_filter.mp hz).2
        · intro z hz w hw h
          exact e.symm.injective h
        · intro i hi
          refine ⟨e i, ?_, ?_⟩
          · simp only [U₁, Finset.mem_filter, Finset.mem_univ, true_and,
              e.symm_apply_apply]
            exact (Finset.mem_filter.mp hi).2
          · exact e.symm_apply_apply i
      _ = m := card_even_indices_two_mul_sub_one m hm
  have hU₂card : U₂.card = m - 1 := by
    let O := (Finset.univ : Finset (Fin (2 * m - 1))).filter
      fun i => i.1 % 2 = 1
    calc
      U₂.card = O.card := by
        apply Finset.card_bij (fun z _ => e.symm z)
        · intro z hz
          simpa [O, U₂] using (Finset.mem_filter.mp hz).2
        · intro z hz w hw h
          exact e.symm.injective h
        · intro i hi
          refine ⟨e i, ?_, ?_⟩
          · simp only [U₂, Finset.mem_filter, Finset.mem_univ, true_and,
              e.symm_apply_apply]
            exact (Finset.mem_filter.mp hi).2
          · exact e.symm_apply_apply i
      _ = m - 1 := card_odd_indices_two_mul_sub_one m hm
  have hcover : U₁ ∪ U₂ = Finset.univ := by
    ext z
    simp only [Finset.mem_union, U₁, U₂, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [iff_true]
    exact Nat.mod_two_eq_zero_or_one _
  have hpart : H.IsBipartiteWith (U₁ : Set C) (U₂ : Set C) := by
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro z hz₁ hz₂
      have h0 : (e.symm z).1 % 2 = 0 := by simpa [U₁] using hz₁
      have h1 : (e.symm z).1 % 2 = 1 := by simpa [U₂] using hz₂
      omega
    · intro x y hxy
      have hidx : (SimpleGraph.pathGraph (2 * m - 1)).Adj
          (e.symm x) (e.symm y) := by
        rw [← e.map_rel_iff]
        simpa using hxy
      rw [SimpleGraph.pathGraph_adj] at hidx
      rcases hidx with hidx | hidx
      · have hyMod : (e.symm y).1 % 2 = ((e.symm x).1 % 2 + 1) % 2 := by
          rw [← hidx, Nat.add_mod]
        rcases Nat.mod_two_eq_zero_or_one (e.symm x).1 with hx0 | hx1
        · left
          constructor
          · simpa [U₁] using hx0
          · simpa [U₂, hx0] using hyMod
        · right
          constructor
          · simpa [U₂] using hx1
          · simpa [U₁, hx1] using hyMod
      · have hxMod : (e.symm x).1 % 2 = ((e.symm y).1 % 2 + 1) % 2 := by
          rw [← hidx, Nat.add_mod]
        rcases Nat.mod_two_eq_zero_or_one (e.symm y).1 with hy0 | hy1
        · right
          constructor
          · simpa [U₂, hy0] using hxMod
          · simpa [U₁] using hy0
        · left
          constructor
          · simpa [U₁, hy1] using hxMod
          · simpa [U₂] using hy1
  have hconnPath : (SimpleGraph.pathGraph (2 * m - 1)).Connected := by
    have heq : 2 * m - 2 + 1 = 2 * m - 1 := by omega
    have hc := SimpleGraph.pathGraph_connected (2 * m - 2)
    rw [heq] at hc
    exact hc
  have htree : H.IsTree := ⟨e.connected_iff.mp hconnPath, hacyclic⟩
  let first : Fin (2 * m - 1) := ⟨0, by omega⟩
  let last : Fin (2 * m - 1) := ⟨2 * m - 2, by omega⟩
  have hleafSub : Erdos547EC2.leafVertices H ⊆ ({e first, e last} : Finset C) := by
    intro z hz
    have hzdeg : H.degree z = 1 := (Finset.mem_filter.mp hz).2
    by_contra hzEnds
    have hzfirst : z ≠ e first := by
      intro h; apply hzEnds; simp [h]
    have hzlast : z ≠ e last := by
      intro h; apply hzEnds; simp [h]
    let i := e.symm z
    have hi0 : i.1 ≠ 0 := by
      intro hi
      apply hzfirst
      have hif : i = first := Fin.ext (by simpa [first] using hi)
      calc
        z = e i := (e.apply_symm_apply z).symm
        _ = e first := congrArg e hif
    have hilast : i.1 ≠ 2 * m - 2 := by
      intro hi
      apply hzlast
      have hil : i = last := Fin.ext (by simpa [last] using hi)
      calc
        z = e i := (e.apply_symm_apply z).symm
        _ = e last := congrArg e hil
    have hiLower : 1 ≤ i.1 := by omega
    have hiUpper : i.1 + 1 < 2 * m - 1 := by omega
    let ip : Fin (2 * m - 1) := ⟨i.1 - 1, by omega⟩
    let is : Fin (2 * m - 1) := ⟨i.1 + 1, hiUpper⟩
    have hip : (SimpleGraph.pathGraph (2 * m - 1)).Adj i ip := by
      rw [SimpleGraph.pathGraph_adj]
      right
      dsimp [ip]
      omega
    have his : (SimpleGraph.pathGraph (2 * m - 1)).Adj i is := by
      rw [SimpleGraph.pathGraph_adj]
      left
      rfl
    have hpis : ip ≠ is := by
      intro h
      have := congrArg Fin.val h
      dsimp [ip, is] at this
      omega
    have hpair : ({ip, is} : Finset (Fin (2 * m - 1))) ⊆
        (SimpleGraph.pathGraph (2 * m - 1)).neighborFinset i := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> simpa
    have hdegPath : 2 ≤ (SimpleGraph.pathGraph (2 * m - 1)).degree i := by
      calc
        2 = ({ip, is} : Finset (Fin (2 * m - 1))).card := by simp [hpis]
        _ ≤ _ := Finset.card_le_card hpair
        _ = _ := SimpleGraph.card_neighborFinset_eq_degree _ _
    have hdegEq := e.degree_eq i
    have hei : e i = z := e.apply_symm_apply z
    rw [hei] at hdegEq
    omega
  have hleafCard : #(Erdos547EC2.leafVertices H) ≤ 2 := by
    have hp : #({e first, e last} : Finset C) = 1 ∨
        #({e first, e last} : Finset C) = 2 := Finset.card_pair_eq_one_or_two
    have hle : #({e first, e last} : Finset C) ≤ 2 := by rcases hp with hp | hp <;> omega
    exact (Finset.card_le_card hleafSub).trans hle
  refine ⟨U₁, U₂, htree, hpart, hcover, hU₁card, hU₂card, ?_, ?_, hleafCard⟩
  · simp [U₁]
  · have heq : 2 * m - 2 = 2 * (m - 1) := by omega
    simp [U₁, heq]

/-- A tree with at most two degree-one vertices has maximum degree two. -/
theorem degree_le_two_of_leafVertices_le_two
    [Fintype S] [DecidableEq S] [Nontrivial S]
    (T : SimpleGraph S) [DecidableRel T.Adj]
    (hT : T.IsTree) (hleaves : #(Erdos547EC2.leafVertices T) ≤ 2) :
    ∀ z, T.degree z ≤ 2 := by
  classical
  intro z
  by_contra hz
  have hzthree : 3 ≤ T.degree z := by omega
  let q : S → ℕ := fun x => T.degree x + if T.degree x = 1 then 1 else 0
  have hq (x : S) : 2 ≤ q x := by
    have hpos : 0 < T.degree x :=
      hT.connected.preconnected.degree_pos_of_nontrivial x
    by_cases hx : T.degree x = 1 <;> simp [q, hx] <;> omega
  have hqz : 2 < q z := by
    have hznot : T.degree z ≠ 1 := by omega
    simp [q, hznot]
    omega
  have hsumlt : (∑ _x : S, (2 : ℕ)) < ∑ x : S, q x := by
    apply Finset.sum_lt_sum
    · intro x hx
      exact hq x
    · exact ⟨z, Finset.mem_univ _, hqz⟩
  have hsumq : (∑ x : S, q x) =
      (∑ x : S, T.degree x) + #(Erdos547EC2.leafVertices T) := by
    simp only [q, Finset.sum_add_distrib]
    congr 1
    simp [Erdos547EC2.leafVertices]
  have hedge := hT.card_edgeFinset
  have hsumdeg := T.sum_degrees_eq_twice_card_edges
  have hsumtwo : (∑ _x : S, (2 : ℕ)) = 2 * Fintype.card S := by
    simp [Nat.mul_comm]
  rw [hsumtwo, hsumq, hsumdeg] at hsumlt
  have hcard : 2 ≤ Fintype.card S := Fintype.one_lt_card
  omega

private theorem Walk.exists_adj_boundary_of_set
    {G : SimpleGraph S} {s : Set S} {u w : S}
    (p : G.Walk u w) (hu : u ∉ s) (hw : w ∈ s) :
    ∃ a b, a ∉ s ∧ b ∈ s ∧ G.Adj a b := by
  induction p with
  | nil => exact (hu hw).elim
  | @cons u v w huv p ih =>
      by_cases hv : v ∈ s
      · exact ⟨u, v, hu, hv, huv⟩
      · exact ih hv hw

/-- A finite connected graph of maximum degree at most two has a Hamiltonian
path, obtained from a longest path. -/
theorem exists_hamiltonian_path_of_connected_degree_le_two
    [Fintype S] [DecidableEq S]
    (T : SimpleGraph S) [DecidableRel T.Adj]
    (hT : T.Connected) (hdeg : ∀ z, T.degree z ≤ 2) :
    ∃ (u w : S) (p : T.Walk u w), p.IsHamiltonian := by
  classical
  letI : Nonempty S := hT.nonempty
  obtain ⟨u, w, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length T
  refine ⟨u, w, p, hp.isHamiltonian_of_mem ?_⟩
  intro x
  by_contra hx
  obtain ⟨q, hq⟩ := hT.exists_isPath x u
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Walk.exists_adj_boundary_of_set (s := {z | z ∈ p.support})
      q hx p.start_mem_support
  obtain ⟨i, hib, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hb
  by_cases hi0 : i = 0
  · subst i
    have hbu : b = u := by rw [← hib]; simp
    have hau : T.Adj a u := hbu ▸ hab
    have hext : (p.cons hau).IsPath := hp.cons ha
    have hle := hmax a w (p.cons hau) hext
    rw [Walk.length_cons] at hle
    omega
  by_cases hilast : i = p.length
  · subst i
    have hbw : b = w := by rw [← hib]; simp
    have hwa : T.Adj w a := hbw ▸ hab.symm
    have hext : (p.concat hwa).IsPath := hp.concat ha hwa
    have hle := hmax u a (p.concat hwa) hext
    rw [Walk.length_concat] at hle
    omega
  · have hilt : i < p.length := by omega
    let left := p.getVert (i - 1)
    let right := p.getVert (i + 1)
    have hlSub : p.toSubgraph.Adj (p.getVert i) left := by
      rw [← Subgraph.mem_neighborSet, hp.neighborSet_toSubgraph_internal hi0 hilt]
      simp [left]
    have hrSub : p.toSubgraph.Adj (p.getVert i) right := by
      rw [← Subgraph.mem_neighborSet, hp.neighborSet_toSubgraph_internal hi0 hilt]
      simp [right]
    have hbl : T.Adj b left := by rw [← hib]; exact hlSub.adj_sub
    have hbr : T.Adj b right := by rw [← hib]; exact hrSub.adj_sub
    have hlmem : left ∈ p.support := p.getVert_mem_support (i - 1)
    have hrmem : right ∈ p.support := p.getVert_mem_support (i + 1)
    have hal : a ≠ left := fun h => ha (h ▸ hlmem)
    have har : a ≠ right := fun h => ha (h ▸ hrmem)
    have hlr : left ≠ right := by
      intro h
      have hind := hp.getVert_injOn
        (show i - 1 ∈ Set.Iic p.length by simp; omega)
        (show i + 1 ∈ Set.Iic p.length by simp; omega) h
      omega
    have hsubset : ({left, right, a} : Finset S) ⊆ T.neighborFinset b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · simpa using hbl
      · simpa using hbr
      · simpa using hab.symm
    have hthree : 3 ≤ T.degree b := by
      calc
        3 = ({left, right, a} : Finset S).card := by
          simp [hlr, hal.symm, har.symm]
        _ ≤ (T.neighborFinset b).card := Finset.card_le_card hsubset
        _ = T.degree b := T.card_neighborFinset_eq_degree b
    have := hdeg b
    omega

theorem exists_hamiltonian_path_of_leafVertices_le_two
    [Fintype S] [DecidableEq S] [Nontrivial S]
    (T : SimpleGraph S) [DecidableRel T.Adj]
    (hT : T.IsTree) (hleaves : #(Erdos547EC2.leafVertices T) ≤ 2) :
    ∃ (u w : S) (p : T.Walk u w), p.IsHamiltonian :=
  exists_hamiltonian_path_of_connected_degree_le_two T hT.connected
    (degree_le_two_of_leafVertices_le_two T hT hleaves)

private theorem card_used
    [Fintype S] [DecidableEq S] [DecidableEq V]
    {H : SimpleGraph S} {G : SimpleGraph V} (f : H.Copy G) :
    #(Finset.univ.image f) = Fintype.card S := by
  simpa using Finset.card_image_of_injective Finset.univ f.injective

/-- A high-degree arbitrary host vertex has a neighbour outside a given
embedded copy. -/
theorem exists_neighbor_outside_copy
    [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
    (H : SimpleGraph S) (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : H.Copy G) (a : V) (hdeg : Fintype.card S < G.degree a) :
    ∃ w, G.Adj a w ∧ ∀ s, f s ≠ w := by
  classical
  let used : Finset V := Finset.univ.image f
  have hcard : used.card = Fintype.card S := card_used f
  have hlt : used.card < (G.neighborFinset a).card := by
    simpa [hcard] using hdeg
  obtain ⟨w, hwN, hwU⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨w, (G.mem_neighborFinset _ _).mp hwN, ?_⟩
  intro s hfs
  exact hwU (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hfs⟩)

/-- At a centre already used by a copy, looplessness saves one occupied
vertex.  Thus a surplus of two over the copy order permits avoiding two
additional reserved vertices. -/
theorem exists_neighbor_outside_copy_and_pair
    [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
    (H : SimpleGraph S) (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : H.Copy G) (r : S) (a b : V) (hab : a ≠ b)
    (hdeg : Fintype.card S + 1 < G.degree (f r)) :
    ∃ w, G.Adj (f r) w ∧ (∀ s, f s ≠ w) ∧ w ≠ a ∧ w ≠ b := by
  classical
  let used : Finset V := Finset.univ.image f
  let blocked : Finset V := (used.erase (f r)) ∪ {a, b}
  have hcard : used.card = Fintype.card S := card_used f
  have hfr : f r ∈ used := Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  have hpair : ({a, b} : Finset V).card = 2 := Finset.card_pair hab
  have hblocked : blocked.card ≤ Fintype.card S + 1 := by
    calc
      blocked.card ≤ (used.erase (f r)).card + ({a, b} : Finset V).card :=
        Finset.card_union_le _ _
      _ = Fintype.card S + 1 := by
        rw [Finset.card_erase_of_mem hfr, hcard, hpair]
        have hpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨r⟩
        omega
  have hlt : blocked.card < (G.neighborFinset (f r)).card := by
    simpa using lt_of_le_of_lt hblocked hdeg
  obtain ⟨w, hwN, hwB⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hadj : G.Adj (f r) w := (G.mem_neighborFinset _ _).mp hwN
  refine ⟨w, hadj, ?_, ?_, ?_⟩
  · intro s hfs
    apply hwB
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hfs⟩⟩
    intro hwfr
    exact G.irrefl (hwfr ▸ hadj)
  · intro hwa
    apply hwB
    exact Finset.mem_union_right _ (by simp [hwa])
  · intro hwb
    apply hwB
    exact Finset.mem_union_right _ (by simp [hwb])

private theorem mem_triple {A : Type*} [DecidableEq A] {p q r z : A}
    (hz : z ∈ ({p, q, r} : Finset A)) : z = p ∨ z = q ∨ z = r := by
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hz

/-- Glue back the three vertices removed in Zhao's odd-path exception.

The local neighbour descriptions are precisely those supplied by a
Hamiltonian ordering of a tree: `x0-x1-x2-...-xLast-xEnd`.  The core copy is
the induced graph after deleting `x0`, `x1`, and `xEnd`; `x2` is prescribed
to `a`.  The images are `x1 ↦ v`, `x0 ↦ w0`, and `xEnd ↦ wEnd`. -/
theorem extend_triply_trimmed_path_copy
    [Fintype S] [DecidableEq S] [DecidableEq V]
    (T : SimpleGraph S) (G : SimpleGraph V)
    (x0 x1 x2 xLast xEnd : S)
    (h01 : x0 ≠ x1) (h0E : x0 ≠ xEnd) (h1E : x1 ≠ xEnd)
    (hx2D : x2 ∉ ({x0, x1, xEnd} : Finset S))
    (hxLastD : xLast ∉ ({x0, x1, xEnd} : Finset S))
    (hx0 : ∀ z, T.Adj x0 z → z = x1)
    (hx1 : ∀ z, T.Adj x1 z → z = x0 ∨ z = x2)
    (hxEnd : ∀ z, T.Adj xEnd z → z = xLast)
    (f : (T.induce ((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)).Copy G)
    (a v w0 wEnd : V)
    (hroot : f ⟨x2, by simpa using hx2D⟩ = a)
    (hav : G.Adj a v) (hvw0 : G.Adj v w0)
    (hLastEnd : G.Adj (f ⟨xLast, by simpa using hxLastD⟩) wEnd)
    (hv_unused : ∀ z, f z ≠ v)
    (hw0_unused : ∀ z, f z ≠ w0)
    (hwEnd_unused : ∀ z, f z ≠ wEnd)
    (hvw0ne : v ≠ w0) (hvEnd : v ≠ wEnd) (hw0End : w0 ≠ wEnd) :
    ∃ F : T.Copy G,
      F x0 = w0 ∧ F x1 = v ∧ F xEnd = wEnd ∧
      ∀ z : ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)), F z = f z := by
  classical
  let D : Finset S := {x0, x1, xEnd}
  let g : D → V := fun z =>
    if z.1 = x0 then w0 else if z.1 = x1 then v else wEnd
  have hg : Function.Injective g := by
    intro p q hpq
    apply Subtype.ext
    have hp := mem_triple p.property
    have hq := mem_triple q.property
    rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq
    · exact hp.trans hq.symm
    · exfalso
      apply hvw0ne
      simpa [g, hp, hq, h01, h01.symm] using hpq.symm
    · exfalso
      apply hw0End
      simpa [g, hp, hq, h0E, h0E.symm, h1E, h1E.symm] using hpq
    · exfalso
      apply hvw0ne
      simpa [g, hp, hq, h01, h01.symm] using hpq
    · exact hp.trans hq.symm
    · exfalso
      apply hvEnd
      simpa [g, hp, hq, h01, h01.symm, h0E, h0E.symm, h1E, h1E.symm] using hpq
    · exfalso
      apply hw0End
      simpa [g, hp, hq, h0E, h0E.symm, h1E, h1E.symm] using hpq.symm
    · exfalso
      apply hvEnd
      simpa [g, hp, hq, h01, h01.symm, h0E, h0E.symm, h1E, h1E.symm] using hpq.symm
    · exact hp.trans hq.symm
  have hfg : ∀ z p, f z ≠ g p := by
    intro z p
    rcases mem_triple p.property with hp | hp | hp
    · simpa [g, hp] using hw0_unused z
    · simpa [g, hp, h01.symm] using hv_unused z
    · simpa [g, hp, h0E.symm, h1E.symm] using hwEnd_unused z
  have hDD : ∀ p q : D, T.Adj p q → G.Adj (g p) (g q) := by
    intro p q hpq
    rcases mem_triple p.property with hp | hp | hp
    · have hq : q.1 = x1 := hx0 q.1 (by simpa [hp] using hpq)
      simpa [g, hp, hq, h01, h01.symm] using hvw0.symm
    · rcases hx1 q.1 (by simpa [hp] using hpq) with hq | hq
      · simpa [g, hp, hq, h01, h01.symm] using hvw0
      · exact False.elim (hx2D (by simpa [D, hq] using q.property))
    · have hq : q.1 = xLast := hxEnd q.1 (by simpa [hp] using hpq)
      exact False.elim (hxLastD (by simpa [D, hq] using q.property))
  have hDC : ∀ p : D, ∀ z : ↥(((D : Set S)ᶜ)),
      T.Adj p z → G.Adj (g p) (f z) := by
    intro p z hpz
    rcases mem_triple p.property with hp | hp | hp
    · have hz : z.1 = x1 := hx0 z.1 (by simpa [hp] using hpz)
      exfalso
      exact z.property (by simp [D, hz])
    · rcases hx1 z.1 (by simpa [hp] using hpz) with hz | hz
      · exfalso
        exact z.property (by simp [D, hz])
      · have hgp : g p = v := by simp [g, hp, h01.symm]
        rw [hgp]
        have hzf : f z = a := by
          rw [← hroot]
          exact congrArg f (Subtype.ext hz)
        rw [hzf]
        exact hav.symm
    · have hz : z.1 = xLast := hxEnd z.1 (by simpa [hp] using hpz)
      have hgp : g p = wEnd := by simp [g, hp, h0E.symm, h1E.symm]
      rw [hgp]
      have hzf : f z = f ⟨xLast, by simpa using hxLastD⟩ :=
        congrArg f (Subtype.ext hz)
      rw [hzf]
      exact hLastEnd.symm
  obtain ⟨F, hFD, hFcore⟩ :=
    Erdos547b.ZhaoLemma710Alt.copy_of_induce_compl_and_extension
      T G D f g hg hfg hDD hDC
  refine ⟨F, ?_, ?_, ?_, hFcore⟩
  · simpa [g] using hFD ⟨x0, by simp [D]⟩
  · simpa [g, h01.symm] using hFD ⟨x1, by simp [D]⟩
  · simpa [g, h0E.symm, h1E.symm] using hFD ⟨xEnd, by simp [D]⟩

/-- The degree form of the three-vertex gluing.  If the original tree has
`n+1` vertices, the triply trimmed core has `n-2` vertices.  Degree `n` at
`v` and at the embedded opposite support supplies two distinct unused
endpoint images. -/
theorem extend_triply_trimmed_path_copy_of_degree
    [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
    (T : SimpleGraph S) (G : SimpleGraph V) [DecidableRel G.Adj]
    (x0 x1 x2 xLast xEnd : S)
    (n : ℕ) (hcoreCard :
      Fintype.card ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)) = n - 2)
    (hn : 2 ≤ n)
    (h01 : x0 ≠ x1) (h0E : x0 ≠ xEnd) (h1E : x1 ≠ xEnd)
    (hx2D : x2 ∉ ({x0, x1, xEnd} : Finset S))
    (hxLastD : xLast ∉ ({x0, x1, xEnd} : Finset S))
    (hx0 : ∀ z, T.Adj x0 z → z = x1)
    (hx1 : ∀ z, T.Adj x1 z → z = x0 ∨ z = x2)
    (hxEnd : ∀ z, T.Adj xEnd z → z = xLast)
    (f : (T.induce ((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)).Copy G)
    (a v : V)
    (hroot : f ⟨x2, by simpa using hx2D⟩ = a)
    (hav : G.Adj a v)
    (hv_unused : ∀ z, f z ≠ v)
    (hvDegree : n ≤ G.degree v)
    (hLastDegree : n ≤ G.degree (f ⟨xLast, by simpa using hxLastD⟩)) :
    ∃ F : T.Copy G, F x1 = v ∧
      ∀ z : ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)), F z = f z := by
  let core := T.induce ((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)
  have hvDeg' : Fintype.card ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)) <
      G.degree v := by rw [hcoreCard]; omega
  obtain ⟨w0, hvw0, hw0_unused⟩ :=
    exists_neighbor_outside_copy core G f v hvDeg'
  have hvw0ne : v ≠ w0 := hvw0.ne
  have hLastDeg' :
      Fintype.card ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)) + 1 <
        G.degree (f ⟨xLast, by simpa using hxLastD⟩) := by
    rw [hcoreCard]
    omega
  obtain ⟨wEnd, hLastEnd, hwEnd_unused, hwEndv, hwEndw0⟩ :=
    exists_neighbor_outside_copy_and_pair core G f
      ⟨xLast, by simpa using hxLastD⟩ v w0 hvw0ne hLastDeg'
  obtain ⟨F, _, hF1, _, hFcore⟩ :=
    extend_triply_trimmed_path_copy T G x0 x1 x2 xLast xEnd
      h01 h0E h1E hx2D hxLastD hx0 hx1 hxEnd f a v w0 wEnd
      hroot hav hvw0 hLastEnd hv_unused hw0_unused hwEnd_unused
      hvw0ne hwEndv.symm hwEndw0.symm
  exact ⟨F, hF1, hFcore⟩

/-- Dense adjacency inside `A` supplies the exceptional edge `a-v`, while
avoiding every endpoint reserved by the host two-path system. -/
theorem exists_adj_pair_avoiding_path_endpoints
    [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj]
    (A B₂ : Finset V) (l : ℕ)
    (P : Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem H A B₂)
    (hB₂ : B₂.card ≤ l) (hAlarge : 3 * l < A.card)
    (hAA : ∀ a ∈ A, A.card - l ≤ (G.neighborFinset a ∩ A).card) :
    ∃ a v, a ∈ A ∧ v ∈ A ∧ a ∉ P.endpoints ∧ v ∉ P.endpoints ∧
      G.Adj a v := by
  classical
  have hEcard : P.endpoints.card ≤ 2 * l := by
    rw [P.card_endpoints]
    omega
  have hEA : P.endpoints ⊆ A := P.endpoints_subset
  have hEltA : P.endpoints.card < A.card := by omega
  have hdiff : 0 < (A \ P.endpoints).card := by
    rw [Finset.card_sdiff_of_subset hEA]
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hdiff
  have haA := (Finset.mem_sdiff.mp ha).1
  have haE := (Finset.mem_sdiff.mp ha).2
  let N : Finset V := G.neighborFinset a ∩ A
  have hN : A.card - l ≤ N.card := hAA a haA
  have hEN : P.endpoints.card < N.card := by omega
  obtain ⟨v, hvN, hvE⟩ := Finset.exists_mem_notMem_of_card_lt_card hEN
  exact ⟨a, v, haA, (Finset.mem_inter.mp hvN).2, haE, hvE,
    (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hvN).1⟩

/-- Restrict the endpoint side of a supplied host path system after deleting
one vertex which is known not to be one of its endpoints. -/
def restrict_centered_paths_erase
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B B₂ : Finset V)
    (P : Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem
      (G.between (A : Set V) (B : Set V)) A B₂)
    (v : V) (hv : v ∉ P.endpoints) (hB₂B : B₂ ⊆ B) :
    Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem
      (G.between ((A.erase v : Finset V) : Set V) (B : Set V)) (A.erase v) B₂ where
  left := P.left
  right := P.right
  left_mem y := by
    apply Finset.mem_erase.mpr
    refine ⟨?_, P.left_mem y⟩
    intro h
    apply hv
    rw [Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem.endpoints]
    exact Finset.mem_image.mpr ⟨(y, 0), Finset.mem_univ _, by simp [h]⟩
  right_mem y := by
    apply Finset.mem_erase.mpr
    refine ⟨?_, P.right_mem y⟩
    intro h
    apply hv
    rw [Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem.endpoints]
    exact Finset.mem_image.mpr ⟨(y, 1), Finset.mem_univ _, by simp [h]⟩
  adj_left y := by
    rw [SimpleGraph.between_adj]
    have hG : G.Adj (P.left y) y :=
      (SimpleGraph.between_adj.mp (P.adj_left y)).1
    exact ⟨hG, Or.inl ⟨by
      apply Finset.mem_erase.mpr
      refine ⟨?_, P.left_mem y⟩
      intro h
      apply hv
      rw [Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem.endpoints]
      exact Finset.mem_image.mpr ⟨(y, 0), Finset.mem_univ _, by simp [h]⟩,
      hB₂B y.property⟩⟩
  adj_right y := by
    rw [SimpleGraph.between_adj]
    have hG : G.Adj y (P.right y) :=
      (SimpleGraph.between_adj.mp (P.adj_right y)).1
    exact ⟨hG, Or.inr ⟨hB₂B y.property, by
      apply Finset.mem_erase.mpr
      refine ⟨?_, P.right_mem y⟩
      intro h
      apply hv
      rw [Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem.endpoints]
      exact Finset.mem_image.mpr ⟨(y, 1), Finset.mem_univ _, by simp [h]⟩⟩⟩
  endpointInjective := P.endpointInjective

/-- End-to-end invocation of Lemma 7.10 followed by the corrected
three-vertex odd-path gluing step.

The hypotheses about the triply trimmed source (`hcoreTree`, `hpart`, the
two exact color classes, and the local endpoint neighbour descriptions) are
the data obtained from a Hamiltonian ordering of a tree with at most two
leaves.  All host hypotheses are direct fields of `LowLeafHostPackage`, plus
the dense `A-A` and global high-degree properties retained in EC3. -/
theorem odd_path_exception_of_core_data
    [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
    (T : SimpleGraph S) (G : SimpleGraph V)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (n l : ℕ) (hcard : Fintype.card S = n + 1) (hn : 2 ≤ n)
    (x0 x1 x2 xLast xEnd : S)
    (h01 : x0 ≠ x1) (h0E : x0 ≠ xEnd) (h1E : x1 ≠ xEnd)
    (hx2D : x2 ∉ ({x0, x1, xEnd} : Finset S))
    (hxLastD : xLast ∉ ({x0, x1, xEnd} : Finset S))
    (hx0 : ∀ z, T.Adj x0 z → z = x1)
    (hx1 : ∀ z, T.Adj x1 z → z = x0 ∨ z = x2)
    (hxEnd : ∀ z, T.Adj xEnd z → z = xLast)
    (U₁ U₂ : Finset ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)))
    (hcoreTree : (T.induce ((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)).IsTree)
    (hpart : (T.induce ((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)).IsBipartiteWith
      (U₁ : Set _) (U₂ : Set _))
    (hcover : U₁ ∪ U₂ = Finset.univ)
    (hx2U₁ : (⟨x2, by simpa using hx2D⟩ :
      ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ))) ∈ U₁)
    (hxLastU₁ : (⟨xLast, by simpa using hxLastD⟩ :
      ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ))) ∈ U₁)
    (hleaves : #(Erdos547EC2.leafVertices
      (T.induce ((({x0, x1, xEnd} : Finset S) : Set S)ᶜ))) ≤ l)
    (hU₁large : 26 * l ≤ U₁.card) (hU₂large : 26 * l ≤ U₂.card)
    (A B B₁ B₂ : Finset V)
    (hAB : Disjoint A B) (hBsplit : B₁ ∪ B₂ = B)
    (hBdisj : Disjoint B₁ B₂) (hB₂B : B₂ ⊆ B)
    (hU₁cap : U₁.card + 1 ≤ A.card) (hU₂cap : U₂.card ≤ B.card)
    (hB₂le : B₂.card ≤ l) (hAlarge : 3 * l < A.card)
    (hleft : ∀ a ∈ A, B₁.card - l ≤ (G.neighborFinset a ∩ B₁).card)
    (hright : ∀ b ∈ B₁, A.card - l ≤ (G.neighborFinset b ∩ A).card)
    (hAA : ∀ a ∈ A, A.card - l ≤ (G.neighborFinset a ∩ A).card)
    (hhigh : ∀ a ∈ A, n ≤ G.degree a)
    (P : Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem
      (G.between (A : Set V) (B : Set V)) A B₂) :
    T ⊑ G := by
  classical
  obtain ⟨a, v, haA, hvA, haE, hvE, hav⟩ :=
    exists_adj_pair_avoiding_path_endpoints G
      (G.between (A : Set V) (B : Set V)) A B₂ l P hB₂le hAlarge hAA
  let X : Finset V := A.erase v
  let H : SimpleGraph V := G.between (X : Set V) (B : Set V)
  let Q := restrict_centered_paths_erase G A B B₂ P v hvE hB₂B
  have haX : a ∈ X := Finset.mem_erase.mpr ⟨hav.ne, haA⟩
  have hXB : Disjoint X B := by
    exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hAB
  have hHbip : H.IsBipartiteWith (X : Set V) (B : Set V) := by
    exact SimpleGraph.between_isBipartiteWith (by
      simpa [Finset.disjoint_left] using Finset.disjoint_left.mp hXB)
  have hXcard : X.card + 1 = A.card := by
    change (A.erase v).card + 1 = A.card
    exact Finset.card_erase_add_one hvA
  have hU₁X : U₁.card ≤ X.card := by omega
  have hleftH : ∀ z ∈ X,
      B₁.card - l ≤ (H.neighborFinset z ∩ B₁).card := by
    intro z hz
    have hzA : z ∈ A := (Finset.mem_erase.mp hz).2
    have heq : H.neighborFinset z ∩ B₁ = G.neighborFinset z ∩ B₁ := by
      ext w
      simp only [Finset.mem_inter, H.mem_neighborFinset, G.mem_neighborFinset]
      constructor
      · intro hw
        exact ⟨(SimpleGraph.between_adj.mp hw.1).1, hw.2⟩
      · intro hw
        rw [show H = G.between (X : Set V) (B : Set V) by rfl,
          SimpleGraph.between_adj]
        refine ⟨⟨hw.1, Or.inl ⟨hz, ?_⟩⟩, hw.2⟩
        rw [← hBsplit]
        exact Finset.mem_union_left B₂ hw.2
    rw [heq]
    exact hleft z hzA
  have hrightH : ∀ b ∈ B₁,
      X.card - l ≤ (H.neighborFinset b ∩ X).card := by
    intro b hb
    have hbB : b ∈ B := by rw [← hBsplit]; exact Finset.mem_union_left B₂ hb
    have heq : H.neighborFinset b ∩ X = G.neighborFinset b ∩ X := by
      ext w
      simp only [Finset.mem_inter, H.mem_neighborFinset, G.mem_neighborFinset]
      constructor
      · intro hw
        exact ⟨(SimpleGraph.between_adj.mp hw.1).1, hw.2⟩
      · intro hw
        rw [show H = G.between (X : Set V) (B : Set V) by rfl,
          SimpleGraph.between_adj]
        exact ⟨⟨hw.1, Or.inr ⟨hbB, hw.2⟩⟩, hw.2⟩
    rw [heq]
    have hloss : (G.neighborFinset b ∩ A).card ≤
        (G.neighborFinset b ∩ X).card + 1 := by
      have hcoverA : G.neighborFinset b ∩ A ⊆
          (G.neighborFinset b ∩ X) ∪ {v} := by
        intro w hw
        have hw' := Finset.mem_inter.mp hw
        by_cases hwv : w = v
        · exact Finset.mem_union_right _ (by simp [hwv])
        · apply Finset.mem_union_left
          apply Finset.mem_inter.mpr
          refine ⟨hw'.1, ?_⟩
          change w ∈ A.erase v
          exact Finset.mem_erase.mpr ⟨hwv, hw'.2⟩
      exact (Finset.card_le_card hcoverA).trans
        (by simpa using Finset.card_union_le (G.neighborFinset b ∩ X) ({v} : Finset V))
    have hold := hright b hb
    omega
  have hQendpoints : Q.endpoints = P.endpoints := rfl
  obtain ⟨fH, hrootH, hfU₁, hfU₂⟩ :=
    Erdos547b.ZhaoLemma710ApplicationAlt.zhao_lemma_7_10
      U₁ U₂ X B B₁ B₂ l ⟨x2, by simpa using hx2D⟩ a
      hcoreTree hpart hcover hx2U₁ hleaves hU₁large hU₂large
      hHbip hBsplit hBdisj hU₁X hU₂cap hleftH hrightH hB₂le Q haX
      (by rw [hQendpoints]; exact haE)
  let f : (T.induce ((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)).Copy G :=
    (SimpleGraph.Copy.ofLE H G SimpleGraph.between_le).comp fH
  have hroot : f ⟨x2, by simpa using hx2D⟩ = a := by
    simpa [f] using hrootH
  have hv_unused : ∀ z, f z ≠ v := by
    intro z hfv
    have hzAll : z ∈ U₁ ∪ U₂ := by rw [hcover]; exact Finset.mem_univ z
    have hz := Finset.mem_union.mp hzAll
    rcases hz with hz | hz
    · have hfX := hfU₁ z hz
      exact (Finset.mem_erase.mp hfX).1 (by simpa [f] using hfv)
    · have hfB := hfU₂ z hz
      have hvnotB : v ∉ B := (Finset.disjoint_left.mp hAB) hvA
      exact hvnotB (by simpa [f] using hfv ▸ hfB)
  have hLastA : f ⟨xLast, by simpa using hxLastD⟩ ∈ A := by
    have hx := hfU₁ ⟨xLast, by simpa using hxLastD⟩ hxLastU₁
    exact (Finset.mem_erase.mp hx).2
  have hcoreCard :
      Fintype.card ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)) = n - 2 := by
    change Fintype.card {z : S // z ∉ ({x0, x1, xEnd} : Finset S)} = _
    rw [Fintype.card_subtype_compl
      (fun z : S => z ∈ ({x0, x1, xEnd} : Finset S))]
    rw [Fintype.card_coe]
    have htriple : ({x0, x1, xEnd} : Finset S).card = 3 := by
      simp [h01, h0E, h1E, h01.symm, h0E.symm, h1E.symm]
    rw [htriple, hcard]
    omega
  obtain ⟨F, -, -⟩ := extend_triply_trimmed_path_copy_of_degree
    T G x0 x1 x2 xLast xEnd n hcoreCard hn h01 h0E h1E
      hx2D hxLastD hx0 hx1 hxEnd f a v hroot hav hv_unused
      (hhigh v hvA) (hhigh _ hLastA)
  exact ⟨F.toHom, F.injective⟩

/-- The Hamiltonian-ordering wrapper: all source-core hypotheses of
`odd_path_exception_of_core_data` are constructed from the path itself. -/
theorem odd_path_exception_of_hamiltonian
    [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
    (T : SimpleGraph S) (G : SimpleGraph V)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (n l : ℕ) (hcard : Fintype.card S = n + 1)
    (hodd : n % 2 = 1) (hn : 4 ≤ n) (hl : 2 ≤ l)
    (hlarge : 26 * l + 1 ≤ n / 2)
    {u w : S} (p : T.Walk u w) (hT : T.IsTree) (hp : p.IsHamiltonian)
    (A B B₁ B₂ : Finset V)
    (hAcard : A.card = (n + 1) / 2) (hBcard : n / 2 - 1 ≤ B.card)
    (hAB : Disjoint A B) (hBsplit : B₁ ∪ B₂ = B)
    (hBdisj : Disjoint B₁ B₂) (hB₂B : B₂ ⊆ B)
    (hB₂le : B₂.card ≤ l)
    (hleft : ∀ a ∈ A, B₁.card - l ≤ (G.neighborFinset a ∩ B₁).card)
    (hright : ∀ b ∈ B₁, A.card - l ≤ (G.neighborFinset b ∩ A).card)
    (hAA : ∀ a ∈ A, A.card - l ≤ (G.neighborFinset a ∩ A).card)
    (hhigh : ∀ a ∈ A, n ≤ G.degree a)
    (P : Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem
      (G.between (A : Set V) (B : Set V)) A B₂) :
    T ⊑ G := by
  classical
  let m := n / 2
  have hnshape : n = 2 * m + 1 := by
    dsimp [m]
    omega
  have hm : 1 ≤ m := by omega
  have hcoreShape : n - 2 = 2 * m - 1 := by omega
  have hlen : p.length = n := by
    have hpLen := hp.length_eq
    rw [hcard] at hpLen
    omega
  have hget : ∀ i j, i ≤ n → j ≤ n →
      p.getVert i = p.getVert j → i = j := by
    intro i j hi hj hij
    exact hp.isPath.getVert_injOn (by simpa [hlen]) (by simpa [hlen]) hij
  let x0 := p.getVert 0
  let x1 := p.getVert 1
  let x2 := p.getVert 2
  let xLast := p.getVert (n - 1)
  let xEnd := p.getVert n
  have h01 : x0 ≠ x1 := by
    intro h
    have := hget 0 1 (by omega) (by omega) h
    omega
  have h0E : x0 ≠ xEnd := by
    intro h
    have := hget 0 n (by omega) (by omega) h
    omega
  have h1E : x1 ≠ xEnd := by
    intro h
    have := hget 1 n (by omega) (by omega) h
    omega
  have hx2D : x2 ∉ ({x0, x1, xEnd} : Finset S) := by
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · have := hget 2 0 (by omega) (by omega) h; omega
    · have := hget 2 1 (by omega) (by omega) h; omega
    · have := hget 2 n (by omega) (by omega) h; omega
  have hxLastD : xLast ∉ ({x0, x1, xEnd} : Finset S) := by
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · have := hget (n - 1) 0 (by omega) (by omega) h; omega
    · have := hget (n - 1) 1 (by omega) (by omega) h; omega
    · have := hget (n - 1) n (by omega) (by omega) h; omega
  have hx0 : ∀ z, T.Adj x0 z → z = x1 := by
    simpa [x0, x1] using hamiltonian_tree_first_neighbor T p hT hp (by omega)
  have hx1 : ∀ z, T.Adj x1 z → z = x0 ∨ z = x2 := by
    simpa [x0, x1, x2] using hamiltonian_tree_second_neighbors T p hT hp (by omega)
  have hxEnd : ∀ z, T.Adj xEnd z → z = xLast := by
    have hh := hamiltonian_tree_last_neighbor T p hT hp (by omega)
    simpa [xEnd, xLast, hlen] using hh
  obtain ⟨e, he⟩ := exists_triply_trimmed_path_iso
    T p hT hp n (2 * m - 1) hcoreShape.symm hcard hn
  have hcoreEq :
      T.induce ((({p.getVert 0, p.getVert 1, p.getVert n} : Finset S) : Set S)ᶜ) =
      T.induce ((({x0, x1, xEnd} : Finset S) : Set S)ᶜ) := by rfl
  obtain ⟨U₁, U₂, hcoreTree, hpart, hcover, hU₁card, hU₂card,
      heFirst, heLast, hcoreLeaves⟩ :=
    path_iso_odd_core_data
      (T.induce ((({x0, x1, xEnd} : Finset S) : Set S)ᶜ)) m hm
      (by simpa [x0, x1, xEnd] using e) (hT.isAcyclic.induce _)
  have he0 : (e ⟨0, by omega⟩).1 = x2 := by
    have h := he ⟨0, by omega⟩
    simpa [x2] using h
  have heL : (e ⟨2 * m - 2, by omega⟩).1 = xLast := by
    have h := he ⟨2 * m - 2, by omega⟩
    have hindex : (2 * m - 2 : ℕ) + 2 = n - 1 := by omega
    simpa [xLast, hindex] using h
  have hx2U₁ : (⟨x2, by simpa using hx2D⟩ :
      ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ))) ∈ U₁ := by
    have heq : (e ⟨0, by omega⟩) =
        (⟨x2, by simpa using hx2D⟩ :
          ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ))) := Subtype.ext he0
    simpa [heq] using heFirst
  have hxLastU₁ : (⟨xLast, by simpa using hxLastD⟩ :
      ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ))) ∈ U₁ := by
    have heq : (e ⟨2 * m - 2, by omega⟩) =
        (⟨xLast, by simpa using hxLastD⟩ :
          ↥(((({x0, x1, xEnd} : Finset S) : Set S)ᶜ))) := Subtype.ext heL
    simpa [heq] using heLast
  have hleaves : #(Erdos547EC2.leafVertices
      (T.induce ((({x0, x1, xEnd} : Finset S) : Set S)ᶜ))) ≤ l :=
    hcoreLeaves.trans hl
  have hU₁large : 26 * l ≤ U₁.card := by rw [hU₁card]; omega
  have hU₂large : 26 * l ≤ U₂.card := by rw [hU₂card]; omega
  have hU₁cap : U₁.card + 1 ≤ A.card := by
    rw [hU₁card, hAcard]
    omega
  have hU₂cap : U₂.card ≤ B.card := by
    rw [hU₂card]
    simpa [m] using hBcard
  have hAlarge : 3 * l < A.card := by
    rw [hAcard]
    omega
  exact odd_path_exception_of_core_data T G n l hcard (by omega)
    x0 x1 x2 xLast xEnd h01 h0E h1E hx2D hxLastD hx0 hx1 hxEnd
    U₁ U₂ hcoreTree hpart hcover hx2U₁ hxLastU₁ hleaves
    hU₁large hU₂large A B B₁ B₂ hAB hBsplit hBdisj hB₂B
    hU₁cap hU₂cap hB₂le hAlarge hleft hright hAA hhigh P

/-- The complete odd-path exceptional case.  A finite tree with at most two
leaves is a path; the Hamiltonian ordering furnished by the preceding lemma
then supplies the triply-trimmed core used by Zhao's Lemma 7.10. -/
theorem odd_path_exception_of_tree
    [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
    (T : SimpleGraph S) (G : SimpleGraph V)
    [DecidableRel T.Adj] [DecidableRel G.Adj]
    (n l : ℕ) (hcard : Fintype.card S = n + 1)
    (hodd : n % 2 = 1) (hn : 4 ≤ n) (hl : 2 ≤ l)
    (hlarge : 26 * l + 1 ≤ n / 2)
    (hT : T.IsTree)
    (hleaves : #(Erdos547EC2.leafVertices T) ≤ 2)
    (A B B₁ B₂ : Finset V)
    (hAcard : A.card = (n + 1) / 2) (hBcard : n / 2 - 1 ≤ B.card)
    (hAB : Disjoint A B) (hBsplit : B₁ ∪ B₂ = B)
    (hBdisj : Disjoint B₁ B₂) (hB₂B : B₂ ⊆ B)
    (hB₂le : B₂.card ≤ l)
    (hleft : ∀ a ∈ A, B₁.card - l ≤ (G.neighborFinset a ∩ B₁).card)
    (hright : ∀ b ∈ B₁, A.card - l ≤ (G.neighborFinset b ∩ A).card)
    (hAA : ∀ a ∈ A, A.card - l ≤ (G.neighborFinset a ∩ A).card)
    (hhigh : ∀ a ∈ A, n ≤ G.degree a)
    (P : Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem
      (G.between (A : Set V) (B : Set V)) A B₂) :
    T ⊑ G := by
  classical
  have htwo : 2 ≤ Fintype.card S := by rw [hcard]; omega
  letI : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp htwo
  obtain ⟨u, w, p, hp⟩ :=
    exists_hamiltonian_path_of_leafVertices_le_two T hT hleaves
  exact odd_path_exception_of_hamiltonian T G n l hcard hodd hn hl hlarge
    p hT hp A B B₁ B₂ hAcard hBcard hAB hBsplit hBdisj hB₂B hB₂le
    hleft hright hAA hhigh P


end Erdos547b.ZhaoOddPathException74

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma74

open SimpleGraph

variable {A V : Type*} [Fintype A] [DecidableEq A]
  [Fintype V] [DecidableEq V]

/-- The last low-leaf exception is a path.  Reconstruct the pruned host
package, take a Hamiltonian ordering of the source, and invoke the checked
odd-path endpoint of Lemma 7.10. -/
theorem EC3Witness.contains_of_odd_path
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (hsource : 1782 * (s + q) ≤ n) (hrpos : 0 < s + q)
    (T : SimpleGraph A) [DecidableRel T.Adj] [Nontrivial A]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1)
    (hleaves : (Erdos547EC2.leafVertices T).card ≤ 2)
    (hodd : n % 2 = 1) : T ⊑ G := by
  classical
  let r := s + q
  let l := 33 * r
  have hqr : q ≤ l := by simp [l, r]; omega
  have hsr : s ≤ l := by simp [l, r]; omega
  obtain ⟨B₁, _hBsub, hAB₁, hBlower, hBupper, hAA, hBA, hAB⟩ :=
    h.exists_prunedPair hscale hqr hsr
  have hABl : ∀ a ∈ h.A₀,
      B₁.card - l ≤ (G.neighborFinset a ∩ B₁).card := by
    intro a ha
    exact le_trans (by simp [l, r]; omega) (hAB a ha)
  have hlargeDeg : ∀ a ∈ h.A₀,
      n ≤ Erdos547EC2.degreeInto G a Finset.univ := by
    intro a ha
    rw [degreeInto_eq_neighborFinset_inter, Finset.inter_univ,
      G.card_neighborFinset_eq_degree]
    exact h.high_A₀ a ha
  have h7 : 7 * r < n / 2 := by simp [r]; omega
  obtain ⟨P⟩ := Erdos547EC2.exists_lowLeafHostPackage
    G h.A₀ B₁ n s r l h.card_host hAB₁ h.card_A₀ hlargeDeg
      hBlower hBupper hAA hBA hABl (by simp [r]) (by simp [l, r]; omega) h7
  have hABhost : Disjoint h.A₀ P.B :=
    Finset.disjoint_coe.mp P.restricted_bipartite.disjoint
  have hB₂sub : P.B₂ ⊆ P.B := by
    rw [← P.B_split]
    exact Finset.subset_union_right
  have hleftG : ∀ a ∈ h.A₀,
      B₁.card - l ≤ (G.neighborFinset a ∩ B₁).card := by
    intro a ha
    rw [← P.left_inter_eq a ha]
    exact P.left_degree_bound a ha
  have hrightG : ∀ b ∈ B₁,
      h.A₀.card - l ≤ (G.neighborFinset b ∩ h.A₀).card := by
    intro b hb
    rw [← P.right_inter_eq b hb]
    exact P.right_degree_bound b hb
  let paths : Erdos547b.ZhaoLemma710Alt.CenteredTwoPathSystem
      (G.between (h.A₀ : Set V) (P.B : Set V)) h.A₀ P.B₂ := by
    simpa [Erdos547EC2.lowLeafHostGraph] using P.paths
  apply Erdos547b.ZhaoOddPathException74.odd_path_exception_of_tree
    T G n l hcardT hodd (by omega) (by simp [l, r]; omega)
      (by simp [l, r]; omega) hT hleaves h.A₀ P.B B₁ P.B₂ h.card_A₀
        P.card_B_lower hABhost P.B_split P.B₁_B₂_disjoint hB₂sub P.card_B₂_le
          hleftG hrightG hAA h.high_A₀ paths

/-- Zhao's EC3 embedding lemma (Lemma 7.4), in exact finite form. -/
theorem EC3Witness.contains_every_exact_tree
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : EC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (hsource : 1782 * (s + q) ≤ n) (hrpos : 0 < s + q)
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1) :
    T ⊑ G := by
  classical
  have hn : 2 ≤ n := by omega
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  rcases h.contains_or_nearIdeal_or_atMostTwoLeaves hscale hsource hrpos
      T hT hcardT with hcopy | hnear | hpath
  · exact hcopy
  · obtain ⟨U₁, U₂, hU⟩ := hnear
    exact Erdos547b.ZhaoNearIdealEC374.EC3Witness.contains_of_nearIdealPartition
      G n q s h hscale hsource hrpos T hT hcardT U₁ U₂ hU
  · exact h.contains_of_odd_path hscale hsource hrpos T hT hcardT
      hpath.1 hpath.2

theorem RawEC3Witness.contains_every_exact_tree
    {G : SimpleGraph V} [DecidableRel G.Adj] {n q s : ℕ}
    (h : RawEC3Witness G n q) (hscale : q * n ≤ s * (s + 1))
    (hsource : 1782 * (s + q) ≤ n) (hrpos : 0 < s + q)
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcardT : Fintype.card A = n + 1) :
    T ⊑ G :=
  h.normalize.contains_every_exact_tree hscale hsource hrpos T hT hcardT

end Erdos547b.ZhaoLemma74

#print axioms Erdos547b.ZhaoLemma74.EC3Witness.contains_every_exact_tree
#print axioms Erdos547b.ZhaoLemma74.RawEC3Witness.contains_every_exact_tree
