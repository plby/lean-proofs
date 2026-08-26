import ErdosProblems.Erdos556.ForbiddenOddCycleDecomposition
import ErdosProblems.Erdos556.ThreeColourTools
import ErdosProblems.Erdos556.CubeMatchingGeometry

/-! Simultaneous decompositions and the resulting 27 vertex profiles. -/

namespace Erdos556

open SimpleGraph Finset

structure ThreeColourDecomposition {V : Type*} (c : ThreeColouring V) (E D : ℝ) where
  bipartite : Fin 3 → SimpleGraph V
  sparse : Fin 3 → SimpleGraph V
  stars : Fin 3 → Finset V
  bicolouring : ∀ i, (bipartite i).Coloring Bool
  bipartite_le : ∀ i, bipartite i ≤ c.graph i
  sparse_le : ∀ i, sparse i ≤ c.graph i
  bipartite_off : ∀ i u v, (bipartite i).Adj u v → u ∉ stars i ∧ v ∉ stars i
  sparse_on : ∀ i u v, (sparse i).Adj u v → u ∈ stars i ∧ v ∈ stars i
  edge_loss : ∀ i, (Nat.card (c.graph i).edgeSet : ℝ) ≤
    Nat.card (bipartite i).edgeSet + Nat.card (sparse i).edgeSet + E
  hereditary_density : ∀ i (A : Finset V), (Nat.card ((sparse i).induce (A : Set V)).edgeSet : ℝ) ≤
    D * A.card

theorem exists_three_colour_decomposition (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (c : ThreeColouring V) (n : ℕ),
      n₀ ≤ n → Odd n → n ≤ Fintype.card V → Fintype.card V ≤ 4 * n →
      (∀ i, ¬ cycleGraph n ⊑ c.graph i) →
      Nonempty (ThreeColourDecomposition c (ε * (Fintype.card V : ℝ) ^ 2)
        ((n : ℝ) / 2 + ε * Fintype.card V)) := by
  obtain ⟨n₀, hn₀⟩ := exists_forbidden_odd_cycle_decomposition ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ c n hn hodd hnN hNn hno
  classical
  choose B F T hBG hFG hcol hBoff hFon he hden using
    fun i => hn₀ (c.graph i) n hn hodd hnN hNn (hno i)
  refine ⟨{
    bipartite := B
    sparse := F
    stars := T
    bicolouring := fun i => (B i).recolorOfEquiv finTwoEquiv (Classical.choice (hcol i))
    bipartite_le := hBG
    sparse_le := hFG
    bipartite_off := hBoff
    sparse_on := hFon
    edge_loss := ?_
    hereditary_density := ?_ }⟩
  · intro i
    simpa only [edgeFinset_card_eq_natCard_edgeSet] using he i
  · intro i A
    simpa only [edgeFinset_card_eq_natCard_edgeSet] using hden i A

def ThreeColourDecomposition.profile {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) (v : V) : CubeProfile :=
  fun i => if v ∈ h.stars i then none else some (h.bicolouring i v)

def ThreeColourDecomposition.profileClass {V : Type*} [Fintype V] [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) (p : CubeProfile) : Finset V :=
  univ.filter (fun v => h.profile v = p)

def ThreeColourDecomposition.retained {V : Type*}
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) : SimpleGraph V :=
  ⨆ i, h.bipartite i ⊔ h.sparse i

def ThreeColourDecomposition.missing {V : Type*}
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) : SimpleGraph V :=
  h.retainedᶜ

theorem ThreeColourDecomposition.bipartite_profiles_opposite {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D)
    (i : Fin 3) (u v : V) (huv : (h.bipartite i).Adj u v) :
    profileOppositeAt (h.profile u) (h.profile v) i := by
  have hu := (h.bipartite_off i u v huv).1
  have hv := (h.bipartite_off i u v huv).2
  have hbits := (h.bicolouring i).valid huv
  simp only [profileOppositeAt, profile, if_neg hu, if_neg hv, Option.some.injEq]
  cases huval : h.bicolouring i u <;> cases hvval : h.bicolouring i v <;> simp_all

theorem ThreeColourDecomposition.sparse_profiles_free {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D)
    (i : Fin 3) (u v : V) (huv : (h.sparse i).Adj u v) :
    h.profile u i = none ∧ h.profile v i = none := by
  have hu := (h.sparse_on i u v huv).1
  have hv := (h.sparse_on i u v huv).2
  simp only [profile, if_pos hu, if_pos hv, and_self]

#print axioms exists_three_colour_decomposition

end Erdos556
