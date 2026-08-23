import ErdosProblems.Erdos1105.UniversalPosaStrict
import ErdosProblems.Erdos1105.LongestSetPath

namespace Erdos1105

open SimpleGraph Finset

/-- A path maximal in length among paths whose endpoints lie in `S`. -/
structure IsLongestSetPath {V : Type*} {G : SimpleGraph V} (S : Set V)
    {x y : V} (p : G.Walk x y) : Prop where
  isPath : p.IsPath
  left_mem : x ∈ S
  right_mem : y ∈ S
  longest : ∀ a ∈ S, ∀ b ∈ S, ∀ q : G.Walk a b, q.IsPath → q.length ≤ p.length

lemma IsLongestSetPath.reverse {V : Type*} {G : SimpleGraph V} {S : Set V}
    {x y : V} {p : G.Walk x y} (hp : IsLongestSetPath S p) :
    IsLongestSetPath S p.reverse := by
  refine ⟨hp.isPath.reverse, hp.right_mem, hp.left_mem, ?_⟩
  intro a ha b hb q hq
  simpa only [Walk.length_reverse] using hp.longest b hb a ha q.reverse hq.reverse

theorem exists_longest_core_path_of_not_clique {V : Type*} [Fintype V]
    (G : SimpleGraph V) {k d : ℕ} (hG : NoLongCycle G k)
    (hmax : ∀ J : SimpleGraph V, G ≤ J → NoLongCycle J k → J = G)
    (hnot : ¬G.IsClique (vertexCore G d : Set V)) :
    ∃ x y, ∃ p : G.Walk x y,
      IsLongestSetPath (vertexCore G d : Set V) p ∧ k ≤ p.length + 1 := by
  classical
  have hex : ∃ a ∈ vertexCore G d, ∃ b ∈ vertexCore G d, a ≠ b ∧ ¬G.Adj a b := by
    by_contra! h
    apply hnot
    intro a ha b hb hab
    exact h a ha b hb hab
  obtain ⟨a, ha, b, hb, hab, hnab⟩ := hex
  obtain ⟨p₀, hp₀, hlen₀⟩ := long_path_of_saturated_nonedge G k hG hmax hab hnab
  obtain ⟨x, hx, y, hy, p, hp, hlong⟩ := exists_longest_path_between_sets G
    (vertexCore G d : Set V) (vertexCore G d : Set V) ⟨a, ha, b, hb, p₀, hp₀⟩
  refine ⟨x, y, p, ⟨hp, hx, hy, hlong⟩, ?_⟩
  have := hlong a ha b hb p₀ hp₀
  omega

lemma IsLongestSetPath.left_neighbors {V : Type*} {G : SimpleGraph V} {S : Set V}
    {x y : V} {p : G.Walk x y} (hp : IsLongestSetPath S p) :
    ∀ w ∈ S, G.Adj x w → w ∈ p.support := by
  intro w hw hxw
  by_contra hwnot
  have hq : (Walk.cons hxw.symm p).IsPath :=
    (Walk.cons_isPath_iff _ _).mpr ⟨hp.isPath, hwnot⟩
  have := hp.longest w hw y hp.right_mem (Walk.cons hxw.symm p) hq
  simp only [Walk.length_cons] at this
  omega

lemma IsLongestSetPath.right_neighbors {V : Type*} {G : SimpleGraph V} {S : Set V}
    {x y : V} {p : G.Walk x y} (hp : IsLongestSetPath S p) :
    ∀ w ∈ S, G.Adj y w → w ∈ p.support := by
  intro w hw hyw
  by_contra hwnot
  have := hp.longest x hp.left_mem w hw (p.concat hyw) (hp.isPath.concat hwnot hyw)
  rw [Walk.length_concat] at this
  omega

/-- At the lower core threshold for an odd forbidden cycle, every long
maximal core path attains equality in both endpoint-degree bounds. -/
theorem longest_low_core_path_degrees {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : 2 * d + 3 ≤ p.length + 1) :
    degreeWithin G (vertexCore G d) x = d + 1 ∧
    degreeWithin G (vertexCore G d) y = d + 1 ∧
    degreeWithin G p.support.toFinset x = d + 1 ∧
    degreeWithin G p.support.toFinset y = d + 1 := by
  classical
  have hxlo := vertexCore_degree G d hp.left_mem
  have hylo := vertexCore_degree G d hp.right_mem
  have hxle := degreeWithin_le_of_neighbors_mem G (vertexCore G d) p.support.toFinset x
    (fun w hw h ↦ List.mem_toFinset.mpr (hp.left_neighbors w hw h))
  have hyle := degreeWithin_le_of_neighbors_mem G (vertexCore G d) p.support.toFinset y
    (fun w hw h ↦ List.mem_toFinset.mpr (hp.right_neighbors w hw h))
  have := universal_posa_degree_bound hG (by omega) hu hconn p hp.isPath hlen
  omega

lemma neighbors_in_left_of_equal_degreeWithin {V : Type*} (G : SimpleGraph V)
    {S T : Finset V} {x : V} (hsub : ∀ w ∈ S, G.Adj x w → w ∈ T)
    (hcard : degreeWithin G S x = degreeWithin G T x) :
    ∀ w ∈ T, G.Adj x w → w ∈ S := by
  classical
  have hle : S.filter (G.Adj x) ⊆ T.filter (G.Adj x) := by
    intro w hw
    exact mem_filter.mpr ⟨hsub w (mem_filter.mp hw).1 (mem_filter.mp hw).2,
      (mem_filter.mp hw).2⟩
  have heq : S.filter (G.Adj x) = T.filter (G.Adj x) :=
    eq_of_subset_of_card_le hle hcard.ge
  intro w hw h
  exact (mem_filter.mp (heq.symm ▸ mem_filter.mpr ⟨hw, h⟩)).1

/-- Equality means that an endpoint has no extra neighbor on the path
outside the low core. -/
theorem longest_low_core_path_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : 2 * d + 3 ≤ p.length + 1) :
    (∀ w ∈ p.support, G.Adj x w → w ∈ vertexCore G d) ∧
    (∀ w ∈ p.support, G.Adj y w → w ∈ vertexCore G d) := by
  classical
  obtain ⟨hxc, hyc, hxp, hyp⟩ := longest_low_core_path_degrees hG hu hconn p hp hlen
  constructor
  · intro w hw h
    exact neighbors_in_left_of_equal_degreeWithin G
      (fun z hz hzadj ↦ List.mem_toFinset.mpr (hp.left_neighbors z hz hzadj))
      (hxc.trans hxp.symm) w (List.mem_toFinset.mpr hw) h
  · intro w hw h
    exact neighbors_in_left_of_equal_degreeWithin G
      (fun z hz hzadj ↦ List.mem_toFinset.mpr (hp.right_neighbors z hz hzadj))
      (hyc.trans hyp.symm) w (List.mem_toFinset.mpr hw) h

/-- A maximal path between vertices of the low core must have crossing
endpoint neighbors. This is the equality case absent from the high-core proof. -/
theorem longest_low_core_path_crossing {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : 2 * d + 3 ≤ p.length + 1) :
    ∃ i ∈ endNeighborIndices p, ∃ j ∈ startNeighborIndices p, i ≤ j := by
  by_contra hcross
  have hdeg := longest_low_core_path_degrees hG hu hconn p hp hlen
  have := universal_posa_noncrossing_bound hG (by omega) hu hconn p hp.isPath hlen hcross
  omega

end Erdos1105

#print axioms Erdos1105.longest_low_core_path_degrees
#print axioms Erdos1105.longest_low_core_path_crossing
