/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Defs

/-!
# Covering around one long path

This file formalizes the elementary path-cover estimate used as Lemma 2.5 in the proof of
Erdős Problem 518.  Vertices outside a fixed path which have a neighbour on the path are paired;
each pair is joined through the fixed path.  Vertices with no such neighbour are left as
singletons.  The paths joining the pairs may overlap on the fixed path.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

/-- Two vertices which can each be attached to a fixed path lie on a common path.  The proof
joins their attachment points by a walk through the fixed path and then erases loops. -/
lemma exists_path_covering_pair_of_adj_mem_path
    {G : SimpleGraph V} {P : List V} (hP : IsPath G P)
    {a b x y : V} (hax : G.Adj a x) (hx : x ∈ P) (hy : y ∈ P) (hyb : G.Adj y b) :
    ∃ q : List V, IsPath G q ∧ a ∈ q ∧ b ∈ q := by
  classical
  let w := pathWalk hP
  have hxw : x ∈ w.support := by simpa [w] using hx
  have hyw : y ∈ w.support := by simpa [w] using hy
  obtain ⟨qx, _rx, _⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_append.mp hxw
  obtain ⟨qy, _ry, _⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_append.mp hyw
  let route : G.Walk a b :=
    SimpleGraph.Walk.cons hax (qx.reverse.append (qy.concat hyb))
  let q : List V := (route.toPath : G.Walk a b).support
  refine ⟨q, ?_, ?_, ?_⟩
  · exact ⟨(route.toPath : G.Walk a b).support_ne_nil,
      route.toPath.property.support_nodup,
      (route.toPath : G.Walk a b).isChain_adj_support⟩
  · exact (route.toPath : G.Walk a b).start_mem_support
  · exact (route.toPath : G.Walk a b).end_mem_support

/-- If every pair of entries of a list can be covered by one path, the list can be covered by
`ceil(length / 2)` paths.  This is the purely combinatorial pairing step. -/
lemma exists_pairing_path_cover (G : SimpleGraph V) (l : List V)
    (hpair : ∀ a ∈ l, ∀ b ∈ l,
      ∃ q : List V, IsPath G q ∧ a ∈ q ∧ b ∈ q) :
    ∃ qs : List (List V),
      qs.length = (l.length + 1) / 2 ∧
      (∀ q ∈ qs, IsPath G q) ∧
      ∀ v ∈ l, ∃ q ∈ qs, v ∈ q := by
  induction l using List.twoStepInduction with
  | nil =>
      exact ⟨[], by simp, by simp, by simp⟩
  | singleton a =>
      refine ⟨[[a]], by norm_num, ?_, ?_⟩
      · simp
      · intro v hv
        simp_all
  | cons_cons a b l ih _ =>
      have hpair_l : ∀ c ∈ l, ∀ d ∈ l,
          ∃ q : List V, IsPath G q ∧ c ∈ q ∧ d ∈ q := by
        intro c hc d hd
        exact hpair c (by simp [hc]) d (by simp [hd])
      obtain ⟨qs, hlen, hpaths, hcover⟩ := ih hpair_l
      obtain ⟨q, hq, haq, hbq⟩ := hpair a (by simp) b (by simp)
      refine ⟨q :: qs, ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hq
        · exact hpaths r hr
      · intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact ⟨q, by simp, haq⟩
        · rcases hv with rfl | hv
          · exact ⟨q, by simp, hbq⟩
          · obtain ⟨r, hr, hvr⟩ := hcover v hv
            exact ⟨r, by simp [hr], hvr⟩

/-- Lemma 2.5 (one-long-path cover).  Let `X` be the vertices of a path `P`, let `Y` be
the vertices outside `P`, let `Y₀` consist of those vertices of `Y` with no neighbour in `X`,
and put `Y₁ = Y \ Y₀`.  Then `G` has a path cover of size at most
`1 + ceil(|Y₁| / 2) + |Y₀|`.

The cover uses `P` itself, one path through `P` for each pair in `Y₁`, and singleton paths
for the remaining vertices. -/
theorem hasPathCoverAtMost_one_long_path [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : List V) (hP : IsPath G P) :
    let X := P.toFinset
    let Y := Finset.univ \ X
    let Y₀ := Y.filter fun y ↦ ∀ x ∈ X, ¬ G.Adj y x
    let Y₁ := Y \ Y₀
    HasPathCoverAtMost G (1 + (Y₁.card + 1) / 2 + Y₀.card) := by
  classical
  dsimp only
  let X : Finset V := P.toFinset
  let Y : Finset V := Finset.univ \ X
  let Y₀ : Finset V := Y.filter fun y ↦ ∀ x ∈ X, ¬ G.Adj y x
  let Y₁ : Finset V := Y \ Y₀
  change HasPathCoverAtMost G (1 + (Y₁.card + 1) / 2 + Y₀.card)
  have hattach : ∀ y ∈ Y₁, ∃ x ∈ X, G.Adj y x := by
    intro y hy
    have hyY : y ∈ Y := (Finset.mem_sdiff.mp hy).1
    have hy0 : y ∉ Y₀ := (Finset.mem_sdiff.mp hy).2
    have hnall : ¬ ∀ x ∈ X, ¬ G.Adj y x := by
      intro hall
      exact hy0 (Finset.mem_filter.mpr ⟨hyY, hall⟩)
    push Not at hnall
    exact hnall
  have hpair : ∀ a ∈ Y₁.toList, ∀ b ∈ Y₁.toList,
      ∃ q : List V, IsPath G q ∧ a ∈ q ∧ b ∈ q := by
    intro a ha b hb
    have ha' : a ∈ Y₁ := by simpa using ha
    have hb' : b ∈ Y₁ := by simpa using hb
    obtain ⟨x, hxX, hax⟩ := hattach a ha'
    obtain ⟨y, hyX, hby⟩ := hattach b hb'
    have hxP : x ∈ P := by simpa [X] using hxX
    have hyP : y ∈ P := by simpa [X] using hyX
    exact exists_path_covering_pair_of_adj_mem_path hP hax hxP hyP hby.symm
  obtain ⟨qs, hqslen, hqspath, hqscover⟩ :=
    exists_pairing_path_cover G Y₁.toList hpair
  let singles : List (List V) := Y₀.toList.map fun y ↦ [y]
  let cover : List (List V) := P :: (qs ++ singles)
  refine ⟨cover, ?_, ?_, ?_⟩
  · simp only [cover, singles, List.length_cons, List.length_append, List.length_map,
      Finset.length_toList, hqslen]
    omega
  · intro q hq
    simp only [cover, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact hP
    · exact hqspath q hq
    · simp only [singles, List.mem_map] at hq
      obtain ⟨y, _hy, rfl⟩ := hq
      simp
  · intro v
    by_cases hvX : v ∈ X
    · refine ⟨P, by simp [cover], ?_⟩
      simpa [X] using hvX
    · have hvY : v ∈ Y := by simp [Y, hvX]
      by_cases hv0 : v ∈ Y₀
      · refine ⟨[v], ?_, by simp⟩
        simp only [cover, List.mem_cons, List.mem_append]
        right
        right
        simp [singles, hv0]
      · have hv1 : v ∈ Y₁ := Finset.mem_sdiff.mpr ⟨hvY, hv0⟩
        obtain ⟨q, hq, hvq⟩ := hqscover v (by simpa using hv1)
        exact ⟨q, by simp [cover, hq], hvq⟩

end Erdos518
