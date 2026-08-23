import ErdosProblems.Erdos1105.LongestCorePath

namespace Erdos1105

open SimpleGraph

/-- Reverse the initial segment of a path and reconnect its old start
to the unchanged suffix using a chord. -/
def posaRotateStart {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (i : ℕ) (h : G.Adj x (p.getVert (i + 1))) :
    G.Walk (p.getVert i) y :=
  (p.take i).reverse.append (Walk.cons h (p.drop (i + 1)))

theorem posaRotateStart_isPath {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) {i : ℕ} (hi : i < p.length)
    (h : G.Adj x (p.getVert (i + 1))) : (posaRotateStart p i h).IsPath := by
  have hdisj := path_prefix_suffix_disjoint p hp (by omega : i < i + 1) (by omega)
  apply Walk.IsPath.mk'
  simp only [posaRotateStart, Walk.support_append, Walk.support_cons, List.tail_cons]
  apply List.nodup_append'.mpr
  refine ⟨(hp.take i).reverse.support_nodup, (hp.drop (i + 1)).support_nodup, ?_⟩
  simpa only [Walk.support_reverse, List.disjoint_reverse_left] using hdisj

theorem posaRotateStart_length {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) {i : ℕ} (hi : i < p.length)
    (h : G.Adj x (p.getVert (i + 1))) : (posaRotateStart p i h).length = p.length := by
  simp only [posaRotateStart, Walk.length_append, Walk.length_reverse, Walk.take_length,
    Walk.length_cons, Walk.drop_length, Nat.min_eq_left hi.le]
  omega

theorem posaRotateStart_mem_support {V : Type*} {G : SimpleGraph V} {x y w : V}
    (p : G.Walk x y) {i : ℕ} (hi : i < p.length)
    (h : G.Adj x (p.getVert (i + 1))) :
    w ∈ (posaRotateStart p i h).support ↔ w ∈ p.support := by
  simp only [posaRotateStart, Walk.support_append, Walk.support_cons, List.tail_cons,
    Walk.support_reverse, List.mem_append, List.mem_reverse]
  rw [Walk.support_take, Walk.drop_support_eq_support_drop_min,
    Nat.min_eq_left (by omega : i + 1 ≤ p.length)]
  exact (List.mem_append (s := p.support.take (i + 1))
    (t := p.support.drop (i + 1))).symm.trans (by rw [List.take_append_drop])

theorem posaRotateStart_getVert_prefix {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) {i : ℕ} (hi : i < p.length)
    (h : G.Adj x (p.getVert (i + 1))) {r : ℕ} (hr : r ≤ i) :
    (posaRotateStart p i h).getVert r = p.getVert (i - r) := by
  rw [posaRotateStart, Walk.getVert_append', Walk.length_reverse, Walk.take_length,
    Nat.min_eq_left hi.le, if_pos hr, Walk.getVert_reverse, Walk.take_length,
    Nat.min_eq_left hi.le, Walk.take_getVert, Nat.min_eq_right (Nat.sub_le i r)]

theorem posaRotateStart_getVert_suffix {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) {i : ℕ} (hi : i < p.length)
    (h : G.Adj x (p.getVert (i + 1))) {r : ℕ} (hr : i < r) :
    (posaRotateStart p i h).getVert r = p.getVert r := by
  rw [posaRotateStart, Walk.getVert_append', Walk.length_reverse, Walk.take_length,
    Nat.min_eq_left hi.le, if_neg (by omega : ¬r ≤ i),
    Walk.getVert_cons _ h (by omega : r - i ≠ 0), Walk.drop_getVert]
  congr 1
  omega

theorem IsLongestSetPath.posaRotateStart {V : Type*} {G : SimpleGraph V}
    {S : Set V} {x y : V} {p : G.Walk x y} (hp : IsLongestSetPath S p)
    {i : ℕ} (hi : i < p.length) (h : G.Adj x (p.getVert (i + 1)))
    (hmem : p.getVert i ∈ S) : IsLongestSetPath S (posaRotateStart p i h) := by
  refine ⟨posaRotateStart_isPath p hp.isPath hi h, hmem, hp.right_mem, ?_⟩
  intro a ha b hb q hq
  rw [posaRotateStart_length p hi h]
  exact hp.longest a ha b hb q hq

end Erdos1105

#print axioms Erdos1105.IsLongestSetPath.posaRotateStart
