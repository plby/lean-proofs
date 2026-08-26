import ErdosProblems.Erdos556.PathSegments

/-!
# Rerouting simple paths

The two elementary reroutings used in the cycle-spectrum proof are a
two-edge detour through a new vertex and a two-chord reversal of an
interior segment. Their length losses and supports are explicit.
-/

namespace Erdos556

open SimpleGraph

theorem exists_path_shortcut_external {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (i j : ℕ) (hij : i < j) (hj : j ≤ p.length)
    (x : V) (hx : x ∉ p.support) (hix : G.Adj (p.getVert i) x)
    (hjx : G.Adj (p.getVert j) x) :
    ∃ q : G.Walk u v, q.IsPath ∧ q.length + j = p.length + i + 2 ∧
      ∀ z ∈ q.support, z ∈ p.support ∨ z = x := by
  have hi : i ≤ p.length := hij.le.trans hj
  have hpre (z : V) (hz : z ∈ (p.take i).support) : z ∈ p.support := by
    obtain ⟨a, _, hax⟩ := (mem_support_take_iff p i hi).mp hz
    exact hax ▸ p.getVert_mem_support a
  have hpost (z : V) (hz : z ∈ (p.drop j).support) : z ∈ p.support := by
    obtain ⟨a, _, _, hax⟩ := (mem_support_drop_iff p j hj).mp hz
    exact hax ▸ p.getVert_mem_support a
  let a : G.Walk u x := (p.take i).concat hix
  let b : G.Walk x v := Walk.cons hjx.symm (p.drop j)
  have ha : a.IsPath := (hp.take i).concat (fun h => hx (hpre x h)) hix
  have hb : b.IsPath := (Walk.cons_isPath_iff _ _).mpr
    ⟨hp.drop j, fun h => hx (hpost x h)⟩
  have hab : (a.append b).IsPath := by
    apply isPath_append_of_support_inter a b ha hb
    intro z hza hzb
    simp only [a, Walk.support_concat, List.mem_append, List.mem_singleton] at hza
    simp only [b, Walk.support_cons, List.mem_cons] at hzb
    rcases hza with hza | hzx
    · rcases hzb with hzx | hzb
      · exact hzx
      · exact ((disjoint_support_take_drop p hp i j hij hj) hza hzb).elim
    · exact hzx
  refine ⟨a.append b, hab, ?_, ?_⟩
  · simp only [a, b, Walk.length_append, Walk.length_concat, Walk.length_cons,
      Walk.take_length, min_eq_left hi, Walk.drop_length]
    omega
  · intro z hz
    rcases (Walk.mem_support_append_iff a b).mp hz with hz | hz
    · simp only [a, Walk.support_concat, List.mem_append, List.mem_singleton] at hz
      exact hz.elim (fun h => Or.inl (hpre z h)) Or.inr
    · simp only [b, Walk.support_cons, List.mem_cons] at hz
      exact hz.elim Or.inr (fun h => Or.inl (hpost z h))

theorem exists_shorter_same_parity_path_external {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (i j : ℕ) (hij : i + 4 ≤ j)
    (hj : j ≤ p.length) (hpar : i % 2 = j % 2)
    (x : V) (hx : x ∉ p.support) (hix : G.Adj (p.getVert i) x)
    (hjx : G.Adj (p.getVert j) x) :
    ∃ q : G.Walk u v, q.IsPath ∧ q.length < p.length ∧
      p.length ≤ q.length + (j - i) ∧ q.length % 2 = p.length % 2 ∧
      ∀ z ∈ q.support, z ∈ p.support ∨ z = x := by
  obtain ⟨q, hq, hlen, hs⟩ := exists_path_shortcut_external p hp i j (by omega) hj x hx hix hjx
  exact ⟨q, hq, by omega, by omega, by omega, hs⟩

#print axioms exists_shorter_same_parity_path_external

theorem exists_path_shortcut_reversal {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (i i' j j' : ℕ)
    (hii : i < i') (hij : i' ≤ j) (hjj : j < j') (hj' : j' ≤ p.length)
    (hchord₁ : G.Adj (p.getVert i) (p.getVert j))
    (hchord₂ : G.Adj (p.getVert i') (p.getVert j')) :
    ∃ q : G.Walk u v, q.IsPath ∧ q.length + i' + j' = p.length + i + j + 2 ∧
      ∀ z ∈ q.support, z ∈ p.support := by
  have hi : i ≤ p.length := by omega
  have hi' : i' ≤ p.length := by omega
  have hj : j ≤ p.length := by omega
  let a := (p.take i).concat hchord₁
  let b := (pathSegment p i' j hij).reverse
  let c := Walk.cons hchord₂ (p.drop j')
  have hbmem (z : V) (hz : z ∈ b.support) :
      ∃ k, i' ≤ k ∧ k ≤ j ∧ p.getVert k = z := by
    apply (mem_support_pathSegment_iff p i' j hij hj).mp
    simpa only [b, Walk.support_reverse, List.mem_reverse] using hz
  have ha : a.IsPath := by
    apply (hp.take i).concat
    intro hz
    obtain ⟨k, hk, hkj⟩ := (mem_support_take_iff p i hi).mp hz
    have hkj' := hp.getVert_injOn (by change k ≤ p.length; omega) hj hkj
    omega
  have hb : b.IsPath := (pathSegment_isPath p hp i' j hij).reverse
  have hab : (a.append b).IsPath := by
    apply isPath_append_of_support_inter a b ha hb
    intro z hza hzb
    simp only [a, Walk.support_concat, List.mem_append, List.mem_singleton] at hza
    rcases hza with hza | hzj
    · obtain ⟨k, hk, hkz⟩ := (mem_support_take_iff p i hi).mp hza
      obtain ⟨l, hil, hlj, hlz⟩ := hbmem z hzb
      have hkl := hp.getVert_injOn (by change k ≤ p.length; omega)
        (by change l ≤ p.length; omega) (hkz.trans hlz.symm)
      omega
    · exact hzj
  have hc : c.IsPath := by
    apply (Walk.cons_isPath_iff _ _).mpr
    refine ⟨hp.drop j', ?_⟩
    intro hz
    obtain ⟨k, hjk, hk, hki⟩ := (mem_support_drop_iff p j' hj').mp hz
    have hki' := hp.getVert_injOn hk hi' hki
    omega
  have habpre (z : V) (hz : z ∈ (a.append b).support) : z ∈ (p.take j).support := by
    apply (mem_support_take_iff p j hj).mpr
    rcases (Walk.mem_support_append_iff a b).mp hz with hza | hzb
    · simp only [a, Walk.support_concat, List.mem_append, List.mem_singleton] at hza
      rcases hza with hza | hzj
      · obtain ⟨k, hk, hkz⟩ := (mem_support_take_iff p i hi).mp hza
        exact ⟨k, by omega, hkz⟩
      · exact ⟨j, le_rfl, hzj.symm⟩
    · obtain ⟨k, _, hk, hkz⟩ := hbmem z hzb
      exact ⟨k, hk, hkz⟩
  have hpath : ((a.append b).append c).IsPath := by
    apply isPath_append_of_support_inter (a.append b) c hab hc
    intro z hzab hzc
    simp only [c, Walk.support_cons, List.mem_cons] at hzc
    rcases hzc with hzi | hzc
    · exact hzi
    · exact ((disjoint_support_take_drop p hp j j' hjj hj') (habpre z hzab) hzc).elim
  refine ⟨(a.append b).append c, hpath, ?_, ?_⟩
  · simp only [a, b, c, Walk.length_append, Walk.length_concat, Walk.take_length,
      min_eq_left hi, Walk.length_reverse, pathSegment_length p i' j hij hj,
      Walk.length_cons, Walk.drop_length]
    omega
  · intro z hz
    rcases (Walk.mem_support_append_iff (a.append b) c).mp hz with hzab | hzc
    · obtain ⟨k, _, hkz⟩ := (mem_support_take_iff p j hj).mp (habpre z hzab)
      exact hkz ▸ p.getVert_mem_support k
    · simp only [c, Walk.support_cons, List.mem_cons] at hzc
      rcases hzc with hzi | hzc
      · exact hzi ▸ p.getVert_mem_support i'
      · obtain ⟨k, _, _, hkz⟩ := (mem_support_drop_iff p j' hj').mp hzc
        exact hkz ▸ p.getVert_mem_support k

theorem exists_shorter_same_parity_path_reversal {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (i i' j j' : ℕ)
    (hii : i + 4 ≤ i') (hij : i' ≤ j) (hjj : j + 2 ≤ j') (hj' : j' ≤ p.length)
    (hpar₁ : i % 2 = i' % 2) (hpar₂ : j % 2 = j' % 2)
    (hchord₁ : G.Adj (p.getVert i) (p.getVert j))
    (hchord₂ : G.Adj (p.getVert i') (p.getVert j')) :
    ∃ q : G.Walk u v, q.IsPath ∧ q.length < p.length ∧
      p.length ≤ q.length + (i' - i) + (j' - j) ∧
      q.length % 2 = p.length % 2 ∧ ∀ z ∈ q.support, z ∈ p.support := by
  obtain ⟨q, hq, hlen, hs⟩ := exists_path_shortcut_reversal p hp i i' j j'
    (by omega) hij (by omega) hj' hchord₁ hchord₂
  exact ⟨q, hq, by omega, by omega, by omega, hs⟩

#print axioms exists_shorter_same_parity_path_reversal

end Erdos556
