import ErdosProblems.Erdos556.ClosingPaths

/-!
# Closing through a bipartite core and an inconsistent ear

An ear whose parity disagrees with the bipartition closes every path in the
core between its endpoints to an odd cycle. This file proves the closure
step; the existence of such an ear is a separate structural theorem.
-/

namespace Erdos556

open SimpleGraph

private theorem parity_consistency_compose (A B C : Prop) :
    ((A ↔ B) ↔ (B ↔ C)) ↔ (A ↔ C) := by
  tauto

/-- A shortest path of inconsistent parity has no internal visit to the
labelled set: otherwise its two pieces cannot both have consistent parity. -/
theorem exists_inconsistent_ear_of_path {V : Type*} {G : SimpleGraph V}
    (S : Set V) (colour : S → Bool) {u v : S}
    (p : G.Walk u.val v.val) (hp : p.IsPath)
    (hwrong : ¬ (Even p.length ↔ (colour u ↔ colour v))) :
    ∃ a b : S, a.val ≠ b.val ∧ ∃ q : G.Walk a.val b.val, q.IsPath ∧
      ¬ (Even q.length ↔ (colour a ↔ colour b)) ∧ q.length ≤ p.length ∧
      ∀ z ∈ q.support, z ≠ a.val → z ≠ b.val → z ∉ S := by
  classical
  let P (m : ℕ) : Prop := ∃ a b : S, ∃ q : G.Walk a.val b.val,
    q.IsPath ∧ ¬ (Even q.length ↔ (colour a ↔ colour b)) ∧ q.length = m
  have hex : ∃ m, P m := ⟨p.length, u, v, p, hp, hwrong, rfl⟩
  obtain ⟨a, b, q, hq, hqw, hlen⟩ := Nat.find_spec hex
  have hmin {x y : S} (r : G.Walk x.val y.val) (hr : r.IsPath)
      (hw : ¬ (Even r.length ↔ (colour x ↔ colour y))) : q.length ≤ r.length := by
    rw [hlen]
    exact Nat.find_min' hex ⟨x, y, r, hr, hw, rfl⟩
  have hcons {x y : S} (r : G.Walk x.val y.val) (hr : r.IsPath)
      (hlt : r.length < q.length) : Even r.length ↔ (colour x ↔ colour y) := by
    by_contra hw
    exact (Nat.not_le_of_gt hlt) (hmin (x := x) (y := y) r hr hw)
  have hab : a.val ≠ b.val := by
    intro h
    have heq : a = b := Subtype.ext h
    subst b
    have hz := (Walk.isPath_iff_nil.mp hq).length_eq_zero
    exact hqw (by simp [hz])
  refine ⟨a, b, hab, q, hq, hqw, hmin (x := u) (y := v) p hp hwrong, ?_⟩
  intro z hz hza hzb hzS
  let x : S := ⟨z, hzS⟩
  let r : G.Walk a.val x.val := q.takeUntil z hz
  let s : G.Walk x.val b.val := q.dropUntil z hz
  have hr := hcons (x := a) (y := x) r (hq.takeUntil hz) (q.length_takeUntil_lt_length hz hzb)
  have hs := hcons (x := x) (y := b) s (hq.dropUntil hz) (q.length_dropUntil_lt_length hz hza)
  have hsum : q.length = r.length + s.length := by
    have h := congrArg Walk.length (q.take_spec hz)
    simpa only [Walk.length_append] using h.symm
  apply hqw
  rw [hsum, Nat.even_add, hr, hs]
  exact parity_consistency_compose _ _ _

theorem odd_cycle_from_inconsistent_ear {V : Type*} {G : SimpleGraph V}
    (S : Set V) (colour : (G.induce S).Coloring Bool) {u v : S}
    (p : (G.induce S).Walk u v) (hp : p.IsPath) (hlen : 1 < p.length)
    (q : G.Walk u.val v.val) (hq : q.IsPath)
    (hqS : ∀ z ∈ q.support, z ≠ u.val → z ≠ v.val → z ∉ S)
    (hwrong : ¬ (Even q.length ↔ (colour u ↔ colour v))) :
    ∃ c : G.Walk u.val u.val, c.IsCycle ∧ Odd c.length ∧ p.length ≤ c.length := by
  let f : G.induce S ↪g G :=
    { toFun := Subtype.val, inj' := Subtype.val_injective, map_rel_iff' := Iff.rfl }
  have hpS (z : V) (hz : z ∈ (p.map f.toHom).support) : z ∈ S := by
    rw [Walk.support_map, List.mem_map] at hz
    obtain ⟨x, _, hx⟩ := hz
    subst z
    exact x.property
  have hcycle : ((p.map f.toHom).append q.reverse).IsCycle := by
    apply isCycle_append_reverse_of_support_inter (p.map f.toHom) q
      (hp.map f.injective) hq (by simpa only [Walk.length_map] using hlen)
    intro z hzp hzq
    by_cases hzu : z = u.val
    · exact Or.inl hzu
    by_cases hzv : z = v.val
    · exact Or.inr hzv
    exact (hqS z hzq hzu hzv (hpS z hzp)).elim
  have hpar : p.length % 2 ≠ q.length % 2 := by
    intro h
    apply hwrong
    have heq : Even q.length ↔ Even p.length := by
      simp only [Nat.even_iff]
      omega
    exact heq.trans (colour.even_length_iff_congr p)
  refine ⟨(p.map f.toHom).append q.reverse, hcycle, ?_, ?_⟩
  · apply Nat.odd_iff.mpr
    change ((p.map f.toHom).append q.reverse).length % 2 = 1
    simp only [Walk.length_append, Walk.length_map, Walk.length_reverse]
    omega
  · change p.length ≤ ((p.map f.toHom).append q.reverse).length
    simp only [Walk.length_append, Walk.length_map, Walk.length_reverse]
    omega

#print axioms odd_cycle_from_inconsistent_ear
#print axioms exists_inconsistent_ear_of_path

end Erdos556
