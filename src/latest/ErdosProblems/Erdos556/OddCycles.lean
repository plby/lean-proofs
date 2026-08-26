import ErdosProblems.Erdos556.ShortPaths

/-!
# Odd cycles and bounded connecting gadgets

An odd closed walk contains an odd cycle no longer than itself. Combined
with shortest paths and distance parity, this produces a bounded odd cycle
in every connected nonbipartite graph of linear minimum degree.
-/

namespace Erdos556

open SimpleGraph

/-- Every odd closed walk contains an odd cycle of no greater length. -/
theorem exists_odd_cycle_of_odd_walk {V : Type*} {G : SimpleGraph V}
    {v : V} (p : G.Walk v v) (hp : Odd p.length) :
    ∃ (w : V) (q : G.Walk w w), q.IsCycle ∧ Odd q.length ∧ q.length ≤ p.length := by
  classical
  let P (m : ℕ) : Prop := ∃ (w : V) (q : G.Walk w w), Odd q.length ∧ q.length = m
  have hex : ∃ m, P m := ⟨p.length, v, p, hp, rfl⟩
  obtain ⟨w, q, hodd, hlen⟩ := Nat.find_spec hex
  have hmin {z : V} (r : G.Walk z z) (hr : Odd r.length) : q.length ≤ r.length := by
    rw [hlen]
    exact Nat.find_min' hex ⟨z, r, hr, rfl⟩
  have hnotnil : ¬ q.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    have hmod := Nat.odd_iff.mp hodd
    omega
  have htail : q.tail.IsPath := by
    apply Walk.isPath_iff_isSubwalk_imp_nil.mpr
    intro z r hr
    by_contra hrnil
    have hrpos : 0 < r.length := Walk.not_nil_iff_lt_length.mp hrnil
    have hrle := Walk.length_le_of_isSubwalk hr
    rw [Walk.length_tail] at hrle
    by_cases hrodd : Odd r.length
    · have := hmin r hrodd
      omega
    · obtain ⟨a, b, hab⟩ := hr
      have htotal : q.length = a.length + r.length + b.length + 1 := by
        have h := congrArg Walk.length hab
        simp only [Walk.length_tail, Walk.length_append] at h
        have hpos := Walk.not_nil_iff_lt_length.mp hnotnil
        omega
      let s := Walk.cons (q.adj_snd hnotnil) (a.append b)
      have hslen : s.length = a.length + b.length + 1 := by
        simp only [s, Walk.length_cons, Walk.length_append]
      have hsodd : Odd s.length := by
        have hqmod := Nat.odd_iff.mp hodd
        have hrmod := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hrodd)
        apply Nat.odd_iff.mpr
        omega
      have := hmin s hsodd
      omega
  have hthree : 3 ≤ q.length := by
    have hne : q.length ≠ 1 := fun h => (Walk.adj_of_length_eq_one h).ne rfl
    have hmod := Nat.odd_iff.mp hodd
    omega
  exact ⟨w, q, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨htail, hthree⟩,
    hodd, hmin p hp⟩

/-- The odd-cycle characterization of bipartiteness, expressed with walks. -/
theorem colorable_two_iff_no_odd_cycle {V : Type*} (G : SimpleGraph V) :
    G.Colorable 2 ↔ ∀ (v : V) (p : G.Walk v v), p.IsCycle → ¬ Odd p.length := by
  rw [two_colorable_iff_forall_loop_even]
  constructor
  · intro h v p _ ho
    exact (Nat.not_even_iff_odd.mpr ho) (h v p)
  · intro h v p
    apply Nat.not_odd_iff_even.mp
    intro ho
    obtain ⟨w, q, hq, hodd, _⟩ := exists_odd_cycle_of_odd_walk p ho
    exact h w q hq hodd

#print axioms exists_odd_cycle_of_odd_walk
#print axioms colorable_two_iff_no_odd_cycle

/-- A connected nonbipartite graph of large minimum degree contains a short
odd cycle. The bound is deliberately coarse; only its uniformity is needed. -/
theorem exists_short_odd_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hnonbip : ¬ G.Colorable 2) (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ v, d ≤ G.degree v) :
    ∃ (w : V) (q : G.Walk w w), q.IsCycle ∧ Odd q.length ∧
      d * q.length < 6 * Fintype.card V + d := by
  classical
  let root : V := Classical.choice hconn.nonempty
  let f (v : V) : Fin 2 := ⟨G.dist root v % 2, Nat.mod_lt _ (by decide)⟩
  have hex : ∃ a b, G.Adj a b ∧ f a = f b := by
    by_contra h
    push Not at h
    apply hnonbip
    exact ⟨{ toFun := f, map_rel' := fun {a b} hab => h a b hab }⟩
  obtain ⟨a, b, hab, hpar⟩ := hex
  obtain ⟨pa, _, hpa⟩ := hconn.exists_path_of_dist root a
  obtain ⟨pb, _, hpb⟩ := hconn.exists_path_of_dist root b
  have hshort {x y : V} (r : G.Walk x y) (hr : r.length = G.dist x y) :
      d * r.length < 3 * Fintype.card V := by
    have hc := shortest_path_neighborhood_count G r hr d hdeg
    have hlen : r.length < 3 * (r.length / 3 + 1) := by omega
    nlinarith
  have ha := hshort pa hpa
  have hb := hshort pb hpb
  let p := (pa.concat hab).append pb.reverse
  have hlen : p.length = pa.length + 1 + pb.length := by
    simp only [p, Walk.length_append, Walk.length_concat, Walk.length_reverse]
  have hodd : Odd p.length := by
    have heq := congrArg Fin.val hpar
    change G.dist root a % 2 = G.dist root b % 2 at heq
    rw [← hpa, ← hpb] at heq
    apply Nat.odd_iff.mpr
    omega
  have hbound : d * p.length < 6 * Fintype.card V + d := by nlinarith
  obtain ⟨w, q, hq, hqodd, hqle⟩ := exists_odd_cycle_of_odd_walk p hodd
  exact ⟨w, q, hq, hqodd, (Nat.mul_le_mul_left d hqle).trans_lt hbound⟩

#print axioms exists_short_odd_cycle

end Erdos556
