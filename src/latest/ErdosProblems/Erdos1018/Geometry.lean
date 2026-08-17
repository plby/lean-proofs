import Mathlib

open Function Set
open SimpleGraph


namespace Erdos1018Aux

variable {V : Type*} (G : SimpleGraph V)
variable {c u v w : V} {r i : ℕ}

/-- The closed graph-metric ball of natural radius `r`, expressed using Mathlib's open
extended-distance balls. -/
def closedBallN (c : V) (r : ℕ) : Set V := G.ball c ((r : ℕ∞) + 1)

/-- The exact BFS layer at natural distance `r` from `c`.  Reachability is included because
`SimpleGraph.dist` uses the junk value zero on disconnected pairs. -/
def layerN (c : V) (r : ℕ) : Set V :=
  {v | G.Reachable v c ∧ G.dist v c = r}

lemma mem_closedBallN_edist :
    v ∈ closedBallN G c r ↔ G.edist v c ≤ (r : ℕ∞) := by
  rw [closedBallN, SimpleGraph.mem_ball,
    ENat.lt_add_one_iff (ENat.natCast_ne_top r)]

lemma mem_closedBallN :
    v ∈ closedBallN G c r ↔ G.Reachable v c ∧ G.dist v c ≤ r := by
  rw [mem_closedBallN_edist]
  constructor
  · intro h
    have hne : G.edist v c ≠ ⊤ := by
      intro heq
      rw [heq] at h
      exact (ENat.natCast_ne_top r) (top_unique h)
    have hreach : G.Reachable v c := SimpleGraph.edist_ne_top_iff_reachable.mp hne
    refine ⟨hreach, ?_⟩
    rw [← hreach.coe_dist_eq_edist] at h
    exact ENat.natCast_le_natCast.mp h
  · rintro ⟨hreach, hdist⟩
    rw [← hreach.coe_dist_eq_edist]
    exact ENat.natCast_le_natCast.mpr hdist

lemma closedBallN_mono {r s : ℕ} (hrs : r ≤ s) :
    closedBallN G c r ⊆ closedBallN G c s := by
  apply SimpleGraph.ball_mono
  exact add_le_add (ENat.natCast_le_natCast.mpr hrs) le_rfl

lemma closedBallN_succ :
    closedBallN G c (r + 1) = closedBallN G c r ∪ layerN G c (r + 1) := by
  ext x
  rw [Set.mem_union, mem_closedBallN, mem_closedBallN]
  simp only [layerN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxc, hdist⟩
    by_cases hle : G.dist x c ≤ r
    · exact Or.inl ⟨hxc, hle⟩
    · exact Or.inr ⟨hxc, by omega⟩
  · rintro (⟨hxc, hle⟩ | ⟨hxc, heq⟩)
    · exact ⟨hxc, by omega⟩
    · exact ⟨hxc, by omega⟩

lemma closedBallN_disjoint_layerN_succ :
    Disjoint (closedBallN G c r) (layerN G c (r + 1)) := by
  rw [Set.disjoint_left]
  intro x hxBall hxLayer
  have hxle := ((mem_closedBallN G).mp hxBall).2
  have hxeq := hxLayer.2
  omega

lemma ncard_closedBallN_succ [Finite V] :
    (closedBallN G c (r + 1)).ncard =
      (closedBallN G c r).ncard + (layerN G c (r + 1)).ncard := by
  rw [closedBallN_succ, Set.ncard_union_eq (closedBallN_disjoint_layerN_succ G)]

lemma dist_le_succ_of_adj (hvw : G.Adj v w)
    (hv : G.dist c v ≤ r) : G.dist c w ≤ r + 1 := by
  have htri := hvw.reachable.dist_triangle_right c
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw] at htri
  omega

lemma dist_getVert_eq_of_geodesic {p : G.Walk c v}
    (hp : p.length = G.dist c v) (hi : i ≤ p.length) :
    G.dist c (p.getVert i) = i := by
  have hsub : (p.take i).IsSubwalk p := p.isSubwalk_take i
  have hdist := SimpleGraph.length_eq_dist_of_subwalk hp hsub
  simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hi] using hdist.symm

lemma geodesic_support_subset_closedBallN {p : G.Walk c v}
    (hp : p.length = G.dist c v) (hv : G.dist c v ≤ r) :
    ∀ x ∈ p.support, x ∈ closedBallN G c r := by
  intro x hx
  obtain ⟨j, hjx, hjle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  rw [mem_closedBallN]
  refine ⟨?_, ?_⟩
  · rw [← hjx]
    exact (p.take j).reachable.symm
  · rw [← hjx, SimpleGraph.dist_comm (u := p.getVert j) (v := c),
      dist_getVert_eq_of_geodesic G hp hjle]
    omega

lemma exists_predecessor_on_geodesic (hr : G.Reachable c v)
    (hd : G.dist c v = i + 1) :
    ∃ w, G.Adj w v ∧ G.dist c w = i := by
  obtain ⟨p, hpPath, hpLen⟩ := hr.exists_path_of_dist
  let w := p.getVert i
  have hil : i < p.length := by omega
  have hlast : p.getVert (i + 1) = v := by
    rw [← hd, ← hpLen]
    exact p.getVert_length
  have hadj : G.Adj w v := by
    rw [← hlast]
    exact p.adj_getVert_succ hil
  refine ⟨w, hadj, ?_⟩
  exact dist_getVert_eq_of_geodesic G hpLen (by omega)

lemma layerN_succ_has_predecessor (hv : v ∈ layerN G c (i + 1)) :
    ∃ w ∈ layerN G c i, G.Adj w v := by
  obtain ⟨hvc, hdvc⟩ := hv
  have hd : G.dist c v = i + 1 := by
    simpa [SimpleGraph.dist_comm] using hdvc
  obtain ⟨w, hwv, hdw⟩ := exists_predecessor_on_geodesic G hvc.symm hd
  refine ⟨w, ⟨?_, ?_⟩, hwv⟩
  · exact (hvc.symm.trans hwv.reachable.symm).symm
  · simpa [SimpleGraph.dist_comm] using hdw

lemma exists_short_path_in_closedBallN [DecidableEq V]
    (hu : u ∈ closedBallN G c r) (hv : v ∈ closedBallN G c r) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length ≤ 2 * r ∧
      ∀ x ∈ p.support, x ∈ closedBallN G c r := by
  rw [mem_closedBallN] at hu hv
  obtain ⟨pu, hpuPath, hpuLen⟩ := hu.1.symm.exists_path_of_dist
  obtain ⟨pv, hpvPath, hpvLen⟩ := hv.1.symm.exists_path_of_dist
  let q : G.Walk u v := pu.reverse.append pv
  let p : G.Walk u v := q.bypass
  refine ⟨p, q.bypass_isPath, ?_, ?_⟩
  · calc
      p.length ≤ q.length := q.length_bypass_le_length
      _ = pu.length + pv.length := by simp [q]
      _ ≤ 2 * r := by
        rw [hpuLen, hpvLen, SimpleGraph.dist_comm (u := c) (v := u),
          SimpleGraph.dist_comm (u := c) (v := v)]
        omega
  · intro x hx
    have hxq : x ∈ q.support := q.support_bypass_subset_support hx
    have hxpu_or_hxpv : x ∈ pu.support ∨ x ∈ pv.support := by
      simpa [q] using hxq
    rcases hxpu_or_hxpv with hxpu | hxpv
    · apply geodesic_support_subset_closedBallN G hpuLen
        (by simpa [SimpleGraph.dist_comm] using hu.2)
      exact hxpu
    · apply geodesic_support_subset_closedBallN G hpvLen
        (by simpa [SimpleGraph.dist_comm] using hv.2)
      exact hxpv

lemma connected_induce_closedBallN :
    (G.induce (closedBallN G c r)).Connected := by
  have hc : c ∈ closedBallN G c r := by
    rw [mem_closedBallN]
    simp
  apply G.induce_connected_of_patches c hc
  intro v hv
  obtain ⟨hvc, hdvc⟩ := (mem_closedBallN G).mp hv
  obtain ⟨p, hpPath, hpLen⟩ := hvc.symm.exists_path_of_dist
  have hpSupp : ∀ x ∈ p.support, x ∈ closedBallN G c r :=
    geodesic_support_subset_closedBallN G hpLen (by
      simpa [SimpleGraph.dist_comm] using hdvc)
  refine ⟨closedBallN G c r, Set.Subset.rfl, hc, hv, ?_⟩
  exact (p.induce (closedBallN G c r) hpSupp).reachable

lemma length_induce_eq {s : Set V} {a b : V} (p : G.Walk a b)
    (hp : ∀ x ∈ p.support, x ∈ s) :
    (p.induce s hp).length = p.length := by
  induction p <;> simp [SimpleGraph.Walk.induce, *]

lemma induced_closedBallN_dist_le (v : closedBallN G c r) :
    (G.induce (closedBallN G c r)).dist ⟨c, by rw [mem_closedBallN]; simp⟩ v ≤ r := by
  obtain ⟨hvc, hdvc⟩ := (mem_closedBallN G).mp v.property
  obtain ⟨p, hpPath, hpLen⟩ := hvc.symm.exists_path_of_dist
  have hpSupp : ∀ x ∈ p.support, x ∈ closedBallN G c r :=
    geodesic_support_subset_closedBallN G hpLen (by
      simpa [SimpleGraph.dist_comm] using hdvc)
  let q := p.induce (closedBallN G c r) hpSupp
  calc
    (G.induce (closedBallN G c r)).dist ⟨c, by rw [mem_closedBallN]; simp⟩ v
        ≤ q.length := by
          simpa [q] using SimpleGraph.dist_le q
    _ = p.length := length_induce_eq G p hpSupp
    _ = G.dist c v := hpLen
    _ ≤ r := by simpa [SimpleGraph.dist_comm] using hdvc

lemma induced_closedBallN_radius_le :
    (G.induce (closedBallN G c r)).radius ≤ (r : ℕ∞) := by
  let center : closedBallN G c r := ⟨c, by rw [mem_closedBallN]; simp⟩
  calc
    (G.induce (closedBallN G c r)).radius
        ≤ (G.induce (closedBallN G c r)).eccent center :=
      SimpleGraph.radius_le_eccent
    _ ≤ (r : ℕ∞) := by
      rw [SimpleGraph.eccent_le_iff]
      intro v
      have hreach := (connected_induce_closedBallN G) center v
      rw [← hreach.coe_dist_eq_edist]
      exact ENat.natCast_le_natCast.mpr (induced_closedBallN_dist_le G v)

end Erdos1018Aux
