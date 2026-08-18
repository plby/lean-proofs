/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleSequence

/-!
# Path-to-cycle closure in graph neighborhoods
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

/-- The vertices at graph distance exactly two from `x`, represented by an
explicit middle vertex.  The first two conjuncts make this set disjoint from
both `x` and its first neighborhood. -/
def secondNeighborSet {V : Type*} (G : SimpleGraph V) (x : V) : Set V :=
  {z | z ≠ x ∧ z ∉ G.neighborSet x ∧
    ∃ u, u ∈ G.neighborSet x ∧ G.Adj u z}

/-- Finite-set form of the exact second neighborhood. -/
def secondNeighborFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun z ↦ z ∈ secondNeighborSet G x

@[simp] theorem mem_secondNeighborFinset {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x z : V} :
    z ∈ secondNeighborFinset G x ↔ z ∈ secondNeighborSet G x := by
  simp [secondNeighborFinset]

@[simp] theorem coe_secondNeighborFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) :
    (secondNeighborFinset G x : Set V) = secondNeighborSet G x := by
  ext z
  simp

theorem mem_secondNeighborSet_iff {V : Type*} {G : SimpleGraph V} {x z : V} :
    z ∈ secondNeighborSet G x ↔
      z ≠ x ∧ ¬G.Adj x z ∧ ∃ u, G.Adj x u ∧ G.Adj u z := by
  rfl

/-- A path on `n` vertices in the neighborhood of a vertex closes with that
vertex to a cycle on `n+1` vertices. -/
theorem cycleGraph_succ_isContained_of_pathGraph_neighbor
    {V : Type*} {G : SimpleGraph V} {n : ℕ} (hn : 2 ≤ n) (x : V)
    (hpath : SimpleGraph.pathGraph n ⊑ G.induce (G.neighborSet x)) :
    SimpleGraph.cycleGraph (n + 1) ⊑ G := by
  obtain ⟨p⟩ := hpath
  let f : Fin (n + 1) → V :=
    Fin.cases x (fun i ↦ (p i).1)
  have hf : Function.Injective f := by
    intro u v huv
    induction u using Fin.cases with
    | zero =>
        induction v using Fin.cases with
        | zero => rfl
        | succ j =>
            exfalso
            have hxj : G.Adj x (p j).1 := (p j).2
            exact hxj.ne (by simpa [f] using huv)
    | succ i =>
        induction v using Fin.cases with
        | zero =>
            exfalso
            have hxi : G.Adj x (p i).1 := (p i).2
            exact hxi.ne (by simpa [f] using huv.symm)
        | succ j =>
            exact congrArg Fin.succ
              (p.injective (Subtype.ext (by simpa [f] using huv)))
  apply cycleGraph_isContained_of_sequence f hf
  · intro u v huv
    induction u using Fin.cases with
    | zero =>
        induction v using Fin.cases with
        | zero => omega
        | succ j => exact (p j).2
    | succ i =>
        induction v using Fin.cases with
        | zero => simp at huv
        | succ j =>
            have hij : i.val + 1 = j.val := by
              simp only [Fin.val_succ] at huv
              omega
            have hadjPath : (SimpleGraph.pathGraph n).Adj i j := by
              rw [SimpleGraph.pathGraph_adj]
              exact Or.inl hij
            exact p.toHom.map_adj hadjPath
  · intro u v hu hv
    induction u using Fin.cases with
    | zero =>
        induction v using Fin.cases with
        | zero => omega
        | succ j => exact (p j).2
    | succ i =>
        simp only [Fin.val_succ] at hu
        omega

/-- Contrapositive form used in the Ramsey induction: in a graph with no
`C_(n+1)`, every vertex neighborhood is `P_n`-free. -/
theorem pathGraph_not_isContained_neighbor_of_cycleGraph_not_isContained
    {V : Type*} {G : SimpleGraph V} {n : ℕ} (hn : 2 ≤ n) (x : V)
    (hcycle : ¬SimpleGraph.cycleGraph (n + 1) ⊑ G) :
    ¬SimpleGraph.pathGraph n ⊑ G.induce (G.neighborSet x) := by
  intro hpath
  exact hcycle (cycleGraph_succ_isContained_of_pathGraph_neighbor hn x hpath)

/-- Along a path in the exact second neighborhood of `x`, chosen middle
vertices at positions differing by `k-4` must agree if the graph is
`C_k`-free.  Otherwise those two middle vertices and the intervening path
segment close to a `k`-cycle. -/
theorem secondNeighbor_connectors_periodic
    {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 5 ≤ k) (x : V)
    (p u : Fin (2 * k) → V) (hp : Function.Injective p)
    (hp_ne : ∀ i, p i ≠ x) (hp_nonadj : ∀ i, ¬G.Adj x (p i))
    (hp_adj : ∀ i j : Fin (2 * k), i.val + 1 = j.val → G.Adj (p i) (p j))
    (hu_root : ∀ i, G.Adj x (u i)) (hu_path : ∀ i, G.Adj (u i) (p i))
    (hcycle : ¬SimpleGraph.cycleGraph k ⊑ G)
    (s : ℕ) (hs : s + (k - 4) < 2 * k) :
    u ⟨s, by omega⟩ = u ⟨s + (k - 4), hs⟩ := by
  let is : Fin (2 * k) := ⟨s, by omega⟩
  let it : Fin (2 * k) := ⟨s + (k - 4), hs⟩
  by_contra hne
  have hust : u is ≠ u it := by simpa [is, it] using hne
  let seg : Fin ((k - 5) + 2) → V := fun i ↦
    p ⟨s + i.val, by have := i.isLt; omega⟩
  have hseg : Function.Injective seg := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (Fin.ext_iff.mp (hp hij))
  have hu_not_seg (i : Fin (2 * k)) : u i ∉ Set.range seg := by
    rintro ⟨j, hj⟩
    have hxseg : G.Adj x (seg j) := by
      rw [hj]
      exact hu_root i
    exact hp_nonadj _ (by simpa only [seg] using hxseg)
  have hx_not_seg : x ∉ Set.range seg := by
    rintro ⟨j, hj⟩
    exact hp_ne _ (by simpa only [seg] using hj)
  have hseg_adj : ∀ i j : Fin ((k - 5) + 2), i.val + 1 = j.val →
      G.Adj (seg i) (seg j) := by
    intro i j hij
    apply hp_adj
    simp only [seg]
    omega
  have hseg_zero : seg 0 = p is := by
    apply congrArg p
    apply Fin.ext
    simp [seg, is]
  have hseg_last : seg (Fin.last ((k - 5) + 1)) = p it := by
    apply congrArg p
    apply Fin.ext
    simp [seg, it]
    omega
  apply hcycle
  rw [← Nat.sub_add_cancel hk]
  exact cycleGraph_add_five_isContained_of_path_connectors
    x (u is) (u it) seg hseg (hu_not_seg it) (hu_not_seg is) hust
    hx_not_seg (hu_root is).ne (hu_root it).ne
    (hu_root is) (hseg_zero ▸ hu_path is)
    hseg_adj (hseg_last ▸ (hu_path it).symm) (hu_root it).symm

/-- The non-periodic branch in the second-neighborhood argument.  The path
used here is
`p 0, p 1, u 1, p (k-3), ..., p (2k-8)`; the vertex `u 0` closes its two
endpoints. -/
theorem secondNeighbor_cycle_of_adjacent_connectors_ne
    {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 5 ≤ k) (x : V)
    (p u : Fin (2 * k) → V) (hp : Function.Injective p)
    (hp_nonadj : ∀ i, ¬G.Adj x (p i))
    (hp_adj : ∀ i j : Fin (2 * k), i.val + 1 = j.val → G.Adj (p i) (p j))
    (hu_root : ∀ i, G.Adj x (u i)) (hu_path : ∀ i, G.Adj (u i) (p i))
    (s : ℕ) (hs : s + (2 * k - 8) < 2 * k)
    (hmiddle : u ⟨s + 1, by omega⟩ = u ⟨s + (k - 3), by omega⟩)
    (hfar : u ⟨s, by omega⟩ = u ⟨s + (2 * k - 8), hs⟩)
    (hne : u ⟨s, by omega⟩ ≠ u ⟨s + 1, by omega⟩) :
    SimpleGraph.cycleGraph k ⊑ G := by
  let i0 : Fin (2 * k) := ⟨s, by omega⟩
  let i1 : Fin (2 * k) := ⟨s + 1, by omega⟩
  let imid : Fin (2 * k) := ⟨s + (k - 3), by omega⟩
  let ifar : Fin (2 * k) := ⟨s + (2 * k - 8), hs⟩
  have hmiddle' : u i1 = u imid := by simpa [i1, imid] using hmiddle
  have hfar' : u i0 = u ifar := by simpa [i0, ifar] using hfar
  have hne' : u i0 ≠ u i1 := by simpa [i0, i1] using hne
  have hu_not_path (i : Fin (2 * k)) : u i ∉ Set.range p := by
    rintro ⟨j, hj⟩
    have hxu := hu_root i
    rw [← hj] at hxu
    exact hp_nonadj j hxu
  let tail : Fin ((k - 5) + 1) → V := fun j ↦
    p ⟨s + (k - 3) + j.val, by have := j.isLt; omega⟩
  have htail : Function.Injective tail := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (Fin.ext_iff.mp (hp hij))
  have hu1_not_tail : u i1 ∉ Set.range tail := by
    rintro ⟨j, hj⟩
    apply hu_not_path i1
    refine ⟨⟨s + (k - 3) + j.val, by have := j.isLt; omega⟩, ?_⟩
    simpa only [tail] using hj
  let utail : Fin ((k - 5) + 2) → V := Fin.cons (u i1) tail
  have hutail : Function.Injective utail :=
    Fin.cons_injective_of_injective hu1_not_tail htail
  have hp1_ne_u1 : p i1 ≠ u i1 := by
    intro h
    exact hu_not_path i1 ⟨i1, h⟩
  have hp1_not_tail : p i1 ∉ Set.range tail := by
    rintro ⟨j, hj⟩
    have heq : p ⟨s + (k - 3) + j.val, by have := j.isLt; omega⟩ = p i1 := by
      simpa only [tail] using hj
    have := Fin.ext_iff.mp (hp heq)
    simp only [i1] at this
    have := j.isLt
    omega
  have hp1_not_utail : p i1 ∉ Set.range utail := by
    change p i1 ∉ Set.range (Fin.cons (u i1) tail)
    rw [Fin.range_cons]
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨hp1_ne_u1, hp1_not_tail⟩
  let p1utail : Fin ((k - 5) + 3) → V := Fin.cons (p i1) utail
  have hp1utail : Function.Injective p1utail :=
    Fin.cons_injective_of_injective hp1_not_utail hutail
  have hp0_ne_p1 : p i0 ≠ p i1 := hp.ne (by simp [i0, i1])
  have hp0_ne_u1 : p i0 ≠ u i1 := by
    intro h
    exact hu_not_path i1 ⟨i0, h⟩
  have hp0_not_tail : p i0 ∉ Set.range tail := by
    rintro ⟨j, hj⟩
    have heq : p ⟨s + (k - 3) + j.val, by have := j.isLt; omega⟩ = p i0 := by
      simpa only [tail] using hj
    have := Fin.ext_iff.mp (hp heq)
    simp only [i0] at this
    have := j.isLt
    omega
  have hp0_not_p1utail : p i0 ∉ Set.range p1utail := by
    change p i0 ∉ Set.range (Fin.cons (p i1) (Fin.cons (u i1) tail))
    simp only [Fin.range_cons, Set.mem_insert_iff, not_or]
    exact ⟨hp0_ne_p1, hp0_ne_u1, hp0_not_tail⟩
  let qseq : Fin ((k - 5) + 4) → V := Fin.cons (p i0) p1utail
  have hqseq : Function.Injective qseq :=
    Fin.cons_injective_of_injective hp0_not_p1utail hp1utail
  have hu0_not_qseq : u i0 ∉ Set.range qseq := by
    change u i0 ∉
      Set.range (Fin.cons (p i0) (Fin.cons (p i1) (Fin.cons (u i1) tail)))
    simp only [Fin.range_cons, Set.mem_insert_iff, not_or]
    refine ⟨?_, ?_, hne', ?_⟩
    · intro h
      exact hu_not_path i0 ⟨i0, h.symm⟩
    · intro h
      exact hu_not_path i0 ⟨i1, h.symm⟩
    · rintro ⟨j, hj⟩
      apply hu_not_path i0
      refine ⟨⟨s + (k - 3) + j.val, by have := j.isLt; omega⟩, ?_⟩
      simpa only [tail] using hj
  have htail_adj : ∀ i j : Fin ((k - 5) + 1), i.val + 1 = j.val →
      G.Adj (tail i) (tail j) := by
    intro i j hij
    apply hp_adj
    simp only [tail]
    omega
  have htail_zero : tail 0 = p imid := by
    apply congrArg p
    apply Fin.ext
    simp [tail, imid]
  have hu1_tail : G.Adj (u i1) (tail 0) := by
    rw [htail_zero, hmiddle']
    exact hu_path imid
  have hutail_adj : ∀ i j : Fin ((k - 5) + 2), i.val + 1 = j.val →
      G.Adj (utail i) (utail j) := by
    simpa only [utail] using cons_sequence_adj (u i1) tail hu1_tail htail_adj
  have hp1_utail : G.Adj (p i1) (utail 0) := by
    simpa [utail] using (hu_path i1).symm
  have hp1utail_adj : ∀ i j : Fin ((k - 5) + 3), i.val + 1 = j.val →
      G.Adj (p1utail i) (p1utail j) := by
    simpa only [p1utail] using cons_sequence_adj (p i1) utail hp1_utail hutail_adj
  have hp0_p1 : G.Adj (p i0) (p1utail 0) := by
    simpa [p1utail, i0, i1] using hp_adj i0 i1 (by simp [i0, i1])
  have hqseq_adj : ∀ i j : Fin ((k - 5) + 4), i.val + 1 = j.val →
      G.Adj (qseq i) (qseq j) := by
    simpa only [qseq] using cons_sequence_adj (p i0) p1utail hp0_p1 hp1utail_adj
  have hqseq_zero : qseq 0 = p i0 := by simp [qseq]
  have hqseq_last : qseq (Fin.last ((k - 5) + 3)) = p ifar := by
    change tail (Fin.last (k - 5)) = p ifar
    apply congrArg p
    apply Fin.ext
    simp [tail, ifar]
    omega
  rw [← Nat.sub_add_cancel hk]
  exact cycleGraph_succ_isContained_of_path_endpoints
    (u i0) qseq hqseq hu0_not_qseq hqseq_adj
    (hqseq_zero ▸ hu_path i0)
    (hqseq_last ▸ (hfar' ▸ hu_path ifar))

/-- The second-neighborhood closure lemma of Cambie--Freschi--Morawski--
Petrova--Pokrovskiy: a path on `2k` vertices in the exact second
neighborhood of a vertex forces a `k`-cycle. -/
theorem cycleGraph_isContained_of_pathGraph_secondNeighbor
    {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 5 ≤ k) (x : V)
    (hpath : SimpleGraph.pathGraph (2 * k) ⊑ G.induce (secondNeighborSet G x)) :
    SimpleGraph.cycleGraph k ⊑ G := by
  obtain ⟨P⟩ := hpath
  let p : Fin (2 * k) → V := fun i ↦ (P i).1
  have hp : Function.Injective p := by
    intro i j hij
    exact P.injective (Subtype.ext hij)
  have hp_ne : ∀ i, p i ≠ x := fun i ↦
    (mem_secondNeighborSet_iff.mp (P i).2).1
  have hp_nonadj : ∀ i, ¬G.Adj x (p i) := fun i ↦
    (mem_secondNeighborSet_iff.mp (P i).2).2.1
  have hex : ∀ i, ∃ u, G.Adj x u ∧ G.Adj u (p i) := fun i ↦
    (mem_secondNeighborSet_iff.mp (P i).2).2.2
  choose u hu_root hu_path using hex
  have hp_adj : ∀ i j : Fin (2 * k), i.val + 1 = j.val →
      G.Adj (p i) (p j) := by
    intro i j hij
    apply P.toHom.map_adj
    rw [SimpleGraph.pathGraph_adj]
    exact Or.inl hij
  by_contra hcycle
  have hperiod (s : ℕ) (hs : s + (k - 4) < 2 * k) :
      u ⟨s, by omega⟩ = u ⟨s + (k - 4), hs⟩ :=
    secondNeighbor_connectors_periodic hk x p u hp hp_ne hp_nonadj hp_adj
      hu_root hu_path hcycle s hs
  let i0 : Fin (2 * k) := ⟨0, by omega⟩
  let i1 : Fin (2 * k) := ⟨1, by omega⟩
  let i2 : Fin (2 * k) := ⟨2, by omega⟩
  let ia : Fin (2 * k) := ⟨k - 4, by omega⟩
  let ib : Fin (2 * k) := ⟨k - 3, by omega⟩
  let ic : Fin (2 * k) := ⟨k - 2, by omega⟩
  let ifar0 : Fin (2 * k) := ⟨2 * k - 8, by omega⟩
  let ifar1 : Fin (2 * k) := ⟨1 + (2 * k - 8), by omega⟩
  have h0a : u i0 = u ia := by
    simpa [i0, ia] using hperiod 0 (by omega)
  have ha0far : u ia = u ifar0 := by
    have h := hperiod (k - 4) (by omega)
    convert h using 1 <;> apply congrArg u <;> apply Fin.ext <;>
      simp [ia, ifar0] <;> omega
  have h0far : u i0 = u ifar0 := h0a.trans ha0far
  have h1b : u i1 = u ib := by
    have h := hperiod 1 (by omega)
    convert h using 1 <;> apply congrArg u <;> apply Fin.ext <;>
      simp [i1, ib] <;> omega
  have hb1far : u ib = u ifar1 := by
    have h := hperiod (k - 3) (by omega)
    convert h using 1 <;> apply congrArg u <;> apply Fin.ext <;>
      simp [ib, ifar1] <;> omega
  have h1far : u i1 = u ifar1 := h1b.trans hb1far
  have h2c : u i2 = u ic := by
    have h := hperiod 2 (by omega)
    convert h using 1 <;> apply congrArg u <;> apply Fin.ext <;>
      simp [i2, ic] <;> omega
  apply hcycle
  by_cases h01 : u i0 = u i1
  · by_cases h12 : u i1 = u i2
    · let seg : Fin ((k - 2) + 1) → V := fun i ↦
        p ⟨i.val, by have := i.isLt; omega⟩
      have hseg : Function.Injective seg := by
        intro i j hij
        have hidx := hp hij
        apply Fin.ext
        exact congrArg (fun z : Fin (2 * k) ↦ z.val) hidx
      have hu0_not_seg : u i0 ∉ Set.range seg := by
        rintro ⟨j, hj⟩
        have hxu := hu_root i0
        have hxseg : G.Adj x (seg j) := by simpa [hj] using hxu
        exact hp_nonadj _ (by simpa only [seg] using hxseg)
      have hseg_adj : ∀ i j : Fin ((k - 2) + 1), i.val + 1 = j.val →
          G.Adj (seg i) (seg j) := by
        intro i j hij
        apply hp_adj
        simpa only [seg] using hij
      have hseg_zero : seg 0 = p i0 := by
        apply congrArg p
        apply Fin.ext
        simp [seg, i0]
      have hseg_last : seg (Fin.last (k - 2)) = p ic := by
        apply congrArg p
        apply Fin.ext
        simp [seg, ic]
      have hu0_last : G.Adj (u i0) (p ic) := by
        rw [h01, h12, h2c]
        exact hu_path ic
      rw [← Nat.sub_add_cancel (show 2 ≤ k by omega)]
      exact cycleGraph_succ_isContained_of_path_endpoints
        (u i0) seg hseg hu0_not_seg hseg_adj
        (hseg_zero ▸ hu_path i0) (hseg_last ▸ hu0_last)
    · exact secondNeighbor_cycle_of_adjacent_connectors_ne hk x p u hp hp_nonadj
        hp_adj hu_root hu_path 1 (by omega)
        (by
          convert h2c using 1 <;> apply congrArg u <;> apply Fin.ext <;>
            simp [i2, ic] <;> omega)
        (by simpa [i1, ifar1] using h1far)
        (by simpa [i1, i2] using h12)
  · exact secondNeighbor_cycle_of_adjacent_connectors_ne hk x p u hp hp_nonadj
      hp_adj hu_root hu_path 0 (by omega)
      (by simpa [i1, ib] using h1b)
      (by simpa [i0, ifar0] using h0far)
      (by simpa [i0, i1] using h01)

/-- Contrapositive form used in the Ramsey induction. -/
theorem pathGraph_not_isContained_secondNeighbor_of_cycleGraph_not_isContained
    {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 5 ≤ k) (x : V)
    (hcycle : ¬SimpleGraph.cycleGraph k ⊑ G) :
    ¬SimpleGraph.pathGraph (2 * k) ⊑ G.induce (secondNeighborSet G x) := by
  intro hpath
  exact hcycle (cycleGraph_isContained_of_pathGraph_secondNeighbor hk x hpath)

end Erdos570
