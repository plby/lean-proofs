/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.Neighborhood
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Shorter paths in second neighborhoods

Informal proof: Cambie--Freschi, arXiv:2606.11174v1, Lemma 7.
The connector arguments below retain all distinctness hypotheses explicitly.
-/

open scoped SimpleGraph

namespace Erdos569

open Erdos570

/-- Along a path in the exact second neighborhood of `x`, chosen middle
vertices at positions differing by `k-4` must agree if the graph is
`C_k`-free.  Otherwise those two middle vertices and the intervening path
segment close to a `k`-cycle. -/
theorem connectors_periodic
    {V : Type*} {G : SimpleGraph V} {k n : ℕ} (hk : 5 ≤ k) (x : V)
    (p u : Fin (n) → V) (hp : Function.Injective p)
    (hp_ne : ∀ i, p i ≠ x) (hp_nonadj : ∀ i, ¬G.Adj x (p i))
    (hp_adj : ∀ i j : Fin (n), i.val + 1 = j.val → G.Adj (p i) (p j))
    (hu_root : ∀ i, G.Adj x (u i)) (hu_path : ∀ i, G.Adj (u i) (p i))
    (hcycle : ¬SimpleGraph.cycleGraph k ⊑ G)
    (s : ℕ) (hs : s + (k - 4) < n) :
    u ⟨s, by omega⟩ = u ⟨s + (k - 4), hs⟩ := by
  let is : Fin (n) := ⟨s, by omega⟩
  let it : Fin (n) := ⟨s + (k - 4), hs⟩
  by_contra hne
  have hust : u is ≠ u it := by simpa [is, it] using hne
  let seg : Fin ((k - 5) + 2) → V := fun i ↦
    p ⟨s + i.val, by have := i.isLt; omega⟩
  have hseg : Function.Injective seg := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (Fin.ext_iff.mp (hp hij))
  have hu_not_seg (i : Fin (n)) : u i ∉ Set.range seg := by
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
    dsimp only
    omega
  have hseg_zero : seg 0 = p is := by
    apply congrArg p
    apply Fin.ext
    simp [is]
  have hseg_last : seg (Fin.last ((k - 5) + 1)) = p it := by
    apply congrArg p
    apply Fin.ext
    simp [it]
    omega
  apply hcycle
  rw [← Nat.sub_add_cancel hk]
  exact cycleGraph_add_five_isContained_of_path_connectors
    x (u is) (u it) seg hseg (hu_not_seg it) (hu_not_seg is) hust
    hx_not_seg (hu_root is).ne (hu_root it).ne
    (hu_root is) (hseg_zero ▸ hu_path is)
    hseg_adj (hseg_last ▸ (hu_path it).symm) (hu_root it).symm


/-- Claim 9: connectors two positions apart cannot agree. -/
theorem connectors_two_apart_ne
    {V : Type*} {G : SimpleGraph V} {k n : ℕ} (hk : 5 ≤ k) (x : V)
    (p u : Fin n → V) (hp : Function.Injective p)
    (hp_ne : ∀ i, p i ≠ x) (hp_nonadj : ∀ i, ¬G.Adj x (p i))
    (hp_adj : ∀ i j : Fin n, i.val + 1 = j.val → G.Adj (p i) (p j))
    (hu_root : ∀ i, G.Adj x (u i)) (hu_path : ∀ i, G.Adj (u i) (p i))
    (hcycle : ¬SimpleGraph.cycleGraph k ⊑ G)
    (s : ℕ) (hs : s + (k - 2) < n) :
    u ⟨s, by omega⟩ ≠ u ⟨s + 2, by omega⟩ := by
  intro heq
  have hperiod := connectors_periodic hk x p u hp hp_ne hp_nonadj hp_adj
    hu_root hu_path hcycle (s + 2) (by omega)
  have hfar : u ⟨s, by omega⟩ = u ⟨s + (k - 2), hs⟩ := by
    convert heq.trans hperiod using 1
    congr 2
    omega
  let seg : Fin ((k - 2) + 1) → V := fun i ↦
    p ⟨s + i.val, by have := i.isLt; omega⟩
  have hseg : Function.Injective seg := by
    intro i j hij
    apply Fin.ext
    have h := Fin.ext_iff.mp (hp hij)
    exact Nat.add_left_cancel h
  have hu_not_seg : u ⟨s, by omega⟩ ∉ Set.range seg := by
    rintro ⟨i, hi⟩
    exact hp_nonadj _ (hi ▸ hu_root ⟨s, by omega⟩)
  have hseg_adj : ∀ i j : Fin ((k - 2) + 1), i.val + 1 = j.val →
      G.Adj (seg i) (seg j) := by
    intro i j hij
    apply hp_adj
    dsimp only
    omega
  have hfirst : G.Adj (u ⟨s, by omega⟩) (seg 0) := by
    simpa only [seg, Fin.val_zero, Nat.add_zero] using hu_path ⟨s, by omega⟩
  have hlast : G.Adj (u ⟨s, by omega⟩) (seg (Fin.last (k - 2))) := by
    simpa only [seg, Fin.val_last, hfar] using hu_path ⟨s + (k - 2), hs⟩
  apply hcycle
  have hc := cycleGraph_succ_isContained_of_path_endpoints
    (u ⟨s, Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hs⟩)
    seg hseg hu_not_seg hseg_adj hfirst hlast
  have he : k - 2 + 2 = k := by omega
  exact he ▸ hc

/-- The two-connector cycle in Figure 1(b), with every index made explicit. -/
theorem cycle_of_two_connectors
    {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 8 ≤ k)
    (p : Fin (k + 1) → V) (a b : V) (hp : Function.Injective p)
    (hab : a ≠ b) (ha : ∀ i, a ≠ p i) (hb : ∀ i, b ≠ p i)
    (hp_adj : ∀ i j : Fin (k + 1), i.val + 1 = j.val → G.Adj (p i) (p j))
    (ha0 : G.Adj a (p ⟨0, by omega⟩))
    (hb2 : G.Adj b (p ⟨2, by omega⟩))
    (hbfar : G.Adj b (p ⟨k - 2, by omega⟩))
    (ha4 : G.Adj a (p ⟨4, by omega⟩)) :
    SimpleGraph.cycleGraph k ⊑ G := by
  let f : Fin k → V := fun i ↦
    if h0 : i.val = 0 then a
    else if h4 : i.val = 4 then b
    else if hlow : i.val < 4 then p ⟨i.val - 1, by omega⟩
    else p ⟨k + 3 - i.val, by omega⟩
  have hpa (i) : p i ≠ a := (ha i).symm
  have hpb (i) : p i ≠ b := (hb i).symm
  have hf : Function.Injective f := by
    intro i j hij
    dsimp only [f] at hij
    split_ifs at hij <;> try simp only [ha, hb, hpa, hpb, hab, Ne.symm hab] at hij
    all_goals
      first
      | have hidx := Fin.ext_iff.mp (hp hij)
        dsimp only at hidx
        apply Fin.ext
        omega
      | apply Fin.ext
        omega
  apply cycleGraph_isContained_of_sequence f hf
  · intro i j hij
    dsimp only [f]
    split_ifs with hi0 hi4 hilow hj0 hj4 hjlow <;> try omega
    all_goals
      first
      | convert ha0 using 1 <;> congr 2 <;> omega
      | convert hb2.symm using 1 <;> congr 2 <;> omega
      | convert hbfar using 1 <;> congr 2 <;> omega
      | apply hp_adj
        dsimp only
        omega
      | apply SimpleGraph.Adj.symm
        apply hp_adj
        dsimp only
        omega
  · intro i j hi hj
    have hj0 : j.val ≠ 0 := by omega
    have hj4 : j.val ≠ 4 := by omega
    have hjlow : ¬ j.val < 4 := by omega
    simp only [f, hi, dif_pos, hj0, hj4, hjlow, dite_false]
    have he : k + 3 - j.val = 4 := by omega
    have hi' : (⟨k + 3 - j.val, by omega⟩ : Fin (k + 1)) = ⟨4, by omega⟩ :=
      Fin.ext he
    rw [hi']
    exact ha4

/-- The three-connector cycle in Figure 1(c). -/
theorem cycle_of_three_connectors
    {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 8 ≤ k)
    (p : Fin (k + 1) → V) (a b c x : V) (hp : Function.Injective p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (ha : ∀ i, a ≠ p i) (hb : ∀ i, b ≠ p i)
    (hc : ∀ i, c ≠ p i) (hx : ∀ i, x ≠ p i)
    (hp_adj : ∀ i j : Fin (k + 1), i.val + 1 = j.val → G.Adj (p i) (p j))
    (ha0 : G.Adj a (p ⟨0, by omega⟩))
    (hb2 : G.Adj b (p ⟨2, by omega⟩))
    (hxb_adj : G.Adj x b) (hxc_adj : G.Adj x c)
    (hc4 : G.Adj c (p ⟨4, by omega⟩))
    (haf : G.Adj a (p ⟨k - 4, by omega⟩)) :
    SimpleGraph.cycleGraph k ⊑ G := by
  let f : Fin k → V := fun i ↦
    if h0 : i.val = 0 then a
    else if h4 : i.val = 4 then b
    else if h5 : i.val = 5 then x
    else if h6 : i.val = 6 then c
    else if hlow : i.val < 4 then p ⟨i.val - 1, by omega⟩
    else p ⟨i.val - 3, by omega⟩
  have hpa (i) : p i ≠ a := (ha i).symm
  have hpb (i) : p i ≠ b := (hb i).symm
  have hpc (i) : p i ≠ c := (hc i).symm
  have hpx (i) : p i ≠ x := (hx i).symm
  have hf : Function.Injective f := by
    intro i j hij
    dsimp only [f] at hij
    split_ifs at hij <;> try simp only [ha, hb, hc, hx, hpa, hpb, hpc, hpx,
      hab, hac, hbc, hxa, hxb, hxc, Ne.symm hab, Ne.symm hac, Ne.symm hbc,
      Ne.symm hxa, Ne.symm hxb, Ne.symm hxc] at hij
    all_goals
      first
      | have hidx := Fin.ext_iff.mp (hp hij)
        dsimp only at hidx
        apply Fin.ext
        omega
      | apply Fin.ext
        omega
  apply cycleGraph_isContained_of_sequence f hf
  · intro i j hij
    dsimp only [f]
    split_ifs <;> try omega
    all_goals
      first
      | exact hxb_adj.symm
      | exact hxc_adj
      | convert ha0 using 1 <;> congr 2 <;> omega
      | convert hb2.symm using 1 <;> congr 2 <;> omega
      | convert hc4 using 1 <;> congr 2 <;> omega
      | apply hp_adj
        dsimp only
        omega
  · intro i j hi hj
    have hj0 : j.val ≠ 0 := by omega
    have hj4 : j.val ≠ 4 := by omega
    have hj5 : j.val ≠ 5 := by omega
    have hj6 : j.val ≠ 6 := by omega
    have hjlow : ¬ j.val < 4 := by omega
    simp only [f, hi, dif_pos, hj0, hj4, hj5, hj6, hjlow, dite_false]
    have hi' : (⟨j.val - 3, by omega⟩ : Fin (k + 1)) = ⟨k - 4, by omega⟩ := by
      apply Fin.ext
      dsimp only
      omega
    rw [hi']
    exact haf

/-- The seven-cycle used in the exceptional `k = 7` case. -/
theorem seven_cycle_of_connectors
    {V : Type*} {G : SimpleGraph V}
    (p : Fin 8 → V) (a b : V) (hp : Function.Injective p)
    (hab : a ≠ b) (ha : ∀ i, a ≠ p i) (hb : ∀ i, b ≠ p i)
    (hp_adj : ∀ i j : Fin 8, i.val + 1 = j.val → G.Adj (p i) (p j))
    (ha0 : G.Adj a (p 0)) (hb2 : G.Adj b (p 2))
    (hb5 : G.Adj b (p 5)) (ha6 : G.Adj a (p 6)) :
    SimpleGraph.cycleGraph 7 ⊑ G := by
  let f : Fin 7 → V := ![a, p 0, p 1, p 2, b, p 5, p 6]
  have hpa (i) : p i ≠ a := (ha i).symm
  have hpb (i) : p i ≠ b := (hb i).symm
  have hpp (i j) : p i = p j ↔ i = j := hp.eq_iff
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f]
  apply cycleGraph_isContained_of_sequence f hf
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    all_goals
      first | exact ha0 | exact hb2.symm | exact hb5 | exact hp_adj _ _ rfl
  · intro i j hi hj
    have hi0 : i = 0 := Fin.ext hi
    have hj6 : j = 6 := Fin.ext (by omega)
    subst i
    subst j
    exact ha6

/-- Lemma 7 of Cambie--Freschi: a path on `k + 1` vertices in the exact
second neighborhood forces a cycle of length `k`, for every `k ≥ 7`. -/
theorem cycleGraph_isContained_of_pathGraph_secondNeighbor
    {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 7 ≤ k) (x : V)
    (hpath : SimpleGraph.pathGraph (k + 1) ⊑ G.induce (secondNeighborSet G x)) :
    SimpleGraph.cycleGraph k ⊑ G := by
  obtain ⟨P⟩ := hpath
  let p : Fin (k + 1) → V := fun i ↦ (P i).1
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
  have hp_adj : ∀ i j : Fin (k + 1), i.val + 1 = j.val →
      G.Adj (p i) (p j) := by
    intro i j hij
    apply P.toHom.map_adj
    rw [SimpleGraph.pathGraph_adj]
    exact Or.inl hij
  have hup (i j) : u i ≠ p j := by
    intro heq
    exact hp_nonadj j (heq ▸ hu_root i)
  by_contra hcycle
  have hperiod (s : ℕ) (hs : s + (k - 4) < k + 1) :
      u ⟨s, by omega⟩ = u ⟨s + (k - 4), hs⟩ :=
    connectors_periodic (by omega) x p u hp hp_ne hp_nonadj hp_adj
      hu_root hu_path hcycle s hs
  have htwo (s : ℕ) (hs : s + (k - 2) < k + 1) :
      u ⟨s, by omega⟩ ≠ u ⟨s + 2, by omega⟩ :=
    connectors_two_apart_ne (by omega) x p u hp hp_ne hp_nonadj hp_adj
      hu_root hu_path hcycle s hs
  apply hcycle
  by_cases hk7 : k = 7
  · subst k
    have h03 : u 0 = u 3 := hperiod 0 (by decide)
    have h36 : u 3 = u 6 := hperiod 3 (by decide)
    have h25 : u 2 = u 5 := hperiod 2 (by decide)
    exact seven_cycle_of_connectors p (u 0) (u 2) hp (htwo 0 (by decide))
      (hup 0) (hup 2) hp_adj (hu_path 0) (hu_path 2)
      (h25 ▸ hu_path 5) ((h03.trans h36) ▸ hu_path 6)
  have hk8 : 8 ≤ k := by omega
  let i0 : Fin (k + 1) := ⟨0, by omega⟩
  let i2 : Fin (k + 1) := ⟨2, by omega⟩
  let i4 : Fin (k + 1) := ⟨4, by omega⟩
  have h02 : u i0 ≠ u i2 := htwo 0 (by omega)
  have h24 : u i2 ≠ u i4 := htwo 2 (by omega)
  have h0far : u i0 = u ⟨k - 4, by omega⟩ := by
    simpa only [Nat.zero_add] using hperiod 0 (by omega)
  have h2far : u i2 = u ⟨k - 2, by omega⟩ := by
    have he : 2 + (k - 4) = k - 2 := by omega
    simpa only [he] using hperiod 2 (by omega)
  by_cases h04 : u i0 = u i4
  · exact cycle_of_two_connectors hk8 p (u i0) (u i2) hp h02
      (hup i0) (hup i2) hp_adj (hu_path i0) (hu_path i2)
      (h2far ▸ hu_path ⟨k - 2, by omega⟩) (h04 ▸ hu_path i4)
  · exact cycle_of_three_connectors hk8 p (u i0) (u i2) (u i4) x hp
      h02 h04 h24 (hu_root i0).ne (hu_root i2).ne (hu_root i4).ne
      (hup i0) (hup i2) (hup i4) (fun i ↦ (hp_ne i).symm)
      hp_adj (hu_path i0) (hu_path i2) (hu_root i2) (hu_root i4)
      (hu_path i4) (h0far ▸ hu_path ⟨k - 4, by omega⟩)

/-- The same path bound also holds for lengths five and six: the
connector periodicity contradicts the two-apart inequality immediately. -/
theorem cycleGraph_isContained_of_pathGraph_secondNeighbor_ge_five
    {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 5 ≤ k) (x : V)
    (hpath : SimpleGraph.pathGraph (k + 1) ⊑ G.induce (secondNeighborSet G x)) :
    SimpleGraph.cycleGraph k ⊑ G := by
  by_cases hk7 : 7 ≤ k
  · exact cycleGraph_isContained_of_pathGraph_secondNeighbor hk7 x hpath
  obtain ⟨P⟩ := hpath
  let p : Fin (k + 1) → V := fun i ↦ (P i).1
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
  have hp_adj : ∀ i j : Fin (k + 1), i.val + 1 = j.val →
      G.Adj (p i) (p j) := by
    intro i j hij
    apply P.toHom.map_adj
    rw [SimpleGraph.pathGraph_adj]
    exact Or.inl hij
  by_contra hcycle
  have hperiod (s : ℕ) (hs : s + (k - 4) < k + 1) :
      u ⟨s, by omega⟩ = u ⟨s + (k - 4), hs⟩ :=
    connectors_periodic (by omega) x p u hp hp_ne hp_nonadj hp_adj
      hu_root hu_path hcycle s hs
  have htwo (s : ℕ) (hs : s + (k - 2) < k + 1) :
      u ⟨s, by omega⟩ ≠ u ⟨s + 2, by omega⟩ :=
    connectors_two_apart_ne (by omega) x p u hp hp_ne hp_nonadj hp_adj
      hu_root hu_path hcycle s hs
  have hk_cases : k = 5 ∨ k = 6 := by omega
  rcases hk_cases with rfl | rfl
  · have h01 : u 0 = u 1 := hperiod 0 (by decide)
    have h12 : u 1 = u 2 := hperiod 1 (by decide)
    exact (htwo 0 (by decide)) (h01.trans h12)
  · exact (htwo 0 (by decide)) (hperiod 0 (by decide))

end Erdos569
