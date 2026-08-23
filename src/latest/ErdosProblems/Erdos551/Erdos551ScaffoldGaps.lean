import ErdosProblems.Erdos551.Erdos551Core

open scoped BigOperators Classical SimpleGraph NNReal
open Filter Asymptotics Topology

namespace Erdos551

open Fintype SimpleGraph

def orderedGapStart {q : ℕ} (C : Finset (Fin q)) :
    Fin (C.card + 1) → ℕ :=
  Fin.cases 0 (fun i => (C.orderEmbOfFin rfl i).val + 1)

def orderedGapEnd {q : ℕ} (C : Finset (Fin q)) :
    Fin (C.card + 1) → ℕ :=
  fun j => if h : j.val < C.card
    then (C.orderEmbOfFin rfl ⟨j.val, h⟩).val else q

def orderedGapCapacity {q : ℕ} (C : Finset (Fin q))
    (j : Fin (C.card + 1)) : ℕ :=
  orderedGapEnd C j - orderedGapStart C j - 1

/-- The number of positive linear gaps left after cutting at `C`.  Unlike
the total length subsequently assigned to those gaps, this number depends
only on the cut set. -/
def orderedPositiveGapCount {q : ℕ} (C : Finset (Fin q)) : ℕ :=
  ((Finset.univ : Finset (Fin (C.card + 1))).filter
    fun j => orderedGapCapacity C j ≠ 0).card

theorem orderedGapStart_le_end {q : ℕ} (C : Finset (Fin q))
    (j : Fin (C.card + 1)) :
    orderedGapStart C j ≤ orderedGapEnd C j := by
  induction j using Fin.cases with
  | zero =>
      simp [orderedGapStart, orderedGapEnd]
  | succ j =>
      by_cases hj : j.val + 1 < C.card
      · let next : Fin C.card := ⟨j.val + 1, hj⟩
        have hmono := (C.orderEmbOfFin rfl).strictMono (show j < next by
          apply Fin.mk_lt_mk.mpr
          simp [next])
        simpa [orderedGapStart, orderedGapEnd, hj] using hmono
      · have hdlt : (C.orderEmbOfFin rfl j).val < q :=
          (C.orderEmbOfFin rfl j).isLt
        simp [orderedGapStart, orderedGapEnd, hj]

theorem sum_orderedGapStart {q : ℕ} (C : Finset (Fin q)) :
    (∑ j, orderedGapStart C j) =
      C.card + ∑ i : Fin C.card, (C.orderEmbOfFin rfl i).val := by
  rw [Fin.sum_univ_succ]
  simp [orderedGapStart, Finset.sum_add_distrib, add_comm]

theorem sum_orderedGapEnd {q : ℕ} (C : Finset (Fin q)) :
    (∑ j, orderedGapEnd C j) =
      q + ∑ i : Fin C.card, (C.orderEmbOfFin rfl i).val := by
  rw [Fin.sum_univ_castSucc]
  simp [orderedGapEnd, add_comm]

theorem sum_orderedGap_vertexCounts {q : ℕ} (C : Finset (Fin q)) :
    (∑ j, (orderedGapEnd C j - orderedGapStart C j)) = q - C.card := by
  have hpoint : ∀ j, (orderedGapEnd C j - orderedGapStart C j) +
      orderedGapStart C j = orderedGapEnd C j := by
    intro j
    exact Nat.sub_add_cancel (orderedGapStart_le_end C j)
  have hsum : (∑ j, (orderedGapEnd C j - orderedGapStart C j)) +
      (∑ j, orderedGapStart C j) = ∑ j, orderedGapEnd C j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hpoint j)
  rw [sum_orderedGapStart, sum_orderedGapEnd] at hsum
  omega

theorem le_sum_orderedGapCapacity {q : ℕ} (C : Finset (Fin q)) :
    q - 2 * C.card - 1 ≤ ∑ j, orderedGapCapacity C j := by
  have hsub (j : Fin (C.card + 1)) :
      orderedGapEnd C j - orderedGapStart C j ≤
        orderedGapCapacity C j + 1 := by
    dsimp [orderedGapCapacity]
    omega
  have hsum := Finset.sum_le_sum fun j (_hj : j ∈ (Finset.univ : Finset (Fin (C.card + 1)))) => hsub j
  rw [sum_orderedGap_vertexCounts] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  have hCq : C.card ≤ q := by
    calc
      C.card ≤ (Finset.univ : Finset (Fin q)).card :=
        Finset.card_le_card (Finset.subset_univ C)
      _ = q := by simp
  have hraw : q ≤ (∑ j, orderedGapCapacity C j) +
      (2 * C.card + 1) := by
    calc
      q = (q - C.card) + C.card :=
        (Nat.sub_add_cancel hCq).symm
      _ ≤ ((∑ j, orderedGapCapacity C j) + (C.card + 1)) +
          C.card := Nat.add_le_add_right hsum C.card
      _ = (∑ j, orderedGapCapacity C j) +
          (2 * C.card + 1) := by omega
  by_cases hbig : 2 * C.card + 1 ≤ q
  · rw [Nat.sub_sub]
    exact Nat.sub_le_iff_le_add.2 hraw
  · have : q ≤ 2 * C.card := by omega
    omega

theorem orderedGapEnd_le {q : ℕ} (C : Finset (Fin q))
    (j : Fin (C.card + 1)) : orderedGapEnd C j ≤ q := by
  by_cases hj : j.val < C.card
  · simp [orderedGapEnd, hj]
  · simp [orderedGapEnd, hj]

theorem orderedGap_start_add_lt_end_of_le_capacity
    {q : ℕ} (C : Finset (Fin q)) (j : Fin (C.card + 1))
    {r : ℕ} (hrpos : 0 < r) (hr : r ≤ orderedGapCapacity C j) :
    orderedGapStart C j + r < orderedGapEnd C j := by
  have hse := orderedGapStart_le_end C j
  dsimp [orderedGapCapacity] at hr
  omega

theorem orderedGap_avoids_cut {q : ℕ} (C : Finset (Fin q))
    (j : Fin (C.card + 1)) {d : Fin q} (hd : d ∈ C) :
    d.val < orderedGapStart C j ∨ orderedGapEnd C j ≤ d.val := by
  let pos : Fin C.card := (C.orderIsoOfFin rfl).symm ⟨d, hd⟩
  have heq : C.orderEmbOfFin rfl pos = d := by
    have h := (C.orderIsoOfFin rfl).apply_symm_apply ⟨d, hd⟩
    exact congrArg Subtype.val h
  by_cases hj0 : j.val = 0
  · right
    have hj : j = 0 := Fin.ext hj0
    subst j
    by_cases hC : C.card = 0
    · have : C = ∅ := Finset.card_eq_zero.mp hC
      simp [this] at hd
    · have hCpos : 0 < C.card := Nat.pos_of_ne_zero hC
      let first : Fin C.card := ⟨0, hCpos⟩
      have hle : first ≤ pos := Fin.mk_le_mk.mpr (Nat.zero_le _)
      have hmono := (C.orderEmbOfFin rfl).monotone hle
      have hmonoVal : (C.orderEmbOfFin rfl first).val ≤
          (C.orderEmbOfFin rfl pos).val := hmono
      rw [heq] at hmonoVal
      simpa [orderedGapEnd, hCpos, first] using hmonoVal
  · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj0
    by_cases hjlast : j.val = C.card
    · left
      let last : Fin C.card := ⟨j.val - 1, by omega⟩
      have hle : pos ≤ last := by
        apply Fin.mk_le_mk.mpr
        have hposlt := pos.isLt
        change pos.val ≤ j.val - 1
        omega
      have hmono := (C.orderEmbOfFin rfl).monotone hle
      have hjEq : j = last.succ := by
        apply Fin.ext
        simp [last]
        omega
      have hmonoVal : (C.orderEmbOfFin rfl pos).val ≤
          (C.orderEmbOfFin rfl last).val := hmono
      rw [heq] at hmonoVal
      rw [hjEq]
      simp [orderedGapStart]
      omega
    · have hjlt : j.val < C.card := by omega
      let prev : Fin C.card := ⟨j.val - 1, by omega⟩
      let curr : Fin C.card := ⟨j.val, hjlt⟩
      by_cases hpos : pos.val < j.val
      · left
        have hle : pos ≤ prev := by
          apply Fin.mk_le_mk.mpr
          change pos.val ≤ j.val - 1
          omega
        have hmono := (C.orderEmbOfFin rfl).monotone hle
        have hjEq : j = prev.succ := by
          apply Fin.ext
          simp [prev]
          omega
        have hmonoVal : (C.orderEmbOfFin rfl pos).val ≤
            (C.orderEmbOfFin rfl prev).val := hmono
        rw [heq] at hmonoVal
        rw [hjEq]
        simp [orderedGapStart]
        omega
      · right
        have hle : curr ≤ pos := Fin.mk_le_mk.mpr (by
          change j.val ≤ pos.val
          omega)
        have hmono := (C.orderEmbOfFin rfl).monotone hle
        have hmonoVal : (C.orderEmbOfFin rfl curr).val ≤
            (C.orderEmbOfFin rfl pos).val := hmono
        rw [heq] at hmonoVal
        simpa [orderedGapEnd, hjlt, curr] using hmonoVal

theorem orderedGapEnd_le_start_of_lt {q : ℕ} (C : Finset (Fin q))
    {i j : Fin (C.card + 1)} (hij : i < j) :
    orderedGapEnd C i ≤ orderedGapStart C j := by
  have hi : i.val < C.card := by omega
  have hjpos : 0 < j.val := by omega
  let ci : Fin C.card := ⟨i.val, hi⟩
  let pj : Fin C.card := ⟨j.val - 1, by omega⟩
  have hle : ci ≤ pj := Fin.mk_le_mk.mpr (by omega)
  have hmono := (C.orderEmbOfFin rfl).monotone hle
  have hmonoVal : (C.orderEmbOfFin rfl ci).val ≤
      (C.orderEmbOfFin rfl pj).val := hmono
  have hjEq : j = pj.succ := by
    apply Fin.ext
    simp [pj]
    omega
  have hend : orderedGapEnd C i = (C.orderEmbOfFin rfl ci).val := by
    simp [orderedGapEnd, hi, ci]
  have hstart : orderedGapStart C j =
      (C.orderEmbOfFin rfl pj).val + 1 := by
    rw [hjEq]
    simp [orderedGapStart]
  rw [hend, hstart]
  omega

/-- An ordered cut set decomposes a linear alternating scaffold into a
family of disjoint positive segments.  Their total internal step budget is
any prescribed value between the number of nonzero gaps and the total gap
capacity. -/
theorem exists_disjoint_scaffold_gap_paths
    {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {q R : ℕ} {A B : Finset V} (hq : 0 < q)
    (a b : Fin q → V) (ha : Function.Injective a)
    (hb : Function.Injective b) (haA : ∀ i, a i ∈ A)
    (hbB : ∀ i, b i ∈ B) (hAB : Disjoint A B)
    (hab : ∀ i, G.Adj (a i) (b i))
    (hba : ∀ i, G.Adj (b i) (a (finCyclicSucc hq i)))
    (C : Finset (Fin q))
    (hmin : ((Finset.univ : Finset (Fin (C.card + 1))).filter
      fun j => orderedGapCapacity C j ≠ 0).card ≤ R)
    (hR : R ≤ q - 2 * C.card - 1) :
    ∃ m : ℕ, m = orderedPositiveGapCount C ∧ m ≤ C.card + 1 ∧
      ∃ u v : Fin m → V, ∃ p : ∀ i : Fin m, G.Walk (u i) (v i),
        (∀ i, u i ∈ A) ∧ (∀ i, v i ∈ A) ∧
        (∀ i, (p i).IsPath) ∧
        (∀ i w, w ∈ (p i).support → w ∈ A ∪ B) ∧
        (∀ i j, i ≠ j → (p i).support.Disjoint (p j).support) ∧
        (∑ i, (p i).length) = 2 * R ∧
        ∀ i d, d ∈ C →
          a d ∉ (p i).support ∧ b d ∉ (p i).support := by
  classical
  let cap : Fin (C.card + 1) → ℕ := orderedGapCapacity C
  have hRcap : R ≤ ∑ j, cap j :=
    hR.trans (le_sum_orderedGapCapacity C)
  obtain ⟨g, hgsum, hgle, hgzero⟩ :=
    exists_positive_fin_weights_sum_eq_le_fun cap hmin hRcap
  let J : Finset (Fin (C.card + 1)) :=
    Finset.univ.filter fun j => cap j ≠ 0
  let e : Fin J.card ≃ J := J.equivFin.symm
  let gap : Fin J.card → Fin (C.card + 1) := fun i => (e i).1
  let s : Fin J.card → ℕ := fun i => orderedGapStart C (gap i)
  let r : Fin J.card → ℕ := fun i => g (gap i)
  have hgapmem : ∀ i, gap i ∈ J := fun i => (e i).2
  have hcapne : ∀ i, cap (gap i) ≠ 0 := by
    intro i
    exact (Finset.mem_filter.mp (hgapmem i)).2
  have hrpos : ∀ i, 0 < r i := by
    intro i
    have hne : g (gap i) ≠ 0 := by
      intro hz
      exact hcapne i ((hgzero (gap i)).mp hz)
    exact Nat.pos_of_ne_zero hne
  have hsr : ∀ i, s i + r i < q := by
    intro i
    exact (orderedGap_start_add_lt_end_of_le_capacity C (gap i)
      (hrpos i) (hgle (gap i))).trans_le (orderedGapEnd_le C (gap i))
  let ea (i : Fin J.card) : Fin (r i + 1) → Fin q :=
    fun t => ⟨s i + t.val, by have := hsr i; omega⟩
  let eb (i : Fin J.card) : Fin (r i) → Fin q :=
    fun t => ⟨s i + t.val, by have := hsr i; omega⟩
  have habdisj : ∀ i j : Fin q, a i ≠ b j := by
    intro i j hij
    exact (Finset.disjoint_left.mp hAB) (haA i) (hij ▸ hbB j)
  choose p hp hplen hpsupp using fun i : Fin J.card =>
    exists_segment_path_of_cyclicAlternatingScaffold_data
      G hq a b ha hb habdisj hab hba (hsr i)
  change ∀ i : Fin J.card, ∀ w ∈ (p i).support,
      (∃ t : Fin (r i + 1), a (ea i t) = w) ∨
        ∃ t : Fin (r i), b (eb i t) = w at hpsupp
  have hploc : ∀ i w, w ∈ (p i).support → w ∈ A ∪ B := by
    intro i w hw
    rcases hpsupp i w hw with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact Finset.mem_union_left _ (haA (ea i t))
    · exact Finset.mem_union_right _ (hbB (eb i t))
  have hgapinj : Function.Injective gap := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hpdisj_lt : ∀ i j, gap i < gap j →
      (p i).support.Disjoint (p j).support := by
    intro i j hlt w hwi hwj
    have hsep := orderedGapEnd_le_start_of_lt C hlt
    rcases hpsupp i w hwi with ⟨ti, hi⟩ | ⟨ti, hi⟩ <;>
      rcases hpsupp j w hwj with ⟨tj, hj⟩ | ⟨tj, hj⟩
    · have heq : ea i ti = ea j tj := ha (hi.trans hj.symm)
      have hv := congrArg Fin.val heq
      have hri := orderedGap_start_add_lt_end_of_le_capacity C (gap i)
        (hrpos i) (hgle (gap i))
      dsimp [ea, s] at hv
      omega
    · exact (Finset.disjoint_left.mp hAB)
        (haA (ea i ti)) (hi ▸ hj ▸ hbB (eb j tj))
    · exact (Finset.disjoint_left.mp hAB)
        (haA (ea j tj)) (hj ▸ hi ▸ hbB (eb i ti))
    · have heq : eb i ti = eb j tj := hb (hi.trans hj.symm)
      have hv := congrArg Fin.val heq
      have hri := orderedGap_start_add_lt_end_of_le_capacity C (gap i)
        (hrpos i) (hgle (gap i))
      dsimp [eb, s] at hv
      omega
  have hpdisj : ∀ i j, i ≠ j →
      (p i).support.Disjoint (p j).support := by
    intro i j hij
    have hgapne : gap i ≠ gap j := fun h => hij (hgapinj h)
    rcases lt_or_gt_of_ne hgapne with hlt | hgt
    · exact hpdisj_lt i j hlt
    · exact (hpdisj_lt j i hgt).symm
  have hpavoid : ∀ i d, d ∈ C →
      a d ∉ (p i).support ∧ b d ∉ (p i).support := by
    intro i d hd
    have havoid := orderedGap_avoids_cut C (gap i) hd
    constructor
    · intro hmem
      rcases hpsupp i (a d) hmem with ⟨t, ht⟩ | ⟨t, ht⟩
      · have heq : d = ea i t := (ha ht).symm
        have hv := congrArg Fin.val heq
        have hr := orderedGap_start_add_lt_end_of_le_capacity C (gap i)
          (hrpos i) (hgle (gap i))
        dsimp [ea, s] at hv
        omega
      · exact (Finset.disjoint_left.mp hAB) (haA d) (ht ▸ hbB (eb i t))
    · intro hmem
      rcases hpsupp i (b d) hmem with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact (Finset.disjoint_left.mp hAB) (haA (ea i t))
          (ht ▸ hbB d)
      · have heq : eb i t = d := hb ht
        have hv := congrArg Fin.val heq
        have hr := orderedGap_start_add_lt_end_of_le_capacity C (gap i)
          (hrpos i) (hgle (gap i))
        dsimp [eb, s] at hv
        omega
  have hrsum : (∑ i, r i) = R := by
    calc
      (∑ i, r i) = ∑ x : J, g x.1 :=
        e.sum_comp (fun x : J => g x.1)
      _ = ∑ x ∈ J.attach, g x.1 := by rw [Finset.attach_eq_univ]
      _ = ∑ j ∈ J, g j := Finset.sum_attach J g
      _ = ∑ j, g j := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _hj hjnot
        have hcapzero : cap j = 0 := by
          by_contra hne
          exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        exact (hgzero j).2 hcapzero
      _ = R := hgsum
  refine ⟨J.card, rfl, ?_, (fun i => a (ea i 0)),
    (fun i => a (ea i (Fin.last (r i)))), p, ?_, ?_, hp,
    hploc, hpdisj, ?_, hpavoid⟩
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  · intro i
    exact haA (ea i 0)
  · intro i
    exact haA (ea i (Fin.last (r i)))
  · calc
      (∑ i, (p i).length) = ∑ i, 2 * r i := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hplen i
      _ = 2 * ∑ i, r i := by simp [Finset.mul_sum]
      _ = 2 * R := by rw [hrsum]

end Erdos551
