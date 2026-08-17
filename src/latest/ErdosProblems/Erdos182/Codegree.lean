import Mathlib

/-!
# The Kővári–Sós–Turán count and codegree cleaning

This file records the finite, integer-valued combinatorial core of Lemmas 3.1 and 3.2
of Janzer--Sudakov.  A bipartite graph is represented by its set of ordered edges in
`A × B`; this avoids any bookkeeping about an ambient one-part graph.
-/

namespace Erdos182

open scoped BigOperators

section Count

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The neighbours in `A` of a vertex in the right class. -/
def leftNeighbors (r : A → B → Prop) [DecidableRel r] (b : B) : Finset A :=
  Finset.univ.filter fun a ↦ r a b

/-- The neighbours in `B` of a vertex in the left class. -/
def rightNeighbors (r : A → B → Prop) [DecidableRel r] (a : A) : Finset B :=
  Finset.univ.filter fun b ↦ r a b

/-- Number of edges of a finite bipartite relation. -/
def bipartiteEdgeCount (r : A → B → Prop) [DecidableRel r] : ℕ :=
  ∑ a : A, (rightNeighbors r a).card

/-- The two degree sums of a finite bipartite relation agree. -/
theorem bipartiteEdgeCount_eq_sum_left
    (r : A → B → Prop) [DecidableRel r] :
    bipartiteEdgeCount r = ∑ b : B, (leftNeighbors r b).card := by
  simpa [bipartiteEdgeCount, rightNeighbors, leftNeighbors,
    Finset.bipartiteAbove, Finset.bipartiteBelow] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset A)) (t := (Finset.univ : Finset B)) (r := r))

/-- The common neighbours in `B` of a finite set of vertices in the left class. -/
def commonRight (r : A → B → Prop) [DecidableRel r] (s : Finset A) : Finset B :=
  Finset.univ.filter fun b ↦ ∀ a ∈ s, r a b

/-- There are no `k` left vertices with `k` common right neighbours. -/
def IsBipartiteKFree (r : A → B → Prop) [DecidableRel r] (k : ℕ) : Prop :=
  ∀ s : Finset A, s.card = k → (commonRight r s).card < k

/-- `K_{k,k}`-freeness is inherited by restricting either vertex class. -/
theorem IsBipartiteKFree.restrict (r : A → B → Prop) [DecidableRel r] {k : ℕ}
    (hfree : IsBipartiteKFree r k) (p : A → Prop) (q : B → Prop)
    [DecidablePred p] [DecidablePred q] :
    IsBipartiteKFree (fun a : {a // p a} ↦ fun b : {b // q b} ↦ r a b) k := by
  classical
  intro s hs
  let ea : {a // p a} ↪ A := ⟨Subtype.val, Subtype.val_injective⟩
  let eb : {b // q b} ↪ B := ⟨Subtype.val, Subtype.val_injective⟩
  let S : Finset A := s.map ea
  have hScard : S.card = k := by simp [S, hs]
  have hsub : (commonRight (fun a : {a // p a} ↦
      fun b : {b // q b} ↦ r a b) s).map eb ⊆ commonRight r S := by
    intro b hb
    simp only [Finset.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    simp only [commonRight, Finset.mem_filter, Finset.mem_univ, true_and] at hb' ⊢
    intro a ha
    simp only [S, Finset.mem_map] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    exact hb' a' ha'
  calc
    (commonRight (fun a : {a // p a} ↦
      fun b : {b // q b} ↦ r a b) s).card =
        ((commonRight (fun a : {a // p a} ↦
          fun b : {b // q b} ↦ r a b) s).map eb).card := by simp
    _ ≤ (commonRight r S).card := Finset.card_le_card hsub
    _ < k := hfree S hScard

omit [Fintype A] in
/-- `K_{k,k}`-freeness is inherited by deleting edges. -/
theorem IsBipartiteKFree.mono {r r' : A → B → Prop}
    [DecidableRel r] [DecidableRel r'] {k : ℕ}
    (hfree : IsBipartiteKFree r k) (hsub : ∀ a b, r' a b → r a b) :
    IsBipartiteKFree r' k := by
  intro s hs
  exact lt_of_le_of_lt (Finset.card_le_card (by
    intro b hb
    simp only [commonRight, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact fun a ha ↦ hsub a b (hb a ha))) (hfree s hs)

/-- The exact double count underlying the bipartite Kővári–Sós–Turán estimate. -/
theorem sum_choose_leftNeighbors_eq_sum_commonRight
    (r : A → B → Prop) [DecidableRel r] (k : ℕ) :
    ∑ b : B, (leftNeighbors r b).card.choose k =
      ∑ s ∈ (Finset.univ : Finset A).powersetCard k, (commonRight r s).card := by
  classical
  let q : Finset A → B → Prop := fun s b ↦ ∀ a ∈ s, r a b
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (Finset.univ : Finset A).powersetCard k)
    (t := (Finset.univ : Finset B)) (r := q)
  symm
  calc
    ∑ s ∈ (Finset.univ : Finset A).powersetCard k, (commonRight r s).card =
        ∑ s ∈ (Finset.univ : Finset A).powersetCard k,
          ((Finset.univ : Finset B).bipartiteAbove q s).card := by
            apply Finset.sum_congr rfl
            intro s hs
            congr 1
            ext b
            simp [commonRight, q]
    _ = ∑ b ∈ (Finset.univ : Finset B),
          (((Finset.univ : Finset A).powersetCard k).bipartiteBelow q b).card := h
    _ = ∑ b : B, (leftNeighbors r b).card.choose k := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Finset.card_powersetCard]
      congr 1
      ext s
      simp only [Finset.mem_bipartiteBelow, Finset.mem_powersetCard, q, leftNeighbors]
      constructor
      · rintro ⟨⟨hs, hk⟩, hrs⟩
        exact ⟨fun a ha ↦ by simpa [leftNeighbors] using hrs a ha, hk⟩
      · rintro ⟨hs, hk⟩
        exact ⟨⟨Finset.subset_univ s, hk⟩,
          fun a ha ↦ by simpa [leftNeighbors] using hs ha⟩

/-- Integer Kővári–Sós–Turán count.  This is the precise combinatorial part of
Janzer--Sudakov, Lemma 3.1; all estimates involving roots are deliberately kept out
of this lemma. -/
theorem sum_choose_leftNeighbors_le_of_isBipartiteKFree
    (r : A → B → Prop) [DecidableRel r] {k : ℕ} (hk : 0 < k)
    (hfree : IsBipartiteKFree r k) :
    ∑ b : B, (leftNeighbors r b).card.choose k ≤
      (k - 1) * (Fintype.card A).choose k := by
  rw [sum_choose_leftNeighbors_eq_sum_commonRight]
  calc
    ∑ s ∈ (Finset.univ : Finset A).powersetCard k, (commonRight r s).card ≤
        ∑ _s ∈ (Finset.univ : Finset A).powersetCard k, (k - 1) := by
          apply Finset.sum_le_sum
          intro s hs
          have hlt := hfree s (Finset.mem_powersetCard.mp hs).2
          omega
    _ = (k - 1) * (Fintype.card A).choose k := by
      simp [mul_comm]

/-- If the numerical part of the KST argument supplies `k * choose |A| k`
incidences, then a copy of `K_{k,k}` exists. -/
theorem exists_complete_bipartite_of_mul_choose_le_sum
    (r : A → B → Prop) [DecidableRel r] {k : ℕ} (hk : 0 < k)
    (hkA : k ≤ Fintype.card A)
    (hcount : k * (Fintype.card A).choose k ≤
      ∑ b : B, (leftNeighbors r b).card.choose k) :
    ∃ s : Finset A, s.card = k ∧ k ≤ (commonRight r s).card := by
  by_contra h
  have hfree : IsBipartiteKFree r k := by
    intro s hs
    have hnle : ¬ k ≤ (commonRight r s).card := by
      intro hle
      exact h ⟨s, hs, hle⟩
    omega
  have hu := sum_choose_leftNeighbors_le_of_isBipartiteKFree r hk hfree
  have hchoose : 0 < (Fintype.card A).choose k := Nat.choose_pos hkA
  have hstrict : (k - 1) * (Fintype.card A).choose k <
      k * (Fintype.card A).choose k := by
    calc
      (k - 1) * (Fintype.card A).choose k <
          (k - 1) * (Fintype.card A).choose k + (Fintype.card A).choose k :=
        Nat.lt_add_of_pos_right hchoose
      _ = (k - 1 + 1) * (Fintype.card A).choose k := by
        rw [add_mul, one_mul]
      _ = k * (Fintype.card A).choose k := by rw [Nat.sub_add_cancel hk]
  exact (Nat.not_lt_of_ge (hcount.trans hu)) hstrict

/-- Lemma 3.1 with its purely numerical Jensen/power estimate exposed as an
integer hypothesis.  This formulation has no floor or real-root convention. -/
theorem kst_edge_bound_of_incidence_lower_bound
    (r : A → B → Prop) [DecidableRel r] {k : ℕ} (hk : 0 < k)
    (hkA : k ≤ Fintype.card A) (hfree : IsBipartiteKFree r k)
    (hincidence : k * Fintype.card B < bipartiteEdgeCount r →
      k * (Fintype.card A).choose k ≤
        ∑ b : B, (leftNeighbors r b).card.choose k) :
    bipartiteEdgeCount r ≤ k * Fintype.card B := by
  by_contra hle
  have hlt : k * Fintype.card B < bipartiteEdgeCount r := Nat.lt_of_not_ge hle
  obtain ⟨s, hs, hcommon⟩ :=
    exists_complete_bipartite_of_mul_choose_le_sum r hk hkA (hincidence hlt)
  exact (Nat.not_lt_of_ge hcommon) (hfree s hs)

/-- Integer degree threshold of order `m^(1-1/k)`.  Its definition uses only
natural powers: `Nat.nthRoot k x + 1` is a strict integral ceiling for the
`k`-th root of `x`. -/
def kstDegreeThreshold (k m : ℕ) : ℕ :=
  k * (Nat.nthRoot k (k * m ^ (k - 1)) + 1)

/-- The power inequality certified by `kstDegreeThreshold`. -/
theorem kstDegreeThreshold_pow_bound {k m t : ℕ} (hk : 0 < k) (htm : t ≤ m) :
    k ^ (k + 1) * t ^ (k - 1) ≤ (kstDegreeThreshold k m) ^ k := by
  let q := Nat.nthRoot k (k * m ^ (k - 1)) + 1
  have hroot : k * m ^ (k - 1) ≤ q ^ k :=
    (Nat.lt_pow_nthRoot_add_one hk.ne' (k * m ^ (k - 1))).le
  have htpow : t ^ (k - 1) ≤ m ^ (k - 1) := Nat.pow_le_pow_left htm _
  calc
    k ^ (k + 1) * t ^ (k - 1) ≤ k ^ (k + 1) * m ^ (k - 1) :=
      Nat.mul_le_mul_left _ htpow
    _ = k ^ k * (k * m ^ (k - 1)) := by rw [pow_succ]; ac_rfl
    _ ≤ k ^ k * q ^ k := Nat.mul_le_mul_left _ hroot
    _ = (k * q) ^ k := by rw [mul_pow]
    _ = (kstDegreeThreshold k m) ^ k := by rfl

/-- Elementary lower bound for the real extension of a binomial coefficient. -/
theorem pow_div_factorial_le_descPochhammer {k : ℕ} (hk : 0 < k)
    {x : ℝ} (hx : (k : ℝ) ≤ x) :
    (x / (k : ℝ)) ^ k / (k.factorial : ℝ) ≤
      (descPochhammer ℝ k).eval x / (k.factorial : ℝ) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [descPochhammer_eval_eq_prod_range]
  have hp : (∏ _i ∈ Finset.range k, (x / (k : ℝ))) =
      (x / (k : ℝ)) ^ k := by rw [div_pow]; simp
  rw [← hp]
  apply Finset.prod_le_prod
  · intro i hi
    exact div_nonneg (le_trans (by positivity) hx) (by positivity)
  · intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hiR' : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
    have hiR : (i : ℝ) ≤ (k : ℝ) - 1 := by linarith
    have hA : 0 ≤ ((k : ℝ) - 1) * (x - k) :=
      mul_nonneg (by linarith) (by linarith)
    have hB : 0 ≤ (k : ℝ) * (((k : ℝ) - 1) - i) :=
      mul_nonneg (by positivity) (by linarith)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k)).2
    nlinarith

/-- The numerical Jensen step in KST, with all root comparisons replaced by
an inequality between natural powers. -/
theorem sum_choose_ge_of_min_sum_and_pow
    {I : Type*} [Fintype I] (p : I → ℕ) {k D a : ℕ}
    (hk : 0 < k) (hb : 0 < Fintype.card I)
    (hsum : k * Fintype.card I < ∑ i, p i)
    (haD : a * D ≤ ∑ i, p i)
    (hD : k ^ (k + 1) * Fintype.card I ^ (k - 1) ≤ D ^ k) :
    k * a.choose k ≤ ∑ i, (p i).choose k := by
  let b : ℕ := Fintype.card I
  let e : ℕ := ∑ i, p i
  let S : ℕ := ∑ i, (p i).choose k
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hfacR : (0 : ℝ) < k.factorial := by positivity
  let w : I → ℝ := fun _ ↦ (b : ℝ)⁻¹
  have hw0 : ∀ i ∈ (Finset.univ : Finset I), 0 ≤ w i := by
    intro i hi
    positivity
  have hw1 : ∑ i ∈ (Finset.univ : Finset I), w i = 1 := by
    simp [w, b, hb.ne']
  have havg : ∑ i ∈ (Finset.univ : Finset I), w i * p i = (e : ℝ) / b := by
    simp only [w]
    rw [← Finset.mul_sum]
    simp [e, b, div_eq_inv_mul]
  have hx : (k : ℝ) < (e : ℝ) / b := by
    rw [lt_div_iff₀ hbR]
    exact_mod_cast hsum
  have hkm1 : (k : ℝ) - 1 ≤ (e : ℝ) / b := by linarith
  have hj := descPochhammer_eval_div_factorial_le_sum_choose
    (n := k) hk.ne' p w hw0 hw1 (by simpa [havg] using hkm1)
  rw [havg] at hj
  have hj' :
      (descPochhammer ℝ k).eval ((e : ℝ) / b) / k.factorial ≤ (S : ℝ) / b := by
    calc
      _ ≤ ∑ i ∈ (Finset.univ : Finset I), w i * (p i).choose k := hj
      _ = (S : ℝ) / b := by
        simp [w, S, b, div_eq_inv_mul, ← Finset.mul_sum]
  have hpoch : (((e : ℝ) / b) / k) ^ k / k.factorial ≤ (S : ℝ) / b :=
    (pow_div_factorial_le_descPochhammer hk hx.le).trans hj'
  let c : ℝ := (k : ℝ) ^ k * (b : ℝ) ^ (k - 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hbpow : (b : ℝ) ^ k = (b : ℝ) ^ (k - 1) * b := by
    nth_rewrite 1 [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  have hfrac : (e : ℝ) ^ k / (c * k.factorial) ≤ (S : ℝ) := by
    calc
      (e : ℝ) ^ k / (c * k.factorial) =
          (b : ℝ) * ((((e : ℝ) / b) / k) ^ k / k.factorial) := by
            dsimp [c]
            rw [div_pow, div_pow]
            field_simp
            rw [hbpow]
            ring
      _ ≤ (b : ℝ) * ((S : ℝ) / b) := by gcongr
      _ = (S : ℝ) := by field_simp
  have hfund : (e : ℝ) ^ k ≤ (S : ℝ) * (c * k.factorial) :=
    (div_le_iff₀ (mul_pos hc hfacR)).mp hfrac
  have hchoose0 : (a.choose k : ℝ) ≤ (a : ℝ) ^ k / k.factorial :=
    Nat.choose_le_pow_div k a
  have hchoose : (a.choose k : ℝ) * k.factorial ≤ (a : ℝ) ^ k :=
    (le_div_iff₀ hfacR).mp hchoose0
  have hDR : (k : ℝ) * c ≤ (D : ℝ) ^ k := by
    have hDcast :
        ((k ^ (k + 1) * Fintype.card I ^ (k - 1) : ℕ) : ℝ) ≤
          (D ^ k : ℕ) := by exact_mod_cast hD
    norm_num only [Nat.cast_mul, Nat.cast_pow] at hDcast
    simpa only [c, b, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hDcast
  have haDR : (a : ℝ) * D ≤ e := by exact_mod_cast haD
  have haDpow : ((a : ℝ) * D) ^ k ≤ (e : ℝ) ^ k := by gcongr
  have hq : 0 < c * (k.factorial : ℝ) := mul_pos hc hfacR
  have hgoalR : (k : ℝ) * a.choose k ≤ S := by
    rw [← mul_le_mul_iff_right₀ hq]
    calc
      (c * k.factorial) * ((k : ℝ) * a.choose k) =
          ((k : ℝ) * c) * ((a.choose k : ℝ) * k.factorial) := by ring
      _ ≤ ((k : ℝ) * c) * (a : ℝ) ^ k := by gcongr
      _ ≤ (D : ℝ) ^ k * (a : ℝ) ^ k := by gcongr
      _ = ((a : ℝ) * D) ^ k := by ring
      _ ≤ (e : ℝ) ^ k := haDpow
      _ ≤ (c * k.factorial) * (S : ℝ) := by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hfund
  exact_mod_cast hgoalR

/-- Root-free Kővári–Sós–Turán local bound with the exact `k |B|`
conclusion used in Janzer--Sudakov Lemma 3.2. -/
theorem kst_edge_bound_of_minDegree_pow
    (r : A → B → Prop) [DecidableRel r] {k D : ℕ}
    (hk : 0 < k) (hfree : IsBipartiteKFree r k)
    (hmin : ∀ a : A, D ≤ (rightNeighbors r a).card)
    (hD : k ^ (k + 1) * Fintype.card B ^ (k - 1) ≤ D ^ k) :
    bipartiteEdgeCount r ≤ k * Fintype.card B := by
  by_cases hb : Fintype.card B = 0
  · have hzero : ∀ a : A, (rightNeighbors r a).card = 0 := by
      intro a
      apply Nat.eq_zero_of_le_zero
      have hle := Finset.card_le_card (Finset.subset_univ (rightNeighbors r a))
      simpa [hb] using hle
    simp [bipartiteEdgeCount, hzero, hb]
  by_cases hkA : k ≤ Fintype.card A
  · by_contra hbound
    have hsum : k * Fintype.card B < bipartiteEdgeCount r := Nat.lt_of_not_ge hbound
    have haD : Fintype.card A * D ≤ bipartiteEdgeCount r := by
      calc
        Fintype.card A * D = ∑ _a : A, D := by simp [mul_comm]
        _ ≤ ∑ a : A, (rightNeighbors r a).card :=
          Finset.sum_le_sum fun a _ ↦ hmin a
        _ = bipartiteEdgeCount r := rfl
    have hcount : k * (Fintype.card A).choose k ≤
        ∑ b : B, (leftNeighbors r b).card.choose k := by
      apply sum_choose_ge_of_min_sum_and_pow
          (p := fun b ↦ (leftNeighbors r b).card) hk (Nat.pos_of_ne_zero hb)
      · simpa [bipartiteEdgeCount_eq_sum_left] using hsum
      · simpa [bipartiteEdgeCount_eq_sum_left] using haD
      · exact hD
    obtain ⟨s, hs, hcommon⟩ :=
      exists_complete_bipartite_of_mul_choose_le_sum r hk hkA hcount
    exact (Nat.not_lt_of_ge hcommon) (hfree s hs)
  · have hcard : Fintype.card A ≤ k := by omega
    calc
      bipartiteEdgeCount r ≤ ∑ _a : A, Fintype.card B := by
        unfold bipartiteEdgeCount
        exact Finset.sum_le_sum fun a _ ↦
          Finset.card_le_card (Finset.subset_univ (rightNeighbors r a))
      _ = Fintype.card A * Fintype.card B := by simp
      _ ≤ k * Fintype.card B := Nat.mul_le_mul_right _ hcard

end Count

namespace CodegreeCleaning

variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

/-- A finite bipartite relation, with an explicitly ordered left class. -/
abbrev EdgeSet (n : ℕ) (B : Type*) := Finset (Fin n × B)

/-- The bipartite relation represented by an ordered edge set. -/
abbrev edgeRel (E : EdgeSet n B) (a : Fin n) (b : B) : Prop := (a, b) ∈ E

/-- Degree of the left vertex whose index is `i` (zero outside `Fin n`). -/
def rowCard (E : EdgeSet n B) (i : ℕ) : ℕ :=
  (E.filter fun e ↦ e.1.val = i).card

theorem rowCard_eq_rightNeighbors (E : EdgeSet n B) (u : Fin n) :
    rowCard E u.val = (rightNeighbors (edgeRel E) u).card := by
  classical
  let L := E.filter fun e ↦ e.1.val = u.val
  let R := (Finset.univ : Finset B).filter fun b ↦ (u, b) ∈ E
  let f : {e // e ∈ L} → {b // b ∈ R} := fun e ↦ ⟨e.1.2, by
    have he := Finset.mem_filter.mp e.2
    have hfst : e.1.1 = u := Fin.ext he.2
    have hpair : e.1 = (u, e.1.2) := Prod.ext hfst rfl
    have hemem : (u, e.1.2) ∈ E := by rw [← hpair]; exact he.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hemem⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e e' heq
      apply Subtype.ext
      apply Prod.ext
      · have he := (Finset.mem_filter.mp e.2).2
        have he' := (Finset.mem_filter.mp e'.2).2
        exact Fin.ext (he.trans he'.symm)
      · exact congrArg Subtype.val heq
    · intro b
      refine ⟨⟨(u, b.1), ?_⟩, ?_⟩
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp b.2).2, rfl⟩
      · apply Subtype.ext
        rfl
  change L.card = R.card
  simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.ofBijective f hf)

/-- Common-neighbour count of two left vertices. -/
def pairCodegree (E : EdgeSet n B) (u v : Fin n) : ℕ :=
  ((Finset.univ : Finset B).filter fun b ↦ (u, b) ∈ E ∧ (v, b) ∈ E).card

/-- One cleaning step at `u`: for every later `v` of codegree greater than
`D`, erase all edges from `v` into the current neighbourhood of `u`. -/
def eraseBadAt (E : EdgeSet n B) (D : ℕ) (u : Fin n) : EdgeSet n B :=
  E.filter fun e ↦
    ¬ (u.val < e.1.val ∧ D < pairCodegree E u e.1 ∧ (u, e.2) ∈ E)

/-- The edge set after the first `i` cleaning stages. -/
def cleanSeq (E : EdgeSet n B) (D : ℕ) : ℕ → EdgeSet n B
  | 0 => E
  | i + 1 =>
      if hi : i < n then eraseBadAt (cleanSeq E D i) D ⟨i, hi⟩
      else cleanSeq E D i

/-- The output of the sequential cleaning algorithm. -/
def cleaned (E : EdgeSet n B) (D : ℕ) : EdgeSet n B := cleanSeq E D n

theorem eraseBadAt_subset (E : EdgeSet n B) (D : ℕ) (u : Fin n) :
    eraseBadAt E D u ⊆ E := by
  intro e he
  exact (Finset.mem_filter.mp he).1

theorem cleanSeq_succ_subset (E : EdgeSet n B) (D i : ℕ) :
    cleanSeq E D (i + 1) ⊆ cleanSeq E D i := by
  rw [cleanSeq]
  split
  · exact eraseBadAt_subset _ _ _
  · exact Finset.Subset.rfl

theorem cleanSeq_antitone (E : EdgeSet n B) (D : ℕ) {i j : ℕ} (hij : i ≤ j) :
    cleanSeq E D j ⊆ cleanSeq E D i := by
  induction j with
  | zero =>
      have : i = 0 := Nat.eq_zero_of_le_zero hij
      subst i
      exact Finset.Subset.rfl
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hij'
      · exact Finset.Subset.rfl
      · exact (cleanSeq_succ_subset E D j).trans (ih (Nat.le_of_lt_succ hij'))

theorem pairCodegree_mono {E F : EdgeSet n B} (hEF : E ⊆ F) (u v : Fin n) :
    pairCodegree E u v ≤ pairCodegree F u v := by
  apply Finset.card_le_card
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  exact ⟨hEF hb.1, hEF hb.2⟩

theorem pairCodegree_comm (E : EdgeSet n B) (u v : Fin n) :
    pairCodegree E u v = pairCodegree E v u := by
  unfold pairCodegree
  congr 1
  ext b
  simp [and_comm]

theorem eraseBadAt_codegree_le (E : EdgeSet n B) (D : ℕ) (u v : Fin n)
    (huv : u.val < v.val) :
    pairCodegree (eraseBadAt E D u) u v ≤ D := by
  by_cases hbad : D < pairCodegree E u v
  · have hz : pairCodegree (eraseBadAt E D u) u v = 0 := by
      unfold pairCodegree
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rcases hb with ⟨hub, hvb⟩
      have huE := (Finset.mem_filter.mp hub).1
      have hvkeep := (Finset.mem_filter.mp hvb).2
      exact hvkeep ⟨huv, hbad, huE⟩
    simp [hz]
  · exact (pairCodegree_mono (eraseBadAt_subset E D u) u v).trans
      (Nat.le_of_not_gt hbad)

theorem rowCard_eraseBadAt_of_le (E : EdgeSet n B) (D : ℕ) (u : Fin n) (i : ℕ)
    (hiu : i ≤ u.val) :
    rowCard (eraseBadAt E D u) i = rowCard E i := by
  apply congrArg Finset.card
  ext e
  simp only [eraseBadAt, Finset.mem_filter]
  constructor
  · rintro ⟨⟨he, -⟩, hei⟩
    exact ⟨he, hei⟩
  · rintro ⟨he, hei⟩
    refine ⟨⟨he, ?_⟩, hei⟩
    rintro ⟨hue, -⟩
    omega

theorem rowCard_cleanSeq_succ_of_le (E : EdgeSet n B) (D i t : ℕ) (hit : i ≤ t) :
    rowCard (cleanSeq E D (t + 1)) i = rowCard (cleanSeq E D t) i := by
  rw [cleanSeq]
  split
  next ht => exact rowCard_eraseBadAt_of_le _ _ ⟨t, ht⟩ i hit
  next => rfl

theorem rowCard_cleanSeq_stable (E : EdgeSet n B) (D : ℕ) {i t : ℕ} (hit : i ≤ t) :
    rowCard (cleanSeq E D i) i = rowCard (cleanSeq E D t) i := by
  induction t with
  | zero =>
      have : i = 0 := Nat.eq_zero_of_le_zero hit
      subst i
      rfl
  | succ t ih =>
      rcases Nat.eq_or_lt_of_le hit with rfl | hit'
      · rfl
      · calc
          rowCard (cleanSeq E D i) i = rowCard (cleanSeq E D t) i :=
            ih (Nat.le_of_lt_succ hit')
          _ = rowCard (cleanSeq E D (t + 1)) i :=
            (rowCard_cleanSeq_succ_of_le E D i t (Nat.le_of_lt_succ hit')).symm

omit [Fintype B] [DecidableEq B] in
theorem card_eq_sum_rowCard (E : EdgeSet n B) :
    E.card = ∑ i ∈ Finset.range n, rowCard E i := by
  simpa only [rowCard] using
    (Finset.card_eq_sum_card_fiberwise (s := E) (t := Finset.range n)
      (f := fun e : Fin n × B ↦ e.1.val) (by
        intro e he
        simpa only [Finset.mem_coe, Finset.mem_range] using e.1.isLt))

/-- If stage `i` erases at most `k` times the current pivot degree, then the
original edge count is at most `k+1` times the final edge count. -/
theorem card_le_succ_mul_card_cleaned (E : EdgeSet n B) (D k : ℕ)
    (hstep : ∀ i (_hi : i < n),
      ((cleanSeq E D i) \ cleanSeq E D (i + 1)).card ≤
        k * rowCard (cleanSeq E D i) i) :
    E.card ≤ (k + 1) * (cleaned E D).card := by
  have aux : ∀ t, t ≤ n →
      E.card ≤ (cleanSeq E D t).card +
        k * ∑ i ∈ Finset.range t, rowCard (cleaned E D) i := by
    intro t ht
    induction t with
    | zero => simp [cleanSeq]
    | succ t ih =>
        have htn : t < n := by omega
        have hsub := cleanSeq_succ_subset E D t
        have hsplit := Finset.card_sdiff_add_card_eq_card hsub
        have hdel := hstep t htn
        have hpivot : rowCard (cleanSeq E D t) t = rowCard (cleaned E D) t := by
          exact rowCard_cleanSeq_stable E D (Nat.le_of_lt htn)
        have hprev := ih (by omega)
        rw [Finset.sum_range_succ, Nat.mul_add]
        calc
          E.card ≤ (cleanSeq E D t).card +
              k * ∑ i ∈ Finset.range t, rowCard (cleaned E D) i := hprev
          _ = ((cleanSeq E D t) \ cleanSeq E D (t + 1)).card +
                (cleanSeq E D (t + 1)).card +
                k * ∑ i ∈ Finset.range t, rowCard (cleaned E D) i := by omega
          _ ≤ k * rowCard (cleanSeq E D t) t +
                (cleanSeq E D (t + 1)).card +
                k * ∑ i ∈ Finset.range t, rowCard (cleaned E D) i := by omega
          _ = (cleanSeq E D (t + 1)).card +
                (k * ∑ i ∈ Finset.range t, rowCard (cleaned E D) i +
                  k * rowCard (cleaned E D) t) := by rw [hpivot]; omega
  have h := aux n le_rfl
  rw [← card_eq_sum_rowCard (cleaned E D)] at h
  simpa [cleaned, Nat.add_mul, Nat.add_comm] using h

/-- Janzer--Sudakov Lemma 3.2, with its Lemma 3.1 application represented by
the exact per-stage deletion estimate `hstep`. -/
theorem sequential_codegree_cleaning (E : EdgeSet n B) (D k : ℕ)
    (hstep : ∀ i (_hi : i < n),
      ((cleanSeq E D i) \ cleanSeq E D (i + 1)).card ≤
        k * rowCard (cleanSeq E D i) i) :
    ∃ E' : EdgeSet n B,
      E' ⊆ E ∧
      E.card ≤ (k + 1) * E'.card ∧
      ∀ u v : Fin n, u ≠ v → pairCodegree E' u v ≤ D := by
  refine ⟨cleaned E D, ?_, card_le_succ_mul_card_cleaned E D k hstep, ?_⟩
  · exact cleanSeq_antitone E D (Nat.zero_le n)
  · intro u v huv
    rcases lt_or_gt_of_ne huv with huv' | hvu'
    · have hstage := eraseBadAt_codegree_le (cleanSeq E D u.val) D u v huv'
      have hfinal := pairCodegree_mono
        (cleanSeq_antitone E D (Nat.succ_le_iff.mpr u.isLt)) u v
      exact hfinal.trans (by simpa [cleanSeq, u.isLt] using hstage)
    · rw [pairCodegree_comm]
      have hstage := eraseBadAt_codegree_le (cleanSeq E D v.val) D v u hvu'
      have hfinal := pairCodegree_mono
        (cleanSeq_antitone E D (Nat.succ_le_iff.mpr v.isLt)) v u
      exact hfinal.trans (by simpa [cleanSeq, v.isLt] using hstage)

/-- The edge count of a bipartite relation is the cardinality of its graph. -/
theorem bipartiteEdgeCount_eq_card_filter
    {A C : Type*} [Fintype A] [Fintype C]
    (r : A → C → Prop) [DecidableRel r] :
    bipartiteEdgeCount r =
      ((Finset.univ : Finset (A × C)).filter fun e ↦ r e.1 e.2).card := by
  classical
  rw [bipartiteEdgeCount]
  symm
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (A × C)).filter fun e ↦ r e.1 e.2)
    (t := (Finset.univ : Finset A)) (f := Prod.fst)
    (by intro e he; simp)
  rw [h]
  apply Finset.sum_congr rfl
  intro a ha
  let emb : C ↪ A × C := ⟨fun c ↦ (a, c), fun _ _ h ↦ congrArg Prod.snd h⟩
  have heq :
      ((Finset.univ : Finset (A × C)).filter fun e ↦ r e.1 e.2).filter
          (fun e ↦ e.1 = a) =
        (rightNeighbors r a).map emb := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      rightNeighbors, emb]
    constructor
    · rintro ⟨hre, hea⟩
      have heq : (a, e.2) = e := Prod.ext hea.symm rfl
      rw [hea] at hre
      exact ⟨e.2, hre, heq⟩
    · rintro ⟨c, hrc, rfl⟩
      exact ⟨hrc, rfl⟩
  rw [heq]
  simp

/-- Edges erased at a pivot inject into the restricted original bipartite
relation between bad later rows and the pivot's current neighbours. -/
theorem erased_card_le_restricted_original
    (E F : EdgeSet n B) (hFE : F ⊆ E) (D : ℕ) (u : Fin n) :
    let P : Fin n → Prop := fun v ↦
      u.val < v.val ∧ D < pairCodegree F u v
    let Q : B → Prop := fun b ↦ (u, b) ∈ F
    let r : {v // P v} → {b // Q b} → Prop := fun v b ↦ (v.1, b.1) ∈ E
    (F \ eraseBadAt F D u).card ≤ bipartiteEdgeCount r := by
  classical
  dsimp only
  let P : Fin n → Prop := fun v ↦ u.val < v.val ∧ D < pairCodegree F u v
  let Q : B → Prop := fun b ↦ (u, b) ∈ F
  let del := F \ eraseBadAt F D u
  let r : {v // P v} → {b // Q b} → Prop := fun v b ↦ (v.1, b.1) ∈ E
  have hcond (e : Fin n × B) (he : e ∈ del) :
      u.val < e.1.val ∧ D < pairCodegree F u e.1 ∧ (u, e.2) ∈ F := by
    have he' := Finset.mem_sdiff.mp he
    refine Classical.byContradiction fun hn ↦ he'.2 ?_
    simp only [eraseBadAt, Finset.mem_filter]
    exact ⟨he'.1, hn⟩
  let emb : {e // e ∈ del} ↪ ({v // P v} × {b // Q b}) :=
    ⟨fun e ↦
      (⟨e.1.1, (hcond e.1 e.2).1, (hcond e.1 e.2).2.1⟩,
       ⟨e.1.2, (hcond e.1 e.2).2.2⟩),
     by
       intro a b hab
       apply Subtype.ext
       apply Prod.ext
       · exact congrArg (fun z ↦ z.1.1) hab
       · exact congrArg (fun z ↦ z.2.1) hab⟩
  let T : Finset ({v // P v} × {b // Q b}) :=
    Finset.univ.filter fun z ↦ r z.1 z.2
  have hsub : del.attach.map emb ⊆ T := by
    intro z hz
    simp only [Finset.mem_map] at hz
    obtain ⟨e, he, rfl⟩ := hz
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, r, emb]
    exact hFE (Finset.mem_sdiff.mp e.2).1
  calc
    (F \ eraseBadAt F D u).card = del.card := rfl
    _ = del.attach.card := by simp
    _ = (del.attach.map emb).card := by simp
    _ ≤ T.card := Finset.card_le_card hsub
    _ = bipartiteEdgeCount r := (bipartiteEdgeCount_eq_card_filter r).symm

theorem card_pivot_subtype (F : EdgeSet n B) (u : Fin n) :
    Fintype.card {b : B // (u, b) ∈ F} = rowCard F u.val := by
  rw [rowCard_eq_rightNeighbors]
  rw [Fintype.card_subtype]
  rfl

/-- The exact Kővári--Sós--Turán estimate bounds the number of edges erased
at one stage by `k` times the pivot degree. -/
theorem eraseBadAt_card_le_mul_rowCard
    (E F : EdgeSet n B) (hFE : F ⊆ E) {k m : ℕ} (hk : 0 < k)
    (hfree : IsBipartiteKFree (edgeRel E) k)
    (hmax : ∀ v : Fin n, rowCard E v.val ≤ m) (u : Fin n) :
    (F \ eraseBadAt F (kstDegreeThreshold k m - 1) u).card ≤
      k * rowCard F u.val := by
  classical
  let D := kstDegreeThreshold k m - 1
  let P : Fin n → Prop := fun v ↦ u.val < v.val ∧ D < pairCodegree F u v
  let Q : B → Prop := fun b ↦ (u, b) ∈ F
  let r : {v // P v} → {b // Q b} → Prop := fun v b ↦ (v.1, b.1) ∈ E
  have hfree_r : IsBipartiteKFree r k := by
    simpa only [r, edgeRel] using
      (IsBipartiteKFree.restrict (A := Fin n) (B := B) (edgeRel E) hfree P Q)
  have hthreshold_pos : 0 < kstDegreeThreshold k m := by
    unfold kstDegreeThreshold
    exact Nat.mul_pos hk (Nat.succ_pos _)
  have hmin : ∀ a : {v // P v},
      kstDegreeThreshold k m ≤ (rightNeighbors r a).card := by
    intro a
    have hcodeg : kstDegreeThreshold k m ≤ pairCodegree F u a.1 := by
      have ha := a.2.2
      dsimp only [D] at ha
      omega
    let valEmb : {b // Q b} ↪ B := ⟨Subtype.val, Subtype.val_injective⟩
    let target : Finset B :=
      Finset.univ.filter fun b ↦ (u, b) ∈ F ∧ (a.1, b) ∈ E
    have hsub :
        ((Finset.univ : Finset B).filter fun b ↦
          (u, b) ∈ F ∧ (a.1, b) ∈ F) ⊆ target := by
      intro b hb
      simp only [target, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact ⟨hb.1, hFE hb.2⟩
    have heq : (rightNeighbors r a).map valEmb = target := by
      ext b
      simp only [Finset.mem_map, rightNeighbors, Finset.mem_filter, Finset.mem_univ,
        true_and, valEmb, target, r, Q]
      constructor
      · rintro ⟨b', hb', rfl⟩
        exact ⟨b'.2, hb'⟩
      · rintro ⟨hub, hab⟩
        exact ⟨⟨b, hub⟩, hab, rfl⟩
    exact hcodeg.trans <| calc
      pairCodegree F u a.1 ≤ target.card := Finset.card_le_card hsub
      _ = (rightNeighbors r a).card := by rw [← heq]; simp
  have hrowmono : rowCard F u.val ≤ rowCard E u.val := by
    unfold rowCard
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨hFE he.1, he.2⟩
  have hQm : Fintype.card {b // Q b} ≤ m := by
    change Fintype.card {b : B // (u, b) ∈ F} ≤ m
    rw [card_pivot_subtype]
    exact hrowmono.trans (hmax u)
  have hkst : bipartiteEdgeCount r ≤ k * Fintype.card {b // Q b} :=
    kst_edge_bound_of_minDegree_pow r hk hfree_r hmin
      (kstDegreeThreshold_pow_bound hk hQm)
  calc
    (F \ eraseBadAt F (kstDegreeThreshold k m - 1) u).card ≤
        bipartiteEdgeCount r := by
      simpa only [D, P, Q, r] using
        (erased_card_le_restricted_original E F hFE D u)
    _ ≤ k * Fintype.card {b // Q b} := hkst
    _ = k * rowCard F u.val := by
      congr 1
      exact card_pivot_subtype F u

/-- Janzer--Sudakov Lemma 3.2 in an exact, root-free integer form. -/
theorem sequential_codegree_cleaning_of_kst
    (E : EdgeSet n B) {k m : ℕ} (hk : 0 < k)
    (hfree : IsBipartiteKFree (edgeRel E) k)
    (hmax : ∀ v : Fin n, rowCard E v.val ≤ m) :
    ∃ E' : EdgeSet n B,
      E' ⊆ E ∧
      E.card ≤ (k + 1) * E'.card ∧
      ∀ u v : Fin n, u ≠ v →
        pairCodegree E' u v ≤ kstDegreeThreshold k m - 1 := by
  apply sequential_codegree_cleaning
  intro i hi
  let F := cleanSeq E (kstDegreeThreshold k m - 1) i
  have hFE : F ⊆ E := cleanSeq_antitone E _ (Nat.zero_le i)
  have hstage := eraseBadAt_card_le_mul_rowCard E F hFE hk hfree hmax ⟨i, hi⟩
  simpa only [F, cleanSeq, hi, ↓reduceDIte] using hstage

end CodegreeCleaning

end Erdos182
