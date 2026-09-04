import ErdosProblems.Erdos182.Roof

/-!
# Finite roof regularization

This file turns the Hall-theoretic roof lemma in `Roof.lean` into a genuine
regularization theorem.  If every right degree is `r + d` and every left
degree is at most `D`, one can successively remove `d` roofs.  At every stage
the residual right degree is at least `r + 1`, so double-counting gives a roof
whose left load is at most `D ⌈/⌉ (r + 1)`.  The union of the removed roofs
is right-regular of degree `d`, and its left degrees have the corresponding
linear bound.

The first part isolates this finite, integer-valued roof-removal step.  The
second part formalizes the full multiplicative-block argument from Shirazi's
Lemma 5.3.3: it chooses the residual level by maximizing feasible side ratios,
applies the Hall roof lemma throughout the block, and proves the real
cross-multiplied estimate in equation (9).  A final wrapper transports the
result between explicitly displayed ambient finite parts.
-/

namespace Erdos182

open Finset
open scoped Classical BigOperators

namespace BipartiteGraph

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The numerical multiplicative-block pigeonhole principle used in roof
regularization.  If the endpoint of a positive sequence is at most `β^t`
and its initial value is at least one, some consecutive multiplicative
increment is at most `β`. -/
theorem exists_multiplicative_block (a : ℕ → ℝ) (t : ℕ) (ht : 0 < t)
    (β : ℝ) (hβ : 1 ≤ β) (ha0 : 1 ≤ a 0) (hat : a t ≤ β ^ t) :
    ∃ j < t, a (j + 1) ≤ β * a j := by
  by_contra h
  push_neg at h
  have hβpos : 0 < β := zero_lt_one.trans_le hβ
  have hiter : ∀ j, 0 < j → j ≤ t → β ^ j * a 0 < a j := by
    intro j hj hle
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases hj0 : j = 0
        · subst j
          simpa using h 0 ht
        · have hprev : β ^ j * a 0 < a j := ih (Nat.pos_of_ne_zero hj0) (by omega)
          calc
            β ^ (j + 1) * a 0 = β * (β ^ j * a 0) := by ring
            _ < β * a j := mul_lt_mul_of_pos_left hprev hβpos
            _ < a (j + 1) := h j (by omega)
  have hstrict := hiter t ht le_rfl
  have hpow_nonneg : 0 ≤ β ^ t := pow_nonneg (zero_le_one.trans hβ) t
  have hlower : β ^ t ≤ β ^ t * a 0 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha0 hpow_nonneg
  linarith

/-! ## Active parts and the finite maximum of side ratios -/

/-- The graph induced on two displayed finite parts, with the parts made into
their own finite vertex types. -/
def onParts (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B) :
    BipartiteGraph A₀ B₀ where
  Adj a b := G.Adj a.1 b.1

@[simp]
theorem onParts_adj (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (a : A₀) (b : B₀) : (G.onParts A₀ B₀).Adj a b ↔ G.Adj a.1 b.1 :=
  Iff.rfl

/-- A pair of active parts supports a right-minimum-degree-`s` subgraph of
`G`.  Since unused edges may be trimmed, this is exactly the feasibility
condition for an `s`-half-regular subgraph on the same parts. -/
def IsFeasiblePair (G : BipartiteGraph A B) (s : ℕ)
    (p : Finset A × Finset B) : Prop :=
  p.1.Nonempty ∧ p.2.Nonempty ∧
    ∀ b : p.2, s ≤ (G.onParts p.1 p.2).rightDegree b

/-- The finite set of all feasible pairs of active parts. -/
noncomputable def feasiblePairs (G : BipartiteGraph A B) (s : ℕ) :
    Finset (Finset A × Finset B) :=
  (((Finset.univ : Finset A).powerset).product
    ((Finset.univ : Finset B).powerset)).filter (G.IsFeasiblePair s)

@[simp]
theorem mem_feasiblePairs (G : BipartiteGraph A B) (s : ℕ)
    (p : Finset A × Finset B) :
    p ∈ G.feasiblePairs s ↔ G.IsFeasiblePair s p := by
  classical
  simp [feasiblePairs]

/-- The regular-side/irregular-side ratio of a pair of nonempty parts. -/
noncomputable def partRatio (p : Finset A × Finset B) : ℝ :=
  (p.2.card : ℝ) / (p.1.card : ℝ)

noncomputable def feasibleRatios (G : BipartiteGraph A B) (s : ℕ) : Finset ℝ :=
  (G.feasiblePairs s).image partRatio

/-- Maximum feasible side ratio at minimum right degree `s`, with value zero
when there is no feasible pair. -/
noncomputable def maxFeasibleRatio (G : BipartiteGraph A B) (s : ℕ) : ℝ :=
  if h : (G.feasibleRatios s).Nonempty then (G.feasibleRatios s).max' h else 0

theorem partRatio_le_maxFeasibleRatio {G : BipartiteGraph A B} {s : ℕ}
    {p : Finset A × Finset B} (hp : G.IsFeasiblePair s p) :
    partRatio p ≤ G.maxFeasibleRatio s := by
  classical
  have hmem : partRatio p ∈ G.feasibleRatios s := by
    exact Finset.mem_image.mpr ⟨p, (mem_feasiblePairs G s p).mpr hp, rfl⟩
  have hne : (G.feasibleRatios s).Nonempty := ⟨partRatio p, hmem⟩
  rw [maxFeasibleRatio, dif_pos hne]
  exact Finset.le_max' _ _ hmem

theorem exists_partRatio_eq_maxFeasibleRatio {G : BipartiteGraph A B} {s : ℕ}
    (hne : (G.feasiblePairs s).Nonempty) :
    ∃ p, G.IsFeasiblePair s p ∧ partRatio p = G.maxFeasibleRatio s := by
  classical
  obtain ⟨p, hp⟩ := hne
  have hrat_ne : (G.feasibleRatios s).Nonempty := by
    refine ⟨partRatio p, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  have hmaxmem := Finset.max'_mem (G.feasibleRatios s) hrat_ne
  obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp hmaxmem
  refine ⟨q, (mem_feasiblePairs G s q).mp hq, ?_⟩
  rw [maxFeasibleRatio, dif_pos hrat_ne]
  exact hqeq

theorem IsFeasiblePair.mono_degree {G : BipartiteGraph A B} {s s' : ℕ}
    {p : Finset A × Finset B} (hp : G.IsFeasiblePair s p) (hss : s' ≤ s) :
    G.IsFeasiblePair s' p :=
  ⟨hp.1, hp.2.1, fun b ↦ hss.trans (hp.2.2 b)⟩

theorem maxFeasibleRatio_mono_degree {G : BipartiteGraph A B} {s s' : ℕ}
    (hss : s' ≤ s) (hne : (G.feasiblePairs s).Nonempty) :
    G.maxFeasibleRatio s ≤ G.maxFeasibleRatio s' := by
  obtain ⟨p, hp, heq⟩ := exists_partRatio_eq_maxFeasibleRatio hne
  rw [← heq]
  exact partRatio_le_maxFeasibleRatio (hp.mono_degree hss)

theorem leftDegree_onParts_le (G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (a : A₀) :
    (G.onParts A₀ B₀).leftDegree a ≤ G.leftDegree a.1 := by
  classical
  let P := G.onParts A₀ B₀
  let e : (P.rightNeighbors a) → (G.rightNeighbors a.1) := fun b ↦
    ⟨b.1.1, (mem_rightNeighbors G a.1 b.1.1).mpr
      ((mem_rightNeighbors P a b.1).mp b.2)⟩
  have heinj : Function.Injective e := by
    intro b b' hbb
    apply Subtype.ext
    apply Subtype.ext
    simpa [e] using congrArg Subtype.val hbb
  change (P.rightNeighbors a).card ≤ (G.rightNeighbors a.1).card
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective e heinj

/-- Every positive-degree feasible pair has ratio at most the maximum left
degree.  This is the endpoint estimate in the multiplicative-block proof. -/
theorem partRatio_le_of_maxLeftDegree {G : BipartiteGraph A B} {s D : ℕ}
    {p : Finset A × Finset B} (hs : 0 < s) (hp : G.IsFeasiblePair s p)
    (hmax : ∀ a, G.leftDegree a ≤ D) :
    partRatio p ≤ (D : ℝ) := by
  classical
  let P := G.onParts p.1 p.2
  have hlower : s * p.2.card ≤ P.edgeCount := by
    rw [edgeCount]
    calc
      s * p.2.card = ∑ _b : p.2, s := by simp [Nat.mul_comm]
      _ ≤ ∑ b : p.2, P.rightDegree b := by
        gcongr with b
        exact hp.2.2 b
  have hupper : P.edgeCount ≤ D * p.1.card := by
    rw [edgeCount_eq_sum_leftDegree]
    calc
      ∑ a : p.1, P.leftDegree a ≤ ∑ _a : p.1, D := by
        gcongr with a
        exact (leftDegree_onParts_le G p.1 p.2 a).trans (hmax a.1)
      _ = D * p.1.card := by simp [Nat.mul_comm]
  have hcard : p.2.card ≤ D * p.1.card := by
    calc
      p.2.card = 1 * p.2.card := by simp
      _ ≤ s * p.2.card := Nat.mul_le_mul_right _ hs
      _ ≤ P.edgeCount := hlower
      _ ≤ D * p.1.card := hupper
  have hApos : (0 : ℝ) < p.1.card := by exact_mod_cast hp.1.card_pos
  rw [partRatio, div_le_iff₀ hApos]
  exact_mod_cast hcard

theorem maxFeasibleRatio_le_of_maxLeftDegree {G : BipartiteGraph A B} {s D : ℕ}
    (hs : 0 < s) (hne : (G.feasiblePairs s).Nonempty)
    (hmax : ∀ a, G.leftDegree a ≤ D) :
    G.maxFeasibleRatio s ≤ (D : ℝ) := by
  obtain ⟨p, hp, heq⟩ := exists_partRatio_eq_maxFeasibleRatio hne
  rw [← heq]
  exact partRatio_le_of_maxLeftDegree hs hp hmax

/-- Trim a feasible pair to an exactly half-regular graph on the subtype
vertex sets. -/
noncomputable def trimmedFeasiblePairGraph (G : BipartiteGraph A B) (s : ℕ)
    (p : Finset A × Finset B) (hp : G.IsFeasiblePair s p) :
    BipartiteGraph p.1 p.2 :=
  let P := G.onParts p.1 p.2
  P.trimRightDegree Finset.univ s (fun b _ ↦ hp.2.2 b)

theorem trimmedFeasiblePairGraph_le (G : BipartiteGraph A B) (s : ℕ)
    (p : Finset A × Finset B) (hp : G.IsFeasiblePair s p) :
    G.trimmedFeasiblePairGraph s p hp ≤ G.onParts p.1 p.2 := by
  exact (G.onParts p.1 p.2).trimRightDegree_le Finset.univ s (fun b _ ↦ hp.2.2 b)

theorem rightDegree_trimmedFeasiblePairGraph (G : BipartiteGraph A B) (s : ℕ)
    (p : Finset A × Finset B) (hp : G.IsFeasiblePair s p) (b : p.2) :
    (G.trimmedFeasiblePairGraph s p hp).rightDegree b = s := by
  exact (G.onParts p.1 p.2).rightDegree_trimRightDegree_of_mem
    Finset.univ s (fun b _ ↦ hp.2.2 b) (Finset.mem_univ b)

/-- Extend a graph on subtype parts by zero outside those parts. -/
def extendParts (A₀ : Finset A) (B₀ : Finset B)
    (K : BipartiteGraph A₀ B₀) : BipartiteGraph A B where
  Adj a b := ∃ (ha : a ∈ A₀) (hb : b ∈ B₀), K.Adj ⟨a, ha⟩ ⟨b, hb⟩

@[simp]
theorem extendParts_adj (A₀ : Finset A) (B₀ : Finset B)
    (K : BipartiteGraph A₀ B₀) (a : A) (b : B) :
    (extendParts A₀ B₀ K).Adj a b ↔
      ∃ (ha : a ∈ A₀) (hb : b ∈ B₀), K.Adj ⟨a, ha⟩ ⟨b, hb⟩ :=
  Iff.rfl

theorem extendParts_le {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B}
    {K : BipartiteGraph A₀ B₀} (hK : K ≤ G.onParts A₀ B₀) :
    extendParts A₀ B₀ K ≤ G := by
  intro a b hab
  obtain ⟨ha, hb, hab⟩ := hab
  exact hK hab

theorem extendParts_supportedOn (A₀ : Finset A) (B₀ : Finset B)
    (K : BipartiteGraph A₀ B₀) :
    (extendParts A₀ B₀ K).SupportedOn A₀ B₀ := by
  rintro a b ⟨ha, hb, _⟩
  exact ⟨ha, hb⟩

theorem rightDegree_extendParts_of_mem (A₀ : Finset A) (B₀ : Finset B)
    (K : BipartiteGraph A₀ B₀) {b : B} (hb : b ∈ B₀) :
    (extendParts A₀ B₀ K).rightDegree b = K.rightDegree ⟨b, hb⟩ := by
  classical
  let e : A₀ ↪ A := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : (extendParts A₀ B₀ K).leftNeighbors b =
      (K.leftNeighbors ⟨b, hb⟩).map e := by
    ext a
    constructor
    · intro ha
      have hadj := ((extendParts A₀ B₀ K).mem_leftNeighbors a b).mp ha
      obtain ⟨haA, _hbB, hadj⟩ := hadj
      apply Finset.mem_map.mpr
      exact ⟨⟨a, haA⟩, (K.mem_leftNeighbors ⟨a, haA⟩ ⟨b, hb⟩).mpr hadj, rfl⟩
    · intro ha
      obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
      exact (extendParts A₀ B₀ K).mem_leftNeighbors a'.1 b |>.mpr
        ⟨a'.2, hb, (K.mem_leftNeighbors a' ⟨b, hb⟩).mp ha'⟩
  rw [rightDegree, rightDegree, heq, Finset.card_map]

theorem rightDegree_extendParts_of_not_mem (A₀ : Finset A) (B₀ : Finset B)
    (K : BipartiteGraph A₀ B₀) {b : B} (hb : b ∉ B₀) :
    (extendParts A₀ B₀ K).rightDegree b = 0 := by
  classical
  rw [rightDegree, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨a, ha⟩
  exact hb (((extendParts A₀ B₀ K).mem_leftNeighbors a b).mp ha).choose_spec.choose

theorem leftDegree_extendParts_of_mem (A₀ : Finset A) (B₀ : Finset B)
    (K : BipartiteGraph A₀ B₀) {a : A} (ha : a ∈ A₀) :
    (extendParts A₀ B₀ K).leftDegree a = K.leftDegree ⟨a, ha⟩ := by
  classical
  let e : B₀ ↪ B := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : (extendParts A₀ B₀ K).rightNeighbors a =
      (K.rightNeighbors ⟨a, ha⟩).map e := by
    ext b
    constructor
    · intro hb
      have hadj := ((extendParts A₀ B₀ K).mem_rightNeighbors a b).mp hb
      obtain ⟨_haA, hbB, hadj⟩ := hadj
      apply Finset.mem_map.mpr
      exact ⟨⟨b, hbB⟩, (K.mem_rightNeighbors ⟨a, ha⟩ ⟨b, hbB⟩).mpr hadj, rfl⟩
    · intro hb
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
      exact (extendParts A₀ B₀ K).mem_rightNeighbors a b'.1 |>.mpr
        ⟨ha, b'.2, (K.mem_rightNeighbors ⟨a, ha⟩ b').mp hb'⟩
  rw [leftDegree, leftDegree, heq, Finset.card_map]

theorem leftDegree_extendParts_of_not_mem (A₀ : Finset A) (B₀ : Finset B)
    (K : BipartiteGraph A₀ B₀) {a : A} (ha : a ∉ A₀) :
    (extendParts A₀ B₀ K).leftDegree a = 0 := by
  classical
  rw [leftDegree, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨b, hb⟩
  exact ha (((extendParts A₀ B₀ K).mem_rightNeighbors a b).mp hb).choose

theorem supportRight_extendParts (A₀ : Finset A) (B₀ : Finset B)
    (K : BipartiteGraph A₀ B₀) :
    (extendParts A₀ B₀ K).supportRight =
      K.supportRight.map ⟨Subtype.val, Subtype.val_injective⟩ := by
  classical
  ext b
  by_cases hb : b ∈ B₀
  · rw [mem_supportRight, rightDegree_extendParts_of_mem A₀ B₀ K hb]
    constructor
    · intro hpos
      apply Finset.mem_map.mpr
      exact ⟨⟨b, hb⟩, (mem_supportRight K ⟨b, hb⟩).mpr hpos, rfl⟩
    · intro hmap
      obtain ⟨b', hb', heq⟩ := Finset.mem_map.mp hmap
      have : b' = ⟨b, hb⟩ := Subtype.ext heq
      subst b'
      exact (mem_supportRight K ⟨b, hb⟩).mp hb'
  · rw [mem_supportRight, rightDegree_extendParts_of_not_mem A₀ B₀ K hb]
    simp only [lt_self_iff_false, Finset.mem_map, false_iff]
    rintro ⟨b', _, rfl⟩
    exact hb b'.2

theorem supportLeft_extendParts (A₀ : Finset A) (B₀ : Finset B)
    (K : BipartiteGraph A₀ B₀) :
    (extendParts A₀ B₀ K).supportLeft =
      K.supportLeft.map ⟨Subtype.val, Subtype.val_injective⟩ := by
  classical
  ext a
  by_cases ha : a ∈ A₀
  · rw [mem_supportLeft, leftDegree_extendParts_of_mem A₀ B₀ K ha]
    constructor
    · intro hpos
      apply Finset.mem_map.mpr
      exact ⟨⟨a, ha⟩, (mem_supportLeft K ⟨a, ha⟩).mpr hpos, rfl⟩
    · intro hmap
      obtain ⟨a', ha', heq⟩ := Finset.mem_map.mp hmap
      have : a' = ⟨a, ha⟩ := Subtype.ext heq
      subst a'
      exact (mem_supportLeft K ⟨a, ha⟩).mp ha'
  · rw [mem_supportLeft, leftDegree_extendParts_of_not_mem A₀ B₀ K ha]
    simp only [lt_self_iff_false, Finset.mem_map, false_iff]
    rintro ⟨a', _, rfl⟩
    exact ha a'.2

@[simp]
theorem card_supportRight_extendParts (A₀ : Finset A) (B₀ : Finset B)
    (K : BipartiteGraph A₀ B₀) :
    (extendParts A₀ B₀ K).supportRight.card = K.supportRight.card := by
  rw [supportRight_extendParts, Finset.card_map]

@[simp]
theorem card_supportLeft_extendParts (A₀ : Finset A) (B₀ : Finset B)
    (K : BipartiteGraph A₀ B₀) :
    (extendParts A₀ B₀ K).supportLeft.card = K.supportLeft.card := by
  rw [supportLeft_extendParts, Finset.card_map]

theorem isHalfRegular_extendParts (A₀ : Finset A) (B₀ : Finset B)
    {K : BipartiteGraph A₀ B₀} {s : ℕ} (hK : K.IsHalfRegular s) :
    (extendParts A₀ B₀ K).IsHalfRegular s := by
  have hs : 0 < s := by
    obtain ⟨b, hb⟩ := hK.1
    have hpos := (mem_supportRight K b).mp hb
    simpa [hK.2 b hb] using hpos
  refine ⟨?_, ?_⟩
  · rw [supportRight_extendParts]
    obtain ⟨b, hb⟩ := hK.1
    exact ⟨b.1, Finset.mem_map.mpr ⟨b, hb, rfl⟩⟩
  · intro b hb
    rw [supportRight_extendParts] at hb
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    change (extendParts A₀ B₀ K).rightDegree b'.1 = s
    rw [rightDegree_extendParts_of_mem A₀ B₀ K b'.2]
    exact hK.2 b' hb'

theorem rightDegree_le_on_supports_of_le {G L : BipartiteGraph A B}
    (hLG : L ≤ G) (b : L.supportRight) :
    L.rightDegree b.1 ≤
      (G.onParts L.supportLeft L.supportRight).rightDegree b := by
  classical
  let P := G.onParts L.supportLeft L.supportRight
  let e : (L.leftNeighbors b.1) → (P.leftNeighbors b) := fun a ↦
    ⟨⟨a.1, L.adj_mem_supportLeft ((L.mem_leftNeighbors a.1 b.1).mp a.2)⟩,
      (P.mem_leftNeighbors
        ⟨a.1, L.adj_mem_supportLeft ((L.mem_leftNeighbors a.1 b.1).mp a.2)⟩ b).mpr
          (hLG ((L.mem_leftNeighbors a.1 b.1).mp a.2))⟩
  have heinj : Function.Injective e := by
    intro a a' haa
    apply Subtype.ext
    simpa [e] using congrArg (fun z : P.leftNeighbors b ↦ z.1.1) haa
  change (L.leftNeighbors b.1).card ≤ (P.leftNeighbors b).card
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective e heinj

/-- The two support sets of a half-regular subgraph form a feasible pair in
the ambient graph. -/
theorem isFeasiblePair_supports_of_le {G L : BipartiteGraph A B} {s : ℕ}
    (hLG : L ≤ G) (hL : L.IsHalfRegular s) :
    G.IsFeasiblePair s (L.supportLeft, L.supportRight) := by
  refine ⟨?_, hL.1, ?_⟩
  · by_cases hs : s = 0
    · obtain ⟨b, hb⟩ := hL.1
      have hpos : 0 < L.rightDegree b := by simpa [mem_supportRight] using hb
      simp [hL.2 b hb, hs] at hpos
    · exact supportLeft_nonempty_of_isHalfRegular hL (Nat.pos_of_ne_zero hs)
  · intro b
    exact (hL.2 b.1 b.2).ge.trans (rightDegree_le_on_supports_of_le hLG b)

/-- A regular graph on active subtype parts has a roof whose load is the
ceiling of the ambient optimum side ratio at that degree.  The proof applies
the cloned Hall lemma to each set of right vertices; its restricted residual,
extended by zero to the ambient types, supplies the required feasible pair. -/
theorem hasRoofLoadAtMost_ceil_maxFeasibleRatio
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B}
    {K : BipartiteGraph A₀ B₀} {s : ℕ}
    (hKG : extendParts A₀ B₀ K ≤ G) (hs : 0 < s)
    (hreg : ∀ b, K.rightDegree b = s) :
    K.HasRoofLoadAtMost ⌈G.maxFeasibleRatio s⌉₊ := by
  classical
  rw [hasRoofLoadAtMost_iff]
  intro X
  by_cases hX : X.Nonempty
  · let Kr := K.restrictRight X
    have hpos : ∀ b ∈ X, 0 < K.rightDegree b := by
      intro b _
      simpa [hreg b] using hs
    have hsuppR : Kr.supportRight = X := K.supportRight_restrictRight X hpos
    have hsuppL : Kr.supportLeft = K.neighborhood X := K.supportLeft_restrictRight X
    have hKr : Kr.IsHalfRegular s := by
      refine ⟨?_, ?_⟩
      · rw [hsuppR]
        exact hX
      · intro b hb
        rw [hsuppR] at hb
        exact (K.rightDegree_restrictRight_of_mem hb).trans (hreg b)
    let L := extendParts A₀ B₀ Kr
    have hLG : L ≤ G := by
      intro a b hab
      obtain ⟨ha, hb, hab⟩ := hab
      exact hKG ⟨ha, hb, hab.1⟩
    have hL : L.IsHalfRegular s := isHalfRegular_extendParts A₀ B₀ hKr
    have hfeas : G.IsFeasiblePair s (L.supportLeft, L.supportRight) :=
      isFeasiblePair_supports_of_le hLG hL
    have hratio := partRatio_le_maxFeasibleRatio hfeas
    have hcardR : L.supportRight.card = X.card := by
      simpa [L, hsuppR] using card_supportRight_extendParts A₀ B₀ Kr
    have hcardL : L.supportLeft.card = (K.neighborhood X).card := by
      simpa [L, hsuppL] using card_supportLeft_extendParts A₀ B₀ Kr
    have hNpos : (0 : ℝ) < (K.neighborhood X).card := by
      have hLnon : L.supportLeft.Nonempty :=
        supportLeft_nonempty_of_isHalfRegular hL hs
      have hcardpos : 0 < L.supportLeft.card := hLnon.card_pos
      rw [hcardL] at hcardpos
      exact_mod_cast hcardpos
    have hreal :
        (X.card : ℝ) / (K.neighborhood X).card ≤
          (⌈G.maxFeasibleRatio s⌉₊ : ℝ) := by
      calc
        (X.card : ℝ) / (K.neighborhood X).card =
            partRatio (L.supportLeft, L.supportRight) := by
              simp [partRatio, hcardR, hcardL]
        _ ≤ G.maxFeasibleRatio s := hratio
        _ ≤ (⌈G.maxFeasibleRatio s⌉₊ : ℝ) := Nat.le_ceil _
    have hmul : (X.card : ℝ) ≤
        (⌈G.maxFeasibleRatio s⌉₊ : ℝ) * (K.neighborhood X).card := by
      exact (div_le_iff₀ hNpos).mp hreal
    exact_mod_cast hmul
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hX, Finset.card_empty,
      Nat.zero_le]

/-- Union of two two-sorted bipartite graphs. -/
def union (G H : BipartiteGraph A B) : BipartiteGraph A B where
  Adj a b := G.Adj a b ∨ H.Adj a b

@[simp]
theorem union_adj (G H : BipartiteGraph A B) (a : A) (b : B) :
    (G.union H).Adj a b ↔ G.Adj a b ∨ H.Adj a b :=
  Iff.rfl

/-- Delete all edges of `H` from `G`. -/
def edgeSdiff (G H : BipartiteGraph A B) : BipartiteGraph A B where
  Adj a b := G.Adj a b ∧ ¬ H.Adj a b

@[simp]
theorem edgeSdiff_adj (G H : BipartiteGraph A B) (a : A) (b : B) :
    (G.edgeSdiff H).Adj a b ↔ G.Adj a b ∧ ¬ H.Adj a b :=
  Iff.rfl

@[simp]
theorem rightDegree_restrictRight (G : BipartiteGraph A B) (X : Finset B) (b : B) :
    (G.restrictRight X).rightDegree b = if b ∈ X then G.rightDegree b else 0 := by
  classical
  by_cases hb : b ∈ X
  · simp [rightDegree, leftNeighbors, restrictRight, hb]
  · simp [rightDegree, leftNeighbors, restrictRight, hb]

theorem leftNeighbors_mono {G H : BipartiteGraph A B} (hHG : H ≤ G) (b : B) :
    H.leftNeighbors b ⊆ G.leftNeighbors b := by
  intro a ha
  exact (mem_leftNeighbors G a b).mpr (hHG ((mem_leftNeighbors H a b).mp ha))

theorem rightNeighbors_mono {G H : BipartiteGraph A B} (hHG : H ≤ G) (a : A) :
    H.rightNeighbors a ⊆ G.rightNeighbors a := by
  intro b hb
  exact (mem_rightNeighbors G a b).mpr (hHG ((mem_rightNeighbors H a b).mp hb))

/-- The one-edge-per-right-vertex graph represented by a roof. -/
def Roof.graph {G : BipartiteGraph A B} (R : G.Roof) : BipartiteGraph A B where
  Adj a b := R.choice b = a

@[simp]
theorem Roof.graph_adj {G : BipartiteGraph A B} (R : G.Roof) (a : A) (b : B) :
    R.graph.Adj a b ↔ R.choice b = a :=
  Iff.rfl

theorem Roof.graph_le {G : BipartiteGraph A B} (R : G.Roof) : R.graph ≤ G := by
  intro a b hab
  rw [← hab]
  exact R.adj_choice b

@[simp]
theorem Roof.rightDegree_graph {G : BipartiteGraph A B} (R : G.Roof) (b : B) :
    R.graph.rightDegree b = 1 := by
  classical
  have heq :
      Finset.univ.filter (fun a ↦ R.choice b = a) = {R.choice b} := by
    ext a
    simp [eq_comm]
  rw [rightDegree, leftNeighbors]
  change (Finset.univ.filter (fun a ↦ R.choice b = a)).card = 1
  rw [heq]
  simp

@[simp]
theorem Roof.leftDegree_graph {G : BipartiteGraph A B} (R : G.Roof) (a : A) :
    R.graph.leftDegree a = R.load a := by
  classical
  simp [leftDegree, rightNeighbors, Roof.load, Roof.graph, eq_comm]

@[simp]
theorem rightDegree_sdiff_roof {G : BipartiteGraph A B} (R : G.Roof) (b : B) :
    (G.edgeSdiff R.graph).rightDegree b = G.rightDegree b - 1 := by
  classical
  have heq :
      (G.edgeSdiff R.graph).leftNeighbors b =
        (G.leftNeighbors b).erase (R.choice b) := by
    ext a
    simp [edgeSdiff, Roof.graph, leftNeighbors, eq_comm, and_comm]
  have hmem : R.choice b ∈ G.leftNeighbors b :=
    (mem_leftNeighbors G (R.choice b) b).mpr (R.adj_choice b)
  rw [rightDegree, heq, card_erase_of_mem hmem]
  rfl

theorem sdiff_roof_le {G : BipartiteGraph A B} (R : G.Roof) :
    G.edgeSdiff R.graph ≤ G := by
  intro a b hab
  exact hab.1

/-- A graph with positive minimum right degree and maximum left degree `D`
has a roof of load at most `D ⌈/⌉ m`, where `m` is the minimum right
degree. -/
theorem hasRoofLoadAtMost_ceilDiv_of_minDegree {G : BipartiteGraph A B}
    {m D : ℕ} (hm : 0 < m) (hmin : ∀ b, m ≤ G.rightDegree b)
    (hmax : ∀ a, G.leftDegree a ≤ D) :
    G.HasRoofLoadAtMost (D ⌈/⌉ m) := by
  classical
  rw [hasRoofLoadAtMost_iff]
  intro X
  let K := G.restrictRight X
  have hKle : K ≤ G := restrictRight_le G X
  have hleft_zero (a : A) (ha : a ∉ G.neighborhood X) : K.leftDegree a = 0 := by
    rw [leftDegree, card_eq_zero]
    ext b
    constructor
    · intro hb
      have hab := (mem_rightNeighbors K a b).mp hb
      exact (ha ((mem_neighborhood G X a).mpr ⟨b, hab.2, hab.1⟩)).elim
    · intro hb
      have : False := by simpa using hb
      exact this.elim
  have hcount_upper : K.edgeCount ≤ D * (G.neighborhood X).card := by
    have hout : ∀ a ∈ (Finset.univ : Finset A), a ∉ G.neighborhood X →
        K.leftDegree a = 0 := by
      intro a _ ha
      exact hleft_zero a ha
    calc
      K.edgeCount = ∑ a ∈ (Finset.univ : Finset A), K.leftDegree a := by
        simpa using edgeCount_eq_sum_leftDegree K
      _ = ∑ a ∈ G.neighborhood X, K.leftDegree a :=
        (sum_subset (subset_univ (G.neighborhood X)) hout).symm
      _ ≤ ∑ _a ∈ G.neighborhood X, D := by
        gcongr with a ha
        exact (leftDegree_mono hKle a).trans (hmax a)
      _ = D * (G.neighborhood X).card := by simp [Nat.mul_comm]
  have hcount_lower : m * X.card ≤ K.edgeCount := by
    rw [edgeCount]
    calc
      m * X.card = ∑ _b ∈ X, m := by simp [Nat.mul_comm]
      _ ≤ ∑ b ∈ X, K.rightDegree b := by
        gcongr with b hb
        simpa [K, hb] using hmin b
      _ ≤ ∑ b, K.rightDegree b := by
        exact sum_le_sum_of_subset_of_nonneg (subset_univ X) (fun _ _ _ ↦ Nat.zero_le _)
  have hD : D ≤ m * (D ⌈/⌉ m) :=
    (ceilDiv_le_iff_le_mul hm).mp le_rfl
  have hmul : m * X.card ≤ m * ((D ⌈/⌉ m) * (G.neighborhood X).card) := by
    calc
      m * X.card ≤ K.edgeCount := hcount_lower
      _ ≤ D * (G.neighborhood X).card := hcount_upper
      _ ≤ (m * (D ⌈/⌉ m)) * (G.neighborhood X).card :=
        Nat.mul_le_mul_right _ hD
      _ = m * ((D ⌈/⌉ m) * (G.neighborhood X).card) := by
        simp [Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_left hmul hm

private theorem rightDegree_sup_roof_of_le_sdiff {G H : BipartiteGraph A B}
    (R : G.Roof) (hH : H ≤ G.edgeSdiff R.graph) (b : B) :
    (R.graph.union H).rightDegree b = H.rightDegree b + 1 := by
  classical
  have hnot : R.choice b ∉ H.leftNeighbors b := by
    intro hb
    have := hH ((mem_leftNeighbors H (R.choice b) b).mp hb)
    exact this.2 rfl
  simp only [rightDegree, leftNeighbors]
  have heq :
      Finset.univ.filter (fun a ↦ (R.graph.union H).Adj a b) =
        insert (R.choice b) (H.leftNeighbors b) := by
    ext a
    simp [Roof.graph, leftNeighbors, eq_comm]
  rw [heq, card_insert_of_notMem hnot]
  rfl

private theorem leftDegree_sup_roof_le {G H : BipartiteGraph A B}
    (R : G.Roof) (a : A) :
    (R.graph.union H).leftDegree a ≤ R.load a + H.leftDegree a := by
  classical
  simp only [leftDegree, rightNeighbors]
  have hsub :
      Finset.univ.filter (fun b ↦ (R.graph.union H).Adj a b) ⊆
        (Finset.univ.filter fun b ↦ R.graph.Adj a b) ∪
          (Finset.univ.filter fun b ↦ H.Adj a b) := by
    intro b hb
    simpa using hb
  calc
    (Finset.univ.filter fun b ↦ (R.graph.union H).Adj a b).card
        ≤ ((Finset.univ.filter fun b ↦ R.graph.Adj a b) ∪
          (Finset.univ.filter fun b ↦ H.Adj a b)).card := card_le_card hsub
    _ ≤ (Finset.univ.filter fun b ↦ R.graph.Adj a b).card +
          (Finset.univ.filter fun b ↦ H.Adj a b).card := card_union_le _ _
    _ = R.load a + H.leftDegree a := by
      change
        (Finset.univ.filter fun b ↦ R.choice b = a).card +
          (H.rightNeighbors a).card = R.load a + (H.rightNeighbors a).card
      rfl

/-- Successively remove roofs whose common load bound is supplied for every
regular residual degree in the interval `[r+1, r+d]`.  This isolates the
inductive graph bookkeeping from the multiplicative-ratio argument. -/
theorem exists_rightRegular_subgraph_of_roof_interval
    (G : BipartiteGraph A B) (r d q : ℕ)
    (hreg : ∀ b, G.rightDegree b = r + d)
    (hroof : ∀ (K : BipartiteGraph A B), K ≤ G → ∀ s,
      r + 1 ≤ s → s ≤ r + d →
      (∀ b, K.rightDegree b = s) → K.HasRoofLoadAtMost q) :
    ∃ H : BipartiteGraph A B,
      H ≤ G ∧
      (∀ b, H.rightDegree b = d) ∧
      ∀ a, H.leftDegree a ≤ d * q := by
  induction d generalizing G with
  | zero =>
      refine ⟨⊥, ?_, ?_, ?_⟩
      · intro a b hab
        exact hab.elim
      · intro b
        simp [rightDegree, leftNeighbors]
      · intro a
        simp [leftDegree, rightNeighbors]
  | succ d ih =>
      have htop_le : r + 1 ≤ r + (d + 1) := by omega
      obtain ⟨R, hRload⟩ := hroof G le_rfl (r + (d + 1)) htop_le le_rfl hreg
      let K : BipartiteGraph A B := G.edgeSdiff R.graph
      have hKle : K ≤ G := sdiff_roof_le R
      have hKreg : ∀ b, K.rightDegree b = r + d := by
        intro b
        simp [K, hreg b]
      have hroofK : ∀ (L : BipartiteGraph A B), L ≤ K → ∀ s,
          r + 1 ≤ s → s ≤ r + d →
          (∀ b, L.rightDegree b = s) → L.HasRoofLoadAtMost q := by
        intro L hLK s hrs hsr hsreg
        exact hroof L (hLK.trans hKle) s hrs (hsr.trans (by omega)) hsreg
      obtain ⟨H, hHK, hHreg, hHmax⟩ := ih K hKreg hroofK
      refine ⟨R.graph.union H, ?_, ?_, ?_⟩
      · intro a b hab
        exact hab.elim (fun h ↦ R.graph_le h) (fun h ↦ hKle (hHK h))
      · intro b
        rw [rightDegree_sup_roof_of_le_sdiff R hHK b, hHreg b]
      · intro a
        calc
          (R.graph.union H).leftDegree a ≤ R.load a + H.leftDegree a :=
            leftDegree_sup_roof_le R a
          _ ≤ q + d * q := Nat.add_le_add (hRload a) (hHmax a)
          _ = (d + 1) * q := by simp [Nat.add_mul, Nat.add_comm]

/-- **Finite roof regularization.**  From a graph which is right-regular of
degree `r + d` and has maximum left degree `D`, extract a subgraph which is
right-regular of degree `d` and has maximum left degree at most
`d * (D ⌈/⌉ (r + 1))`.

Writing `r = δ - d`, this is the successive-roof form used after choosing a
good residual level in the PRS/Shirazi multiplicative-block argument. -/
theorem exists_rightRegular_subgraph_of_add_degree (G : BipartiteGraph A B)
    (r d D : ℕ) (hreg : ∀ b, G.rightDegree b = r + d)
    (hmax : ∀ a, G.leftDegree a ≤ D) :
    ∃ H : BipartiteGraph A B,
      H ≤ G ∧
      (∀ b, H.rightDegree b = d) ∧
      ∀ a, H.leftDegree a ≤ d * (D ⌈/⌉ (r + 1)) := by
  induction d generalizing G with
  | zero =>
      refine ⟨⊥, ?_, ?_, ?_⟩
      · intro a b hab
        exact hab.elim
      · intro b
        simp [rightDegree, leftNeighbors]
      · intro a
        simp [leftDegree, rightNeighbors]
  | succ d ih =>
      have hrp : 0 < r + 1 := Nat.succ_pos r
      have hmin : ∀ b, r + 1 ≤ G.rightDegree b := by
        intro b
        rw [hreg b]
        omega
      obtain ⟨R, hRload⟩ := hasRoofLoadAtMost_ceilDiv_of_minDegree hrp hmin hmax
      let K : BipartiteGraph A B := G.edgeSdiff R.graph
      have hKle : K ≤ G := sdiff_roof_le R
      have hKreg : ∀ b, K.rightDegree b = r + d := by
        intro b
        simp [K, hreg b]
      have hKmax : ∀ a, K.leftDegree a ≤ D := by
        intro a
        exact (leftDegree_mono hKle a).trans (hmax a)
      obtain ⟨H, hHG, hHreg, hHmax⟩ := ih K hKreg hKmax
      refine ⟨R.graph.union H, ?_, ?_, ?_⟩
      · intro a b hab
        exact hab.elim (fun h ↦ R.graph_le h) (fun h ↦ hKle (hHG h))
      · intro b
        rw [rightDegree_sup_roof_of_le_sdiff R hHG b, hHreg b]
      · intro a
        calc
          (R.graph.union H).leftDegree a ≤ R.load a + H.leftDegree a :=
            leftDegree_sup_roof_le R a
          _ ≤ (D ⌈/⌉ (r + 1)) + d * (D ⌈/⌉ (r + 1)) :=
            Nat.add_le_add (hRload a) (hHmax a)
          _ = (d + 1) * (D ⌈/⌉ (r + 1)) := by
            simp [Nat.add_mul, Nat.add_comm]

/-- The same theorem with the original degree `δ` and the retained degree `d`
as parameters. -/
theorem exists_rightRegular_subgraph_of_le_degree (G : BipartiteGraph A B)
    (δ d D : ℕ) (hd : d ≤ δ) (hreg : ∀ b, G.rightDegree b = δ)
    (hmax : ∀ a, G.leftDegree a ≤ D) :
    ∃ H : BipartiteGraph A B,
      H ≤ G ∧
      (∀ b, H.rightDegree b = d) ∧
      ∀ a, H.leftDegree a ≤ d * (D ⌈/⌉ (δ - d + 1)) := by
  have hadd : δ - d + d = δ := Nat.sub_add_cancel hd
  simpa [hadd] using
    exists_rightRegular_subgraph_of_add_degree G (δ - d) d D
      (fun b ↦ by simpa [hadd] using hreg b) hmax

/-- Cross-multiplied form of the left-degree estimate.  This is the integer
interface used when deriving the normalized estimate in equation (9). -/
theorem exists_rightRegular_subgraph_card_mul_le (G : BipartiteGraph A B)
    (δ d D Q : ℕ) (hd : d ≤ δ) (hreg : ∀ b, G.rightDegree b = δ)
    (hmax : ∀ a, G.leftDegree a ≤ D)
    (hscale : (D ⌈/⌉ (δ - d + 1)) * Fintype.card B ≤ Q) :
    ∃ H : BipartiteGraph A B,
      H ≤ G ∧
      (∀ b, H.rightDegree b = d) ∧
      ∀ a, H.leftDegree a * Fintype.card B ≤ d * Q := by
  obtain ⟨H, hHG, hHreg, hHmax⟩ :=
    exists_rightRegular_subgraph_of_le_degree G δ d D hd hreg hmax
  refine ⟨H, hHG, hHreg, fun a ↦ ?_⟩
  calc
    H.leftDegree a * Fintype.card B
        ≤ (d * (D ⌈/⌉ (δ - d + 1))) * Fintype.card B :=
      Nat.mul_le_mul_right _ (hHmax a)
    _ = d * ((D ⌈/⌉ (δ - d + 1)) * Fintype.card B) := by
      simp [Nat.mul_assoc]
    _ ≤ d * Q := Nat.mul_le_mul_left d hscale

/-! ## The multiplicative-block form (Shirazi, Lemma 5.3.3) -/

@[simp]
theorem rightDegree_onParts_univ (G : BipartiteGraph A B)
    (b : (Finset.univ : Finset B)) :
    (G.onParts Finset.univ Finset.univ).rightDegree b = G.rightDegree b.1 := by
  classical
  simp only [rightDegree, leftNeighbors, onParts]
  refine Finset.card_bij (fun a _ha ↦ a.1) ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ a.1, (Finset.mem_filter.mp ha).2⟩
  · intro a ha a' ha' haa'
    exact Subtype.ext haa'
  · intro a ha
    refine ⟨⟨a, Finset.mem_univ a⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨by simp, ?_⟩
    exact (Finset.mem_filter.mp ha).2

theorem HasRoofLoadAtMost.mono {G : BipartiteGraph A B} {q q' : ℕ}
    (hG : G.HasRoofLoadAtMost q) (hqq : q ≤ q') :
    G.HasRoofLoadAtMost q' := by
  obtain ⟨R, hR⟩ := hG
  exact ⟨R, fun a ↦ (hR a).trans hqq⟩

/-- The full finite multiplicative-block roof regularization lemma.

The right side of `G` is assumed to be globally `δ`-regular (the wrapper for
a half-regular graph simply takes its two supports as the ambient types).  If
the displayed side ratio is at least `α`, and the maximum left degree is at
most `D ≤ β^floor((δ-1)/(γ-1))`, the theorem finds active subparts and a
right-`γ`-regular subgraph on them.  Its last conclusion is precisely the
cross-multiplied real estimate used as equation (9) in Shirazi's proof. -/
theorem exists_multiplicativeBlock_regularization
    [Nonempty A] [Nonempty B]
    (G : BipartiteGraph A B) (δ γ α D : ℕ) (β : ℝ)
    (hγ : 2 ≤ γ) (hγδ : γ ≤ δ) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hreg : ∀ b, G.rightDegree b = δ)
    (hratio : α * Fintype.card A ≤ Fintype.card B)
    (hmax : ∀ a, G.leftDegree a ≤ D)
    (hD : (D : ℝ) ≤ β ^ ((δ - 1) / (γ - 1))) :
    ∃ (A₃ : Finset A) (B₃ : Finset B) (H : BipartiteGraph A B),
      H ≤ G ∧
      H.SupportedOn A₃ B₃ ∧
      A₃.Nonempty ∧ B₃.Nonempty ∧
      H.IsRightRegularOn B₃ γ ∧
      α * A₃.card ≤ B₃.card ∧
      Fintype.card B * A₃.card ≤ B₃.card * Fintype.card A ∧
      ∀ a ∈ A₃,
        (H.leftDegree a * A₃.card : ℝ) ≤
          (β * (1 + 1 / (α : ℝ))) * γ * B₃.card := by
  classical
  let t : ℕ := (δ - 1) / (γ - 1)
  let level : ℕ → ℕ := fun j ↦ δ - j * (γ - 1)
  let value : ℕ → ℝ := fun j ↦ G.maxFeasibleRatio (level j)
  let p₀ : Finset A × Finset B := (Finset.univ, Finset.univ)
  have hδpos : 0 < δ := by omega
  have htpos : 0 < t := by
    apply Nat.div_pos
    · omega
    · omega
  have hlevel_zero : level 0 = δ := by simp [level]
  have hp₀ : G.IsFeasiblePair δ p₀ := by
    refine ⟨Finset.univ_nonempty, Finset.univ_nonempty, ?_⟩
    intro b
    rw [rightDegree_onParts_univ]
    exact (hreg b.1).ge
  have hfeasδ : (G.feasiblePairs δ).Nonempty :=
    ⟨p₀, (mem_feasiblePairs G δ p₀).mpr hp₀⟩
  have ht_mul : t * (γ - 1) ≤ δ - 1 := by
    exact Nat.div_mul_le_self (δ - 1) (γ - 1)
  have hlevel_t_pos : 0 < level t := by
    dsimp [level]
    omega
  have hp₀_t : G.IsFeasiblePair (level t) p₀ :=
    hp₀.mono_degree (Nat.sub_le δ (t * (γ - 1)))
  have hfeas_t : (G.feasiblePairs (level t)).Nonempty :=
    ⟨p₀, (mem_feasiblePairs G (level t) p₀).mpr hp₀_t⟩
  have hvalue_t : value t ≤ β ^ t := by
    calc
      value t = G.maxFeasibleRatio (level t) := rfl
      _ ≤ (D : ℝ) :=
        maxFeasibleRatio_le_of_maxLeftDegree hlevel_t_pos hfeas_t hmax
      _ ≤ β ^ t := by simpa [t] using hD
  have hApos : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos
  have hratio_real :
      (α : ℝ) * Fintype.card A ≤ (Fintype.card B : ℝ) := by
    exact_mod_cast hratio
  have hα_le_p₀ : (α : ℝ) ≤ partRatio p₀ := by
    rw [partRatio]
    simpa [p₀] using (le_div_iff₀ hApos).2 hratio_real
  have hone_value : 1 ≤ value 0 := by
    calc
      (1 : ℝ) ≤ α := by exact_mod_cast hα
      _ ≤ partRatio p₀ := hα_le_p₀
      _ ≤ G.maxFeasibleRatio δ := partRatio_le_maxFeasibleRatio hp₀
      _ = value 0 := by simp [value, hlevel_zero]
  obtain ⟨j, hjt, hblock⟩ :=
    exists_multiplicative_block value t htpos β hβ hone_value hvalue_t
  have hj1t : j + 1 ≤ t := by omega
  have hj_mul : j * (γ - 1) ≤ δ - 1 :=
    (Nat.mul_le_mul_right (γ - 1) (Nat.le_of_lt hjt)).trans ht_mul
  have hj1_mul : (j + 1) * (γ - 1) ≤ δ - 1 :=
    (Nat.mul_le_mul_right (γ - 1) hj1t).trans ht_mul
  have hlevel_succ : level (j + 1) + (γ - 1) = level j := by
    dsimp [level]
    have hmul : (j + 1) * (γ - 1) = j * (γ - 1) + (γ - 1) := by ring
    rw [hmul]
    omega
  have hnext_pos : 0 < level (j + 1) := by
    dsimp [level]
    omega
  have hcurrent_ge : γ ≤ level j := by omega
  have hcurrent_le_delta : level j ≤ δ := Nat.sub_le _ _
  have hp₀_current : G.IsFeasiblePair (level j) p₀ :=
    hp₀.mono_degree hcurrent_le_delta
  have hfeas_current : (G.feasiblePairs (level j)).Nonempty :=
    ⟨p₀, (mem_feasiblePairs G (level j) p₀).mpr hp₀_current⟩
  obtain ⟨p, hp, hpvalue⟩ :=
    exists_partRatio_eq_maxFeasibleRatio hfeas_current
  let P : BipartiteGraph p.1 p.2 := G.trimmedFeasiblePairGraph (level j) p hp
  let q : ℕ := ⌈G.maxFeasibleRatio (level (j + 1))⌉₊
  have hP_reg : ∀ b, P.rightDegree b = (level j - γ) + γ := by
    intro b
    rw [show P.rightDegree b = level j from
      rightDegree_trimmedFeasiblePairGraph G (level j) p hp b]
    omega
  have hP_le_on : P ≤ G.onParts p.1 p.2 :=
    trimmedFeasiblePairGraph_le G (level j) p hp
  have hroof : ∀ (K : BipartiteGraph p.1 p.2), K ≤ P → ∀ s,
      level j - γ + 1 ≤ s → s ≤ level j - γ + γ →
      (∀ b, K.rightDegree b = s) → K.HasRoofLoadAtMost q := by
    intro K hKP s hslow hshigh hKreg
    have hKGon : K ≤ G.onParts p.1 p.2 := hKP.trans hP_le_on
    have hKG : extendParts p.1 p.2 K ≤ G := extendParts_le hKGon
    have hspos : 0 < s := by omega
    have hKroof := hasRoofLoadAtMost_ceil_maxFeasibleRatio hKG hspos hKreg
    have hsnext : level (j + 1) ≤ s := by omega
    have hpair_s : G.IsFeasiblePair s p := by
      refine ⟨hp.1, hp.2.1, ?_⟩
      intro b
      calc
        s = K.rightDegree b := (hKreg b).symm
        _ ≤ P.rightDegree b := rightDegree_mono hKP b
        _ ≤ (G.onParts p.1 p.2).rightDegree b := rightDegree_mono hP_le_on b
    have hfeas_s : (G.feasiblePairs s).Nonempty :=
      ⟨p, (mem_feasiblePairs G s p).mpr hpair_s⟩
    have hmono : G.maxFeasibleRatio s ≤
        G.maxFeasibleRatio (level (j + 1)) :=
      maxFeasibleRatio_mono_degree hsnext hfeas_s
    exact hKroof.mono (Nat.ceil_mono hmono)
  obtain ⟨H₀, hH₀P, hH₀reg, hH₀max⟩ :=
    exists_rightRegular_subgraph_of_roof_interval P (level j - γ) γ q
      hP_reg hroof
  let H : BipartiteGraph A B := extendParts p.1 p.2 H₀
  have hHG : H ≤ G := by
    exact extendParts_le (hH₀P.trans hP_le_on)
  have hHsupp : H.SupportedOn p.1 p.2 := extendParts_supportedOn p.1 p.2 H₀
  have hHreg_on : H.IsRightRegularOn p.2 γ := by
    intro b hb
    rw [show H.rightDegree b = H₀.rightDegree ⟨b, hb⟩ from
      rightDegree_extendParts_of_mem p.1 p.2 H₀ hb]
    exact hH₀reg ⟨b, hb⟩
  have hvalue_zero_current : value 0 ≤ value j := by
    have hmono := maxFeasibleRatio_mono_degree hcurrent_le_delta hfeasδ
    simpa [value, hlevel_zero] using hmono
  have hα_le_current : (α : ℝ) ≤ partRatio p := by
    calc
      (α : ℝ) ≤ partRatio p₀ := hα_le_p₀
      _ ≤ value 0 := by
        simpa [value, hlevel_zero] using partRatio_le_maxFeasibleRatio hp₀
      _ ≤ value j := hvalue_zero_current
      _ = partRatio p := by simpa [value] using hpvalue.symm
  have hp₀_le_p : partRatio p₀ ≤ partRatio p := by
    calc
      partRatio p₀ ≤ value 0 := by
        simpa [value, hlevel_zero] using partRatio_le_maxFeasibleRatio hp₀
      _ ≤ value j := hvalue_zero_current
      _ = partRatio p := by simpa [value] using hpvalue.symm
  have hpApos : (0 : ℝ) < p.1.card := by exact_mod_cast hp.1.card_pos
  have hpBnonneg : (0 : ℝ) ≤ p.2.card := by positivity
  have hratio_p_real : (α : ℝ) * p.1.card ≤ (p.2.card : ℝ) := by
    apply (le_div_iff₀ hpApos).mp
    simpa [partRatio] using hα_le_current
  have hratio_p : α * p.1.card ≤ p.2.card := by exact_mod_cast hratio_p_real
  have hratio_nondec_real :
      (Fintype.card B : ℝ) * p.1.card ≤
        (p.2.card : ℝ) * Fintype.card A := by
    apply (div_le_div_iff₀ hApos hpApos).mp
    simpa [partRatio, p₀] using hp₀_le_p
  have hratio_nondec :
      Fintype.card B * p.1.card ≤ p.2.card * Fintype.card A := by
    exact_mod_cast hratio_nondec_real
  refine ⟨p.1, p.2, H, hHG, hHsupp, hp.1, hp.2.1, hHreg_on, hratio_p,
    hratio_nondec, ?_⟩
  intro a ha
  have hHdeg : H.leftDegree a = H₀.leftDegree ⟨a, ha⟩ :=
    leftDegree_extendParts_of_mem p.1 p.2 H₀ ha
  have hdegR : (H.leftDegree a : ℝ) ≤ (γ : ℝ) * q := by
    rw [hHdeg]
    exact_mod_cast hH₀max ⟨a, ha⟩
  have hpnext : G.IsFeasiblePair (level (j + 1)) p₀ :=
    hp₀.mono_degree (Nat.sub_le δ ((j + 1) * (γ - 1)))
  have hnext_nonneg : 0 ≤ G.maxFeasibleRatio (level (j + 1)) := by
    have hratio_nonneg : (0 : ℝ) ≤ partRatio p₀ := by
      simp [partRatio, p₀]
      positivity
    exact hratio_nonneg.trans (partRatio_le_maxFeasibleRatio hpnext)
  have hqR : (q : ℝ) ≤ G.maxFeasibleRatio (level (j + 1)) + 1 := by
    exact (Nat.ceil_lt_add_one hnext_nonneg).le
  have hqblock : (q : ℝ) ≤ β * partRatio p + 1 := by
    calc
      (q : ℝ) ≤ G.maxFeasibleRatio (level (j + 1)) + 1 := hqR
      _ = value (j + 1) + 1 := rfl
      _ ≤ β * value j + 1 := by linarith
      _ = β * partRatio p + 1 := by rw [hpvalue]
  have hαposR : (0 : ℝ) < α := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hα)
  have hA_le_div : (p.1.card : ℝ) ≤ (p.2.card : ℝ) / α := by
    exact (le_div_iff₀ hαposR).2 (by simpa [mul_comm] using hratio_p_real)
  have hdiv_nonneg : (0 : ℝ) ≤ (p.2.card : ℝ) / α :=
    div_nonneg hpBnonneg hαposR.le
  have hA_le_beta_div : (p.1.card : ℝ) ≤
      β * ((p.2.card : ℝ) / α) := by
    calc
      (p.1.card : ℝ) ≤ (p.2.card : ℝ) / α := hA_le_div
      _ = 1 * ((p.2.card : ℝ) / α) := by ring
      _ ≤ β * ((p.2.card : ℝ) / α) :=
        mul_le_mul_of_nonneg_right hβ hdiv_nonneg
  have hqA : (q : ℝ) * p.1.card ≤
      β * p.2.card + p.1.card := by
    calc
      (q : ℝ) * p.1.card ≤
          (β * partRatio p + 1) * p.1.card :=
        mul_le_mul_of_nonneg_right hqblock hpApos.le
      _ = β * p.2.card + p.1.card := by
        rw [partRatio]
        field_simp
        <;> ring
  calc
    (H.leftDegree a * p.1.card : ℝ)
        ≤ ((γ : ℝ) * q) * p.1.card :=
          mul_le_mul_of_nonneg_right hdegR hpApos.le
    _ = (γ : ℝ) * ((q : ℝ) * p.1.card) := by ring
    _ ≤ (γ : ℝ) * (β * p.2.card + p.1.card) :=
      mul_le_mul_of_nonneg_left hqA (by positivity)
    _ ≤ (γ : ℝ) *
        (β * p.2.card + β * ((p.2.card : ℝ) / α)) :=
      mul_le_mul_of_nonneg_left (by
        simpa [add_comm] using add_le_add_left hA_le_beta_div (β * p.2.card))
        (by positivity)
    _ = (β * (1 + 1 / (α : ℝ))) * γ * p.2.card := by
      field_simp
      <;> ring

theorem extendParts_onParts_eq_of_supportedOn (G : BipartiteGraph A B)
    {A₀ : Finset A} {B₀ : Finset B} (hG : G.SupportedOn A₀ B₀) :
    extendParts A₀ B₀ (G.onParts A₀ B₀) = G := by
  ext a b
  constructor
  · rintro ⟨_ha, _hb, hab⟩
    exact hab
  · intro hab
    exact ⟨(hG hab).1, (hG hab).2, hab⟩

theorem rightDegree_onParts_eq_of_supportedOn (G : BipartiteGraph A B)
    {A₀ : Finset A} {B₀ : Finset B} (hG : G.SupportedOn A₀ B₀)
    (b : B₀) :
    (G.onParts A₀ B₀).rightDegree b = G.rightDegree b.1 := by
  rw [← rightDegree_extendParts_of_mem A₀ B₀ (G.onParts A₀ B₀) b.2,
    extendParts_onParts_eq_of_supportedOn G hG]

/-- Ambient finite-set wrapper for `exists_multiplicativeBlock_regularization`.
It is the direct interface used after a previous extraction theorem has
produced a half-regular subgraph supported on displayed parts. -/
theorem IsHalfRegularSubgraphOf.exists_multiplicativeBlock_regularization
    {G₁ G₂ : BipartiteGraph A B} {A₂ : Finset A} {B₂ : Finset B}
    {δ γ α D : ℕ} {β : ℝ}
    (hG₂ : G₂.IsHalfRegularSubgraphOf G₁ A₂ B₂ δ)
    (hA₂ : A₂.Nonempty)
    (hγ : 2 ≤ γ) (hγδ : γ ≤ δ) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hratio : α * A₂.card ≤ B₂.card)
    (hmax : ∀ a ∈ A₂, G₂.leftDegree a ≤ D)
    (hD : (D : ℝ) ≤ β ^ ((δ - 1) / (γ - 1))) :
    ∃ (A₃ : Finset A) (B₃ : Finset B) (G₃ : BipartiteGraph A B),
      G₃ ≤ G₂ ∧
      A₃ ⊆ A₂ ∧ B₃ ⊆ B₂ ∧
      G₃.SupportedOn A₃ B₃ ∧
      A₃.Nonempty ∧ B₃.Nonempty ∧
      G₃.IsRightRegularOn B₃ γ ∧
      α * A₃.card ≤ B₃.card ∧
      B₂.card * A₃.card ≤ B₃.card * A₂.card ∧
      ∀ a ∈ A₃,
        (G₃.leftDegree a * A₃.card : ℝ) ≤
          (β * (1 + 1 / (α : ℝ))) * γ * B₃.card := by
  classical
  let P : BipartiteGraph A₂ B₂ := G₂.onParts A₂ B₂
  let : Nonempty A₂ := hA₂.to_subtype
  let : Nonempty B₂ := hG₂.2.2.1.to_subtype
  have hPreg : ∀ b, P.rightDegree b = δ := by
    intro b
    rw [show P.rightDegree b = G₂.rightDegree b.1 from
      rightDegree_onParts_eq_of_supportedOn G₂ hG₂.2.1 b]
    exact hG₂.2.2.2 b.1 b.2
  have hPmax : ∀ a, P.leftDegree a ≤ D := by
    intro a
    exact (leftDegree_onParts_le G₂ A₂ B₂ a).trans (hmax a.1 a.2)
  have hPratio : α * Fintype.card A₂ ≤ Fintype.card B₂ := by
    simpa only [Fintype.card_coe] using hratio
  obtain ⟨A₃', B₃', H₃', hH₃P, hH₃supp, hA₃'ne, hB₃'ne, hH₃reg,
      hratio₃, hratioNondec₃, hleft₃⟩ :=
    Erdos182.BipartiteGraph.exists_multiplicativeBlock_regularization
      P δ γ α D β hγ hγδ hα hβ
      hPreg hPratio hPmax hD
  let eA : A₂ ↪ A := ⟨Subtype.val, Subtype.val_injective⟩
  let eB : B₂ ↪ B := ⟨Subtype.val, Subtype.val_injective⟩
  let A₃ : Finset A := A₃'.map eA
  let B₃ : Finset B := B₃'.map eB
  let G₃ : BipartiteGraph A B := extendParts A₂ B₂ H₃'
  have hG₃G₂ : G₃ ≤ G₂ := by
    exact extendParts_le hH₃P
  have hA₃sub : A₃ ⊆ A₂ := by
    intro a ha
    obtain ⟨a', _ha', rfl⟩ := Finset.mem_map.mp ha
    exact a'.2
  have hB₃sub : B₃ ⊆ B₂ := by
    intro b hb
    obtain ⟨b', _hb', rfl⟩ := Finset.mem_map.mp hb
    exact b'.2
  have hG₃supp : G₃.SupportedOn A₃ B₃ := by
    rintro a b ⟨ha₂, hb₂, hab⟩
    obtain ⟨ha₃, hb₃⟩ := hH₃supp hab
    exact ⟨Finset.mem_map.mpr ⟨⟨a, ha₂⟩, ha₃, rfl⟩,
      Finset.mem_map.mpr ⟨⟨b, hb₂⟩, hb₃, rfl⟩⟩
  have hA₃ne : A₃.Nonempty := by
    obtain ⟨a, ha⟩ := hA₃'ne
    exact ⟨a.1, Finset.mem_map.mpr ⟨a, ha, rfl⟩⟩
  have hB₃ne : B₃.Nonempty := by
    obtain ⟨b, hb⟩ := hB₃'ne
    exact ⟨b.1, Finset.mem_map.mpr ⟨b, hb, rfl⟩⟩
  have hG₃reg : G₃.IsRightRegularOn B₃ γ := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    change (extendParts A₂ B₂ H₃').rightDegree b'.1 = γ
    rw [rightDegree_extendParts_of_mem A₂ B₂ H₃' b'.2]
    exact hH₃reg b' hb'
  have hratio₃' : α * A₃.card ≤ B₃.card := by
    simpa [A₃, B₃] using hratio₃
  have hratioNondec₃' : B₂.card * A₃.card ≤ B₃.card * A₂.card := by
    simpa [A₃, B₃] using hratioNondec₃
  refine ⟨A₃, B₃, G₃, hG₃G₂, hA₃sub, hB₃sub, hG₃supp,
    hA₃ne, hB₃ne, hG₃reg, hratio₃', hratioNondec₃', ?_⟩
  intro a ha
  obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
  change ((extendParts A₂ B₂ H₃').leftDegree a'.1 * A₃.card : ℝ) ≤ _
  rw [leftDegree_extendParts_of_mem A₂ B₂ H₃' a'.2]
  simpa [A₃, B₃] using hleft₃ a' ha'

end BipartiteGraph

end Erdos182
