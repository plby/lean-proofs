/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied with the original proof repository.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 619.
Informal proof: Claude Fable 5.
Formal proof: GPT-5.5 with Codex, following a formalization sketch and guidance
from Claude Fable 5. Human contributor and publisher: Nick (Nikolas) Kuhn.
Source: https://www.erdosproblems.com/619#post-6986
https://github.com/nick-kuhn/erdos-619/tree/7f65718b8c1019ecc24e6c9a6b04ec4c66a4e26f
Original Lean/Mathlib version: 4.28.0.
Original Mathlib revision: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import ErdosProblems.Erdos619.Basic

open SimpleGraph
open scoped BigOperators

set_option linter.mathlibStandardSet false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos619

/-- Maximum-degree bound, stated pointwise to avoid depending on a particular max-degree API. -/
def MaxDegreeAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) : Prop :=
  ∀ v : Fin n, (G.neighborSet v).ncard ≤ d

/-- The independence-number constant supplied by the finite-counting Lemma E route. -/
def hostC : ℝ := 15

/-- Lemma E's target host-graph package. -/
def HostGraph (d m : ℕ) (H : SimpleGraph (Fin m)) : Prop :=
  H.Connected ∧
    H.CliqueFree 3 ∧
      MaxDegreeAtMost H d ∧
        (H.indepNum : ℝ) ≤ hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)

lemma HostGraph.connected {d m : ℕ} {H : SimpleGraph (Fin m)}
    (h : HostGraph d m H) : H.Connected := h.1

lemma HostGraph.cliqueFree_three {d m : ℕ} {H : SimpleGraph (Fin m)}
    (h : HostGraph d m H) : H.CliqueFree 3 := h.2.1

lemma HostGraph.maxDegreeAtMost {d m : ℕ} {H : SimpleGraph (Fin m)}
    (h : HostGraph d m H) : MaxDegreeAtMost H d := h.2.2.1

lemma HostGraph.indepNum_le {d m : ℕ} {H : SimpleGraph (Fin m)}
    (h : HostGraph d m H) :
    (H.indepNum : ℝ) ≤ hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := h.2.2.2

def AdjacentPairSet {n : ℕ} (H : SimpleGraph (Fin n)) : Set (Fin n × Fin n) :=
  {p | H.Adj p.1 p.2}

def adjacentPairSetEquivSigma {n : ℕ} (H : SimpleGraph (Fin n)) :
    AdjacentPairSet H ≃ Σ v : Fin n, H.neighborSet v where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv := by
    rintro ⟨⟨v, w⟩, h⟩
    rfl
  right_inv := by
    rintro ⟨v, ⟨w, h⟩⟩
    rfl

lemma adjacentPairSet_nat_card_le_card_mul_of_maxDegreeAtMost {n d : ℕ} {H : SimpleGraph (Fin n)}
    (hdeg : MaxDegreeAtMost H d) : Nat.card (AdjacentPairSet H) ≤ n * d := by
  classical
  have hcard : Nat.card (AdjacentPairSet H) = ∑ v : Fin n, (H.neighborSet v).ncard := by
    calc
      Nat.card (AdjacentPairSet H) = Nat.card (Σ v : Fin n, H.neighborSet v) :=
        Nat.card_congr (adjacentPairSetEquivSigma H)
      _ = ∑ v : Fin n, Nat.card (H.neighborSet v) := by
        rw [Nat.card_sigma]
      _ = ∑ v : Fin n, (H.neighborSet v).ncard := by
        refine Finset.sum_congr rfl ?_
        intro v _
        simpa [SimpleGraph.neighborSet] using Nat.card_coe_set_eq (H.neighborSet v)
  calc
    Nat.card (AdjacentPairSet H) = ∑ v : Fin n, (H.neighborSet v).ncard := hcard
    _ ≤ ∑ _v : Fin n, d := by
      exact Finset.sum_le_sum fun v _ => hdeg v
    _ = n * d := by simp [Fintype.card_fin]

noncomputable def edgeToAdjacentPair {n : ℕ} (H : SimpleGraph (Fin n))
    (e : H.edgeSet) : AdjacentPairSet H :=
  ⟨e.1.out, by
    rw [AdjacentPairSet]
    change H.Adj e.1.out.1 e.1.out.2
    rw [← SimpleGraph.mem_edgeSet]
    simp [Sym2.mk, e.1.out_eq, e.2]⟩

lemma edgeToAdjacentPair_injective {n : ℕ} (H : SimpleGraph (Fin n)) :
    Function.Injective (edgeToAdjacentPair H) := by
  intro e f hef
  apply Subtype.ext
  have hp : e.1.out = f.1.out := congrArg Subtype.val hef
  have hmk : s(e.1.out.1, e.1.out.2) = s(f.1.out.1, f.1.out.2) :=
    congrArg (Function.uncurry Sym2.mk) hp
  simpa [Sym2.mk, e.1.out_eq, f.1.out_eq] using hmk

lemma edgeSet_nat_card_le_card_mul_of_maxDegreeAtMost {n d : ℕ} {H : SimpleGraph (Fin n)}
    (hdeg : MaxDegreeAtMost H d) : Nat.card H.edgeSet ≤ n * d := by
  classical
  exact (Nat.card_le_card_of_injective (edgeToAdjacentPair H)
    (edgeToAdjacentPair_injective H)).trans
      (adjacentPairSet_nat_card_le_card_mul_of_maxDegreeAtMost hdeg)

lemma HostGraph.edgeSet_nat_card_le_card_mul {d m : ℕ} {H : SimpleGraph (Fin m)}
    (h : HostGraph d m H) : Nat.card H.edgeSet ≤ m * d :=
  edgeSet_nat_card_le_card_mul_of_maxDegreeAtMost h.maxDegreeAtMost

/-- Seed-graph package from the `lemmae.md` replacement strategy.

The `+ 3` spelling avoids truncated subtraction and leaves room for the two reconnection edges
used in the deterministic gluing step.  The constant is the modified value from
`lemmaeupdate.md`. -/
def SeedGraph (d n₀ : ℕ) (G : SimpleGraph (Fin n₀)) : Prop :=
  G.CliqueFree 3 ∧
    (∀ v : Fin n₀, (G.neighborSet v).ncard + 3 ≤ d) ∧
      (G.indepNum : ℝ) ≤ 14 * (n₀ : ℝ) * Real.log (d : ℝ) / (d : ℝ)

namespace SeedCounting

/-- Edge slots of the complete graph on `Fin N`. -/
def Slot (N : ℕ) : Type :=
  {p : Fin N × Fin N // p.1 < p.2}

instance (N : ℕ) : Fintype (Slot N) := by
  unfold Slot
  infer_instance

instance (N : ℕ) : DecidableEq (Slot N) := by
  unfold Slot
  infer_instance

/-- Sample space: a label in `Fin q` on every edge slot. -/
abbrev Sample (N q : ℕ) :=
  Slot N → Fin q

/-- The graph associated to a sample; an edge is present when its slot has label zero. -/
def graphOf {N q : ℕ} (hq : 0 < q) (ω : Sample N q) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun u v => ∃ h : u < v, ω ⟨(u, v), h⟩ = ⟨0, hq⟩

lemma graphOf_adj {N q : ℕ} (hq : 0 < q) (ω : Sample N q) (u v : Fin N) :
    (graphOf hq ω).Adj u v ↔
      u ≠ v ∧
        ((∃ h : u < v, ω ⟨(u, v), h⟩ = ⟨0, hq⟩) ∨
          ∃ h : v < u, ω ⟨(v, u), h⟩ = ⟨0, hq⟩) := by
  simp [graphOf, SimpleGraph.fromRel_adj]

/-- The slot determined by a distinct unordered pair, stored in increasing order. -/
def slotOf {N : ℕ} (u v : Fin N) (h : u ≠ v) : Slot N :=
  if huv : u < v then ⟨(u, v), huv⟩
  else ⟨(v, u), lt_of_le_of_ne (not_lt.mp huv) h.symm⟩

@[simp] lemma slotOf_of_lt {N : ℕ} {u v : Fin N} (h : u ≠ v) (huv : u < v) :
    slotOf u v h = ⟨(u, v), huv⟩ := by
  simp [slotOf, huv]

@[simp] lemma slotOf_of_gt {N : ℕ} {u v : Fin N} (h : u ≠ v) (hvu : v < u) :
    slotOf u v h = ⟨(v, u), hvu⟩ := by
  have huv : ¬ u < v := not_lt_of_ge hvu.le
  simp [slotOf, huv]

lemma graphOf_adj_iff_slot {N q : ℕ} (hq : 0 < q) (ω : Sample N q)
    {u v : Fin N} (h : u ≠ v) :
    (graphOf hq ω).Adj u v ↔ ω (slotOf u v h) = ⟨0, hq⟩ := by
  by_cases huv : u < v
  · rw [graphOf_adj hq ω u v, slotOf_of_lt h huv]
    constructor
    · rintro ⟨_, ⟨h', hz⟩ | ⟨hvu, _⟩⟩
      · simpa using hz
      · exact False.elim ((not_lt_of_ge huv.le) hvu)
    · intro hz
      exact ⟨h, Or.inl ⟨huv, hz⟩⟩
  · have hvu : v < u := lt_of_le_of_ne (not_lt.mp huv) h.symm
    rw [graphOf_adj hq ω u v, slotOf_of_gt h hvu]
    constructor
    · rintro ⟨_, ⟨huv', _⟩ | ⟨h', hz⟩⟩
      · exact False.elim (huv huv')
      · simpa using hz
    · intro hz
      exact ⟨h, Or.inr ⟨hvu, hz⟩⟩

@[simp] lemma card_sample (N q : ℕ) :
    Fintype.card (Sample N q) = q ^ Fintype.card (Slot N) := by
  classical
  simp [Sample, Fintype.card_fin]

/-- Witness for a vertex having at least `d - 3` zero-labelled incident slots. -/
def HighDegWitness (N d : ℕ) : Type :=
  {x : Fin N × Finset (Fin N) // x.2.card = d - 3 ∧ x.1 ∉ x.2}

instance (N d : ℕ) : Fintype (HighDegWitness N d) := by
  unfold HighDegWitness
  infer_instance

instance (N d : ℕ) : DecidableEq (HighDegWitness N d) := by
  unfold HighDegWitness
  infer_instance

/-- Count high-degree witnesses directly, avoiding a separate high-degree deletion step. -/
noncomputable def highDegWitnessCount {N q : ℕ} (hq : 0 < q) (d : ℕ)
    (ω : Sample N q) : ℕ := by
  classical
  exact (Finset.univ.filter fun W : HighDegWitness N d =>
    ∀ (t : Fin N) (ht : t ∈ W.1.2),
      ω (slotOf W.1.1 t (by
        intro h
        exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩).card

lemma slotOf_fixed_left_injective {N : ℕ} {v : Fin N} {s : Finset (Fin N)}
    (hv : v ∉ s) :
    Function.Injective fun t : {x // x ∈ s} =>
      slotOf v t.1 (by intro h; exact hv (by simp [h])) := by
  intro a b hslot
  by_cases hva : v < a.1
  · by_cases hvb : v < b.1
    · have hpair : (v, a.1) = (v, b.1) := by
        simpa [slotOf, hva, hvb] using congrArg (fun e : Slot N => e.1) hslot
      exact Subtype.ext (congrArg Prod.snd hpair)
    · have hpair : (v, a.1) = (b.1, v) := by
        simpa [slotOf, hva, hvb] using congrArg (fun e : Slot N => e.1) hslot
      have hv_eq_b : v = b.1 := congrArg Prod.fst hpair
      exact False.elim (hv (by simpa [← hv_eq_b] using b.2))
  · by_cases hvb : v < b.1
    · have hpair : (a.1, v) = (v, b.1) := by
        simpa [slotOf, hva, hvb] using congrArg (fun e : Slot N => e.1) hslot
      have ha_eq_v : a.1 = v := congrArg Prod.fst hpair
      exact False.elim (hv (by simpa [ha_eq_v] using a.2))
    · have hpair : (a.1, v) = (b.1, v) := by
        simpa [slotOf, hva, hvb] using congrArg (fun e : Slot N => e.1) hslot
      exact Subtype.ext (congrArg Prod.fst hpair)

/-- The forced-zero slots associated to a high-degree witness. -/
def highDegWitnessSlots {N d : ℕ} (W : HighDegWitness N d) : Finset (Slot N) :=
  W.1.2.attach.map
    ⟨fun t => slotOf W.1.1 t.1 (by
        intro h
        exact W.2.2 (by simp [h])),
      slotOf_fixed_left_injective W.2.2⟩

@[simp] lemma card_highDegWitnessSlots {N d : ℕ} (W : HighDegWitness N d) :
    (highDegWitnessSlots W).card = d - 3 := by
  simp [highDegWitnessSlots, W.2.1]

lemma highDegWitnessSlots_forall_zero_iff {N q d : ℕ} (hq : 0 < q)
    (ω : Sample N q) (W : HighDegWitness N d) :
    (∀ e, e ∈ highDegWitnessSlots W → ω e = ⟨0, hq⟩) ↔
      ∀ (t : Fin N) (ht : t ∈ W.1.2),
        ω (slotOf W.1.1 t (by
          intro h
          exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩ := by
  constructor
  · intro h t ht
    exact h _ (Finset.mem_map.mpr ⟨⟨t, ht⟩, by simp, by apply Subtype.ext; rfl⟩)
  · intro h e he
    rcases Finset.mem_map.mp he with ⟨t, _ht, hte⟩
    rw [← hte]
    exact h t.1 t.2

lemma highDegWitnessCount_eq_zero_iff {N q : ℕ} (hq : 0 < q) (d : ℕ)
    (ω : Sample N q) :
    highDegWitnessCount hq d ω = 0 ↔
      ∀ W : HighDegWitness N d,
        ¬ (∀ (t : Fin N) (ht : t ∈ W.1.2),
          ω (slotOf W.1.1 t (by
            intro h
            exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩) := by
  classical
  simp [highDegWitnessCount]

lemma degree_add_three_le_of_highDegWitnessCount_eq_zero {N q d : ℕ} (hq : 0 < q)
    (ω : Sample N q) (hd : 3 ≤ d) (hzero : highDegWitnessCount hq d ω = 0) :
    ∀ v : Fin N, ((graphOf hq ω).neighborSet v).ncard + 3 ≤ d := by
  classical
  intro v
  by_contra hnot
  let S := ((graphOf hq ω).neighborSet v).toFinset
  have hScard : S.card = ((graphOf hq ω).neighborSet v).ncard := by
    calc
      S.card = Fintype.card ((graphOf hq ω).neighborSet v) := by
        simp [S]
      _ = ((graphOf hq ω).neighborSet v).ncard := by
        rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hle : d - 3 ≤ S.card := by
    omega
  rcases Finset.exists_subset_card_eq (s := S) (n := d - 3) hle with ⟨T, hTS, hTcard⟩
  have hvnot : v ∉ T := by
    intro hvT
    have hvS : v ∈ S := hTS hvT
    have hvadj : (graphOf hq ω).Adj v v := by
      simp [S] at hvS
    exact (graphOf hq ω).irrefl hvadj
  let W : HighDegWitness N d := ⟨(v, T), hTcard, hvnot⟩
  have hpred :
      ∀ (t : Fin N) (ht : t ∈ W.1.2),
        ω (slotOf W.1.1 t (by
          intro h
          exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩ := by
    intro t ht
    have htT : t ∈ T := ht
    have htS : t ∈ S := hTS htT
    have hadj : (graphOf hq ω).Adj v t := by
      simpa [S] using htS
    have hvne : v ≠ t := (graphOf_adj hq ω v t).1 hadj |>.1
    simpa [W] using (graphOf_adj_iff_slot hq ω hvne).1 hadj
  exact ((highDegWitnessCount_eq_zero_iff hq d ω).1 hzero W) hpred

/-- Witness for an independent set of a prescribed cardinality. -/
def IndepWitness (N k : ℕ) : Type :=
  {A : Finset (Fin N) // A.card = k}

instance (N k : ℕ) : Fintype (IndepWitness N k) := by
  unfold IndepWitness
  infer_instance

instance (N k : ℕ) : DecidableEq (IndepWitness N k) := by
  unfold IndepWitness
  infer_instance

/-- Count `k`-sets whose internal slots are all nonzero. -/
noncomputable def indepWitnessCount {N q : ℕ} (hq : 0 < q) (k : ℕ)
    (ω : Sample N q) : ℕ := by
  classical
  exact (Finset.univ.filter fun A : IndepWitness N k =>
    ∀ (u : Fin N), u ∈ A.1 → ∀ (v : Fin N), v ∈ A.1 → ∀ h : u ≠ v,
      ω (slotOf u v h) ≠ ⟨0, hq⟩).card

lemma card_offDiag_filter_lt_fin {N : ℕ} (s : Finset (Fin N)) :
    (s.offDiag.filter fun p : Fin N × Fin N => p.1 < p.2).card = s.card.choose 2 := by
  classical
  rw [← Sym2.card_image_offDiag s]
  refine Finset.card_bij (s := s.offDiag.filter fun p : Fin N × Fin N => p.1 < p.2)
    (t := s.offDiag.image (Function.uncurry Sym2.mk))
    (fun p _ => s(p.1, p.2)) ?hi ?hinj ?hsurj
  · intro p hp
    exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩
  · intro p hp q hq hsym
    have hplt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hqlt : q.1 < q.2 := (Finset.mem_filter.mp hq).2
    rw [Sym2.eq_iff] at hsym
    rcases hsym with hpq | hpq
    · exact Prod.ext hpq.1 hpq.2
    · have : q.2 < q.1 := by simpa [hpq.1, hpq.2] using hplt
      exact False.elim ((not_lt_of_ge hqlt.le) this)
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    by_cases hlt : p.1 < p.2
    · exact ⟨p, Finset.mem_filter.mpr ⟨hp, hlt⟩, rfl⟩
    · have hgt : p.2 < p.1 := lt_of_le_of_ne (not_lt.mp hlt) hpne.symm
      refine ⟨(p.2, p.1), Finset.mem_filter.mpr ?_, ?_⟩
      · exact ⟨Finset.mem_offDiag.mpr ⟨(Finset.mem_offDiag.mp hp).2.1,
          (Finset.mem_offDiag.mp hp).1, hpne.symm⟩, hgt⟩
      · exact Sym2.eq_swap

/-- The unordered internal slots of an independent-set witness, represented by ordered pairs
`u < v`. -/

lemma card_slot (N : ℕ) :
    Fintype.card (Slot N) = N.choose 2 := by
  classical
  rw [show Fintype.card (Slot N) =
      ((Finset.univ : Finset (Fin N × Fin N)).filter fun p => p.1 < p.2).card by
    simp [Slot, Fintype.card_subtype]]
  rw [show ((Finset.univ : Finset (Fin N × Fin N)).filter fun p => p.1 < p.2) =
      ((Finset.univ : Finset (Fin N)).offDiag.filter fun p : Fin N × Fin N => p.1 < p.2) by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hp
      exact ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, ne_of_lt hp⟩, hp⟩
    · intro hp
      exact hp.2]
  simpa using card_offDiag_filter_lt_fin (Finset.univ : Finset (Fin N))

def indepWitnessSlots {N k : ℕ} (A : IndepWitness N k) : Finset (Slot N) :=
  (A.1.offDiag.filter fun p : Fin N × Fin N => p.1 < p.2).attach.map
    ⟨fun p => (⟨p.1, by simpa using (Finset.mem_filter.mp p.2).2⟩ : Slot N),
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun e : Slot N => e.1) hpq⟩

@[simp] lemma card_indepWitnessSlots {N k : ℕ} (A : IndepWitness N k) :
    (indepWitnessSlots A).card =
      (A.1.offDiag.filter fun p : Fin N × Fin N => p.1 < p.2).card := by
  simp [indepWitnessSlots]

lemma card_indepWitnessSlots_choose {N k : ℕ} (A : IndepWitness N k) :
    (indepWitnessSlots A).card = k.choose 2 := by
  rw [card_indepWitnessSlots, card_offDiag_filter_lt_fin]
  simp

lemma indepWitnessSlots_forall_nonzero_iff {N q k : ℕ} (hq : 0 < q)
    (ω : Sample N q) (A : IndepWitness N k) :
    (∀ e, e ∈ indepWitnessSlots A → ω e ≠ ⟨0, hq⟩) ↔
      ∀ (u : Fin N), u ∈ A.1 → ∀ (v : Fin N), v ∈ A.1 → ∀ h : u ≠ v,
        ω (slotOf u v h) ≠ ⟨0, hq⟩ := by
  constructor
  · intro h u hu v hv huv
    by_cases huvlt : u < v
    · have hmem : (⟨(u, v), huvlt⟩ : Slot N) ∈ indepWitnessSlots A := by
        refine Finset.mem_map.mpr ⟨⟨(u, v), ?_⟩, by simp, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hu, hv, huv⟩, huvlt⟩
      simpa [slotOf_of_lt huv huvlt] using h _ hmem
    · have hvult : v < u := lt_of_le_of_ne (not_lt.mp huvlt) huv.symm
      have hmem : (⟨(v, u), hvult⟩ : Slot N) ∈ indepWitnessSlots A := by
        refine Finset.mem_map.mpr ⟨⟨(v, u), ?_⟩, by simp, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hv, hu, huv.symm⟩, hvult⟩
      simpa [slotOf_of_gt huv hvult] using h _ hmem
  · intro h e he
    rcases Finset.mem_map.mp he with ⟨p, _hp, hpe⟩
    rcases p with ⟨⟨u, v⟩, hp⟩
    have hp' := Finset.mem_filter.mp hp
    have hu : u ∈ A.1 := (Finset.mem_offDiag.mp hp'.1).1
    have hv : v ∈ A.1 := (Finset.mem_offDiag.mp hp'.1).2.1
    have huvne : u ≠ v := (Finset.mem_offDiag.mp hp'.1).2.2
    have huvlt : u < v := hp'.2
    rw [← hpe]
    simpa [slotOf_of_lt huvne huvlt] using h u hu v hv huvne

lemma indepWitnessCount_eq_zero_iff {N q : ℕ} (hq : 0 < q) (k : ℕ)
    (ω : Sample N q) :
    indepWitnessCount hq k ω = 0 ↔
      ∀ A : IndepWitness N k,
        ¬ (∀ (u : Fin N), u ∈ A.1 → ∀ (v : Fin N), v ∈ A.1 → ∀ h : u ≠ v,
          ω (slotOf u v h) ≠ ⟨0, hq⟩) := by
  classical
  simp [indepWitnessCount]

lemma indepNum_lt_of_indepWitnessCount_eq_zero {N q k : ℕ} (hq : 0 < q)
    (ω : Sample N q) (hzero : indepWitnessCount hq k ω = 0) :
    (graphOf hq ω).indepNum < k := by
  classical
  by_contra hnot
  have hk : k ≤ (graphOf hq ω).indepNum := le_of_not_gt hnot
  rcases (graphOf hq ω).exists_isNIndepSet_indepNum with ⟨s, hs⟩
  rcases Finset.exists_subset_card_eq (s := s) (n := k) (by simpa [hs.card_eq] using hk) with
    ⟨t, hts, htcard⟩
  let A : IndepWitness N k := ⟨t, htcard⟩
  have hpred :
      ∀ (u : Fin N), u ∈ A.1 → ∀ (v : Fin N), v ∈ A.1 → ∀ h : u ≠ v,
        ω (slotOf u v h) ≠ ⟨0, hq⟩ := by
    intro u hu v hv huv hslot
    have hadj : (graphOf hq ω).Adj u v := (graphOf_adj_iff_slot hq ω huv).2 hslot
    exact hs.isIndepSet (hts hu) (hts hv) huv hadj
  exact ((indepWitnessCount_eq_zero_iff hq k ω).1 hzero A) hpred

/-- Ordered triangle witness `u < v < w`. -/
def TriangleWitness (N : ℕ) : Type :=
  {p : Fin N × Fin N × Fin N // p.1 < p.2.1 ∧ p.2.1 < p.2.2}

instance (N : ℕ) : Fintype (TriangleWitness N) := by
  unfold TriangleWitness
  infer_instance

instance (N : ℕ) : DecidableEq (TriangleWitness N) := by
  unfold TriangleWitness
  infer_instance

lemma card_triangleWitness_le_cube (N : ℕ) :
    Fintype.card (TriangleWitness N) ≤ N ^ 3 := by
  calc
    Fintype.card (TriangleWitness N) ≤ Fintype.card (Fin N × Fin N × Fin N) :=
      Fintype.card_subtype_le _
    _ = N ^ 3 := by
      simp [Fintype.card_prod, Fintype.card_fin, pow_succ, mul_assoc]

/-- Count labelled triangles directly as ordered triples `u < v < w`. -/
noncomputable def triangleCount {N q : ℕ} (hq : 0 < q) (ω : Sample N q) : ℕ := by
  classical
  exact (Finset.univ.filter fun T : TriangleWitness N =>
    ω ⟨(T.1.1, T.1.2.1), T.2.1⟩ = ⟨0, hq⟩ ∧
      ω ⟨(T.1.2.1, T.1.2.2), T.2.2⟩ = ⟨0, hq⟩ ∧
        ω ⟨(T.1.1, T.1.2.2), T.2.1.trans T.2.2⟩ = ⟨0, hq⟩).card

lemma triangleCount_eq_zero_iff {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    triangleCount hq ω = 0 ↔
      ∀ T : TriangleWitness N,
        ¬ (ω ⟨(T.1.1, T.1.2.1), T.2.1⟩ = ⟨0, hq⟩ ∧
          ω ⟨(T.1.2.1, T.1.2.2), T.2.2⟩ = ⟨0, hq⟩ ∧
            ω ⟨(T.1.1, T.1.2.2), T.2.1.trans T.2.2⟩ = ⟨0, hq⟩) := by
  classical
  simp [triangleCount]

/-- The three slots supporting an ordered triangle witness. -/
def triangleSlots {N : ℕ} (T : TriangleWitness N) : Finset (Slot N) :=
  {⟨(T.1.1, T.1.2.1), T.2.1⟩,
    ⟨(T.1.2.1, T.1.2.2), T.2.2⟩,
    ⟨(T.1.1, T.1.2.2), T.2.1.trans T.2.2⟩}

@[simp] lemma card_triangleSlots {N : ℕ} (T : TriangleWitness N) :
    (triangleSlots T).card = 3 := by
  rcases T with ⟨⟨u, v, w⟩, huv, hvw⟩
  have hnot12_23 :
      (⟨(u, v), huv⟩ : Slot N) ≠ ⟨(v, w), hvw⟩ := by
    intro h
    have huv_eq : u = v := by simpa using congrArg (fun e : Slot N => e.1.1) h
    exact (ne_of_lt huv) huv_eq
  have hnot12_13 :
      (⟨(u, v), huv⟩ : Slot N) ≠ ⟨(u, w), huv.trans hvw⟩ := by
    intro h
    have hvw_eq : v = w := by simpa using congrArg (fun e : Slot N => e.1.2) h
    exact (ne_of_lt hvw) hvw_eq
  have hnot23_13 :
      (⟨(v, w), hvw⟩ : Slot N) ≠ ⟨(u, w), huv.trans hvw⟩ := by
    intro h
    have hvu_eq : v = u := by simpa using congrArg (fun e : Slot N => e.1.1) h
    exact (ne_of_gt huv) hvu_eq
  simp [triangleSlots, hnot12_23, hnot12_13, hnot23_13,     ]

lemma triangleSlots_forall_zero_iff {N q : ℕ} (hq : 0 < q) (ω : Sample N q)
    (T : TriangleWitness N) :
    (∀ e, e ∈ triangleSlots T → ω e = ⟨0, hq⟩) ↔
      ω ⟨(T.1.1, T.1.2.1), T.2.1⟩ = ⟨0, hq⟩ ∧
        ω ⟨(T.1.2.1, T.1.2.2), T.2.2⟩ = ⟨0, hq⟩ ∧
          ω ⟨(T.1.1, T.1.2.2), T.2.1.trans T.2.2⟩ = ⟨0, hq⟩ := by
  simp [triangleSlots]

/-- A graph on any finite vertex type satisfying the modified seed bounds. -/
def SeedGraphOn (d : ℕ) {V : Type*} [Finite V] (G : SimpleGraph V) : Prop :=
  G.CliqueFree 3 ∧
    (∀ v : V, (G.neighborSet v).ncard + 3 ≤ d) ∧
      (G.indepNum : ℝ) ≤ 14 * (Nat.card V : ℝ) * Real.log (d : ℝ) / (d : ℝ)

lemma isIndepSet_image_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {s : Set V} (hs : G.IsIndepSet s) :
    H.IsIndepSet (φ '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne hadj
  exact hs ha hb (fun h => hne (by simp [h])) (φ.map_rel_iff.1 hadj)

lemma isNIndepSet_map_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {n : ℕ} {s : Finset V} (hs : G.IsNIndepSet n s) :
    H.IsNIndepSet n (s.map φ.toEquiv.toEmbedding) := by
  refine ⟨?_, ?_⟩
  · simpa [Finset.coe_map] using isIndepSet_image_of_iso φ hs.isIndepSet
  · simpa using (Finset.card_map φ.toEquiv.toEmbedding).trans hs.card_eq

lemma isIndepSet_image_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ↪g H) {s : Set V} (hs : G.IsIndepSet s) :
    H.IsIndepSet (φ '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne hadj
  exact hs ha hb (fun h => hne (by simp [h])) (φ.map_rel_iff.1 hadj)

lemma isNIndepSet_map_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ↪g H) {n : ℕ} {s : Finset V} (hs : G.IsNIndepSet n s) :
    H.IsNIndepSet n (s.map φ.toEmbedding) := by
  refine ⟨?_, ?_⟩
  · simpa [Finset.coe_map] using isIndepSet_image_of_embedding φ hs.isIndepSet
  · simpa using (Finset.card_map φ.toEmbedding).trans hs.card_eq

lemma indepNum_le_of_embedding {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ↪g H) :
    G.indepNum ≤ H.indepNum := by
  classical
  rcases G.exists_isNIndepSet_indepNum with ⟨s, hs⟩
  have hle := (isNIndepSet_map_of_embedding φ hs).isIndepSet.card_le_indepNum
  simpa [hs.card_eq] using hle

lemma indepNum_induce_le {V : Type*} [Finite V] (G : SimpleGraph V) (s : Set V) :
    (G.induce s).indepNum ≤ G.indepNum := by
  exact indepNum_le_of_embedding (SimpleGraph.Embedding.induce (G := G) s)

lemma indepNum_eq_of_iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) :
    G.indepNum = H.indepNum := by
  classical
  apply le_antisymm
  · rcases G.exists_isNIndepSet_indepNum with ⟨s, hs⟩
    have hle := (isNIndepSet_map_of_iso φ hs).isIndepSet.card_le_indepNum
    simpa [hs.card_eq] using hle
  · rcases H.exists_isNIndepSet_indepNum with ⟨s, hs⟩
    have hle := (isNIndepSet_map_of_iso φ.symm hs).isIndepSet.card_le_indepNum
    simpa [hs.card_eq] using hle

lemma neighborSet_ncard_eq_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (v : V) :
    (H.neighborSet (φ v)).ncard = (G.neighborSet v).ncard := by
  have himage : φ '' G.neighborSet v = H.neighborSet (φ v) := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact φ.map_rel_iff.2 hu
    · intro hw
      refine ⟨φ.symm w, ?_, by simp⟩
      exact φ.map_rel_iff.1 (by simpa using hw)
  rw [← himage]
  simpa using (Set.ncard_image_of_injective (G.neighborSet v) φ.toEquiv.injective)

lemma neighborSet_ncard_induce_le {V : Type*} [Finite V] (G : SimpleGraph V) (s : Set V)
    (v : s) :
    ((G.induce s).neighborSet v).ncard ≤ (G.neighborSet v.1).ncard := by
  exact Set.ncard_le_ncard_of_injOn (fun x : s => (x : V))
    (fun x hx => by simpa using hx)
    (by intro a _ b _ h; exact Subtype.ext h)

/-- Host-graph package on an arbitrary finite vertex type. -/
def HostGraphOn (d : ℕ) {V : Type*} [Finite V] (H : SimpleGraph V) : Prop :=
  H.Connected ∧
    H.CliqueFree 3 ∧
      (∀ v : V, (H.neighborSet v).ncard ≤ d) ∧
        (H.indepNum : ℝ) ≤ 15 * (Nat.card V : ℝ) * Real.log (d : ℝ) / (d : ℝ)

lemma connected_iff_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) : G.Connected ↔ H.Connected := by
  constructor
  · intro hG
    refine { preconnected := ?_, nonempty := ?_ }
    · intro x y
      obtain ⟨x', rfl⟩ := φ.toEquiv.surjective x
      obtain ⟨y', rfl⟩ := φ.toEquiv.surjective y
      exact (hG.preconnected x' y').map φ.toHom
    · exact hG.nonempty.map φ
  · intro hH
    refine { preconnected := ?_, nonempty := ?_ }
    · intro x y
      have h := hH.preconnected (φ x) (φ y)
      simpa using h.map φ.symm.toHom
    · exact hH.nonempty.map φ.symm

lemma hostGraph_of_hostGraphOn {d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    {H : SimpleGraph V} (hH : HostGraphOn d H) :
    ∃ K : SimpleGraph (Fin (Fintype.card V)), HostGraph d (Fintype.card V) K := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let K : SimpleGraph (Fin (Fintype.card V)) := H.map e.toEmbedding
  let φ : H ≃g K := SimpleGraph.Iso.map e H
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · exact (connected_iff_of_iso φ).1 hH.1
  · simpa [K] using (SimpleGraph.cliqueFree_map_iff (G := H) (f := e.toEmbedding)).2 hH.2.1
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    have hn := hH.2.2.1 u
    rw [← neighborSet_ncard_eq_of_iso φ u] at hn
    have hφu : φ u = e u := rfl
    simpa [K, hφu] using hn
  · have hi := hH.2.2.2
    rw [Nat.card_eq_fintype_card] at hi
    rw [← indepNum_eq_of_iso φ]
    simpa [K, hostC] using hi

lemma seedGraph_of_seedGraphOn {d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hG : SeedGraphOn d G) :
    ∃ H : SimpleGraph (Fin (Fintype.card V)), SeedGraph d (Fintype.card V) H := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let H : SimpleGraph (Fin (Fintype.card V)) := G.map e.toEmbedding
  let φ : G ≃g H := SimpleGraph.Iso.map e G
  refine ⟨H, ?_, ?_, ?_⟩
  · simpa [H] using (SimpleGraph.cliqueFree_map_iff (G := G) (f := e.toEmbedding)).2 hG.1
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    have hn := hG.2.1 u
    rw [← neighborSet_ncard_eq_of_iso φ u] at hn
    have hφu : φ u = e u := rfl
    simpa [H, hφu] using hn
  · have hi := hG.2.2
    rw [Nat.card_eq_fintype_card] at hi
    rw [← indepNum_eq_of_iso φ]
    simpa [H] using hi

/-- Markov's inequality for finite counting with natural-valued functions. -/
lemma card_filter_mul_le_sum_of_le {α : Type*} [Fintype α] (f : α → ℕ) (a : ℕ) :
    (Finset.univ.filter fun x : α => a ≤ f x).card * a ≤ ∑ x, f x := by
  classical
  calc
    (Finset.univ.filter fun x : α => a ≤ f x).card * a
        = ∑ x ∈ Finset.univ.filter (fun x : α => a ≤ f x), a := by
          simp [Finset.sum_const, mul_comm]
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x : α => a ≤ f x), f x := by
          exact Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x, f x := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (by intro x _ _; exact Nat.zero_le _)

/-- Functions with prescribed values on `s` are equivalent to arbitrary functions on the
complement of `s`. -/
def fixedOnEquiv {ι γ : Type*} [DecidableEq ι] (s : Finset ι) (a : γ) :
    {f : ι → γ // ∀ i, i ∈ s → f i = a} ≃ ({i : ι // i ∉ s} → γ) where
  toFun f i := f.1 i.1
  invFun g :=
    ⟨fun i => if h : i ∈ s then a else g ⟨i, h⟩, by
      intro i hi
      simp [hi]
    ⟩
  left_inv f := by
    ext i
    by_cases hi : i ∈ s
    · simp [hi, f.2 i hi]
    · simp [hi]
  right_inv g := by
    ext i
    simp [i.2]

/-- Count functions with a fixed value on a finite set of coordinates. -/
lemma card_filter_forall_eq {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    [DecidableEq γ] (s : Finset ι) (a : γ) :
    (Finset.univ.filter fun f : ι → γ => ∀ i, i ∈ s → f i = a).card =
      Fintype.card γ ^ (Fintype.card ι - s.card) := by
  classical
  rw [← Fintype.card_subtype (fun f : ι → γ => ∀ i, i ∈ s → f i = a)]
  rw [Fintype.card_congr (fixedOnEquiv s a)]
  rw [Fintype.card_pi]
  have hcomp : Fintype.card {i : ι // i ∉ s} = Fintype.card ι - s.card := by
    rw [Fintype.card_subtype (fun i : ι => i ∉ s)]
    have hfilter : (Finset.univ.filter fun i : ι => i ∉ s) = sᶜ := by
      ext i
      simp
    rw [hfilter, Finset.card_compl]
  simp [hcomp]

/-- Count samples whose labels are forced to zero on a chosen slot set. -/
lemma card_forced_zero {N q : ℕ} (hq : 0 < q) (Z : Finset (Slot N)) :
    (Finset.univ.filter fun ω : Sample N q =>
        ∀ e, e ∈ Z → ω e = ⟨0, hq⟩).card =
      q ^ (Fintype.card (Slot N) - Z.card) := by
  simpa [Sample, Fintype.card_fin] using
    (card_filter_forall_eq (ι := Slot N) (γ := Fin q) Z ⟨0, hq⟩)

lemma card_highDegWitness_forced_zero {N q d : ℕ} (hq : 0 < q)
    (W : HighDegWitness N d) :
    (Finset.univ.filter fun ω : Sample N q =>
      ∀ (t : Fin N) (ht : t ∈ W.1.2),
        ω (slotOf W.1.1 t (by
          intro h
          exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩).card =
      q ^ (Fintype.card (Slot N) - (d - 3)) := by
  calc
    (Finset.univ.filter fun ω : Sample N q =>
      ∀ (t : Fin N) (ht : t ∈ W.1.2),
        ω (slotOf W.1.1 t (by
          intro h
          exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩).card
        = q ^ (Fintype.card (Slot N) - (highDegWitnessSlots W).card) := by
          convert card_forced_zero hq (highDegWitnessSlots W) using 2
          ext ω
          simpa using (highDegWitnessSlots_forall_zero_iff hq ω W).symm
    _ = q ^ (Fintype.card (Slot N) - (d - 3)) := by
          simp [card_highDegWitnessSlots W]

lemma sum_highDegWitnessCount {N q d : ℕ} (hq : 0 < q) :
    (∑ ω : Sample N q, highDegWitnessCount hq d ω) =
      Fintype.card (HighDegWitness N d) * q ^ (Fintype.card (Slot N) - (d - 3)) := by
  classical
  simp_rw [highDegWitnessCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  simp [card_highDegWitness_forced_zero hq, Finset.sum_const]

lemma card_triangle_forced_zero {N q : ℕ} (hq : 0 < q) (T : TriangleWitness N) :
    (Finset.univ.filter fun ω : Sample N q =>
      ω ⟨(T.1.1, T.1.2.1), T.2.1⟩ = ⟨0, hq⟩ ∧
        ω ⟨(T.1.2.1, T.1.2.2), T.2.2⟩ = ⟨0, hq⟩ ∧
          ω ⟨(T.1.1, T.1.2.2), T.2.1.trans T.2.2⟩ = ⟨0, hq⟩).card =
      q ^ (Fintype.card (Slot N) - 3) := by
  rw [← card_triangleSlots T]
  convert card_forced_zero hq (triangleSlots T) using 2
  ext ω
  simpa using (triangleSlots_forall_zero_iff hq ω T).symm

lemma sum_triangleCount {N q : ℕ} (hq : 0 < q) :
    (∑ ω : Sample N q, triangleCount hq ω) =
      Fintype.card (TriangleWitness N) * q ^ (Fintype.card (Slot N) - 3) := by
  classical
  simp_rw [triangleCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  simp [card_triangle_forced_zero hq, Finset.sum_const]

/-- Functions avoiding a prescribed value on `s` split into nonzero choices on `s` and arbitrary
choices off `s`. -/
def avoidOnEquiv {ι γ : Type*} [DecidableEq ι] [DecidableEq γ] (s : Finset ι) (a : γ) :
    {f : ι → γ // ∀ i, i ∈ s → f i ≠ a} ≃
      (({i : ι // i ∈ s} → {x : γ // x ≠ a}) × ({i : ι // i ∉ s} → γ)) where
  toFun f :=
    (fun i => ⟨f.1 i.1, f.2 i.1 i.2⟩, fun i => f.1 i.1)
  invFun g :=
    ⟨fun i => if h : i ∈ s then (g.1 ⟨i, h⟩).1 else g.2 ⟨i, h⟩, by
      intro i hi
      simp [hi, (g.1 ⟨i, hi⟩).2]
    ⟩
  left_inv f := by
    ext i
    by_cases hi : i ∈ s
    · simp [hi]
    · simp [hi]
  right_inv g := by
    rcases g with ⟨gS, gC⟩
    ext i <;> simp [i.2]

/-- Count functions avoiding a fixed value on a finite set of coordinates. -/
lemma card_filter_forall_ne {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    [DecidableEq γ] (s : Finset ι) (a : γ) :
    (Finset.univ.filter fun f : ι → γ => ∀ i, i ∈ s → f i ≠ a).card =
      (Fintype.card γ - 1) ^ s.card * Fintype.card γ ^ (Fintype.card ι - s.card) := by
  classical
  rw [← Fintype.card_subtype (fun f : ι → γ => ∀ i, i ∈ s → f i ≠ a)]
  rw [Fintype.card_congr (avoidOnEquiv s a)]
  rw [Fintype.card_prod]
  rw [Fintype.card_pi, Fintype.card_pi]
  have hS : Fintype.card {i : ι // i ∈ s} = s.card := by
    rw [Fintype.card_subtype (fun i : ι => i ∈ s)]
    have hfilter : (Finset.univ.filter fun i : ι => i ∈ s) = s := by
      ext i
      simp
    rw [hfilter]
  have hC : Fintype.card {i : ι // i ∉ s} = Fintype.card ι - s.card := by
    rw [Fintype.card_subtype (fun i : ι => i ∉ s)]
    have hfilter : (Finset.univ.filter fun i : ι => i ∉ s) = sᶜ := by
      ext i
      simp
    rw [hfilter, Finset.card_compl]
  have hne : Fintype.card {x : γ // x ≠ a} = Fintype.card γ - 1 := by
    have hcompl := Fintype.card_subtype_compl (fun x : γ => x = a)
    have heq : Fintype.card {x : γ // x = a} = 1 := Fintype.card_subtype_eq a
    simp []
  simp [hC, hne]

/-- Count samples where a chosen slot set is forced to avoid zero. -/
lemma card_forced_nonzero {N q : ℕ} (hq : 0 < q) (T : Finset (Slot N)) :
    (Finset.univ.filter fun ω : Sample N q =>
        ∀ e, e ∈ T → ω e ≠ ⟨0, hq⟩).card =
      (q - 1) ^ T.card * q ^ (Fintype.card (Slot N) - T.card) := by
  simpa [Sample, Fintype.card_fin] using
    (card_filter_forall_ne (ι := Slot N) (γ := Fin q) T ⟨0, hq⟩)

/-- Count samples with a prescribed zero/nonzero pattern on a finite slot set. -/
lemma card_indepWitness_forced_nonzero {N q k : ℕ} (hq : 0 < q)
    (A : IndepWitness N k) :
    (Finset.univ.filter fun ω : Sample N q =>
      ∀ (u : Fin N), u ∈ A.1 → ∀ (v : Fin N), v ∈ A.1 → ∀ h : u ≠ v,
        ω (slotOf u v h) ≠ ⟨0, hq⟩).card =
      (q - 1) ^ (indepWitnessSlots A).card *
        q ^ (Fintype.card (Slot N) - (indepWitnessSlots A).card) := by
  convert card_forced_nonzero hq (indepWitnessSlots A) using 2
  ext ω
  simpa using (indepWitnessSlots_forall_nonzero_iff hq ω A).symm

lemma sum_indepWitnessCount {N q k : ℕ} (hq : 0 < q) :
    (∑ ω : Sample N q, indepWitnessCount hq k ω) =
      ∑ A : IndepWitness N k,
        (q - 1) ^ (indepWitnessSlots A).card *
          q ^ (Fintype.card (Slot N) - (indepWitnessSlots A).card) := by
  classical
  simp_rw [indepWitnessCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  simp [card_indepWitness_forced_nonzero hq]

lemma sum_indepWitnessCount_eq {N q k : ℕ} (hq : 0 < q) :
    (∑ ω : Sample N q, indepWitnessCount hq k ω) =
      Fintype.card (IndepWitness N k) *
        ((q - 1) ^ (k.choose 2) * q ^ (Fintype.card (Slot N) - k.choose 2)) := by
  rw [sum_indepWitnessCount]
  simp [card_offDiag_filter_lt_fin, Finset.sum_const]

lemma card_pattern {N q : ℕ} (hq : 0 < q) (T Z : Finset (Slot N)) (hZ : Z ⊆ T) :
    (Finset.univ.filter fun ω : Sample N q =>
        (∀ e, e ∈ Z → ω e = ⟨0, hq⟩) ∧
          ∀ e, e ∈ T \ Z → ω e ≠ ⟨0, hq⟩).card =
      (q - 1) ^ (T.card - Z.card) * q ^ (Fintype.card (Slot N) - T.card) := by
  classical
  let A : Finset (Slot N) := Z
  let B : Finset (Slot N) := T \ Z
  have hAunionB : A ∪ B = T := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_union.mp he with heA | heB
      · exact hZ (by simpa [A] using heA)
      · exact (Finset.mem_sdiff.mp (by simpa [B] using heB)).1
    · intro heT
      by_cases heZ : e ∈ Z
      · exact Finset.mem_union_left _ (by simpa [A] using heZ)
      · exact Finset.mem_union_right _ (by simpa [B] using ⟨heT, heZ⟩)
  rw [← Fintype.card_subtype (fun ω : Sample N q =>
      (∀ e, e ∈ Z → ω e = ⟨0, hq⟩) ∧
        ∀ e, e ∈ T \ Z → ω e ≠ ⟨0, hq⟩)]
  let patternEquiv :
      {ω : Sample N q //
        (∀ e, e ∈ Z → ω e = ⟨0, hq⟩) ∧
          ∀ e, e ∈ T \ Z → ω e ≠ ⟨0, hq⟩} ≃
        (({e : Slot N // e ∈ B} → {x : Fin q // x ≠ ⟨0, hq⟩}) ×
          ({e : Slot N // e ∉ A ∪ B} → Fin q)) :=
    { toFun := fun ω =>
        (fun e => ⟨ω.1 e.1, ω.2.2 e.1 (by simp [B])⟩,
          fun e => ω.1 e.1)
      invFun := fun g =>
        ⟨fun e =>
            if hA : e ∈ A then ⟨0, hq⟩
            else if hB : e ∈ B then (g.1 ⟨e, hB⟩).1
            else g.2 ⟨e, by simp [hA, hB]⟩,
          by
            constructor
            · intro e he
              have hA : e ∈ A := by simpa [A] using he
              simp [hA]
            · intro e he
              have hnotA : e ∉ A := by
                intro hA
                exact (Finset.mem_sdiff.mp (by simpa [B] using he)).2 (by simpa [A] using hA)
              have hB : e ∈ B := by simpa [B] using he
              simp [hnotA, hB, (g.1 ⟨e, hB⟩).2]
        ⟩
      left_inv := by
        intro ω
        ext e
        by_cases hA : e ∈ A
        · have hz : e ∈ Z := by simpa [A] using hA
          simp [hA, ω.2.1 e hz]
        · by_cases hB : e ∈ B
          · simp [hA, hB]
          · simp [hA, hB]
      right_inv := by
        intro g
        rcases g with ⟨gB, gC⟩
        apply Prod.ext
        · funext e
          have heB : e.1 ∈ T \ Z := by
            simpa only [B] using e.2
          have hnotA : e.1 ∉ A := by
            intro hA
            exact (Finset.mem_sdiff.mp heB).2 (by simpa [A] using hA)
          simp [hnotA, e.2]
        · funext e
          have hnotA : e.1 ∉ A := (Finset.notMem_union.mp e.2).1
          have hnotB : e.1 ∉ B := (Finset.notMem_union.mp e.2).2
          simp [hnotA, hnotB] }
  rw [Fintype.card_congr patternEquiv]
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
  have hBcardFinset : B.card = T.card - Z.card := by
    simpa [B] using (Finset.card_sdiff_of_subset hZ)
  have hBcard : Fintype.card {e : Slot N // e ∈ B} = T.card - Z.card := by
    rw [Fintype.card_subtype (fun e : Slot N => e ∈ B)]
    have hfilter : (Finset.univ.filter fun e : Slot N => e ∈ B) = B := by
      ext e
      simp
    rw [hfilter, hBcardFinset]
  have hCcard : Fintype.card {e : Slot N // e ∉ A ∧ e ∉ B} =
      Fintype.card (Slot N) - T.card := by
    rw [Fintype.card_subtype (fun e : Slot N => e ∉ A ∧ e ∉ B)]
    have hfilter : (Finset.univ.filter fun e : Slot N => e ∉ A ∧ e ∉ B) = (A ∪ B)ᶜ := by
      ext e
      simp
    rw [hfilter, Finset.card_compl, hAunionB]
  have hne : Fintype.card {x : Fin q // x ≠ ⟨0, hq⟩} = q - 1 := by
    have hcompl := Fintype.card_subtype_compl (fun x : Fin q => x = ⟨0, hq⟩)
    have heq : Fintype.card {x : Fin q // x = ⟨0, hq⟩} = 1 :=
      Fintype.card_subtype_eq (⟨0, hq⟩ : Fin q)
    simp [Fintype.card_fin]
  simp [hBcardFinset, hCcard, hne, Fintype.card_fin]

/-- If three bad-event sets have total cardinality below the full sample space, some point avoids
all three. -/
lemma exists_not_of_three_bad_card_sum_lt {α : Type*} [Fintype α]
    (P Q R : α → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hbad : (Finset.univ.filter P).card + (Finset.univ.filter Q).card +
        (Finset.univ.filter R).card < Fintype.card α) :
    ∃ x : α, ¬ P x ∧ ¬ Q x ∧ ¬ R x := by
  classical
  let bad := Finset.univ.filter fun x : α => P x ∨ Q x ∨ R x
  have hbad_card : bad.card < Fintype.card α := by
    have hQR : (Finset.univ.filter fun x : α => Q x ∨ R x).card ≤
        (Finset.univ.filter Q).card + (Finset.univ.filter R).card := by
      rw [Finset.filter_or]
      exact Finset.card_union_le _ _
    have hPQR : bad.card ≤ (Finset.univ.filter P).card +
        (Finset.univ.filter fun x : α => Q x ∨ R x).card := by
      dsimp [bad]
      rw [Finset.filter_or]
      exact Finset.card_union_le _ _
    omega
  have hlt_univ : bad.card < (Finset.univ : Finset α).card := by
    simpa [Finset.card_univ] using hbad_card
  rcases Finset.exists_mem_notMem_of_card_lt_card hlt_univ with ⟨x, _, hx⟩
  refine ⟨x, ?_, ?_, ?_⟩ <;> intro h
  · exact hx (by simp [bad, h])
  · exact hx (by simp [bad, h])
  · exact hx (by simp [bad, h])

/-- A finite Markov corollary: if the sum of an `ℕ`-valued count is at most `b * a`, then
the number of samples with count at least `a` is at most `b`. -/
lemma card_filter_le_of_sum_le_mul {α : Type*} [Fintype α] (f : α → ℕ)
    {a b : ℕ} (ha : 0 < a) (hsum : (∑ x, f x) ≤ b * a) :
    (Finset.univ.filter fun x : α => a ≤ f x).card ≤ b := by
  have hmark := card_filter_mul_le_sum_of_le f a
  exact le_of_mul_le_mul_right (hmark.trans hsum) ha

/-- Three finite Markov bounds imply the existence of a sample below all three thresholds. -/
lemma exists_lt_of_three_sum_bounds {α : Type*} [Fintype α] (f₁ f₂ f₃ : α → ℕ)
    {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hsum₁ : (∑ x, f₁ x) ≤ b₁ * a₁)
    (hsum₂ : (∑ x, f₂ x) ≤ b₂ * a₂)
    (hsum₃ : (∑ x, f₃ x) ≤ b₃ * a₃)
    (hbad : b₁ + b₂ + b₃ < Fintype.card α) :
    ∃ x : α, f₁ x < a₁ ∧ f₂ x < a₂ ∧ f₃ x < a₃ := by
  classical
  have h₁ := card_filter_le_of_sum_le_mul f₁ ha₁ hsum₁
  have h₂ := card_filter_le_of_sum_le_mul f₂ ha₂ hsum₂
  have h₃ := card_filter_le_of_sum_le_mul f₃ ha₃ hsum₃
  rcases exists_not_of_three_bad_card_sum_lt
      (fun x => a₁ ≤ f₁ x) (fun x => a₂ ≤ f₂ x) (fun x => a₃ ≤ f₃ x)
      (by omega) with ⟨x, hx₁, hx₂, hx₃⟩
  exact ⟨x, Nat.lt_of_not_ge hx₁, Nat.lt_of_not_ge hx₂, Nat.lt_of_not_ge hx₃⟩

/-- Scaled first-moment interface recommended by `update2.md`: if each bad count has
`3 * sum < threshold * |Ω|`, then one sample is below all three thresholds. -/
lemma exists_lt_of_three_scaled_sum_bounds {α : Type*} [Fintype α] (f₁ f₂ f₃ : α → ℕ)
    {a₁ a₂ a₃ : ℕ}
    (hsum₁ : 3 * (∑ x, f₁ x) < a₁ * Fintype.card α)
    (hsum₂ : 3 * (∑ x, f₂ x) < a₂ * Fintype.card α)
    (hsum₃ : 3 * (∑ x, f₃ x) < a₃ * Fintype.card α) :
    ∃ x : α, f₁ x < a₁ ∧ f₂ x < a₂ ∧ f₃ x < a₃ := by
  classical
  let B₁ := (Finset.univ.filter fun x : α => a₁ ≤ f₁ x).card
  let B₂ := (Finset.univ.filter fun x : α => a₂ ≤ f₂ x).card
  let B₃ := (Finset.univ.filter fun x : α => a₃ ≤ f₃ x).card
  have hB₁ : 3 * B₁ < Fintype.card α := by
    have hmark := card_filter_mul_le_sum_of_le f₁ a₁
    change B₁ * a₁ ≤ ∑ x, f₁ x at hmark
    apply Nat.lt_of_mul_lt_mul_right (a := a₁)
    nlinarith [hmark, hsum₁]
  have hB₂ : 3 * B₂ < Fintype.card α := by
    have hmark := card_filter_mul_le_sum_of_le f₂ a₂
    change B₂ * a₂ ≤ ∑ x, f₂ x at hmark
    apply Nat.lt_of_mul_lt_mul_right (a := a₂)
    nlinarith [hmark, hsum₂]
  have hB₃ : 3 * B₃ < Fintype.card α := by
    have hmark := card_filter_mul_le_sum_of_le f₃ a₃
    change B₃ * a₃ ≤ ∑ x, f₃ x at hmark
    apply Nat.lt_of_mul_lt_mul_right (a := a₃)
    nlinarith [hmark, hsum₃]
  have hbad : B₁ + B₂ + B₃ < Fintype.card α := by
    omega
  rcases exists_not_of_three_bad_card_sum_lt
      (fun x => a₁ ≤ f₁ x) (fun x => a₂ ≤ f₂ x) (fun x => a₃ ≤ f₃ x)
      (by simpa [B₁, B₂, B₃] using hbad) with ⟨x, hx₁, hx₂, hx₃⟩
  exact ⟨x, Nat.lt_of_not_ge hx₁, Nat.lt_of_not_ge hx₂, Nat.lt_of_not_ge hx₃⟩

lemma card_indepWitness (N k : ℕ) :
    Fintype.card (IndepWitness N k) = N.choose k := by
  simp [IndepWitness]

lemma card_highDegWitness_le (N d : ℕ) :
    Fintype.card (HighDegWitness N d) ≤ N * N.choose (d - 3) := by
  classical
  let f : HighDegWitness N d → Fin N × {s : Finset (Fin N) // s.card = d - 3} :=
    fun W => (W.1.1, ⟨W.1.2, W.2.1⟩)
  have hf : Function.Injective f := by
    intro W W' h
    rcases W with ⟨⟨v, s⟩, hsW⟩
    rcases W' with ⟨⟨v', s'⟩, hsW'⟩
    simp [f] at h
    rcases h with ⟨hv, hs⟩
    subst v'
    subst s'
    rfl
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f, Fintype.card_prod, Fintype.card_fin, Fintype.card_finset_len] using hcard

lemma exists_sample_of_scaled_sum_bounds {N q d k : ℕ} (hq : 0 < q)
    (hdeg : 3 * (∑ ω : Sample N q, highDegWitnessCount hq d ω) <
      1 * Fintype.card (Sample N q))
    (hindep : 3 * (∑ ω : Sample N q, indepWitnessCount hq k ω) <
      1 * Fintype.card (Sample N q))
    (htri : 3 * (∑ ω : Sample N q, triangleCount hq ω) <
      d ^ 3 * Fintype.card (Sample N q)) :
    ∃ ω : Sample N q,
      highDegWitnessCount hq d ω = 0 ∧ indepWitnessCount hq k ω = 0 ∧
        triangleCount hq ω < d ^ 3 := by
  rcases exists_lt_of_three_scaled_sum_bounds
      (fun ω : Sample N q => highDegWitnessCount hq d ω)
      (fun ω : Sample N q => indepWitnessCount hq k ω)
      (fun ω : Sample N q => triangleCount hq ω) hdeg hindep htri with
    ⟨ω, hω₁, hω₂, hω₃⟩
  exact ⟨ω, Nat.lt_one_iff.mp hω₁, Nat.lt_one_iff.mp hω₂, hω₃⟩

lemma exists_sample_of_explicit_moment_bounds {N q d k : ℕ} (hq : 0 < q)
    (hdeg : 3 * (Fintype.card (HighDegWitness N d) *
        q ^ (Fintype.card (Slot N) - (d - 3))) < Fintype.card (Sample N q))
    (hindep : 3 * (Fintype.card (IndepWitness N k) *
        ((q - 1) ^ (k.choose 2) * q ^ (Fintype.card (Slot N) - k.choose 2))) <
      Fintype.card (Sample N q))
    (htri : 3 * (Fintype.card (TriangleWitness N) *
        q ^ (Fintype.card (Slot N) - 3)) < d ^ 3 * Fintype.card (Sample N q)) :
    ∃ ω : Sample N q,
      highDegWitnessCount hq d ω = 0 ∧ indepWitnessCount hq k ω = 0 ∧
        triangleCount hq ω < d ^ 3 := by
  apply exists_sample_of_scaled_sum_bounds hq
  · simpa [sum_highDegWitnessCount hq, one_mul] using hdeg
  · simpa [sum_indepWitnessCount_eq hq, one_mul] using hindep
  · simpa [sum_triangleCount hq] using htri

lemma exists_sample_of_highDeg_indep_triangle_moments {N q d k : ℕ} (hq : 0 < q)
    (hdeg : 3 * (Fintype.card (HighDegWitness N d) *
        q ^ (Fintype.card (Slot N) - (d - 3))) < Fintype.card (Sample N q))
    (hindep : 3 * (∑ ω : Sample N q, indepWitnessCount hq k ω) <
      Fintype.card (Sample N q))
    (htri : 3 * (Fintype.card (TriangleWitness N) *
        q ^ (Fintype.card (Slot N) - 3)) < d ^ 3 * Fintype.card (Sample N q)) :
    ∃ ω : Sample N q,
      highDegWitnessCount hq d ω = 0 ∧ indepWitnessCount hq k ω = 0 ∧
        triangleCount hq ω < d ^ 3 := by
  apply exists_sample_of_scaled_sum_bounds hq
  · simpa [sum_highDegWitnessCount hq, one_mul] using hdeg
  · simpa [one_mul] using hindep
  · simpa [sum_triangleCount hq] using htri

@[simp] lemma card_sample_choose (N q : ℕ) :
    Fintype.card (Sample N q) = q ^ N.choose 2 := by
  simp [card_slot]

lemma triangle_moment_bound_params {d : ℕ} (hd : 2 ≤ d) :
    3 * (((d ^ 6) ^ 3) *
        (6 * d ^ 5) ^ (Fintype.card (Slot (d ^ 6)) - 3)) <
      d ^ 3 * Fintype.card (Sample (d ^ 6) (6 * d ^ 5)) := by
  have hN : 3 ≤ d ^ 6 := by
    have hpow := Nat.pow_le_pow_left hd 6
    norm_num at hpow
    omega
  have hM : 3 ≤ (d ^ 6).choose 2 := by
    have hchoose := Nat.choose_le_choose 2 hN
    norm_num at hchoose
    exact hchoose
  have hApos : 0 < (6 * d ^ 5) ^ ((d ^ 6).choose 2 - 3) := by positivity
  have hsplit :
      (6 * d ^ 5) ^ (d ^ 6).choose 2 =
        (6 * d ^ 5) ^ ((d ^ 6).choose 2 - 3) * (6 * d ^ 5) ^ 3 := by
    rw [← pow_add, Nat.sub_add_cancel hM]
  have hcoeff : 3 * (d ^ 6) ^ 3 < d ^ 3 * (6 * d ^ 5) ^ 3 := by
    have hdpos : 0 < d := by omega
    have hd18 : 0 < d ^ 18 := by positivity
    nlinarith
  have hmul := Nat.mul_lt_mul_of_pos_right hcoeff hApos
  simp [card_slot]
  rw [hsplit]
  nlinarith

lemma exists_sample_of_cardinal_moment_bounds {N q d k : ℕ} (hq : 0 < q)
    (hdeg : 3 * ((N * N.choose (d - 3)) *
        q ^ (Fintype.card (Slot N) - (d - 3))) < Fintype.card (Sample N q))
    (hindep : 3 * (N.choose k *
        ((q - 1) ^ (k.choose 2) * q ^ (Fintype.card (Slot N) - k.choose 2))) <
      Fintype.card (Sample N q))
    (htri : 3 * (N ^ 3 * q ^ (Fintype.card (Slot N) - 3)) <
      d ^ 3 * Fintype.card (Sample N q)) :
    ∃ ω : Sample N q,
      highDegWitnessCount hq d ω = 0 ∧ indepWitnessCount hq k ω = 0 ∧
        triangleCount hq ω < d ^ 3 := by
  apply exists_sample_of_explicit_moment_bounds hq
  · exact lt_of_le_of_lt
      (Nat.mul_le_mul_left 3
        (Nat.mul_le_mul_right (q ^ (Fintype.card (Slot N) - (d - 3)))
          (card_highDegWitness_le N d))) hdeg
  · simpa [card_indepWitness] using hindep
  · exact lt_of_le_of_lt
      (Nat.mul_le_mul_left 3
        (Nat.mul_le_mul_right (q ^ (Fintype.card (Slot N) - 3))
          (card_triangleWitness_le_cube N))) htri

lemma exists_sample_of_param_moment_bounds {d k : ℕ} (hd : 2 ≤ d)
    (hdeg : 3 * (((d ^ 6) * (d ^ 6).choose (d - 3)) *
        (6 * d ^ 5) ^ ((d ^ 6).choose 2 - (d - 3))) <
      (6 * d ^ 5) ^ (d ^ 6).choose 2)
    (hindep : 3 * ((d ^ 6).choose k *
        (((6 * d ^ 5) - 1) ^ (k.choose 2) *
          (6 * d ^ 5) ^ ((d ^ 6).choose 2 - k.choose 2))) <
      (6 * d ^ 5) ^ (d ^ 6).choose 2) :
    ∃ ω : Sample (d ^ 6) (6 * d ^ 5),
      highDegWitnessCount (by positivity) d ω = 0 ∧
        indepWitnessCount (by positivity) k ω = 0 ∧ triangleCount (by positivity) ω < d ^ 3 := by
  apply exists_sample_of_cardinal_moment_bounds (by positivity)
  · simpa [card_sample_choose, card_slot] using hdeg
  · simpa [card_sample_choose, card_slot] using hindep
  · simpa [card_sample_choose, card_slot] using triangle_moment_bound_params hd

noncomputable def realizedTriangles {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    Finset (TriangleWitness N) :=
  Finset.univ.filter fun T : TriangleWitness N =>
    ∀ e, e ∈ triangleSlots T → ω e = ⟨0, hq⟩

@[simp] lemma card_realizedTriangles {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    (realizedTriangles hq ω).card = triangleCount hq ω := by
  simp [realizedTriangles, triangleCount, triangleSlots]

def triangleVertexFinset {N : ℕ} (T : TriangleWitness N) : Finset (Fin N) :=
  {T.1.1, T.1.2.1, T.1.2.2}

lemma card_triangleVertexFinset_le {N : ℕ} (T : TriangleWitness N) :
    (triangleVertexFinset T).card ≤ 3 := by
  rcases T with ⟨⟨u, v, w⟩, huv, hvw⟩
  have huvne : u ≠ v := ne_of_lt huv
  have hvwne : v ≠ w := ne_of_lt hvw
  have huwne : u ≠ w := ne_of_lt (huv.trans hvw)
  simp [triangleVertexFinset, huvne, hvwne, huwne]

noncomputable def triangleVertices {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    Finset (Fin N) :=
  (realizedTriangles hq ω).biUnion triangleVertexFinset

lemma card_triangleVertices_le {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    (triangleVertices hq ω).card ≤ 3 * triangleCount hq ω := by
  calc
    (triangleVertices hq ω).card ≤
        ∑ T ∈ realizedTriangles hq ω, (triangleVertexFinset T).card := by
      simpa [triangleVertices] using
        (Finset.card_biUnion_le (s := realizedTriangles hq ω) (t := triangleVertexFinset))
    _ ≤ ∑ T ∈ realizedTriangles hq ω, 3 := by
      exact Finset.sum_le_sum fun T _ => card_triangleVertexFinset_le T
    _ = 3 * triangleCount hq ω := by
      simp [Nat.mul_comm]

lemma mem_triangleVertices_of_ordered_triangle {N q : ℕ} (hq : 0 < q) (ω : Sample N q)
    {u v w : Fin N} (huv : u < v) (hvw : v < w)
    (huvAdj : (graphOf hq ω).Adj u v) (hvwAdj : (graphOf hq ω).Adj v w)
    (huwAdj : (graphOf hq ω).Adj u w) :
    u ∈ triangleVertices hq ω ∧ v ∈ triangleVertices hq ω ∧ w ∈ triangleVertices hq ω := by
  let T : TriangleWitness N := ⟨(u, v, w), huv, hvw⟩
  have hT : T ∈ realizedTriangles hq ω := by
    simp [realizedTriangles, triangleSlots, T]
    constructor
    · have hne : u ≠ v := ne_of_lt huv
      simpa [slotOf_of_lt hne huv] using (graphOf_adj_iff_slot hq ω hne).1 huvAdj
    constructor
    · have hne : v ≠ w := ne_of_lt hvw
      simpa [slotOf_of_lt hne hvw] using (graphOf_adj_iff_slot hq ω hne).1 hvwAdj
    · have huw : u < w := huv.trans hvw
      have hne : u ≠ w := ne_of_lt huw
      simpa [slotOf_of_lt hne huw] using (graphOf_adj_iff_slot hq ω hne).1 huwAdj
  have hu : u ∈ triangleVertexFinset T := by simp [triangleVertexFinset, T]
  have hv : v ∈ triangleVertexFinset T := by simp [triangleVertexFinset, T]
  have hw : w ∈ triangleVertexFinset T := by simp [triangleVertexFinset, T]
  exact ⟨Finset.mem_biUnion.mpr ⟨T, hT, hu⟩,
    Finset.mem_biUnion.mpr ⟨T, hT, hv⟩,
    Finset.mem_biUnion.mpr ⟨T, hT, hw⟩⟩

lemma mem_triangleVertices_of_triangle {N q : ℕ} (hq : 0 < q) (ω : Sample N q)
    {u v w : Fin N} (huvAdj : (graphOf hq ω).Adj u v)
    (huwAdj : (graphOf hq ω).Adj u w) (hvwAdj : (graphOf hq ω).Adj v w) :
    u ∈ triangleVertices hq ω ∧ v ∈ triangleVertices hq ω ∧ w ∈ triangleVertices hq ω := by
  rcases lt_trichotomy u v with huv | huv_eq | hvu
  · rcases lt_trichotomy v w with hvw | hvw_eq | hwv
    · exact mem_triangleVertices_of_ordered_triangle hq ω huv hvw huvAdj hvwAdj huwAdj
    · exact False.elim (hvwAdj.ne hvw_eq)
    · rcases lt_trichotomy u w with huw | huw_eq | hwu
      · rcases mem_triangleVertices_of_ordered_triangle hq ω huw hwv huwAdj hvwAdj.symm huvAdj with
          ⟨hu, hw, hv⟩
        exact ⟨hu, hv, hw⟩
      · exact False.elim (huwAdj.ne huw_eq)
      · rcases mem_triangleVertices_of_ordered_triangle hq ω hwu huv huwAdj.symm huvAdj hvwAdj.symm with
          ⟨hw, hu, hv⟩
        exact ⟨hu, hv, hw⟩
  · exact False.elim (huvAdj.ne huv_eq)
  · rcases lt_trichotomy u w with huw | huw_eq | hwu
    · rcases mem_triangleVertices_of_ordered_triangle hq ω hvu huw huvAdj.symm huwAdj hvwAdj with
        ⟨hv, hu, hw⟩
      exact ⟨hu, hv, hw⟩
    · exact False.elim (huwAdj.ne huw_eq)
    · rcases lt_trichotomy v w with hvw | hvw_eq | hwv
      · rcases mem_triangleVertices_of_ordered_triangle hq ω hvw hwu hvwAdj huwAdj.symm huvAdj.symm with
          ⟨hv, hw, hu⟩
        exact ⟨hu, hv, hw⟩
      · exact False.elim (hvwAdj.ne hvw_eq)
      · rcases mem_triangleVertices_of_ordered_triangle hq ω hwv hvu hvwAdj.symm huvAdj.symm huwAdj.symm with
          ⟨hw, hv, hu⟩
        exact ⟨hu, hv, hw⟩

lemma cliqueFree_induce_compl_triangleVertices {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    ((graphOf hq ω).induce {v : Fin N | v ∉ triangleVertices hq ω}).CliqueFree 3 := by
  classical
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  rcases hs with ⟨a, b, c, hab, hac, hbc, _⟩
  have habG : (graphOf hq ω).Adj a.1 b.1 := by simpa using hab
  have hacG : (graphOf hq ω).Adj a.1 c.1 := by simpa using hac
  have hbcG : (graphOf hq ω).Adj b.1 c.1 := by simpa using hbc
  have hmem := mem_triangleVertices_of_triangle hq ω habG hacG hbcG
  exact a.2 hmem.1

lemma card_compl_finset_subtype (N : ℕ) (D : Finset (Fin N)) :
    Fintype.card {v : Fin N // v ∉ D} = N - D.card := by
  classical
  rw [Fintype.card_subtype]
  rw [show ({x : Fin N | x ∉ D} : Finset (Fin N)) = Dᶜ by
    ext x
    simp]
  simpa [Fintype.card_fin] using (Finset.card_compl D)

lemma card_survivors_triangleVertices {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    Fintype.card {v : Fin N // v ∉ triangleVertices hq ω} =
      N - (triangleVertices hq ω).card := by
  exact card_compl_finset_subtype N (triangleVertices hq ω)

lemma natCard_survivors_triangleVertices {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    Nat.card {v : Fin N // v ∉ triangleVertices hq ω} =
      N - (triangleVertices hq ω).card := by
  rw [Nat.card_eq_fintype_card]
  exact card_survivors_triangleVertices hq ω

lemma nonempty_survivors_of_triangle_bound {d q : ℕ} (hq : 0 < q) (ω : Sample (d ^ 6) q)
    (hd : 2 ≤ d) (htri : triangleCount hq ω < d ^ 3) :
    Nonempty {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} := by
  have hdel_lt : (triangleVertices hq ω).card < d ^ 6 := by
    have hdel_le := card_triangleVertices_le hq ω
    have htri3 : 3 * triangleCount hq ω < 3 * d ^ 3 := by
      exact Nat.mul_lt_mul_of_pos_left htri (by norm_num)
    have hd3_gt3 : 3 < d ^ 3 := by
      have hpow := Nat.pow_le_pow_left hd 3
      norm_num at hpow
      omega
    have hd3_pos : 0 < d ^ 3 := by positivity
    have hpoly : 3 * d ^ 3 < d ^ 6 := by
      calc
        3 * d ^ 3 < d ^ 3 * d ^ 3 := Nat.mul_lt_mul_of_pos_right hd3_gt3 hd3_pos
        _ = d ^ 6 := by ring
    exact lt_of_le_of_lt hdel_le (lt_trans htri3 hpoly)
  rw [← Fintype.card_pos_iff]
  rw [card_survivors_triangleVertices hq ω]
  omega

noncomputable def seedIndepThreshold (d : ℕ) : ℕ :=
  Nat.ceil (13 * (d : ℝ) ^ 5 * Real.log (d : ℝ))

lemma seedIndepThreshold_ge (d : ℕ) :
    13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) ≤ (seedIndepThreshold d : ℝ) := by
  unfold seedIndepThreshold
  exact Nat.le_ceil _

lemma seedIndepThreshold_pos_eventually :
    ∀ᶠ d : ℕ in Filter.atTop, 0 < seedIndepThreshold d := by
  filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with d hd
  have hkreal : 0 < (seedIndepThreshold d : ℝ) := by
    have hlog : 0 < Real.log (d : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (by omega : 1 < d))
    exact lt_of_lt_of_le (by positivity) (seedIndepThreshold_ge d)
  exact_mod_cast hkreal

lemma seedIndepThreshold_lt_add_one {d : ℕ} (hd : 1 ≤ d) :
    (seedIndepThreshold d : ℝ) <
      13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) + 1 := by
  unfold seedIndepThreshold
  exact Nat.ceil_lt_add_one (by positivity)

lemma alpha_real_budget_aux {d : ℕ} (hd : 100 ≤ d) :
    13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) + 1 ≤
      14 * (((d : ℝ) ^ 6 - 3 * (d : ℝ) ^ 3)) * Real.log (d : ℝ) / (d : ℝ) := by
  have hdreal : (100 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by nlinarith
  have hlog_ge_one : 1 ≤ Real.log (d : ℝ) := by
    have hexp_le : Real.exp 1 ≤ (d : ℝ) := by
      have hexp_lt : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
      nlinarith
    rw [← Real.log_exp 1]
    exact Real.log_le_log (by positivity) hexp_le
  have hd2_ge_one : 1 ≤ (d : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1) (by nlinarith : (1 : ℝ) ≤ d) 2
    simpa using h
  have hd3_ge : (43 : ℝ) ≤ (d : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (100 : ℝ)) hdreal 3
    norm_num at h
    nlinarith
  have hdiff_ge_one : 1 ≤ (d : ℝ) ^ 3 - 42 := by nlinarith
  have hcoef_ge_one : 1 ≤ (d : ℝ) ^ 5 - 42 * (d : ℝ) ^ 2 := by
    calc
      (1 : ℝ) ≤ (d : ℝ) ^ 2 * ((d : ℝ) ^ 3 - 42) := by
        nlinarith [mul_le_mul hd2_ge_one hdiff_ge_one (by nlinarith) (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2)]
      _ = (d : ℝ) ^ 5 - 42 * (d : ℝ) ^ 2 := by ring
  have hgap : 1 ≤ ((d : ℝ) ^ 5 - 42 * (d : ℝ) ^ 2) * Real.log (d : ℝ) := by
    nlinarith [mul_le_mul hcoef_ge_one hlog_ge_one (by norm_num : (0 : ℝ) ≤ 1) (by nlinarith : 0 ≤ (d : ℝ) ^ 5 - 42 * (d : ℝ) ^ 2)]
  field_simp [ne_of_gt hdpos]
  ring_nf
  nlinarith

lemma eventually_twenty_six_log_le_nat :
    ∀ᶠ d : ℕ in Filter.atTop, (26 : ℝ) * Real.log (d : ℝ) ≤ (d : ℝ) := by
  have hreal : ∀ᶠ x : ℝ in Filter.atTop, (26 : ℝ) * Real.log x ≤ x := by
    have h := (Asymptotics.isLittleO_iff_nat_mul_le'.1 Real.isLittleO_log_id_atTop 26)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx_nonneg : 0 ≤ x := le_trans (by norm_num) hx1
    simpa [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hx_nonneg] using hx
  exact tendsto_natCast_atTop_atTop.eventually hreal

lemma seedIndepThreshold_le_d6_eventually :
    ∀ᶠ d : ℕ in Filter.atTop, seedIndepThreshold d ≤ d ^ 6 := by
  filter_upwards [eventually_twenty_six_log_le_nat, Filter.eventually_ge_atTop (2 : ℕ)] with d hlog hd
  have hk_lt := seedIndepThreshold_lt_add_one (by omega : 1 ≤ d)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hd6_ge_two : (2 : ℝ) ≤ (d : ℝ) ^ 6 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ)) (by exact_mod_cast hd : (2 : ℝ) ≤ d) 6
    norm_num at hpow
    nlinarith
  have hmain : 13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) + 1 ≤ (d : ℝ) ^ 6 := by
    have hhalf : 13 * Real.log (d : ℝ) ≤ (d : ℝ) / 2 := by
      nlinarith
    have hmul : 13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) ≤ ((d : ℝ) ^ 6) / 2 := by
      calc
        13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) = (d : ℝ) ^ 5 * (13 * Real.log (d : ℝ)) := by ring
        _ ≤ (d : ℝ) ^ 5 * ((d : ℝ) / 2) := by
          exact mul_le_mul_of_nonneg_left hhalf (by positivity)
        _ = ((d : ℝ) ^ 6) / 2 := by ring
    nlinarith
  have hk_real : (seedIndepThreshold d : ℝ) ≤ (d ^ 6 : ℕ) := by
    exact_mod_cast (le_of_lt (hk_lt.trans_le hmain))
  exact_mod_cast hk_real

lemma seedIndepThreshold_slots_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      (seedIndepThreshold d).choose 2 ≤ (d ^ 6).choose 2 := by
  filter_upwards [seedIndepThreshold_le_d6_eventually] with d hk
  exact Nat.choose_le_choose 2 hk

lemma seedIndepThreshold_alpha_le_survivors {d q : ℕ} (hq : 0 < q)
    (ω : Sample (d ^ 6) q) (hd : 100 ≤ d) (htri : triangleCount hq ω < d ^ 3) :
    (seedIndepThreshold d : ℝ) ≤
      14 * (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) *
        Real.log (d : ℝ) / (d : ℝ) := by
  have hk_lt := seedIndepThreshold_lt_add_one (by omega : 1 ≤ d)
  have hdel_lt : (triangleVertices hq ω).card < 3 * d ^ 3 := by
    have hdel_le := card_triangleVertices_le hq ω
    have htri3 : 3 * triangleCount hq ω < 3 * d ^ 3 := by
      exact Nat.mul_lt_mul_of_pos_left htri (by norm_num)
    exact lt_of_le_of_lt hdel_le htri3
  have hdel_le : (triangleVertices hq ω).card ≤ 3 * d ^ 3 := le_of_lt hdel_lt
  have hsurv_lower_nat : d ^ 6 - 3 * d ^ 3 ≤
      Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} := by
    rw [natCard_survivors_triangleVertices hq ω]
    omega
  have hsub_le : 3 * d ^ 3 ≤ d ^ 6 := by
    have h3_le_d3 : 3 ≤ d ^ 3 := by
      have hpow := Nat.pow_le_pow_left (by omega : 2 ≤ d) 3
      norm_num at hpow
      omega
    have hd3_pos : 0 < d ^ 3 := by positivity
    calc
      3 * d ^ 3 ≤ d ^ 3 * d ^ 3 := Nat.mul_le_mul_right (d ^ 3) h3_le_d3
      _ = d ^ 6 := by ring
  have hsurv_lower_real :
      (d : ℝ) ^ 6 - 3 * (d : ℝ) ^ 3 ≤
        (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) := by
    have hcast : ((d ^ 6 - 3 * d ^ 3 : ℕ) : ℝ) =
        (d : ℝ) ^ 6 - 3 * (d : ℝ) ^ 3 := by
      rw [Nat.cast_sub hsub_le]
      norm_num
    have hrealcast : ((d ^ 6 - 3 * d ^ 3 : ℕ) : ℝ) ≤
        (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) := by
      exact_mod_cast hsurv_lower_nat
    rw [← hcast]
    exact hrealcast
  have hbudget := alpha_real_budget_aux hd
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hlog_nonneg : 0 ≤ Real.log (d : ℝ) := by
    have hlog_ge_one : 1 ≤ Real.log (d : ℝ) := by
      have hdreal : (100 : ℝ) ≤ d := by exact_mod_cast hd
      have hexp_le : Real.exp 1 ≤ (d : ℝ) := by
        have hexp_lt : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
        nlinarith
      rw [← Real.log_exp 1]
      exact Real.log_le_log (by positivity) hexp_le
    nlinarith
  have hmono :
      14 * (((d : ℝ) ^ 6 - 3 * (d : ℝ) ^ 3)) * Real.log (d : ℝ) / (d : ℝ) ≤
        14 * (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) *
          Real.log (d : ℝ) / (d : ℝ) := by
    gcongr
  exact (le_of_lt hk_lt).trans (hbudget.trans hmono)

lemma seedGraphOn_survivors_of_good_sample {N q d k : ℕ} (hq : 0 < q) (ω : Sample N q)
    (hd : 3 ≤ d)
    (hdeg : highDegWitnessCount hq d ω = 0)
    (hindep : indepWitnessCount hq k ω = 0)
    (halpha : (k : ℝ) ≤
      14 * (Nat.card {v : Fin N // v ∉ triangleVertices hq ω} : ℝ) *
        Real.log (d : ℝ) / (d : ℝ)) :
    SeedGraphOn d ((graphOf hq ω).induce {v : Fin N | v ∉ triangleVertices hq ω}) := by
  classical
  constructor
  · exact cliqueFree_induce_compl_triangleVertices hq ω
  constructor
  · intro v
    have hbase := degree_add_three_le_of_highDegWitnessCount_eq_zero hq ω hd hdeg v.1
    have hle := neighborSet_ncard_induce_le (graphOf hq ω)
      ({v : Fin N | v ∉ triangleVertices hq ω}) v
    omega
  · have hnat :
        ((graphOf hq ω).induce {v : Fin N | v ∉ triangleVertices hq ω}).indepNum < k := by
      exact lt_of_le_of_lt
        (indepNum_induce_le (graphOf hq ω) ({v : Fin N | v ∉ triangleVertices hq ω}))
        (indepNum_lt_of_indepWitnessCount_eq_zero hq ω hindep)
    exact (Nat.cast_lt.mpr hnat).le.trans halpha

lemma highDeg_param_moment_bound_of_cancelled {d : ℕ} (hdpos : 0 < d)
    (hslots : d - 3 ≤ (d ^ 6).choose 2)
    (h : 3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) <
      (6 * d ^ 5) ^ (d - 3)) :
    3 * (((d ^ 6) * (d ^ 6).choose (d - 3)) *
        (6 * d ^ 5) ^ ((d ^ 6).choose 2 - (d - 3))) <
      (6 * d ^ 5) ^ (d ^ 6).choose 2 := by
  have hqpos : 0 < 6 * d ^ 5 := by positivity
  have hApos : 0 < (6 * d ^ 5) ^ ((d ^ 6).choose 2 - (d - 3)) := by positivity
  have hsplit :
      (6 * d ^ 5) ^ (d ^ 6).choose 2 =
        (6 * d ^ 5) ^ ((d ^ 6).choose 2 - (d - 3)) *
          (6 * d ^ 5) ^ (d - 3) := by
    rw [← pow_add, Nat.sub_add_cancel hslots]
  have hmul := Nat.mul_lt_mul_of_pos_right h hApos
  rw [hsplit]
  nlinarith

lemma indep_param_moment_bound_of_cancelled {d k : ℕ} (hdpos : 0 < d)
    (hslots : k.choose 2 ≤ (d ^ 6).choose 2)
    (h : 3 * ((d ^ 6).choose k * ((6 * d ^ 5 - 1) ^ (k.choose 2))) <
      (6 * d ^ 5) ^ (k.choose 2)) :
    3 * ((d ^ 6).choose k *
        (((6 * d ^ 5) - 1) ^ (k.choose 2) *
          (6 * d ^ 5) ^ ((d ^ 6).choose 2 - k.choose 2))) <
      (6 * d ^ 5) ^ (d ^ 6).choose 2 := by
  have hqpos : 0 < 6 * d ^ 5 := by positivity
  have hApos : 0 < (6 * d ^ 5) ^ ((d ^ 6).choose 2 - k.choose 2) := by positivity
  have hsplit :
      (6 * d ^ 5) ^ (d ^ 6).choose 2 =
        (6 * d ^ 5) ^ ((d ^ 6).choose 2 - k.choose 2) *
          (6 * d ^ 5) ^ (k.choose 2) := by
    rw [← pow_add, Nat.sub_add_cancel hslots]
  have hmul := Nat.mul_lt_mul_of_pos_right h hApos
  rw [hsplit]
  nlinarith

lemma highDeg_slots_param_le {d : ℕ} (hd : 2 ≤ d) :
    d - 3 ≤ (d ^ 6).choose 2 := by
  have hd_le_pow : d ≤ d ^ 6 := by
    exact Nat.le_self_pow (n := 6) (Nat.ne_of_gt (by norm_num : 0 < 6)) d
  have hN : 3 ≤ d ^ 6 := by
    have hpow := Nat.pow_le_pow_left hd 6
    norm_num at hpow
    omega
  have hchoose_ge : d ^ 6 ≤ (d ^ 6).choose 2 := by
    rw [Nat.choose_two_right]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have hNm1 : 2 ≤ d ^ 6 - 1 := by omega
    exact Nat.mul_le_mul_left (d ^ 6) hNm1
  omega

lemma exists_sample_of_param_cancelled_bounds {d k : ℕ} (hd : 2 ≤ d)
    (hdegSlots : d - 3 ≤ (d ^ 6).choose 2)
    (hindepSlots : k.choose 2 ≤ (d ^ 6).choose 2)
    (hdeg : 3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) <
      (6 * d ^ 5) ^ (d - 3))
    (hindep : 3 * ((d ^ 6).choose k * ((6 * d ^ 5 - 1) ^ (k.choose 2))) <
      (6 * d ^ 5) ^ (k.choose 2)) :
    ∃ ω : Sample (d ^ 6) (6 * d ^ 5),
      highDegWitnessCount (by positivity) d ω = 0 ∧
        indepWitnessCount (by positivity) k ω = 0 ∧ triangleCount (by positivity) ω < d ^ 3 := by
  have hdpos : 0 < d := by omega
  exact exists_sample_of_param_moment_bounds hd
    (highDeg_param_moment_bound_of_cancelled hdpos hdegSlots hdeg)
    (indep_param_moment_bound_of_cancelled hdpos hindepSlots hindep)

lemma exists_sample_of_param_cancelled_bounds' {d k : ℕ} (hd : 2 ≤ d)
    (hindepSlots : k.choose 2 ≤ (d ^ 6).choose 2)
    (hdeg : 3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) <
      (6 * d ^ 5) ^ (d - 3))
    (hindep : 3 * ((d ^ 6).choose k * ((6 * d ^ 5 - 1) ^ (k.choose 2))) <
      (6 * d ^ 5) ^ (k.choose 2)) :
    ∃ ω : Sample (d ^ 6) (6 * d ^ 5),
      highDegWitnessCount (by positivity) d ω = 0 ∧
        indepWitnessCount (by positivity) k ω = 0 ∧ triangleCount (by positivity) ω < d ^ 3 := by
  exact exists_sample_of_param_cancelled_bounds hd (highDeg_slots_param_le hd)
    hindepSlots hdeg hindep

lemma real_pow_div_three_le_factorial (n : ℕ) :
    ((n : ℝ) / 3) ^ n ≤ (Nat.factorial n : ℝ) := by
  rcases n with _ | n
  · norm_num
  · have hdiv : ((n.succ : ℝ) / 3) ≤ ((n.succ : ℝ) / Real.exp 1) := by
      gcongr
      exact Real.exp_one_lt_three.le
    have hpow : ((n.succ : ℝ) / 3) ^ n.succ ≤
        ((n.succ : ℝ) / Real.exp 1) ^ n.succ := by
      exact pow_le_pow_left₀ (by positivity) hdiv n.succ
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n.succ : ℝ)) := by
      rw [Real.one_le_sqrt]
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hn : (1 : ℝ) ≤ n.succ := by exact_mod_cast Nat.succ_pos n
      nlinarith
    calc
      ((n.succ : ℝ) / 3) ^ n.succ ≤
          ((n.succ : ℝ) / Real.exp 1) ^ n.succ := hpow
      _ ≤ Real.sqrt (2 * Real.pi * (n.succ : ℝ)) *
          ((n.succ : ℝ) / Real.exp 1) ^ n.succ := by
        nth_rewrite 1 [← one_mul (((n.succ : ℝ) / Real.exp 1) ^ n.succ)]
        exact mul_le_mul_of_nonneg_right hsqrt (by positivity)
      _ ≤ (Nat.factorial n.succ : ℝ) := Stirling.le_factorial_stirling n.succ

lemma choose_le_three_mul_pow_div {N k : ℕ} (hk : 0 < k) :
    (N.choose k : ℝ) ≤ (3 * (N : ℝ) / (k : ℝ)) ^ k := by
  have hchoose₁ : (N.choose k : ℝ) ≤ ((N : ℝ) ^ k) / (Nat.factorial k : ℝ) := by
    exact Nat.choose_le_pow_div (α := ℝ) k N
  have hfact : ((k : ℝ) / 3) ^ k ≤ (Nat.factorial k : ℝ) :=
    real_pow_div_three_le_factorial k
  have hdenpos : 0 < ((k : ℝ) / 3) ^ k := by positivity
  have hchoose₂ : (N.choose k : ℝ) ≤ ((N : ℝ) ^ k) / (((k : ℝ) / 3) ^ k) := by
    exact hchoose₁.trans (div_le_div_of_nonneg_left (by positivity) hdenpos hfact)
  have hratio_eq : ((N : ℝ) ^ k) / (((k : ℝ) / 3) ^ k) =
      (3 * (N : ℝ) / (k : ℝ)) ^ k := by
    have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
    rw [div_pow, div_pow, mul_pow]
    field_simp [pow_ne_zero k hkreal]
  exact hchoose₂.trans_eq hratio_eq

lemma highDeg_cancelled_bound_of_exp_poly {d : ℕ} (hd : 12 ≤ d)
    (hpoly : 2 ^ (d - 3) * (3 * d ^ 6) < 3 ^ (d - 3)) :
    3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) < (6 * d ^ 5) ^ (d - 3) := by
  let r := d - 3
  have hrpos_nat : 0 < r := by omega
  have hchoose₁ : (((d ^ 6).choose r : ℕ) : ℝ) ≤
      (((d ^ 6 : ℕ) : ℝ) ^ r) / (Nat.factorial r : ℝ) := by
    exact Nat.choose_le_pow_div (α := ℝ) r (d ^ 6)
  have hfact : ((r : ℝ) / 3) ^ r ≤ (Nat.factorial r : ℝ) :=
    real_pow_div_three_le_factorial r
  have hdenpos : 0 < ((r : ℝ) / 3) ^ r := by positivity
  have hchoose₂ : (((d ^ 6).choose r : ℕ) : ℝ) ≤
      (((d ^ 6 : ℕ) : ℝ) ^ r) / (((r : ℝ) / 3) ^ r) := by
    exact hchoose₁.trans (div_le_div_of_nonneg_left (by positivity) hdenpos hfact)
  have hratio_eq :
      (((d ^ 6 : ℕ) : ℝ) ^ r) / (((r : ℝ) / 3) ^ r) =
        (3 * ((d ^ 6 : ℕ) : ℝ) / (r : ℝ)) ^ r := by
    have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos_nat
    rw [div_pow, div_pow, mul_pow]
    field_simp [pow_ne_zero r hrne]
  have hratio_le : 3 * ((d ^ 6 : ℕ) : ℝ) / (r : ℝ) ≤ 4 * (d : ℝ) ^ 5 := by
    have hdreal : (12 : ℝ) ≤ d := by exact_mod_cast hd
    have hr_eq : (r : ℝ) = (d : ℝ) - 3 := by
      simp [r, Nat.cast_sub (by omega : 3 ≤ d)]
    rw [show (((d ^ 6 : ℕ) : ℝ)) = (d : ℝ) ^ 6 by norm_num]
    rw [hr_eq]
    rw [div_le_iff₀ (show 0 < (d : ℝ) - 3 by nlinarith)]
    have hnonneg : 0 ≤ (d : ℝ) ^ 5 * ((d : ℝ) - 12) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hdreal)
    nlinarith
  have hchoose₃ : (((d ^ 6).choose r : ℕ) : ℝ) ≤ (4 * (d : ℝ) ^ 5) ^ r := by
    calc
      (((d ^ 6).choose r : ℕ) : ℝ) ≤
          (((d ^ 6 : ℕ) : ℝ) ^ r) / (((r : ℝ) / 3) ^ r) := hchoose₂
      _ = (3 * ((d ^ 6 : ℕ) : ℝ) / (r : ℝ)) ^ r := hratio_eq
      _ ≤ (4 * (d : ℝ) ^ 5) ^ r := pow_le_pow_left₀ (by positivity) hratio_le r
  have hpoly_real : (2 : ℝ) ^ r * (3 * (d : ℝ) ^ 6) < (3 : ℝ) ^ r := by
    have hp : ((2 ^ r * (3 * d ^ 6) : ℕ) : ℝ) < ((3 ^ r : ℕ) : ℝ) := by
      exact_mod_cast (by simpa [r] using hpoly)
    simpa using hp
  have hcoeff : 3 * (d : ℝ) ^ 6 * (4 * (d : ℝ) ^ 5) ^ r < (6 * (d : ℝ) ^ 5) ^ r := by
    have hmul := mul_lt_mul_of_pos_left hpoly_real
      (show 0 < (2 : ℝ) ^ r * ((d : ℝ) ^ 5) ^ r by positivity)
    rw [mul_assoc] at hmul
    calc
      3 * (d : ℝ) ^ 6 * (4 * (d : ℝ) ^ 5) ^ r
          = ((2 : ℝ) ^ r * ((d : ℝ) ^ 5) ^ r) * ((2 : ℝ) ^ r * (3 * (d : ℝ) ^ 6)) := by
            rw [show (4 : ℝ) = 2 * 2 by norm_num]
            rw [mul_pow, mul_pow]
            ring
      _ < ((2 : ℝ) ^ r * ((d : ℝ) ^ 5) ^ r) * (3 : ℝ) ^ r := by
        simpa [mul_assoc] using hmul
      _ = (6 * (d : ℝ) ^ 5) ^ r := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num]
        rw [mul_pow, mul_pow]
        ring
  have hreal : (3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) : ℝ) <
      ((6 * d ^ 5) ^ (d - 3) : ℝ) := by
    have hmulchoose : (3 * (d : ℝ) ^ 6) * (((d ^ 6).choose r : ℕ) : ℝ) ≤
        (3 * (d : ℝ) ^ 6) * (4 * (d : ℝ) ^ 5) ^ r := by
      exact mul_le_mul_of_nonneg_left hchoose₃ (by positivity)
    calc
      (3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) : ℝ)
          = (3 * (d : ℝ) ^ 6) * (((d ^ 6).choose r : ℕ) : ℝ) := by
            simp [r]
            ring
      _ ≤ (3 * (d : ℝ) ^ 6) * (4 * (d : ℝ) ^ 5) ^ r := hmulchoose
      _ = 3 * (d : ℝ) ^ 6 * (4 * (d : ℝ) ^ 5) ^ r := by ring
      _ < (6 * (d : ℝ) ^ 5) ^ r := hcoeff
      _ = ((6 * d ^ 5) ^ (d - 3) : ℝ) := by
        simp [r]
  exact_mod_cast hreal

lemma poly_step_two_three {d : ℕ} (hd : 20 ≤ d) :
    2 * (d + 1) ^ 6 ≤ 3 * d ^ 6 := by
  have hreal : (2 * ((d + 1 : ℕ) : ℝ) ^ 6) ≤ (3 * (d : ℝ) ^ 6) := by
    have hdreal : (20 : ℝ) ≤ d := by exact_mod_cast hd
    have hle : ((d + 1 : ℕ) : ℝ) ≤ (21 / 20 : ℝ) * d := by
      norm_num
      nlinarith
    have hpow : ((d + 1 : ℕ) : ℝ) ^ 6 ≤ ((21 / 20 : ℝ) * d) ^ 6 := by
      exact pow_le_pow_left₀ (by positivity) hle 6
    have hmul : 2 * ((d + 1 : ℕ) : ℝ) ^ 6 ≤ 2 * (((21 / 20 : ℝ) * d) ^ 6) := by
      exact mul_le_mul_of_nonneg_left hpow (by norm_num)
    have hcoef : 2 * (((21 / 20 : ℝ) * d) ^ 6) ≤ 3 * (d : ℝ) ^ 6 := by
      calc
        2 * (((21 / 20 : ℝ) * d) ^ 6) =
            (2 * (21 / 20 : ℝ) ^ 6) * (d : ℝ) ^ 6 := by ring
        _ ≤ 3 * (d : ℝ) ^ 6 := by
          exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    exact hmul.trans hcoef
  exact_mod_cast hreal

lemma two_three_pow_dom_poly_aux :
    ∀ d : ℕ, 100 ≤ d → 2 ^ (d - 3) * (3 * d ^ 6) < 3 ^ (d - 3)
  | 0, h => by omega
  | d + 1, h => by
      by_cases hd100 : 100 ≤ d
      · have ih := two_three_pow_dom_poly_aux d hd100
        have hstep : 2 * (d + 1) ^ 6 ≤ 3 * d ^ 6 :=
          poly_step_two_three (by omega : 20 ≤ d)
        have hstep' : 2 * (3 * (d + 1) ^ 6) ≤ 3 * (3 * d ^ 6) := by
          nlinarith
        have hleft_le :
            2 * (2 ^ (d - 3) * (3 * (d + 1) ^ 6)) ≤
              3 * (2 ^ (d - 3) * (3 * d ^ 6)) := by
          have hmul := Nat.mul_le_mul_left (2 ^ (d - 3)) hstep'
          nlinarith
        have hleft_eq :
            2 ^ (d + 1 - 3) * (3 * (d + 1) ^ 6) =
              2 * (2 ^ (d - 3) * (3 * (d + 1) ^ 6)) := by
          have hexp : d + 1 - 3 = (d - 3) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        have hright_eq : 3 ^ (d + 1 - 3) = 3 * 3 ^ (d - 3) := by
          have hexp : d + 1 - 3 = (d - 3) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        rw [hleft_eq, hright_eq]
        exact lt_of_le_of_lt hleft_le (Nat.mul_lt_mul_of_pos_left ih (by norm_num))
      · have hd : d = 99 := by omega
        subst d
        norm_num

lemma highDeg_cancelled_bound_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) < (6 * d ^ 5) ^ (d - 3) := by
  filter_upwards [Filter.eventually_ge_atTop (100 : ℕ)] with d hd
  exact highDeg_cancelled_bound_of_exp_poly (by omega : 12 ≤ d)
    (two_three_pow_dom_poly_aux d hd)

lemma graph_degree_and_indep_of_good_sample {N q d k : ℕ} (hq : 0 < q)
    (ω : Sample N q) (hd : 3 ≤ d)
    (hdeg : highDegWitnessCount hq d ω = 0)
    (hindep : indepWitnessCount hq k ω = 0) :
    (∀ v : Fin N, ((graphOf hq ω).neighborSet v).ncard + 3 ≤ d) ∧
      (graphOf hq ω).indepNum < k :=
  ⟨degree_add_three_le_of_highDegWitnessCount_eq_zero hq ω hd hdeg,
    indepNum_lt_of_indepWitnessCount_eq_zero hq ω hindep⟩

lemma not_ordered_triangle_of_triangleCount_eq_zero {N q : ℕ} (hq : 0 < q)
    (ω : Sample N q) (hzero : triangleCount hq ω = 0)
    {u v w : Fin N} (huv : u < v) (hvw : v < w) :
    ¬ ((graphOf hq ω).Adj u v ∧ (graphOf hq ω).Adj v w ∧
      (graphOf hq ω).Adj u w) := by
  intro htri
  let T : TriangleWitness N := ⟨(u, v, w), huv, hvw⟩
  have hbad := (triangleCount_eq_zero_iff hq ω).1 hzero T
  apply hbad
  constructor
  · have hne : u ≠ v := ne_of_lt huv
    simpa [T, slotOf_of_lt hne huv] using (graphOf_adj_iff_slot hq ω hne).1 htri.1
  constructor
  · have hne : v ≠ w := ne_of_lt hvw
    simpa [T, slotOf_of_lt hne hvw] using (graphOf_adj_iff_slot hq ω hne).1 htri.2.1
  · have huw : u < w := huv.trans hvw
    have hne : u ≠ w := ne_of_lt huw
    simpa [T, slotOf_of_lt hne huw] using (graphOf_adj_iff_slot hq ω hne).1 htri.2.2

lemma ratio_pow_le_exp_neg {q r : ℕ} (hq : 1 ≤ q) :
    (((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ r ≤ Real.exp (-(r : ℝ) / (q : ℝ)) := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hq)
  have hratio_eq : (((q - 1 : ℕ) : ℝ) / (q : ℝ)) = 1 - (q : ℝ)⁻¹ := by
    rw [Nat.cast_sub hq]
    norm_num
    field_simp [ne_of_gt hqpos]
  have hbase_nonneg : 0 ≤ 1 - (q : ℝ)⁻¹ := by
    rw [sub_nonneg]
    rw [inv_le_one₀ hqpos]
    exact_mod_cast hq
  calc
    (((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ r = (1 - (q : ℝ)⁻¹) ^ r := by rw [hratio_eq]
    _ ≤ (Real.exp (-(q : ℝ)⁻¹)) ^ r :=
      pow_le_pow_left₀ hbase_nonneg (Real.one_sub_le_exp_neg ((q : ℝ)⁻¹)) r
    _ = Real.exp (-(r : ℝ) / (q : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [ne_of_gt hqpos]

lemma indep_cancelled_bound_of_ratio {N q k : ℕ} (hq : 0 < q)
    (h : (3 : ℝ) * (N.choose k : ℝ) *
        ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ (k.choose 2)) < 1) :
    3 * (N.choose k * ((q - 1) ^ (k.choose 2))) < q ^ (k.choose 2) := by
  let r := k.choose 2
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqpowpos : 0 < (q : ℝ) ^ r := by positivity
  have hmul := mul_lt_mul_of_pos_right h hqpowpos
  have hratio_mul : ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ r) * (q : ℝ) ^ r =
      ((q - 1 : ℕ) : ℝ) ^ r := by
    rw [div_pow]
    field_simp [ne_of_gt hqpos]
  have hleft_eq :
      ((3 : ℝ) * (N.choose k : ℝ) *
          ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ r)) * (q : ℝ) ^ r =
        ((3 * (N.choose k * ((q - 1) ^ r)) : ℕ) : ℝ) := by
    rw [mul_assoc, hratio_mul]
    norm_num
    ring
  have hreal : ((3 * (N.choose k * ((q - 1) ^ r)) : ℕ) : ℝ) < ((q ^ r : ℕ) : ℝ) := by
    rw [← hleft_eq]
    simpa [r] using hmul
  exact_mod_cast hreal

lemma indep_ratio_bound_of_exp_estimate {N q k : ℕ} (hk : 0 < k) (hq : 1 ≤ q)
    (h : (3 : ℝ) * (3 * (N : ℝ) / (k : ℝ)) ^ k *
        Real.exp (-((k.choose 2 : ℕ) : ℝ) / (q : ℝ)) < 1) :
    (3 : ℝ) * (N.choose k : ℝ) *
        ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ (k.choose 2)) < 1 := by
  calc
    (3 : ℝ) * (N.choose k : ℝ) *
        ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ (k.choose 2))
        ≤ 3 * (3 * (N : ℝ) / (k : ℝ)) ^ k *
            ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ (k.choose 2)) := by
          gcongr
          exact choose_le_three_mul_pow_div hk
    _ ≤ 3 * (3 * (N : ℝ) / (k : ℝ)) ^ k *
            Real.exp (-((k.choose 2 : ℕ) : ℝ) / (q : ℝ)) := by
          gcongr
          exact ratio_pow_le_exp_neg hq
    _ < 1 := h

lemma exp_power_estimate_of_log_neg {A B : ℝ} {k : ℕ} (hA : 0 < A)
    (h : Real.log 3 + (k : ℝ) * Real.log A - B < 0) :
    (3 : ℝ) * A ^ k * Real.exp (-B) < 1 := by
  have h_eq : (3 : ℝ) * A ^ k * Real.exp (-B) =
      Real.exp (Real.log 3 + (k : ℝ) * Real.log A - B) := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    rw [Real.exp_nat_mul, Real.exp_log hA, Real.exp_neg]
    ring_nf
  rw [h_eq]
  simpa using (Real.exp_lt_exp.mpr h)

/-- Final logarithmic calculus estimate left for the finite-counting independence bound. -/
lemma indep_log_estimate_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      Real.log 3 + (seedIndepThreshold d : ℝ) *
          Real.log (3 * ((d ^ 6 : ℕ) : ℝ) / (seedIndepThreshold d : ℝ)) -
        (((seedIndepThreshold d).choose 2 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ) < 0 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (13 : ℝ)] with d hd hlog13
  let k := seedIndepThreshold d
  let L := Real.log (d : ℝ)
  have hdpos_nat : 0 < d := by omega
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hdpos_nat
  have hd5pos : 0 < (d : ℝ) ^ 5 := by positivity
  have hd5nonneg : 0 ≤ (d : ℝ) ^ 5 := by positivity
  have hd5ge1 : 1 ≤ (d : ℝ) ^ 5 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (1 : ℝ)) (by exact_mod_cast hd : (1 : ℝ) ≤ d) 5
    simpa using hpow
  have hL13 : (13 : ℝ) ≤ L := by simpa [L] using hlog13
  have hLpos : 0 < L := by nlinarith
  have hk_ge : 13 * (d : ℝ) ^ 5 * L ≤ (k : ℝ) := by
    simpa [k, L] using seedIndepThreshold_ge d
  have hkpos : 0 < (k : ℝ) := by
    have : 0 < 13 * (d : ℝ) ^ 5 * L := by positivity
    exact lt_of_lt_of_le this hk_ge
  have hk_nonneg : 0 ≤ (k : ℝ) := le_of_lt hkpos
  have hApos : 0 < 3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ) := by positivity
  have h3d5_le_k : 3 * (d : ℝ) ^ 5 ≤ (k : ℝ) := by
    have hcoef : (3 : ℝ) ≤ 13 * L := by nlinarith
    have hbase : 3 * (d : ℝ) ^ 5 ≤ 13 * (d : ℝ) ^ 5 * L := by
      nlinarith [mul_le_mul_of_nonneg_right hcoef hd5nonneg]
    exact hbase.trans hk_ge
  have hA_le_d : 3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ) ≤ (d : ℝ) := by
    rw [div_le_iff₀ hkpos]
    have hmul := mul_le_mul_of_nonneg_left h3d5_le_k (le_of_lt hdpos)
    calc
      3 * ((d ^ 6 : ℕ) : ℝ) = (d : ℝ) * (3 * (d : ℝ) ^ 5) := by
        norm_num
        ring
      _ ≤ (d : ℝ) * (k : ℝ) := hmul
  have hlogA_le : Real.log (3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ)) ≤ L := by
    simpa [L] using Real.log_le_log hApos hA_le_d
  have hpos_part : (k : ℝ) * Real.log (3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ)) ≤ (k : ℝ) * L := by
    exact mul_le_mul_of_nonneg_left hlogA_le hk_nonneg
  have hfactor_num : 12 * (d : ℝ) ^ 5 * (L + 1) ≤ (k : ℝ) - 1 := by
    have hneed : 12 * (d : ℝ) ^ 5 + 1 ≤ (d : ℝ) ^ 5 * L := by
      have h13mul : 13 * (d : ℝ) ^ 5 ≤ (d : ℝ) ^ 5 * L := by
        nlinarith [mul_le_mul_of_nonneg_left hL13 hd5nonneg]
      nlinarith
    nlinarith
  have hfactor : L + 1 ≤ ((k : ℝ) - 1) / (12 * (d : ℝ) ^ 5) := by
    rw [le_div_iff₀ (by positivity : 0 < 12 * (d : ℝ) ^ 5)]
    nlinarith
  have hchoose_eq : (((k.choose 2 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ)) =
      (k : ℝ) * (((k : ℝ) - 1) / (12 * (d : ℝ) ^ 5)) := by
    rw [Nat.cast_choose_two]
    norm_num
    field_simp [ne_of_gt hdpos]
    ring
  have hneg_lower : (k : ℝ) * (L + 1) ≤
      (((k.choose 2 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ)) := by
    rw [hchoose_eq]
    exact mul_le_mul_of_nonneg_left hfactor hk_nonneg
  have hlog3_lt_k : Real.log 3 < (k : ℝ) := by
    have hlog3_le : Real.log 3 ≤ (3 : ℝ) := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 3)
    have hk_large : (169 : ℝ) ≤ (k : ℝ) := by
      have hprod : (13 : ℝ) ≤ (d : ℝ) ^ 5 * L := by
        exact le_trans (by norm_num : (13 : ℝ) ≤ 1 * 13) <|
          mul_le_mul hd5ge1 hL13 (by norm_num : (0 : ℝ) ≤ 13) hd5nonneg
      have hbase : (169 : ℝ) ≤ 13 * (d : ℝ) ^ 5 * L := by nlinarith
      exact hbase.trans hk_ge
    nlinarith
  have hmain : Real.log 3 + (k : ℝ) * Real.log (3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ)) <
      (((k.choose 2 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ)) := by
    have hupper : Real.log 3 + (k : ℝ) * Real.log (3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ)) ≤
        Real.log 3 + (k : ℝ) * L := by nlinarith
    have hlower : (k : ℝ) * L + (k : ℝ) ≤
        (((k.choose 2 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ)) := by
      nlinarith
    nlinarith
  simpa [k, L, sub_lt_iff_lt_add] using hmain
/-- Exponential form of the finite-counting independence estimate. -/
lemma indep_exp_estimate_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      (3 : ℝ) * (3 * ((d ^ 6 : ℕ) : ℝ) / (seedIndepThreshold d : ℝ)) ^
          (seedIndepThreshold d) *
        Real.exp (-(((seedIndepThreshold d).choose 2 : ℕ) : ℝ) /
          ((6 * d ^ 5 : ℕ) : ℝ)) < 1 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), seedIndepThreshold_pos_eventually,
    indep_log_estimate_eventually] with d hd hk hlog
  have hA : 0 < 3 * ((d ^ 6 : ℕ) : ℝ) / (seedIndepThreshold d : ℝ) := by
    positivity
  simpa [neg_div] using exp_power_estimate_of_log_neg (A := 3 * ((d ^ 6 : ℕ) : ℝ) /
    (seedIndepThreshold d : ℝ)) hA hlog

/-- Pure-real independence estimate for the finite-counting seed. -/
lemma indep_ratio_bound_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      (3 : ℝ) * ((d ^ 6).choose (seedIndepThreshold d) : ℝ) *
          ((((6 * d ^ 5 - 1 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ)) ^
            ((seedIndepThreshold d).choose 2)) < 1 := by
  filter_upwards [seedIndepThreshold_pos_eventually, Filter.eventually_ge_atTop (1 : ℕ),
    indep_exp_estimate_eventually] with d hk hd h
  exact indep_ratio_bound_of_exp_estimate (N := d ^ 6) (q := 6 * d ^ 5)
    (k := seedIndepThreshold d) hk (by
      have hd5 : 1 ≤ d ^ 5 := by
        have hpow := Nat.pow_le_pow_left hd 5
        norm_num at hpow
        exact hpow
      omega) h

/-- Natural-number form of the remaining independence moment estimate. -/
lemma indep_cancelled_bound_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      3 * ((d ^ 6).choose (seedIndepThreshold d) *
          ((6 * d ^ 5 - 1) ^ ((seedIndepThreshold d).choose 2))) <
        (6 * d ^ 5) ^ ((seedIndepThreshold d).choose 2) := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), indep_ratio_bound_eventually] with d hd h
  exact indep_cancelled_bound_of_ratio (N := d ^ 6) (q := 6 * d ^ 5)
    (k := seedIndepThreshold d) (by positivity) h

/-- Finite counting output from the witness-count strategy in `update2.md`.

The intended proof now asks for zero high-degree witnesses, zero independent-set witnesses, and at
most `d ^ 3` triangle witnesses.  High-degree vertices no longer need to be deleted; only triangle
vertices are removed before inducing the survivor graph. -/
theorem good_seed_graph_on_exists :
    ∀ᶠ d : ℕ in Filter.atTop,
      ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (G : SimpleGraph V),
        SeedGraphOn d G := by
  filter_upwards [Filter.eventually_ge_atTop (100 : ℕ), highDeg_cancelled_bound_eventually,
    seedIndepThreshold_slots_eventually, indep_cancelled_bound_eventually] with
    d hd hdeg hslots hindep
  let hq : 0 < 6 * d ^ 5 := by positivity
  let k := seedIndepThreshold d
  rcases exists_sample_of_param_cancelled_bounds' (d := d) (k := k) (by omega : 2 ≤ d)
      hslots hdeg (by simpa [k] using hindep) with ⟨ω, hdeg0, hindep0, htri⟩
  let V := {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω}
  have hVne : Nonempty V := by
    exact nonempty_survivors_of_triangle_bound hq ω (by omega : 2 ≤ d) htri
  refine ⟨V, inferInstance, hVne,
    (graphOf hq ω).induce {v : Fin (d ^ 6) | v ∉ triangleVertices hq ω}, ?_⟩
  have halpha : (k : ℝ) ≤
      14 * (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) *
        Real.log (d : ℝ) / (d : ℝ) := by
    change (seedIndepThreshold d : ℝ) ≤
      14 * (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) *
        Real.log (d : ℝ) / (d : ℝ)
    exact seedIndepThreshold_alpha_le_survivors hq ω hd htri
  exact seedGraphOn_survivors_of_good_sample hq ω (by omega : 3 ≤ d) hdeg0 hindep0 halpha

/-- Modified seed existence from the finite counting output. -/
theorem seed_graph_exists :
    ∀ᶠ d : ℕ in Filter.atTop,
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ G : SimpleGraph (Fin n₀), SeedGraph d n₀ G := by
  filter_upwards [good_seed_graph_on_exists] with d h
  rcases h with ⟨V, hV, hVne, G, hG⟩
  let : Fintype V := hV
  let : Nonempty V := hVne
  rcases seedGraph_of_seedGraphOn (d := d) (G := G) hG with ⟨H, hH⟩
  refine ⟨Fintype.card V, Fintype.card_pos, H, hH⟩

end SeedCounting

/-- Probabilistic seed existence, proved by finite counting above. -/
theorem seed_graph_exists :
    ∀ᶠ d : ℕ in Filter.atTop,
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ G : SimpleGraph (Fin n₀), SeedGraph d n₀ G := by
  exact SeedCounting.seed_graph_exists

end Erdos619
