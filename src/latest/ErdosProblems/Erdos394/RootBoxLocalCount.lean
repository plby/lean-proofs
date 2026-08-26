import ErdosProblems.Erdos394.PairLattice

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Actual one-prime root-box hit counts

This identifies the arithmetic weights of F-028 with cardinalities of the
local congruence events for a block of `K` consecutive terms.
-/

open Nat Finset

namespace Erdos394

noncomputable local instance zmodUnitsFintypeRootBox (p : ℕ) [NeZero p] :
    Fintype (ZMod p)ˣ := Fintype.ofFinite _

/-- A unit multiplier `h` hits one of the `K` consecutive local roots at time
`j` modulo `p`. -/
def localBlockHit (p K j : ℕ) (h : (ZMod p)ˣ) : Prop :=
  ∃ i ∈ Finset.range K,
    ((h : ZMod p) * (j : ZMod p) + (i : ZMod p)) = 0

/-- Finite set of local unit multipliers producing a hit. -/
noncomputable def localBlockHitSet (p K j : ℕ) [NeZero p] :
    Finset (ZMod p)ˣ := by
  classical
  exact Finset.univ.filter (localBlockHit p K j)

/-- If `p|j`, every unit multiplier hits via the zero label. -/
theorem card_localBlockHitSet_of_dvd {p K j : ℕ} [NeZero p]
    (hp : p.Prime) (hK : 0 < K) (hpj : p ∣ j) :
    (localBlockHitSet p K j).card = p - 1 := by
  classical
  have hjz : (j : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff j p).mpr hpj
  have hall : ∀ h : (ZMod p)ˣ, localBlockHit p K j h := by
    intro h
    refine ⟨0, Finset.mem_range.mpr hK, ?_⟩
    simp [hjz]
  have hset : localBlockHitSet p K j = Finset.univ := by
    ext h
    simp [localBlockHitSet, hall h]
  rw [hset, Finset.card_univ, ZMod.card_units_eq_totient, Nat.totient_prime hp]

/-- If `p∤j`, exactly the `K-1` nonzero labels determine a unit multiplier. -/
theorem card_localBlockHitSet_of_not_dvd {p K j : ℕ} [NeZero p]
    (hp : p.Prime) (hK : 1 ≤ K) (hKp : K < p) (hpj : ¬p ∣ j) :
    (localBlockHitSet p K j).card = K - 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let s := localBlockHitSet p K j
  let u := Icc 1 (K - 1)
  have hjz : (j : ZMod p) ≠ 0 := by
    intro hz
    exact hpj ((ZMod.natCast_eq_zero_iff j p).mp hz)
  let label : (ZMod p)ˣ → ℕ := fun h ↦
    (-((h : ZMod p) * (j : ZMod p))).val
  have hcardu : u.card = K - 1 := by
    simp [u, Nat.card_Icc]
  calc
    s.card = u.card := by
      apply Finset.card_bij (fun h _ ↦ label h)
      · intro h hh
        have hh' : h ∈ localBlockHitSet p K j := by simpa [s] using hh
        have hhit := (Finset.mem_filter.mp hh').2
        obtain ⟨i, hiK, hieq⟩ := hhit
        have hi_ltK : i < K := Finset.mem_range.mp hiK
        have hi_lt_p : i < p := hi_ltK.trans hKp
        have hprod_ne : (h : ZMod p) * (j : ZMod p) ≠ 0 :=
          mul_ne_zero h.ne_zero hjz
        have hi_ne : i ≠ 0 := by
          intro hi0
          subst i
          have hz : (h : ZMod p) * (j : ZMod p) = 0 := by
            simpa only [Nat.cast_zero, add_zero] using hieq
          exact hprod_ne hz
        have hlabel : label h = i := by
          unfold label
          have hz : -((h : ZMod p) * (j : ZMod p)) = (i : ZMod p) :=
            neg_eq_of_add_eq_zero_right hieq
          rw [hz, ZMod.val_natCast_of_lt hi_lt_p]
        rw [hlabel]
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro h₁ hh₁ h₂ hh₂ heq
        have hval :
            (-((h₁ : ZMod p) * (j : ZMod p))).val =
              (-((h₂ : ZMod p) * (j : ZMod p))).val := heq
        have hz : -((h₁ : ZMod p) * (j : ZMod p)) =
            -((h₂ : ZMod p) * (j : ZMod p)) :=
          ZMod.val_injective p hval
        have hmul : (h₁ : ZMod p) * (j : ZMod p) =
            (h₂ : ZMod p) * (j : ZMod p) := by
          exact neg_injective hz
        apply Units.ext
        exact mul_right_cancel₀ hjz hmul
      · intro i hi
        have hiI := Finset.mem_Icc.mp hi
        have hi_pos : 0 < i := by omega
        have hi_ltK : i < K := by omega
        have hi_lt_p : i < p := hi_ltK.trans hKp
        have hiz : (i : ZMod p) ≠ 0 :=
          natCast_zmod_ne_zero_of_pos_of_lt hi_pos hi_lt_p
        let x : ZMod p := -(i : ZMod p) * (j : ZMod p)⁻¹
        have hxz : x ≠ 0 :=
          mul_ne_zero (neg_ne_zero.mpr hiz) (inv_ne_zero hjz)
        let h : (ZMod p)ˣ := Units.mk0 x hxz
        have hhit : localBlockHit p K j h := by
          refine ⟨i, Finset.mem_range.mpr hi_ltK, ?_⟩
          change x * (j : ZMod p) + (i : ZMod p) = 0
          dsimp [x]
          field_simp
          ring
        refine ⟨h, ?_, ?_⟩
        · change h ∈ localBlockHitSet p K j
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ h, hhit⟩
        · unfold label
          rw [show (h : ZMod p) = x by rfl]
          have heq : -(x * (j : ZMod p)) = (i : ZMod p) := by
            dsimp [x]
            field_simp
          rw [heq, ZMod.val_natCast_of_lt hi_lt_p]
    _ = K - 1 := hcardu

/-- Uniform local count: `p-1` when `p|j`, and `K-1` otherwise. -/
theorem card_localBlockHitSet {p K j : ℕ} [NeZero p]
    (hp : p.Prime) (hK : 1 ≤ K) (hKp : K < p) :
    (localBlockHitSet p K j).card =
      if p ∣ j then p - 1 else K - 1 := by
  by_cases hpj : p ∣ j
  · rw [if_pos hpj]
    exact card_localBlockHitSet_of_dvd hp (by omega) hpj
  · rw [if_neg hpj]
    exact card_localBlockHitSet_of_not_dvd hp hK hKp hpj

/-- Number of independent local unit-multiplier tuples producing a root-box
hit at time `j`. -/
noncomputable def rootBoxHitTupleCount (P : Finset ℕ) (K j : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) : ℕ := by
  classical
  letI (p : ↥P) : NeZero p.1 :=
    ⟨(hprime p.1 p.2).ne_zero⟩
  exact ((Finset.univ : Finset ↥P).pi
    (fun p ↦ localBlockHitSet p.1 K j)).card

/-- Total number of independent local unit-multiplier tuples. -/
noncomputable def rootBoxTupleUniverseCount (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) : ℕ := by
  classical
  letI (p : ↥P) : NeZero p.1 :=
    ⟨(hprime p.1 p.2).ne_zero⟩
  letI (p : ↥P) : Fintype (ZMod p.1)ˣ := Fintype.ofFinite _
  exact ((Finset.univ : Finset ↥P).pi
    (fun p ↦ (Finset.univ : Finset (ZMod p.1)ˣ))).card

/-- The actual CRT tuple hit count equals the arithmetic local weight used in
F-028. -/
theorem rootBoxHitTupleCount_eq_weight (P : Finset ℕ) (K j : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hK : 1 ≤ K)
    (hlarge : ∀ p ∈ P, K < p) :
    rootBoxHitTupleCount P K j hprime = rootBoxLocalWeight P K j := by
  classical
  letI (p : ↥P) : NeZero p.1 :=
    ⟨(hprime p.1 p.2).ne_zero⟩
  unfold rootBoxHitTupleCount
  rw [Finset.card_pi]
  calc
    (∏ p ∈ (Finset.univ : Finset ↥P),
        (localBlockHitSet p.1 K j).card) =
      ∏ p ∈ (Finset.univ : Finset ↥P),
        (if p.1 ∣ j then p.1 - 1 else K - 1) := by
          apply Finset.prod_congr rfl
          intro p hp
          exact card_localBlockHitSet (hprime p.1 p.2) hK (hlarge p.1 p.2)
    _ = ∏ p ∈ P, (if p ∣ j then p - 1 else K - 1) := by
          rw [← Finset.attach_eq_univ]
          simpa using Finset.prod_attach P
            (fun p ↦ if p ∣ j then p - 1 else K - 1)
    _ = rootBoxLocalWeight P K j := rfl

/-- The full CRT tuple universe has the expected product cardinality `Φ`. -/
theorem rootBoxTupleUniverseCount_eq_primeUnitCount (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    rootBoxTupleUniverseCount P hprime = primeUnitCount P := by
  classical
  letI (p : ↥P) : NeZero p.1 :=
    ⟨(hprime p.1 p.2).ne_zero⟩
  letI (p : ↥P) : Fintype (ZMod p.1)ˣ := Fintype.ofFinite _
  unfold rootBoxTupleUniverseCount
  rw [Finset.card_pi]
  calc
    (∏ p ∈ (Finset.univ : Finset ↥P),
        (Finset.univ : Finset (ZMod p.1)ˣ).card) =
      ∏ p ∈ (Finset.univ : Finset ↥P), (p.1 - 1) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [Finset.card_univ, ZMod.card_units_eq_totient,
            Nat.totient_prime (hprime p.1 p.2)]
    _ = ∏ p ∈ P, (p - 1) := by
          rw [← Finset.attach_eq_univ]
          simpa using Finset.prod_attach P (fun p ↦ p - 1)
    _ = primeUnitCount P := rfl

/-- Actual unnormalized first moment in the independent local CRT model. -/
noncomputable def rootBoxTupleFirstMoment (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) : ℕ :=
  ∑ j ∈ Icc 1 Y, rootBoxHitTupleCount P K j hprime

/-- The actual tuple first moment is exactly F-028's arithmetic moment. -/
theorem rootBoxTupleFirstMoment_eq (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hK : 1 ≤ K)
    (hlarge : ∀ p ∈ P, K < p) :
    rootBoxTupleFirstMoment P K Y hprime = rootBoxFirstMoment P K Y := by
  unfold rootBoxTupleFirstMoment rootBoxFirstMoment
  apply Finset.sum_congr rfl
  intro j hj
  exact rootBoxHitTupleCount_eq_weight P K j hprime hK hlarge

/-- Therefore the normalized actual CRT tuple first moment lies between
`K^|P|Y/q-1` and `K^|P|Y/q`. -/
theorem normalized_rootBoxTupleFirstMoment_bounds (P : Finset ℕ) (K Y : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hK : 1 ≤ K)
    (hlarge : ∀ p ∈ P, K < p) :
    (K ^ P.card : ℝ) * (Y : ℝ) / (primeProduct P : ℝ) - 1 ≤
        (rootBoxTupleFirstMoment P K Y hprime : ℝ) /
          (rootBoxTupleUniverseCount P hprime : ℝ) ∧
    (rootBoxTupleFirstMoment P K Y hprime : ℝ) /
          (rootBoxTupleUniverseCount P hprime : ℝ) ≤
        (K ^ P.card : ℝ) * (Y : ℝ) / (primeProduct P : ℝ) := by
  rw [rootBoxTupleFirstMoment_eq P K Y hprime hK hlarge,
    rootBoxTupleUniverseCount_eq_primeUnitCount P hprime]
  exact normalized_rootBoxFirstMoment_bounds P K Y hK hprime
    (fun p hp ↦ (hlarge p hp).le)

end Erdos394
