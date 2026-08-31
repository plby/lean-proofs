/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# A cyclic Freiman model lemma

This file contains the elementary finite counting argument used in the
Fox--Pohoata reduction.  A subset of a sufficiently large prime cyclic group
has a subset of at least half its size which is Freiman-isomorphic of order
two to a subset of a cyclic group whose order is controlled by
`2 • A - 2 • A`.
-/

open Finset Set
open scoped Pointwise

namespace Erdos179

namespace CyclicModel

/-- The small target modulus used by the model lemma. -/
def modelModulus {p : ℕ} (A : Finset (ZMod p)) : ℕ :=
  16 * ((2 • A - 2 • A).card + 1)

/-- The set of all differences of two two-term sums from `A`. -/
def pairDiff {p : ℕ} (A : Finset (ZMod p)) : Finset (ZMod p) :=
  (A + A) - (A + A)

/-- Residues which would turn a nonzero signed difference into a multiple of
the target modulus. -/
def badResidues (p q : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter fun z ↦ q ∣ z.val ∨ q ∣ p - z.val

lemma card_badResidues_le (p q : ℕ) [NeZero p] :
    (badResidues p q).card ≤ 2 * (p / q + 1) := by
  let f : ZMod p → ℕ := fun z ↦ z.val
  let U : Finset ℕ := (Finset.range (p + 1)).filter fun k ↦ q ∣ k
  have hmaps : ∀ z ∈ badResidues p q, f z ∈ U ∪ (U.image fun k ↦ p - k) := by
    intro z hz
    have hz' : q ∣ z.val ∨ q ∣ p - z.val := by
      exact (mem_filter.mp (show z ∈ Finset.univ.filter
        (fun z : ZMod p ↦ q ∣ z.val ∨ q ∣ p - z.val) by simpa [badResidues] using hz)).2
    rcases hz' with hz | hz
    · apply Finset.mem_union_left
      simp only [U, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_lt z.val_lt, hz⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨p - z.val, ?_, ?_⟩
      · simp only [U, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le (Nat.sub_le _ _), hz⟩
      · dsimp [f]
        have hzle : z.val ≤ p := Nat.le_of_lt z.val_lt
        omega
  have hinj : Set.InjOn f (badResidues p q : Set (ZMod p)) :=
    (ZMod.val_injective p).injOn
  have hcard : (badResidues p q).card ≤ (U ∪ U.image fun k ↦ p - k).card := by
    exact Finset.card_le_card_of_injOn f hmaps hinj
  have hU : U.card ≤ p / q + 1 := by
    let V : Finset ℕ := {0} ∪ (Finset.range (p + 1)).filter fun k ↦ k ≠ 0 ∧ q ∣ k
    have hUV : U ⊆ V := by
      intro k hk
      simp only [U, mem_filter, Finset.mem_range] at hk
      by_cases hk0 : k = 0
      · simp [V, hk0]
      · simp [V, hk.1, hk0, hk.2]
    calc
      U.card ≤ V.card := card_le_card hUV
      _ ≤ 1 + ((Finset.range (p + 1)).filter fun k ↦ k ≠ 0 ∧ q ∣ k).card :=
        card_union_le _ _
      _ = 1 + p / q := by rw [Nat.card_multiples']
      _ = p / q + 1 := by omega
  calc
    (badResidues p q).card ≤ (U ∪ U.image fun k ↦ p - k).card := hcard
    _ ≤ U.card + (U.image fun k ↦ p - k).card := card_union_le _ _
    _ ≤ U.card + U.card := Nat.add_le_add_left card_image_le _
    _ ≤ 2 * (p / q + 1) := by omega

/-- Dilations which send at least one nonzero member of `D` to a bad
residue. -/
def badDilations {p : ℕ} [NeZero p] (D : Finset (ZMod p)) (q : ℕ) :
    Finset (ZMod p) :=
  (D.erase 0).biUnion fun d ↦
    Finset.univ.filter fun lambda ↦ lambda * d ∈ badResidues p q

private lemma card_biUnion_le_mul {alpha beta : Type*}
    [DecidableEq beta] (s : Finset alpha)
    (t : alpha → Finset beta) (B : ℕ) (h : ∀ x ∈ s, (t x).card ≤ B) :
    (s.biUnion t).card ≤ s.card * B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert]
      calc
        ((t a) ∪ s.biUnion t).card ≤ (t a).card + (s.biUnion t).card :=
          card_union_le _ _
        _ ≤ B + s.card * B := Nat.add_le_add (h a (by simp))
          (ih fun x hx ↦ h x (by simp [hx]))
        _ = (insert a s).card * B := by simp [ha, Nat.succ_mul, Nat.add_comm]

lemma card_badDilations_le {p : ℕ} [NeZero p] (hp : p.Prime) (D : Finset (ZMod p))
    (q : ℕ) :
    (badDilations D q).card ≤ D.card * (2 * (p / q + 1)) := by
  let : Fact p.Prime := ⟨hp⟩
  let E := D.erase 0
  let t : ZMod p → Finset (ZMod p) := fun d ↦
    Finset.univ.filter fun lambda ↦ lambda * d ∈ badResidues p q
  have ht : ∀ d ∈ E, (t d).card ≤ 2 * (p / q + 1) := by
    intro d hd
    have hd0 : d ≠ 0 := (mem_erase.mp hd).1
    have hpre : (t d).card ≤ (badResidues p q).card := by
      apply Finset.card_le_card_of_injOn (fun lambda ↦ lambda * d)
      · intro lambda hlambda
        exact (mem_filter.mp hlambda).2
      · exact (Equiv.mulRight₀ d hd0).injective.injOn
    exact hpre.trans (card_badResidues_le p q)
  calc
    (badDilations D q).card = (E.biUnion t).card := rfl
    _ ≤ E.card * (2 * (p / q + 1)) := card_biUnion_le_mul E t _ ht
    _ ≤ D.card * (2 * (p / q + 1)) := by
      apply Nat.mul_le_mul_right
      exact Finset.card_le_card (erase_subset 0 D)

lemma badDilations_card_lt {p : ℕ} [NeZero p] (hp : p.Prime) (D : Finset (ZMod p))
    (hp_large : 16 * D.card < p) :
    (badDilations D (16 * (D.card + 1))).card < p := by
  let q := 16 * (D.card + 1)
  have hq : 0 < q := by simp [q]
  have hcard := card_badDilations_le hp D q
  have hdiv : q * (p / q) ≤ p := by
    simpa [mul_comm] using Nat.div_mul_le_self p q
  have hmain : D.card * (2 * (p / q + 1)) < p := by
    have hscaled : 16 * (D.card * (p / q)) ≤ p := by
      calc
        16 * (D.card * (p / q)) ≤ 16 * ((D.card + 1) * (p / q)) := by
          gcongr
          omega
        _ = q * (p / q) := by simp [q]; ring
        _ ≤ p := hdiv
    have h8 : 8 * (D.card * (2 * (p / q + 1))) < 8 * p := by
      calc
        8 * (D.card * (2 * (p / q + 1))) =
            16 * (D.card * (p / q)) + 16 * D.card := by ring
        _ < p + p := Nat.add_lt_add_of_le_of_lt hscaled hp_large
        _ ≤ 8 * p := by omega
    omega
  exact hcard.trans_lt hmain

lemma exists_good_dilation {p : ℕ} [NeZero p] (hp : p.Prime) (D : Finset (ZMod p))
    (hp_large : 16 * D.card < p) :
    ∃ lambda : ZMod p, lambda ∉ badDilations D (16 * (D.card + 1)) := by
  have hcard := badDilations_card_lt hp D hp_large
  have huniv : (Finset.univ : Finset (ZMod p)).card = p := by simp [ZMod.card]
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆
      badDilations D (16 * (D.card + 1)) := by
    intro lambda _
    exact h lambda
  have := Finset.card_le_card hsub
  rw [huniv] at this
  omega

private lemma eq_of_modEq_of_common_interval {p U V : ℕ} (hmod : U ≡ V [MOD p])
    (hinterval : (U < p ∧ V < p) ∨
      (p ≤ U ∧ U < 2 * p ∧ p ≤ V ∧ V < 2 * p)) :
    U = V := by
  rcases le_total U V with hUV | hVU
  · have hdvd : p ∣ V - U := (Nat.modEq_iff_dvd' hUV).mp hmod
    have hlt : V - U < p := by rcases hinterval with h | h <;> omega
    by_contra hne
    have hstrict : U < V := lt_of_le_of_ne hUV hne
    have hpos : 0 < V - U := Nat.sub_pos_of_lt hstrict
    have hple : p ≤ V - U := Nat.le_of_dvd hpos hdvd
    omega
  · have hdvd : p ∣ U - V :=
      (Nat.modEq_iff_dvd' hVU).mp hmod.symm
    have hlt : U - V < p := by rcases hinterval with h | h <;> omega
    by_contra hne
    have hstrict : V < U := lt_of_le_of_ne hVU (Ne.symm hne)
    have hpos : 0 < U - V := Nat.sub_pos_of_lt hstrict
    have hple : p ≤ U - V := Nat.le_of_dvd hpos hdvd
    omega

/-- The reduction of a dilated residue to a smaller cyclic group. -/
def modelMap {p : ℕ} (q : ℕ) (lambda : ZMod p) (x : ZMod p) : ZMod q :=
  ((lambda * x).val : ℕ)

/-- The four-variable formulation of a Freiman isomorphism of order two. -/
def PairFreimanOn {G H : Type*} [Add G] [Add H]
    (A : Finset G) (f : G → H) : Prop :=
  ∀ ⦃a b c d : G⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    (f a + f b = f c + f d ↔ a + b = c + d)

private lemma modelMap_pair_eq_iff {p q : ℕ} [NeZero p]
    (lambda : ZMod p) (a b c d : ZMod p) :
    modelMap q lambda a + modelMap q lambda b =
        modelMap q lambda c + modelMap q lambda d ↔
      (lambda * a).val + (lambda * b).val ≡
        (lambda * c).val + (lambda * d).val [MOD q] := by
  simpa only [modelMap, ← Nat.cast_add] using
    ZMod.natCast_eq_natCast_iff
      ((lambda * a).val + (lambda * b).val)
      ((lambda * c).val + (lambda * d).val) q

private lemma pairFreiman_of_same_half {p q : ℕ} [NeZero p]
    (D A : Finset (ZMod p))
    (lambda : ZMod p)
    (hgood : ∀ x ∈ D, x ≠ 0 → lambda * x ∉ badResidues p q)
    (hdiff : ∀ ⦃a b c d : ZMod p⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a + b - c - d ∈ D)
    (hhalf : (∀ x ∈ A, 2 * (lambda * x).val < p) ∨
      (∀ x ∈ A, p ≤ 2 * (lambda * x).val)) : 0 < q →
    PairFreimanOn A (modelMap q lambda) := by
  intro hq
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  intro a b c d ha hb hc hd
  let U := (lambda * a).val + (lambda * b).val
  let V := (lambda * c).val + (lambda * d).val
  have hinterval : (U < p ∧ V < p) ∨
      (p ≤ U ∧ U < 2 * p ∧ p ≤ V ∧ V < 2 * p) := by
    rcases hhalf with hlo | hhi
    · left
      have ha' := hlo a ha
      have hb' := hlo b hb
      have hc' := hlo c hc
      have hd' := hlo d hd
      dsimp [U, V]
      omega
    · right
      have ha' := hhi a ha
      have hb' := hhi b hb
      have hc' := hhi c hc
      have hd' := hhi d hd
      have hap := (lambda * a).val_lt
      have hbp := (lambda * b).val_lt
      have hcp := (lambda * c).val_lt
      have hdp := (lambda * d).val_lt
      dsimp [U, V]
      omega
  constructor
  · intro htarget
    have hmodq : U ≡ V [MOD q] :=
      (modelMap_pair_eq_iff lambda a b c d).mp htarget
    rcases le_total V U with hVU | hUV
    · let x := a + b - c - d
      have hxD : x ∈ D := hdiff ha hb hc hd
      by_cases hx0 : x = 0
      · dsimp [x] at hx0
        have hzero : a + b - (c + d) = 0 := by
          linear_combination hx0
        exact sub_eq_zero.mp hzero
      · have hnot := hgood x hxD hx0
        have hdvd : q ∣ U - V := (Nat.modEq_iff_dvd' hVU).mp hmodq.symm
        have hlt : U - V < p := by rcases hinterval with h | h <;> omega
        have hx : lambda * x = ((U - V : ℕ) : ZMod p) := by
          calc
            lambda * x = (lambda * a + lambda * b) -
                (lambda * c + lambda * d) := by dsimp [x]; ring
            _ = (U : ZMod p) - (V : ZMod p) := by
              simp [U, V]
            _ = ((U - V : ℕ) : ZMod p) := by rw [Nat.cast_sub hVU]
        have hxval : (lambda * x).val = U - V := by
          rw [hx, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
        exact (hnot <| by
          unfold badResidues
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          exact Or.inl (by simpa [hxval] using hdvd)).elim
    · let x := c + d - a - b
      have hxD : x ∈ D := hdiff hc hd ha hb
      by_cases hx0 : x = 0
      · dsimp [x] at hx0
        have hzero : c + d - (a + b) = 0 := by
          linear_combination hx0
        exact (sub_eq_zero.mp hzero).symm
      · have hnot := hgood x hxD hx0
        have hdvd : q ∣ V - U := (Nat.modEq_iff_dvd' hUV).mp hmodq
        have hlt : V - U < p := by rcases hinterval with h | h <;> omega
        have hx : lambda * x = ((V - U : ℕ) : ZMod p) := by
          calc
            lambda * x = (lambda * c + lambda * d) -
                (lambda * a + lambda * b) := by dsimp [x]; ring
            _ = (V : ZMod p) - (U : ZMod p) := by
              simp [U, V]
            _ = ((V - U : ℕ) : ZMod p) := by rw [Nat.cast_sub hUV]
        have hxval : (lambda * x).val = V - U := by
          rw [hx, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
        exact (hnot <| by
          unfold badResidues
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          exact Or.inl (by simpa [hxval] using hdvd)).elim
  · intro hsource
    have hpmod : U ≡ V [MOD p] := by
      apply (ZMod.natCast_eq_natCast_iff U V p).mp
      calc
        (U : ZMod p) = lambda * a + lambda * b := by simp [U]
        _ = lambda * c + lambda * d := by rw [← mul_add, hsource, mul_add]
        _ = (V : ZMod p) := by simp [V]
    have hUV : U = V := eq_of_modEq_of_common_interval hpmod hinterval
    apply (modelMap_pair_eq_iff lambda a b c d).mpr
    change U ≡ V [MOD q]
    rw [hUV]

/-- Cyclic Freiman modeling.  The large prime modulus makes it possible to
choose a dilation avoiding every nonzero two-sum difference.  Restricting to
the larger of the lower and upper residue halves removes wraparound. -/
theorem exists_cyclic_model {p : ℕ} [NeZero p] (hp : p.Prime)
    (S : Finset (ZMod p))
    (hp_large : 16 * (pairDiff S).card < p) :
    let q := 16 * ((pairDiff S).card + 1)
    ∃ lambda : ZMod p, ∃ A ⊆ S,
      2 * A.card ≥ S.card ∧ PairFreimanOn A (modelMap q lambda) := by
  let D := pairDiff S
  let q := 16 * (D.card + 1)
  have hq : 0 < q := by simp [q]
  obtain ⟨lambda, hlambda⟩ := exists_good_dilation hp D (by simpa [D] using hp_large)
  have hgood : ∀ x ∈ D, x ≠ 0 → lambda * x ∉ badResidues p q := by
    intro x hxD hx0 hxbad
    apply hlambda
    unfold badDilations
    apply Finset.mem_biUnion.mpr
    refine ⟨x, Finset.mem_erase.mpr ⟨hx0, hxD⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxbad⟩
  let L := S.filter fun x ↦ 2 * (lambda * x).val < p
  let H := S.filter fun x ↦ p ≤ 2 * (lambda * x).val
  have hLH : L ∪ H = S := by
    ext x
    simp only [L, H, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    · intro hx
      rcases lt_or_ge (2 * (lambda * x).val) p with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hdisj : Disjoint L H := by
    rw [Finset.disjoint_left]
    intro x hxL hxH
    have hxL' := (mem_filter.mp hxL).2
    have hxH' := (mem_filter.mp hxH).2
    omega
  have hcards : L.card + H.card = S.card := by
    rw [← hLH, card_union_of_disjoint hdisj]
  have hdiffA : ∀ (A : Finset (ZMod p)), A ⊆ S →
      ∀ ⦃a b c d : ZMod p⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
        a + b - c - d ∈ D := by
    intro A hAS a b c d ha hb hc hd
    have haS := hAS ha
    have hbS := hAS hb
    have hcS := hAS hc
    have hdS := hAS hd
    unfold D pairDiff
    rw [Finset.mem_sub]
    refine ⟨a + b, ?_, c + d, ?_, by ring⟩
    · rw [Finset.mem_add]
      exact ⟨a, haS, b, hbS, rfl⟩
    · rw [Finset.mem_add]
      exact ⟨c, hcS, d, hdS, rfl⟩
  by_cases hlarge : S.card ≤ 2 * L.card
  · refine ⟨lambda, L, ?_, hlarge, ?_⟩
    · exact filter_subset _ _
    · apply pairFreiman_of_same_half D L lambda hgood
        (hdiffA L (filter_subset _ _)) _ hq
      left
      intro x hx
      exact (mem_filter.mp hx).2
  · have hlargeH : S.card ≤ 2 * H.card := by omega
    refine ⟨lambda, H, ?_, hlargeH, ?_⟩
    · exact filter_subset _ _
    · apply pairFreiman_of_same_half D H lambda hgood
        (hdiffA H (filter_subset _ _)) _ hq
      right
      intro x hx
      exact (mem_filter.mp hx).2

lemma PairFreimanOn.injOn {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {A : Finset G} {f : G → H} (hf : PairFreimanOn A f) :
    Set.InjOn f A := by
  intro a ha b hb hab
  have hpair : f a + f a = f b + f a := by rw [hab]
  have := (hf ha ha hb ha).mp hpair
  exact add_right_cancel this

end CyclicModel

end Erdos179
