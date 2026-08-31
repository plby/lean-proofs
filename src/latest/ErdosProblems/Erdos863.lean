/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 863.
https://www.erdosproblems.com/forum/thread/863

Informal authors:
- Boon Suan Ho
- Javier Cilleruelo
- Imre Ruzsa
- Carlos Trujillo
- GPT-5.4 Pro

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos863.md
-/
/-
Erdős Problem 863.

For r ≥ 2, the asymptotic constant for maximum subsets of [1,N] with at
most r unordered representations of every sum is strictly larger than the
corresponding constant for maximum subsets with at most r representations
of every positive difference (provided, as in the question, that the two
asymptotic constants exist).

The lower bound is the Cilleruelo--Ruzsa--Trujillo pasting construction.
The upper bound is the Erdős--Turán shifting argument.
-/

import Mathlib

open scoped BigOperators

namespace Erdos863

open Filter Real

noncomputable section

/-- Ordered representations of `n` as a sum of two members of `A`. -/
def orderedSumReps (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun x => x.1 + x.2 = n

/-- Representations of `n` as `a + b`, counted once by imposing `a ≤ b`. -/
def sumReps (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun x => x.1 ≤ x.2 ∧ x.1 + x.2 = n

/-- Representations of `n` as the natural-number difference `a - b`. -/
def diffReps (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun x => x.1 - x.2 = n

/-- The usual `B₂[r]` condition, with unordered summands. -/
def IsB2 (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ n : ℕ, (sumReps A n).card ≤ r

/-- At most `r` representations of every positive difference. -/
def IsDiffB2 (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → (diffReps A n).card ≤ r

/-- Maximum cardinality of a `B₂[r]` subset of `{1, ..., N}`. -/
noncomputable def sumMax (r N : ℕ) : ℕ :=
  letI : DecidablePred (IsB2 r) := Classical.decPred _
  ((Finset.Icc 1 N).powerset.filter (IsB2 r)).sup Finset.card

/-- Maximum cardinality of a positive-difference `B₂[r]` subset of `{1, ..., N}`. -/
noncomputable def diffMax (r N : ℕ) : ℕ :=
  letI : DecidablePred (IsDiffB2 r) := Classical.decPred _
  ((Finset.Icc 1 N).powerset.filter (IsDiffB2 r)).sup Finset.card

/-- A sequence has the square-root asymptotic constant `c`. -/
def HasSqrtAsymptotic (f : ℕ → ℕ) (c : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (f N : ℝ) / Real.sqrt N) atTop (nhds c)

/-! ### Ruzsa's optimal modular Sidon sets -/

/-- A Sidon set in an additive commutative monoid. -/
def Sidon {α : Type*} [AddCommMonoid α] (S : Set α) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → ({a, b} : Set α) = {c, d}

/-- Sidonicity after reduction modulo `M`. -/
def SidonMod (M : ℕ) (S : Set ℕ) : Prop :=
  Sidon ((fun x : ℕ => (x : ZMod M)) '' S)

lemma eq_of_zmod_eq_of_lt (M : ℕ) [NeZero M] (a b : ℕ)
    (ha : a < M) (hb : b < M) (h : (a : ZMod M) = (b : ZMod M)) : a = b :=
  (ZMod.val_natCast_of_lt ha).symm.trans
    ((congrArg ZMod.val h).trans (ZMod.val_natCast_of_lt hb))

lemma pair_eq_of_zmod_pair_eq (M : ℕ) [NeZero M] {a b c d : ℕ}
    (ha : a < M) (hb : b < M) (hc : c < M) (hd : d < M)
    (h : ({(a : ZMod M), (b : ZMod M)} : Set (ZMod M)) =
      {(c : ZMod M), (d : ZMod M)}) :
    ({a, b} : Set ℕ) = {c, d} := by
  rcases Set.pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    apply Set.pair_eq_pair_iff.mpr
  · exact Or.inl ⟨eq_of_zmod_eq_of_lt M a c ha hc h1,
      eq_of_zmod_eq_of_lt M b d hb hd h2⟩
  · exact Or.inr ⟨eq_of_zmod_eq_of_lt M a d ha hd h1,
      eq_of_zmod_eq_of_lt M b c hb hc h2⟩

/-- Ruzsa's Sidon set in `ZMod (p-1) × ZMod p`. -/
def ruzsaSet (p : ℕ) (g : ZMod p) : Finset (ZMod (p - 1) × ZMod p) :=
  (Finset.range (p - 1)).image fun i : ℕ => ((i : ZMod (p - 1)), g ^ i)

lemma ruzsaSet_sidon (p : ℕ) (hp : p.Prime) (g : ZMod p)
    (hg : IsPrimitiveRoot g (p - 1)) :
    Sidon (ruzsaSet p g : Set (ZMod (p - 1) × ZMod p)) := by
  intro a b c d
  simp only [ruzsaSet, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
    forall_exists_index, and_imp]
  rintro x hx rfl y hy rfl z hz rfl w hw rfl h
  have := Fact.mk hp
  simp_all +decide only [Prod.mk_add_mk, Prod.mk.injEq]
  have hprod : g ^ x * g ^ y = g ^ z * g ^ w := by
    have hexp : (x + y : ℕ) ≡ (z + w : ℕ) [MOD (p - 1)] := by
      have := Fact.mk hp
      rw [← ZMod.natCast_eq_natCast_iff]
      aesop
    rw [← pow_add, ← pow_add, ← Nat.mod_add_div (x + y) (p - 1),
      ← Nat.mod_add_div (z + w) (p - 1), hexp]
    simp +decide [pow_add, pow_mul, hg.pow_eq_one]
  have hcases : g ^ x = g ^ z ∧ g ^ y = g ^ w ∨
      g ^ x = g ^ w ∧ g ^ y = g ^ z := by
    have hz : (g ^ x - g ^ z) * (g ^ y - g ^ z) = 0 := by
      grind +ring
    have := Fact.mk hp
    simp_all +decide [sub_eq_iff_eq_add]
    grind
  cases hcases <;> simp_all +decide [Set.Subset.antisymm_iff, Set.subset_def]
  · have := hg.pow_inj (by omega : x < p - 1) (by omega : z < p - 1)
    have := hg.pow_inj (by omega : y < p - 1) (by omega : w < p - 1)
    aesop
  · have := hg.pow_inj (by omega : x < p - 1) (by omega : w < p - 1)
    have := hg.pow_inj (by omega : y < p - 1) (by omega : z < p - 1)
    simp_all +decide [add_comm]

/-- For every prime `p`, a modular Sidon set of size `p-1` exists modulo `p(p-1)`. -/
lemma exists_modular_sidon (p : ℕ) (hp : p.Prime) :
    ∃ T : Finset (ZMod (p * (p - 1))),
      T.card = p - 1 ∧ Sidon (T : Set (ZMod (p * (p - 1)))) := by
  obtain ⟨g, hg⟩ : ∃ g : ZMod p, IsPrimitiveRoot g (p - 1) := by
    have := Fact.mk hp
    exact HasEnoughRootsOfUnity.prim
  have hsidon : Sidon (ruzsaSet p g : Set (ZMod (p - 1) × ZMod p)) := by
    convert ruzsaSet_sidon p hp g hg
  have hiso : Nonempty (ZMod (p - 1) × ZMod p ≃+ ZMod (p * (p - 1))) := by
    have h' : Nonempty (ZMod (p - 1) × ZMod p ≃+ ZMod ((p - 1) * p)) := by
      have hcoprime : Nat.gcd (p - 1) p = 1 := by
        simp +decide [hp.one_lt.le]
      exact ⟨(ZMod.chineseRemainder hcoprime).toAddEquiv.symm⟩
    generalize_proofs at *
    rwa [Nat.mul_comm] at h'
  obtain ⟨f⟩ := hiso
  refine ⟨Finset.image (fun x : ZMod (p - 1) × ZMod p => f x) (ruzsaSet p g),
    ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ f.injective, Finset.card_eq_of_bijective]
    · use fun i _ => (i, g ^ i)
    · unfold ruzsaSet
      aesop
    · exact fun i hi => Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
    · simp +contextual only [ZMod.natCast_eq_natCast_iff', Prod.mk.injEq, and_imp]
      exact fun i j hi hj hij h =>
        Nat.mod_eq_of_lt hi ▸ Nat.mod_eq_of_lt hj ▸ hij ▸ rfl
  · intro a b c d ha hb hc hd habcd
    change a ∈ Finset.image f (ruzsaSet p g) at ha
    change b ∈ Finset.image f (ruzsaSet p g) at hb
    change c ∈ Finset.image f (ruzsaSet p g) at hc
    change d ∈ Finset.image f (ruzsaSet p g) at hd
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hd
    have hadd : a' + b' = c' + d' := f.injective (by simpa only [map_add] using habcd)
    have hpairs := hsidon a' b' c' d' ha' hb' hc' hd' hadd
    have himage := congrArg (Set.image f) hpairs
    simpa only [Set.image_insert_eq, Set.image_singleton] using himage

/-- Translate a modular Sidon set so that it avoids zero. -/
lemma shift_sidon_mod (M : ℕ) (hM : 1 < M) (S : Finset (ZMod M))
    (hS : Sidon (S : Set (ZMod M))) (hcard : S.card < M) :
    ∃ S' : Finset (ZMod M), Sidon (S' : Set (ZMod M)) ∧
      S'.card = S.card ∧ (0 : ZMod M) ∉ S' := by
  classical
  have : Fact (1 < M) := ⟨hM⟩
  have ⟨x, hx⟩ : ∃ x : ZMod M, x ∉ S := by
    by_contra h
    push Not at h
    simp [Finset.eq_univ_iff_forall.2 h, ZMod.card M] at hcard
  let S' := S.image (· - x)
  have hinj : Function.Injective (fun y : ZMod M => y - x) := sub_left_injective
  refine ⟨S', ?_, Finset.card_image_of_injective S hinj, ?_⟩
  · intro a b c d ha hb hc hd habcd
    have hmem : ∀ z, z ∈ S' → z + x ∈ (S : Set _) := fun z hz => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      simp [hy]
    have heq := hS _ _ _ _ (hmem a ha) (hmem b hb) (hmem c hc) (hmem d hd)
      (by linear_combination habcd)
    have h1 : (· - x) '' ({a + x, b + x} : Set _) = {a, b} := by
      simp only [Set.image_insert_eq, Set.image_singleton, add_sub_cancel_right]
    have h2 : (· - x) '' ({c + x, d + x} : Set _) = {c, d} := by
      simp only [Set.image_insert_eq, Set.image_singleton, add_sub_cancel_right]
    rw [← h1, ← h2, Set.image_eq_image hinj]
    exact heq
  · intro h0
    obtain ⟨y, hyS, hy0⟩ := Finset.mem_image.1 h0
    exact hx (sub_eq_zero.mp hy0 ▸ hyS)

/-- Lift a zero-free modular Sidon set to representatives in `[1,M-1]`. -/
lemma lift_sidon_mod (M : ℕ) (hM : 1 < M) (S : Finset (ZMod M))
    (hS : Sidon (S : Set (ZMod M))) (h0 : (0 : ZMod M) ∉ S) :
    ∃ T : Finset ℕ, SidonMod M (T : Set ℕ) ∧ T.card = S.card ∧
      (T : Set ℕ) ⊆ Finset.Icc 1 (M - 1) := by
  classical
  have : NeZero M := ⟨by omega⟩
  have hinj : Function.Injective (ZMod.val : ZMod M → ℕ) := ZMod.val_injective M
  refine ⟨S.image ZMod.val, ?_, Finset.card_image_of_injective S hinj, ?_⟩
  · intro a b c d ha hb hc hd habcd
    obtain ⟨na, hna, rfl⟩ := ha
    obtain ⟨nb, hnb, rfl⟩ := hb
    obtain ⟨nc, hnc, rfl⟩ := hc
    obtain ⟨nd, hnd, rfl⟩ := hd
    obtain ⟨za, hza, rfl⟩ := Finset.mem_image.1 hna
    obtain ⟨zb, hzb, rfl⟩ := Finset.mem_image.1 hnb
    obtain ⟨zc, hzc, rfl⟩ := Finset.mem_image.1 hnc
    obtain ⟨zd, hzd, rfl⟩ := Finset.mem_image.1 hnd
    simp only [ZMod.natCast_zmod_val] at habcd ⊢
    exact hS za zb zc zd hza hzb hzc hzd habcd
  · intro n hn
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.1 hn
    have hx0 : x.val ≠ 0 := fun h => h0 ((ZMod.val_eq_zero x).1 h ▸ hxS)
    exact Finset.mem_Icc.2 ⟨Nat.pos_of_ne_zero hx0,
      Nat.le_pred_of_lt (ZMod.val_lt x)⟩

/-! ### The Cilleruelo--Ruzsa--Trujillo auxiliary set -/

/-- The sparse high part of the CRT auxiliary set. -/
def highPart (r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (r / 2)).image fun j => r - 1 + 2 * j

/-- The auxiliary set `[0,r-1] ∪ {r-1+2j : 1 ≤ j ≤ ⌊r/2⌋}`. -/
def indexSet (r : ℕ) : Finset ℕ :=
  Finset.Icc 0 (r - 1) ∪ highPart r

lemma mem_indexSet_cases {r x : ℕ} (hr : 1 ≤ r) (hx : x ∈ indexSet r) :
    x < r ∨ ∃ j ∈ Finset.Icc 1 (r / 2), x = r - 1 + 2 * j := by
  rcases Finset.mem_union.1 hx with hx | hx
  · left
    have := Finset.mem_Icc.1 hx
    omega
  · right
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨j, hj, rfl⟩

lemma highPart_of_mem_indexSet_of_ge {r x : ℕ} (hr : 1 ≤ r)
    (hx : x ∈ indexSet r) (hrx : r ≤ x) : x ∈ highPart r := by
  rcases Finset.mem_union.1 hx with hx | hx
  · have := Finset.mem_Icc.1 hx
    omega
  · exact hx

lemma highPart_min {r x : ℕ} (hx : x ∈ highPart r) : r + 1 ≤ x := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
  have := Finset.mem_Icc.1 hj
  omega

lemma highPart_max {r x : ℕ} (hx : x ∈ highPart r) :
    x ≤ r + 2 * (r / 2) - 1 := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
  have := Finset.mem_Icc.1 hj
  omega

lemma indexSet_subset_Icc {r : ℕ} (hr : 1 ≤ r) :
    indexSet r ⊆ Finset.Icc 0 (r + 2 * (r / 2) - 1) := by
  intro x hx
  refine Finset.mem_Icc.2 ⟨Nat.zero_le x, ?_⟩
  rcases Finset.mem_union.1 hx with hx | hx
  · have := Finset.mem_Icc.1 hx
    omega
  · exact highPart_max hx

lemma highPart_card (r : ℕ) : (highPart r).card = r / 2 := by
  rw [highPart, Finset.card_image_of_injective _ (by
    intro a b h
    exact Nat.mul_left_cancel (by omega) (Nat.add_left_cancel h))]
  simp

lemma indexSet_card {r : ℕ} (hr : 1 ≤ r) : (indexSet r).card = r + r / 2 := by
  rw [indexSet, Finset.card_union_of_disjoint]
  · rw [highPart_card]
    simp [hr]
  · rw [Finset.disjoint_left]
    intro x hxL hxH
    have hxL' := Finset.mem_Icc.1 hxL
    have hxH' := highPart_min hxH
    omega

lemma indexSet_orderedSumReps_le {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (orderedSumReps (indexSet r) n).card ≤ r := by
  classical
  let R := orderedSumReps (indexSet r) n
  have memR : ∀ {p : ℕ × ℕ}, p ∈ R →
      p.1 ∈ indexSet r ∧ p.2 ∈ indexSet r ∧ p.1 + p.2 = n := by
    intro p hp
    have h : (p.1 ∈ indexSet r ∧ p.2 ∈ indexSet r) ∧ p.1 + p.2 = n := by
      simpa [R, orderedSumReps] using hp
    exact ⟨h.1.1, h.1.2, h.2⟩
  by_cases hn0 : n < r
  · let code : ℕ × ℕ → ℕ := fun p => p.1
    have hsub : R.image code ⊆ Finset.range r := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      have h := memR hp
      apply Finset.mem_range.2
      rcases mem_indexSet_cases hr h.1 with hpL | ⟨j, hj, hpH⟩
      · exact hpL
      · have hj1 := (Finset.mem_Icc.1 hj).1
        omega
    have hinj : Set.InjOn code R := by
      intro p hp q hq heq
      have hp' := memR hp
      have hq' := memR hq
      change p.1 = q.1 at heq
      apply Prod.ext
      · exact heq
      · omega
    calc
      R.card = (R.image code).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range r).card := Finset.card_le_card hsub
      _ = r := Finset.card_range r
  · by_cases hn1 : n < 2 * r
    · let code : ℕ × ℕ → ℕ := fun p => if p.1 < r then p.1 else p.2 + 1
      have hsub : R.image code ⊆ Finset.range r := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
        have h := memR hp
        simp only [code]
        split_ifs with hpL
        · exact Finset.mem_range.2 hpL
        · apply Finset.mem_range.2
          have hpH := highPart_of_mem_indexSet_of_ge hr h.1 (by omega)
          have hpMin := highPart_min hpH
          omega
      have hinj : Set.InjOn code R := by
        intro p hp q hq heq
        have hp' := memR hp
        have hq' := memR hq
        simp only [code] at heq
        split_ifs at heq with hpL hqL
        · apply Prod.ext
          · exact heq
          · omega
        · have hqH := highPart_of_mem_indexSet_of_ge hr hq'.1 (by omega)
          obtain ⟨j, hj, hqj⟩ := Finset.mem_image.1 hqH
          have hp2ge : r ≤ p.2 := by
            have hqMin := highPart_min hqH
            omega
          have hp2H := highPart_of_mem_indexSet_of_ge hr hp'.2.1 hp2ge
          obtain ⟨k, hk, hpk⟩ := Finset.mem_image.1 hp2H
          omega
        · have hpH := highPart_of_mem_indexSet_of_ge hr hp'.1 (by omega)
          obtain ⟨j, hj, hpj⟩ := Finset.mem_image.1 hpH
          have hq2ge : r ≤ q.2 := by
            have hpMin := highPart_min hpH
            omega
          have hq2H := highPart_of_mem_indexSet_of_ge hr hq'.2.1 hq2ge
          obtain ⟨k, hk, hqk⟩ := Finset.mem_image.1 hq2H
          omega
        · apply Prod.ext
          · omega
          · exact Nat.add_right_cancel heq
      calc
        R.card = (R.image code).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range r).card := Finset.card_le_card hsub
        _ = r := Finset.card_range r
    · let code : ℕ × ℕ → ℕ × ℕ := fun p =>
        if p.1 < r then (p.2, 1) else (p.1, 0)
      have hsub : R.image code ⊆ highPart r ×ˢ Finset.range 2 := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
        have h := memR hp
        simp only [code]
        split_ifs with hpL
        · apply Finset.mem_product.2
          refine ⟨highPart_of_mem_indexSet_of_ge hr h.2.1 ?_, by simp⟩
          omega
        · apply Finset.mem_product.2
          exact ⟨highPart_of_mem_indexSet_of_ge hr h.1 (by omega), by simp⟩
      have hinj : Set.InjOn code R := by
        intro p hp q hq heq
        have hp' := memR hp
        have hq' := memR hq
        simp only [code] at heq
        split_ifs at heq with hpL hqL
        · have hcoord := Prod.mk.inj heq |>.1
          apply Prod.ext
          · omega
          · exact hcoord
        · have := Prod.mk.inj heq |>.2
          omega
        · have := Prod.mk.inj heq |>.2
          omega
        · have hcoord := Prod.mk.inj heq |>.1
          apply Prod.ext
          · exact hcoord
          · omega
      calc
        R.card = (R.image code).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (highPart r ×ˢ Finset.range 2).card := Finset.card_le_card hsub
        _ = (r / 2) * 2 := by simp [highPart_card]
        _ ≤ r := by omega

/-! ### Pasting a modular Sidon set -/

/-- Paste copies of `C` at the positions indexed by `I`, in base `M`. -/
def paste (M : ℕ) (C I : Finset ℕ) : Finset ℕ :=
  (C ×ˢ I).image fun p => p.1 + M * p.2

lemma paste_encode_injOn {M : ℕ} (hM : 0 < M) {C I : Finset ℕ}
    (hC : C ⊆ Finset.range M) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + M * p.2)
      (↑(C ×ˢ I) : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  have hpC := Finset.mem_product.1 hp |>.1
  have hqC := Finset.mem_product.1 hq |>.1
  have hpLt := Finset.mem_range.1 (hC hpC)
  have hqLt := Finset.mem_range.1 (hC hqC)
  have hfirst : p.1 = q.1 := by
    have hmod := congrArg (fun x : ℕ => x % M) heq
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hpLt, Nat.mod_eq_of_lt hqLt] using hmod
  apply Prod.ext
  · exact hfirst
  · apply Nat.mul_left_cancel hM
    change p.1 + M * p.2 = q.1 + M * q.2 at heq
    rw [hfirst] at heq
    exact Nat.add_left_cancel heq

lemma paste_card {M : ℕ} (hM : 0 < M) {C I : Finset ℕ}
    (hC : C ⊆ Finset.range M) : (paste M C I).card = C.card * I.card := by
  rw [paste, Finset.card_image_of_injOn (paste_encode_injOn hM hC),
    Finset.card_product]

lemma mem_paste_decode {M : ℕ} (hM : 0 < M) {C I : Finset ℕ}
    (hC : C ⊆ Finset.range M) {x : ℕ} (hx : x ∈ paste M C I) :
    x % M ∈ C ∧ x / M ∈ I ∧ x = x % M + M * (x / M) := by
  obtain ⟨p, hp, hpx⟩ := Finset.mem_image.1 hx
  have hp' := Finset.mem_product.1 hp
  have hpLt := Finset.mem_range.1 (hC hp'.1)
  have hrem : x % M = p.1 := by
    rw [← hpx]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hpLt]
  have hquot : x / M = p.2 := by
    rw [← hpx, Nat.add_mul_div_left p.1 p.2 hM, Nat.div_eq_of_lt hpLt]
    simp
  exact ⟨hrem ▸ hp'.1, hquot ▸ hp'.2,
    (Nat.mod_add_div x M).symm.trans (by rw [Nat.mul_comm])⟩

lemma nat_eq_of_mod_eq_of_div_eq {M x y : ℕ}
    (hmod : x % M = y % M) (hdiv : x / M = y / M) : x = y := by
  calc
    x = x % M + M * (x / M) :=
      (Nat.mod_add_div x M).symm.trans (by rw [Nat.mul_comm])
    _ = y % M + M * (y / M) := by rw [hmod, hdiv]
    _ = y := by simpa [Nat.mul_comm] using (Nat.mod_add_div y M)

lemma quotient_sum_eq_of_sum_eq {M a b c d : ℕ} (hM : 0 < M)
    (hsum : a + b = c + d)
    (hres : ({a % M, b % M} : Set ℕ) = {c % M, d % M}) :
    a / M + b / M = c / M + d / M := by
  have hresSum : a % M + b % M = c % M + d % M := by
    rcases Set.pair_eq_pair_iff.mp hres with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have ha := Nat.mod_add_div a M
  have hb := Nat.mod_add_div b M
  have hc := Nat.mod_add_div c M
  have hd := Nat.mod_add_div d M
  have hmul : M * (a / M + b / M) = M * (c / M + d / M) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  exact Nat.mul_left_cancel hM hmul

lemma paste_residue_pair_eq {M : ℕ} (hM : 0 < M) {C I : Finset ℕ}
    (hC : C ⊆ Finset.range M) (hSidon : SidonMod M (C : Set ℕ))
    {p q : ℕ × ℕ}
    (hp1 : p.1 ∈ paste M C I) (hp2 : p.2 ∈ paste M C I)
    (hq1 : q.1 ∈ paste M C I) (hq2 : q.2 ∈ paste M C I)
    (hsum : p.1 + p.2 = q.1 + q.2) :
    ({p.1 % M, p.2 % M} : Set ℕ) = {q.1 % M, q.2 % M} := by
  have : NeZero M := ⟨hM.ne'⟩
  have dp1 := mem_paste_decode hM hC hp1
  have dp2 := mem_paste_decode hM hC hp2
  have dq1 := mem_paste_decode hM hC hq1
  have dq2 := mem_paste_decode hM hC hq2
  have hz := hSidon (p.1 % M : ZMod M) (p.2 % M : ZMod M)
    (q.1 % M : ZMod M) (q.2 % M : ZMod M)
    ⟨p.1 % M, dp1.1, rfl⟩ ⟨p.2 % M, dp2.1, rfl⟩
    ⟨q.1 % M, dq1.1, rfl⟩ ⟨q.2 % M, dq2.1, rfl⟩ (by
      have hcast := congrArg (fun x : ℕ => (x : ZMod M)) hsum
      simpa only [Nat.cast_add, ZMod.natCast_mod] using hcast)
  exact pair_eq_of_zmod_pair_eq M (Nat.mod_lt _ hM) (Nat.mod_lt _ hM)
    (Nat.mod_lt _ hM) (Nat.mod_lt _ hM) hz

lemma paste_subset_Icc {M D : ℕ} (hM : 0 < M) (hD : 0 < D) {C I : Finset ℕ}
    (hC : C ⊆ Finset.Icc 1 (M - 1)) (hI : I ⊆ Finset.Icc 0 (D - 1)) :
    paste M C I ⊆ Finset.Icc 1 (M * D) := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
  have hp' := Finset.mem_product.1 hp
  have hc := Finset.mem_Icc.1 (hC hp'.1)
  have hi := Finset.mem_Icc.1 (hI hp'.2)
  apply Finset.mem_Icc.2
  constructor
  · omega
  · have hcLt : p.1 < M := by omega
    have hiSucc : p.2 + 1 ≤ D := by omega
    have hmul := Nat.mul_le_mul_left M hiSucc
    rw [Nat.mul_add] at hmul
    omega

lemma paste_isB2 {M r : ℕ} (hM : 0 < M) {C I : Finset ℕ}
    (hC : C ⊆ Finset.range M) (hSidon : SidonMod M (C : Set ℕ))
    (hI : ∀ k : ℕ, (orderedSumReps I k).card ≤ r) :
    IsB2 r (paste M C I) := by
  classical
  intro n
  let R := sumReps (paste M C I) n
  have memR : ∀ {p : ℕ × ℕ}, p ∈ R →
      p.1 ∈ paste M C I ∧ p.2 ∈ paste M C I ∧
        p.1 ≤ p.2 ∧ p.1 + p.2 = n := by
    intro p hp
    have h : (p.1 ∈ paste M C I ∧ p.2 ∈ paste M C I) ∧
        (p.1 ≤ p.2 ∧ p.1 + p.2 = n) := by
      simpa [R, sumReps] using hp
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  by_cases hR : R = ∅
  · simp [R, hR]
  · have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.2 hR
    let p0 : ℕ × ℕ := hRne.choose
    have hp0 : p0 ∈ R := hRne.choose_spec
    have hp0' := memR hp0
    let u := p0.1 % M
    let v := p0.2 % M
    let k := p0.1 / M + p0.2 / M
    let align : ℕ × ℕ → ℕ × ℕ := fun p =>
      if p.1 % M = u then (p.1 / M, p.2 / M) else (p.2 / M, p.1 / M)
    have residueCases : ∀ {p : ℕ × ℕ}, p ∈ R →
        (p.1 % M = u ∧ p.2 % M = v) ∨
          (p.1 % M = v ∧ p.2 % M = u) := by
      intro p hp
      have hp' := memR hp
      have hpair := paste_residue_pair_eq hM hC hSidon hp'.1 hp'.2.1
        hp0'.1 hp0'.2.1 (by omega)
      exact Set.pair_eq_pair_iff.mp hpair
    have alignedResidues : ∀ {p : ℕ × ℕ}, p ∈ R →
        if p.1 % M = u then (p.1 % M = u ∧ p.2 % M = v)
        else (p.2 % M = u ∧ p.1 % M = v) := by
      intro p hp
      rcases residueCases hp with h | h <;> split_ifs <;> simp_all
    have hsub : R.image align ⊆ orderedSumReps I k := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hz
      have hp' := memR hp
      have d1 := mem_paste_decode hM hC hp'.1
      have d2 := mem_paste_decode hM hC hp'.2.1
      have hpair := paste_residue_pair_eq hM hC hSidon hp'.1 hp'.2.1
        hp0'.1 hp0'.2.1 (by omega)
      have hqsum := quotient_sum_eq_of_sum_eq hM (by omega) hpair
      simp only [orderedSumReps, Finset.mem_filter, Finset.mem_product, align]
      split_ifs
      · exact ⟨⟨d1.2.1, d2.2.1⟩, hqsum⟩
      · exact ⟨⟨d2.2.1, d1.2.1⟩, by simpa [k, add_comm] using hqsum⟩
    have hinj : Set.InjOn align R := by
      intro p hp q hq heq
      have hp' := memR hp
      have hq' := memR hq
      have hpr := alignedResidues hp
      have hqr := alignedResidues hq
      by_cases hpCase : p.1 % M = u
      · by_cases hqCase : q.1 % M = u
        · simp only [align, hpCase, hqCase, if_pos] at heq
          rw [if_pos hpCase] at hpr
          rw [if_pos hqCase] at hqr
          have hd := Prod.mk.inj heq
          have h1 := nat_eq_of_mod_eq_of_div_eq
            (hpr.1.trans hqr.1.symm) hd.1
          have h2 := nat_eq_of_mod_eq_of_div_eq
            (hpr.2.trans hqr.2.symm) hd.2
          exact Prod.ext h1 h2
        · simp only [align, hpCase, hqCase, if_pos] at heq
          rw [if_pos hpCase] at hpr
          rw [if_neg hqCase] at hqr
          have hd := Prod.mk.inj heq
          have h1 : p.1 = q.2 := nat_eq_of_mod_eq_of_div_eq
            (hpr.1.trans hqr.1.symm) hd.1
          have h2 : p.2 = q.1 := nat_eq_of_mod_eq_of_div_eq
            (hpr.2.trans hqr.2.symm) hd.2
          apply Prod.ext <;> omega
      · by_cases hqCase : q.1 % M = u
        · simp only [align, hpCase, hqCase, if_pos] at heq
          rw [if_neg hpCase] at hpr
          rw [if_pos hqCase] at hqr
          have hd := Prod.mk.inj heq
          have h1 : p.2 = q.1 := nat_eq_of_mod_eq_of_div_eq
            (hpr.1.trans hqr.1.symm) hd.1
          have h2 : p.1 = q.2 := nat_eq_of_mod_eq_of_div_eq
            (hpr.2.trans hqr.2.symm) hd.2
          apply Prod.ext <;> omega
        · simp only [align, hpCase, hqCase] at heq
          rw [if_neg hpCase] at hpr
          rw [if_neg hqCase] at hqr
          have hd := Prod.mk.inj heq
          have h2 := nat_eq_of_mod_eq_of_div_eq
            (hpr.1.trans hqr.1.symm) hd.1
          have h1 := nat_eq_of_mod_eq_of_div_eq
            (hpr.2.trans hqr.2.symm) hd.2
          exact Prod.ext h1 h2
    calc
      (sumReps (paste M C I) n).card = R.card := rfl
      _ = (R.image align).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (orderedSumReps I k).card := Finset.card_le_card hsub
      _ ≤ r := hI k

lemma sumMax_special_lower {r p : ℕ} (hr : 1 ≤ r) (hp : p.Prime) :
    (p - 1) * (r + r / 2) ≤
      sumMax r ((p * (p - 1)) * (r + 2 * (r / 2))) := by
  let M := p * (p - 1)
  let D := r + 2 * (r / 2)
  have hM : 1 < M := by
    dsimp [M]
    have hp2 : 2 ≤ p := hp.two_le
    have hle : 2 * (p - 1) ≤ p * (p - 1) :=
      Nat.mul_le_mul_right (p - 1) hp.two_le
    omega
  obtain ⟨S, hScard, hSsidon⟩ := exists_modular_sidon p hp
  obtain ⟨S', hS'sidon, hS'card, hS'zero⟩ :=
    shift_sidon_mod M hM S hSsidon (by
      rw [hScard]
      dsimp [M]
      have hp2 : 2 ≤ p := hp.two_le
      have hle : 2 * (p - 1) ≤ p * (p - 1) :=
        Nat.mul_le_mul_right (p - 1) hp.two_le
      omega)
  obtain ⟨C, hCsidon, hCcard, hCsub⟩ :=
    lift_sidon_mod M hM S' hS'sidon hS'zero
  have hCrange : C ⊆ Finset.range M := by
    intro x hx
    have := Finset.mem_Icc.1 (hCsub hx)
    exact Finset.mem_range.2 (by omega)
  let P := paste M C (indexSet r)
  have hPB2 : IsB2 r P := by
    exact paste_isB2 (by omega) hCrange hCsidon (indexSet_orderedSumReps_le hr)
  have hPsub : P ⊆ Finset.Icc 1 (M * D) := by
    exact paste_subset_Icc (by omega) (by dsimp [D]; omega) hCsub
      (by simpa [D] using indexSet_subset_Icc hr)
  have hPcard : P.card = (p - 1) * (r + r / 2) := by
    dsimp [P]
    rw [paste_card (by omega) hCrange, indexSet_card hr, hCcard, hS'card, hScard]
  rw [← hPcard]
  classical
  unfold sumMax
  apply Finset.le_sup
  exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hPsub, hPB2⟩

/-! ### The Erdős--Turán upper bound for positive differences -/

lemma diff_erdos_turan_inequality {N m r : ℕ} (hm : 0 < m) (A : Finset ℕ)
    (hDiff : IsDiffB2 r A) (hA : A ⊆ Finset.Icc 1 N) :
    (A.card ^ 2 : ℝ) ≤ (N + m : ℝ) * (A.card / m + r) := by
  have h_cauchy_schwarz :
      ((A.card * m : ℝ)) ^ 2 ≤
      ((Finset.card (Finset.biUnion (Finset.Icc 1 m)
        (fun j => Finset.image (fun a => a + j) A))) : ℝ) *
      ((A.card * m : ℝ) + r * (m * (m - 1))) := by
    have h_cs_inner :
        ((A.card * m : ℝ)) ^ 2 ≤
        ((Finset.card (Finset.biUnion (Finset.Icc 1 m)
          (fun j => Finset.image (fun a => a + j) A))) : ℝ) *
        ((∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
          (fun j => Finset.image (fun a => a + j) A),
          ((∑ j ∈ Finset.Icc 1 m,
            (if ∃ a ∈ A, a + j = x then 1 else 0)) : ℝ) ^ 2)) := by
      have h_cs : ∀ (S : Finset ℕ) (g : ℕ → ℝ),
          (∑ x ∈ S, g x) ^ 2 ≤ (S.card : ℝ) * ∑ x ∈ S, g x ^ 2 := by
        intro S g
        have hnonneg := Finset.sum_le_sum fun x (_ : x ∈ S) =>
          mul_self_nonneg (g x - (∑ y ∈ S, g y) / S.card)
        by_cases hS : S = ∅
        · simp_all
        · have hne : (S.card : ℝ) ≠ 0 := by
            exact Nat.cast_ne_zero.mpr <| Finset.card_ne_zero_of_mem <|
              Classical.choose_spec <| Finset.nonempty_of_ne_empty hS
          have h_exp : ∑ x ∈ S, (g x - (∑ y ∈ S, g y) / S.card) ^ 2 =
              ∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 / S.card := by
            calc
              ∑ x ∈ S, (g x - (∑ y ∈ S, g y) / S.card) ^ 2 =
                  ∑ x ∈ S, (g x ^ 2 - 2 * g x * ((∑ y ∈ S, g y) / S.card) +
                    ((∑ y ∈ S, g y) / S.card) ^ 2) := by
                      congr 1 with x
                      rw [sub_sq]
              _ = ∑ x ∈ S, g x ^ 2 -
                    ∑ x ∈ S, 2 * g x * ((∑ y ∈ S, g y) / S.card) +
                    ∑ x ∈ S, ((∑ y ∈ S, g y) / S.card) ^ 2 := by
                      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              _ = ∑ x ∈ S, g x ^ 2 -
                    2 * ((∑ y ∈ S, g y) / S.card) * (∑ x ∈ S, g x) +
                    S.card * ((∑ y ∈ S, g y) / S.card) ^ 2 := by
                      rw [Finset.sum_const, nsmul_eq_mul]
                      have hsum : ∑ x ∈ S,
                          2 * g x * ((∑ y ∈ S, g y) / S.card) =
                          2 * ((∑ y ∈ S, g y) / S.card) * (∑ x ∈ S, g x) := by
                        rw [Finset.mul_sum]
                        congr 1 with x
                        ring
                      rw [hsum]
              _ = ∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 / S.card := by
                    rw [sq]
                    field_simp [hne]
                    ring
          have hge : 0 ≤ ∑ x ∈ S,
              (g x - (∑ y ∈ S, g y) / S.card) ^ 2 := by positivity
          rw [h_exp] at hge
          have hcard : (0 : ℝ) < S.card := Nat.cast_pos.mpr
            (Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hS))
          have hmul : 0 ≤ S.card * ∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 := by
            have := mul_nonneg hcard.le hge
            field_simp [hne] at this
            exact this
          nlinarith [sq_nonneg (∑ y ∈ S, g y)]
      have hinner (x : ℕ) (hx : x ∈ Finset.Icc 1 m) :
          (∑ x' ∈ Finset.biUnion (Finset.Icc 1 m)
            (fun j => Finset.image (fun a => a + j) A),
            if ∃ a ∈ A, a + x = x' then (1 : ℝ) else 0) = A.card := by
        simp +zetaDelta only [Finset.mem_Icc, Finset.sum_boole, Nat.cast_inj] at *
        rw [show {x' ∈ Finset.biUnion (Finset.Icc 1 m)
            (fun j => Finset.image (fun a => a + j) A) |
            ∃ a ∈ A, a + x = x'} = Finset.image (fun a => a + x) A from ?_]
        · exact Finset.card_image_of_injective _ (add_left_injective x)
        · ext
          aesop
      convert h_cs _ _ using 2
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_eq_sum_ones]
      norm_num
      rw [mul_comm]
    have h_sum_r_sq :
        (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
          (fun j => Finset.image (fun a => a + j) A),
          ((∑ j ∈ Finset.Icc 1 m,
            (if ∃ a ∈ A, a + j = x then 1 else 0)) : ℝ) ^ 2) ≤
        (A.card * m : ℝ) + r * (m * (m - 1)) := by
      have h_sum_bound :
          ∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
            (fun j => Finset.image (fun a => a + j) A),
            ((∑ j ∈ Finset.Icc 1 m,
              (if ∃ a ∈ A, a + j = x then 1 else 0)) : ℝ) ^ 2 ≤
          ∑ j ∈ Finset.Icc 1 m, ∑ j' ∈ Finset.Icc 1 m,
            (if j = j' then (A.card : ℝ) else r) := by
        have h_pair_bound : ∀ j j' : ℕ, j ∈ Finset.Icc 1 m →
            j' ∈ Finset.Icc 1 m →
            (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
              (fun j => Finset.image (fun a => a + j) A),
              (if ∃ a ∈ A, a + j = x then 1 else 0) *
              (if ∃ a ∈ A, a + j' = x then 1 else 0) : ℝ) ≤
            if j = j' then (A.card : ℝ) else r := by
          intro j j' hj hj'
          have h_le_filter :
              (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
                (fun j => Finset.image (fun a => a + j) A),
                (if ∃ a ∈ A, a + j = x then 1 else 0) *
                (if ∃ a ∈ A, a + j' = x then 1 else 0) : ℝ) ≤
              (Finset.filter (fun x => ∃ a ∈ A, a + j = x ∧
                ∃ b ∈ A, b + j' = x)
                (Finset.biUnion (Finset.Icc 1 m)
                  (fun j => Finset.image (fun a => a + j) A))).card := by
            rw [Finset.card_filter]
            push_cast [Finset.sum_mul _ _ _]
            gcongr
            aesop
          split_ifs with heq
          · subst j'
            refine h_le_filter.trans ?_
            norm_cast
            exact le_trans (Finset.card_le_card
              (show Finset.filter (fun x => ∃ a ∈ A, a + j = x ∧
                  ∃ b ∈ A, b + j = x)
                (Finset.biUnion (Finset.Icc 1 m)
                  (fun j => Finset.image (fun a => a + j) A)) ⊆
                Finset.image (fun a => a + j) A from fun x hx => by
                  obtain ⟨_, a, ha, hax, _⟩ := Finset.mem_filter.1 hx
                  exact Finset.mem_image.2 ⟨a, ha, hax⟩))
              Finset.card_image_le
          · refine h_le_filter.trans ?_
            rcases lt_or_gt_of_ne heq with hjj' | hj'j
            · calc
                ((Finset.filter (fun x => ∃ a ∈ A, a + j = x ∧
                    ∃ b ∈ A, b + j' = x)
                    (Finset.biUnion (Finset.Icc 1 m)
                      (fun j => Finset.image (fun a => a + j) A))).card : ℝ) ≤
                    (Finset.image (fun z : ℕ × ℕ => z.1 + j)
                      (diffReps A (j' - j))).card := by
                  norm_cast
                  apply Finset.card_le_card
                  intro x hx
                  obtain ⟨hxU, a, ha, hax, b, hb, hbx⟩ := Finset.mem_filter.1 hx
                  apply Finset.mem_image.2
                  refine ⟨(a, b), ?_, by omega⟩
                  simp [diffReps, ha, hb]
                  omega
                _ ≤ (diffReps A (j' - j)).card := by exact_mod_cast Finset.card_image_le
                _ ≤ r := by exact_mod_cast hDiff (j' - j) (by omega)
            · calc
                ((Finset.filter (fun x => ∃ a ∈ A, a + j = x ∧
                    ∃ b ∈ A, b + j' = x)
                    (Finset.biUnion (Finset.Icc 1 m)
                      (fun j => Finset.image (fun a => a + j) A))).card : ℝ) ≤
                    (Finset.image (fun z : ℕ × ℕ => z.1 + j')
                      (diffReps A (j - j'))).card := by
                  norm_cast
                  apply Finset.card_le_card
                  intro x hx
                  obtain ⟨hxU, a, ha, hax, b, hb, hbx⟩ := Finset.mem_filter.1 hx
                  apply Finset.mem_image.2
                  refine ⟨(b, a), ?_, by omega⟩
                  simp [diffReps, ha, hb]
                  omega
                _ ≤ (diffReps A (j - j')).card := by exact_mod_cast Finset.card_image_le
                _ ≤ r := by exact_mod_cast hDiff (j - j') (by omega)
        have h_expand :
            ∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
              (fun j => Finset.image (fun a => a + j) A),
              (∑ j ∈ Finset.Icc 1 m,
                (if ∃ a ∈ A, a + j = x then 1 else 0) : ℝ) ^ 2 =
            ∑ j ∈ Finset.Icc 1 m, ∑ j' ∈ Finset.Icc 1 m,
              (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
                (fun j => Finset.image (fun a => a + j) A),
                (if ∃ a ∈ A, a + j = x then 1 else 0) *
                (if ∃ a ∈ A, a + j' = x then 1 else 0) : ℝ) := by
          simp +decide only [pow_two, Finset.sum_mul _ _ _]
          rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
          simp +decide only [Finset.mul_sum _ _ _]
        exact h_expand.symm ▸ Finset.sum_le_sum fun i hi =>
          Finset.sum_le_sum fun j hj => h_pair_bound i j hi hj
      simp_all [Finset.sum_ite, Finset.filter_eq, Finset.filter_ne]
      linarith
    exact h_cs_inner.trans (mul_le_mul_of_nonneg_left h_sum_r_sq (by positivity))
  have h_support_size :
      (Finset.card (Finset.biUnion (Finset.Icc 1 m)
        (fun j => Finset.image (fun a => a + j) A)) : ℝ) ≤ N + m - 1 := by
    norm_cast
    rw [Int.subNatNat_of_le (by omega)]
    norm_cast
    exact le_trans (Finset.card_le_card
      (show Finset.biUnion (Finset.Icc 1 m)
        (fun j => Finset.image (fun a => a + j) A) ⊆ Finset.Icc 2 (N + m) from
        Finset.biUnion_subset.2 fun j hj =>
          Finset.image_subset_iff.2 fun a ha => Finset.mem_Icc.2 ⟨by
            have := Finset.mem_Icc.1 (hA ha)
            have := Finset.mem_Icc.1 hj
            omega, by
            have := Finset.mem_Icc.1 (hA ha)
            have := Finset.mem_Icc.1 hj
            omega⟩)) (by norm_num; omega)
  have h_sub : ((A.card * m : ℝ)) ^ 2 ≤
      (N + m - 1 : ℝ) * ((A.card * m : ℝ) + r * (m * (m - 1))) :=
    h_cauchy_schwarz.trans (mul_le_mul_of_nonneg_right h_support_size (by
      exact add_nonneg (by positivity)
        (mul_nonneg (by positivity)
          (mul_nonneg (by positivity) (sub_nonneg.mpr (by norm_cast))))) )
  field_simp at *
  nlinarith [show (m : ℝ) ≥ 1 by norm_cast]

lemma card_le_sumMax {r N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hB2 : IsB2 r A) : A.card ≤ sumMax r N := by
  classical
  unfold sumMax
  apply Finset.le_sup
  exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hA, hB2⟩

lemma card_le_diffMax {r N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hB2 : IsDiffB2 r A) : A.card ≤ diffMax r N := by
  classical
  unfold diffMax
  apply Finset.le_sup
  exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hA, hB2⟩

lemma sumMax_le_of {r N K : ℕ}
    (h : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → IsB2 r A → A.card ≤ K) :
    sumMax r N ≤ K := by
  classical
  unfold sumMax
  exact Finset.sup_le fun A hA => h A (Finset.mem_powerset.1 (Finset.mem_filter.1 hA).1)
    (Finset.mem_filter.1 hA).2

lemma diffMax_le_of {r N K : ℕ}
    (h : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → IsDiffB2 r A → A.card ≤ K) :
    diffMax r N ≤ K := by
  classical
  unfold diffMax
  exact Finset.sup_le fun A hA => h A (Finset.mem_powerset.1 (Finset.mem_filter.1 hA).1)
    (Finset.mem_filter.1 hA).2

/-! ### The asymptotic difference upper bound -/

/-- The positive root bound for a quadratic inequality. -/
lemma quadratic_bound_pos {x b c : ℝ} (hc : 0 ≤ c)
    (h : x ^ 2 ≤ b * x + c) :
    x ≤ (b + Real.sqrt (b ^ 2 + 4 * c)) / 2 := by
  nlinarith [Real.sqrt_nonneg (b ^ 2 + 4 * c),
    Real.mul_self_sqrt (by positivity : 0 ≤ b ^ 2 + 4 * c)]

/-- The finite difference estimate, normalized by `sqrt N`. -/
lemma diff_normalized_bound {N m r : ℕ} (hN : 0 < N) (hm : 0 < m)
    (A : Finset ℕ) (hDiff : IsDiffB2 r A) (hA : A ⊆ Finset.Icc 1 N) :
    (A.card : ℝ) / Real.sqrt N ≤
      ((Real.sqrt N / m + 1 / Real.sqrt N) +
        Real.sqrt ((Real.sqrt N / m + 1 / Real.sqrt N) ^ 2 +
          4 * r * (1 + (m : ℝ) / N))) / 2 := by
  convert quadratic_bound_pos
      (x := (A.card : ℝ) / Real.sqrt N)
      (b := Real.sqrt N / m + 1 / Real.sqrt N)
      (c := (r : ℝ) * (1 + (m : ℝ) / N)) (by positivity) ?_ using 1 <;> try ring_nf
  have hET := diff_erdos_turan_inequality hm A hDiff hA
  have hET' := hET
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNR
  have hsquare : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hNR.le
  field_simp [hmR.ne', hNR.ne', hspos.ne'] at hET'
  have hETN := mul_le_mul_of_nonneg_left hET' hNR.le
  field_simp [hmR.ne', hNR.ne', hspos.ne']
  rw [hsquare]
  nlinarith

/-- The normalized quadratic majorant converges to `sqrt r` whenever
`m/N → 0` and `sqrt N/m → 0`. -/
lemma diff_majorant_tendsto {r : ℕ} {m : ℕ → ℝ}
    (hm1 : Tendsto (fun n : ℕ => m n / (n : ℝ)) atTop (nhds 0))
    (hm2 : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / m n) atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        ((Real.sqrt n / m n + 1 / Real.sqrt n) +
          Real.sqrt ((Real.sqrt n / m n + 1 / Real.sqrt n) ^ 2 +
            4 * r * (1 + m n / n))) / 2)
      atTop (nhds (Real.sqrt r)) := by
  have hinv : Tendsto (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_nhds_zero_nat.sqrt
  have hu := hm2.add hinv
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hv := hone.add hm1
  have hfourr : Tendsto (fun _ : ℕ => (4 : ℝ) * r) atTop (nhds ((4 : ℝ) * r)) :=
    tendsto_const_nhds
  have hroot := ((hu.pow 2).add (hfourr.mul hv)).sqrt
  have hall := (hu.add hroot).div_const 2
  have hsqrt_four : Real.sqrt ((4 : ℝ) * r) = 2 * Real.sqrt r := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4)]
    norm_num
  simpa [hsqrt_four] using hall

/-- The classical Erdős--Turán auxiliary shift length `floor(N^(3/4))`. -/
def shiftLength (N : ℕ) : ℕ := Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))

lemma shiftLength_eventually_pos : ∀ᶠ N : ℕ in atTop, 0 < shiftLength N := by
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  exact Nat.floor_pos.mpr (Real.one_le_rpow hN' (by norm_num))

lemma shiftLength_div_tendsto_zero :
    Tendsto (fun N : ℕ => (shiftLength N : ℝ) / N) atTop (nhds 0) := by
  have h_floor_le : ∀ N : ℕ,
      (shiftLength N : ℝ) / N ≤ (N : ℝ) ^ (-1 / 4 : ℝ) := by
    intro N
    by_cases hN : N = 0
    · simp [hN, shiftLength]
    · rw [div_le_iff₀ (by positivity)]
      exact le_trans (Nat.floor_le (by positivity)) (by
        rw [← Real.rpow_add_one (by positivity)]
        norm_num)
  exact squeeze_zero (fun N => by positivity) h_floor_le (by
    simpa [neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)

lemma sqrt_div_shiftLength_tendsto_zero :
    Tendsto (fun N : ℕ => Real.sqrt N / (shiftLength N : ℝ)) atTop (nhds 0) := by
  suffices h_sqrt_div_floor_le :
      Tendsto (fun N : ℕ =>
        Real.sqrt (N : ℝ) / ((N : ℝ) ^ (3 / 4 : ℝ) - 1)) atTop (nhds 0) by
    refine squeeze_zero_norm' ?_ h_sqrt_div_floor_le
    filter_upwards [eventually_gt_atTop 1] with n hn
    rw [Real.norm_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left (by positivity)
      (sub_pos.mpr <| Real.one_lt_rpow (by norm_cast) <| by norm_num)
      (by
        change (n : ℝ) ^ (3 / 4 : ℝ) - 1 ≤ (shiftLength n : ℝ)
        unfold shiftLength
        linarith [Nat.lt_floor_add_one ((n : ℝ) ^ (3 / 4 : ℝ))])
  suffices h_simplify :
      Tendsto (fun N : ℕ =>
        (N : ℝ) ^ (1 / 2 : ℝ) / ((N : ℝ) ^ (3 / 4 : ℝ) - 1))
        atTop (nhds 0) by
    simpa only [Real.sqrt_eq_rpow] using h_simplify
  suffices h_div :
      Tendsto (fun N : ℕ =>
        (N : ℝ) ^ (1 / 2 - 3 / 4 : ℝ) /
          (1 - 1 / (N : ℝ) ^ (3 / 4 : ℝ))) atTop (nhds 0) by
    refine h_div.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [one_sub_div (by positivity), div_div_eq_mul_div,
      ← Real.rpow_add (by positivity)]
    ring_nf
  norm_num [Real.rpow_neg]
  exact le_trans
    (Tendsto.div
      (tendsto_inv_atTop_zero.comp
        ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop))
      (tendsto_const_nhds.sub <|
        tendsto_inv_atTop_zero.comp
          ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop))
      (by norm_num))
    (by norm_num)

lemma exists_diffMax_set (r N : ℕ) :
    ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧ IsDiffB2 r A ∧ A.card = diffMax r N := by
  classical
  let F := (Finset.Icc 1 N).powerset.filter (IsDiffB2 r)
  have hempty : (∅ : Finset ℕ) ∈ F := by
    simp [F, IsDiffB2, diffReps]
  obtain ⟨A, hAF, hsup⟩ := Finset.exists_mem_eq_sup F ⟨∅, hempty⟩ Finset.card
  refine ⟨A, Finset.mem_powerset.1 (Finset.mem_filter.1 hAF).1,
    (Finset.mem_filter.1 hAF).2, ?_⟩
  exact hsup.symm

/-- Every putative positive-difference asymptotic constant is at most `sqrt r`. -/
theorem diff_constant_upper {r : ℕ} {c : ℝ}
    (hlim : HasSqrtAsymptotic (diffMax r) c) : c ≤ Real.sqrt r := by
  have hmajor := diff_majorant_tendsto
    (r := r) shiftLength_div_tendsto_zero sqrt_div_shiftLength_tendsto_zero
  apply le_of_tendsto_of_tendsto hlim hmajor
  filter_upwards [eventually_gt_atTop 1, shiftLength_eventually_pos] with N hN hm
  obtain ⟨A, hA, hDiff, hcard⟩ := exists_diffMax_set r N
  rw [← hcard]
  exact diff_normalized_bound (by omega) hm A hDiff hA

/-! ### The asymptotic sum lower bound -/

/-- The sequence of primes, indexed from zero. -/
def primeSeq (n : ℕ) : ℕ := Nat.nth Nat.Prime n

lemma primeSeq_prime (n : ℕ) : (primeSeq n).Prime := Nat.prime_nth_prime n

lemma primeSeq_tendsto_atTop : Tendsto primeSeq atTop atTop := by
  refine tendsto_atTop_mono' atTop (Eventually.of_forall fun n => ?_) tendsto_id
  exact le_trans (Nat.le_add_right n 2) (Nat.add_two_le_nth_prime n)

/-- The elementary normalization identity used for the CRT construction. -/
lemma lower_ratio_identity {p D S : ℕ} (hp : 1 < p) (hD : 0 < D) :
    (((p - 1) * S : ℕ) : ℝ) /
        Real.sqrt (((p * (p - 1) * D : ℕ) : ℝ)) =
      (S : ℝ) / Real.sqrt D *
        Real.sqrt ((((p - 1 : ℕ) : ℝ) / (p : ℝ))) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hq : 0 < (p : ℝ) := by positivity
  have hqm1 : 0 < (p : ℝ) - 1 := sub_pos.mpr hpR
  have hrootD : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.2 hDR
  have hrootQ : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hq
  have hrootQm1 : 0 < Real.sqrt ((p : ℝ) - 1) := Real.sqrt_pos.2 hqm1
  push_cast [Nat.cast_sub hp.le]
  rw [show (p : ℝ) * ((p : ℝ) - 1) * D =
      ((p : ℝ) - 1) * ((p : ℝ) * D) by ring,
    Real.sqrt_mul hqm1.le, Real.sqrt_mul hq.le,
    Real.sqrt_div hqm1.le]
  field_simp [hrootD.ne', hrootQ.ne', hrootQm1.ne']
  rw [Real.sq_sqrt hqm1.le]
  ring

lemma primeSeq_ratio_tendsto_one :
    Tendsto (fun n : ℕ =>
      (((primeSeq n - 1 : ℕ) : ℝ) / (primeSeq n : ℝ))) atTop (nhds 1) := by
  have hpCast : Tendsto (fun n : ℕ => (primeSeq n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp primeSeq_tendsto_atTop
  have hinv : Tendsto (fun n : ℕ => 1 / (primeSeq n : ℝ)) atTop (nhds 0) := by
    convert tendsto_inv_atTop_zero.comp hpCast using 1
    funext n
    simp [one_div]
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have heq : (fun n : ℕ =>
      (((primeSeq n - 1 : ℕ) : ℝ) / (primeSeq n : ℝ))) =
      (fun n : ℕ => 1 - 1 / (primeSeq n : ℝ)) := by
    funext n
    have hp : 1 < primeSeq n := (primeSeq_prime n).one_lt
    have hp0 : (primeSeq n : ℝ) ≠ 0 := by positivity
    push_cast [Nat.cast_sub hp.le]
    field_simp [hp0]
  rw [heq]
  simpa using hone.sub hinv

lemma lower_constructed_ratio_tendsto {r : ℕ} (hr : 2 ≤ r) :
    Tendsto
      (fun n : ℕ =>
        ((((primeSeq n - 1) * (r + r / 2) : ℕ) : ℝ) /
          Real.sqrt (((primeSeq n * (primeSeq n - 1) *
            (r + 2 * (r / 2)) : ℕ) : ℝ))))
      atTop
      (nhds (((r + r / 2 : ℕ) : ℝ) /
        Real.sqrt ((r + 2 * (r / 2) : ℕ) : ℝ))) := by
  have hD : 0 < r + 2 * (r / 2) := by omega
  have hratio := primeSeq_ratio_tendsto_one.sqrt
  let C : ℝ := ((r + r / 2 : ℕ) : ℝ) /
    Real.sqrt ((r + 2 * (r / 2) : ℕ) : ℝ)
  have hconst : Tendsto (fun _ : ℕ => C) atTop (nhds C) := tendsto_const_nhds
  have hscaled := hconst.mul hratio
  have heq : (fun n : ℕ =>
      ((((primeSeq n - 1) * (r + r / 2) : ℕ) : ℝ) /
        Real.sqrt (((primeSeq n * (primeSeq n - 1) *
          (r + 2 * (r / 2)) : ℕ) : ℝ)))) =
      (fun n : ℕ => C * Real.sqrt
        (((primeSeq n - 1 : ℕ) : ℝ) / (primeSeq n : ℝ))) := by
    funext n
    exact lower_ratio_identity (primeSeq_prime n).one_lt hD
  rw [heq]
  simpa [C] using hscaled

/-- Every putative sum asymptotic constant is at least the
Cilleruelo--Ruzsa--Trujillo constant. -/
theorem sum_constant_lower {r : ℕ} (hr : 2 ≤ r) {c : ℝ}
    (hlim : HasSqrtAsymptotic (sumMax r) c) :
    (((r + r / 2 : ℕ) : ℝ) /
      Real.sqrt ((r + 2 * (r / 2) : ℕ) : ℝ)) ≤ c := by
  let D := r + 2 * (r / 2)
  let S := r + r / 2
  let P : ℕ → ℕ := fun n => primeSeq n * (primeSeq n - 1) * D
  have hD : 0 < D := by dsimp [D]; omega
  have hP : Tendsto P atTop atTop := by
    refine tendsto_atTop_mono' atTop (Eventually.of_forall fun n => ?_)
      primeSeq_tendsto_atTop
    dsimp [P]
    have hpSub : 0 < primeSeq n - 1 := by
      have := (primeSeq_prime n).two_le
      omega
    exact (Nat.le_mul_of_pos_right _ hpSub).trans
      (Nat.le_mul_of_pos_right _ hD)
  have hmaxlim :
      Tendsto (fun n : ℕ => (sumMax r (P n) : ℝ) / Real.sqrt (P n))
        atTop (nhds c) := hlim.comp hP
  have hlower :
      Tendsto (fun n : ℕ =>
        ((((primeSeq n - 1) * S : ℕ) : ℝ) / Real.sqrt (P n)))
        atTop (nhds ((S : ℝ) / Real.sqrt D)) := by
    simpa [P, S, D] using lower_constructed_ratio_tendsto hr
  have hcompare : ∀ n : ℕ,
      ((((primeSeq n - 1) * S : ℕ) : ℝ) / Real.sqrt (P n)) ≤
        (sumMax r (P n) : ℝ) / Real.sqrt (P n) := by
    intro n
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact_mod_cast sumMax_special_lower (r := r) (by omega : 1 ≤ r)
      (primeSeq_prime n)
  exact le_of_tendsto_of_tendsto hlower hmaxlim (Eventually.of_forall hcompare)

/-! ### The strict separation and the resolution of Problem 863 -/

lemma crt_constant_strictly_greater {r : ℕ} (hr : 2 ≤ r) :
    Real.sqrt r <
      (((r + r / 2 : ℕ) : ℝ) /
        Real.sqrt ((r + 2 * (r / 2) : ℕ) : ℝ)) := by
  have htNat : 0 < r / 2 := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hr)
  have htR : (0 : ℝ) < (r / 2 : ℕ) := by exact_mod_cast htNat
  push_cast
  have hDR : (0 : ℝ) < (r : ℝ) + 2 * (r / 2 : ℕ) := by positivity
  rw [lt_div_iff₀ (Real.sqrt_pos.2 hDR)]
  have hsqR : Real.sqrt (r : ℝ) ^ 2 = r := Real.sq_sqrt hrR.le
  have hsqD : Real.sqrt ((r : ℝ) + 2 * (r / 2 : ℕ)) ^ 2 =
      (r : ℝ) + 2 * (r / 2 : ℕ) := Real.sq_sqrt hDR.le
  have hprodSq :
      (Real.sqrt (r : ℝ) * Real.sqrt ((r : ℝ) + 2 * (r / 2 : ℕ))) ^ 2 =
        (r : ℝ) * ((r : ℝ) + 2 * (r / 2 : ℕ)) := by
    rw [mul_pow, hsqR, hsqD]
  have hstrict :
      (r : ℝ) * ((r : ℝ) + 2 * (r / 2 : ℕ)) <
        ((r : ℝ) + (r / 2 : ℕ)) ^ 2 := by
    nlinarith [sq_pos_of_pos htR]
  have hleft : 0 ≤ Real.sqrt (r : ℝ) *
      Real.sqrt ((r : ℝ) + 2 * (r / 2 : ℕ)) := by positivity
  nlinarith [sq_nonneg
    (Real.sqrt (r : ℝ) * Real.sqrt ((r : ℝ) + 2 * (r / 2 : ℕ)) -
      ((r : ℝ) + (r / 2 : ℕ)))]

/-- The complete quantitative resolution: the difference constant is at most
`sqrt r`, while the sum constant is at least the strictly larger CRT constant. -/
theorem erdos_863_bounds {r : ℕ} (hr : 2 ≤ r) {cSum cDiff : ℝ}
    (hsum : HasSqrtAsymptotic (sumMax r) cSum)
    (hdiff : HasSqrtAsymptotic (diffMax r) cDiff) :
    cDiff ≤ Real.sqrt r ∧
      Real.sqrt r <
        (((r + r / 2 : ℕ) : ℝ) /
          Real.sqrt ((r + 2 * (r / 2) : ℕ) : ℝ)) ∧
      (((r + r / 2 : ℕ) : ℝ) /
          Real.sqrt ((r + 2 * (r / 2) : ℕ) : ℝ)) ≤ cSum := by
  exact ⟨diff_constant_upper hdiff, crt_constant_strictly_greater hr,
    sum_constant_lower hr hsum⟩

/-- Erdős Problem 863: whenever the two square-root asymptotic constants
exist and `r ≥ 2`, the difference constant is strictly smaller. -/
theorem erdos_863 {r : ℕ} (hr : 2 ≤ r) {cSum cDiff : ℝ}
    (hsum : HasSqrtAsymptotic (sumMax r) cSum)
    (hdiff : HasSqrtAsymptotic (diffMax r) cDiff) :
    cDiff < cSum := by
  obtain ⟨hupper, hstrict, hlower⟩ := erdos_863_bounds hr hsum hdiff
  exact lt_of_le_of_lt hupper (lt_of_lt_of_le hstrict hlower)

theorem erdos_863_constants_ne {r : ℕ} (hr : 2 ≤ r) {cSum cDiff : ℝ}
    (hsum : HasSqrtAsymptotic (sumMax r) cSum)
    (hdiff : HasSqrtAsymptotic (diffMax r) cDiff) :
    cSum ≠ cDiff := ne_of_gt (erdos_863 hr hsum hdiff)

#print axioms erdos_863

end

end Erdos863
