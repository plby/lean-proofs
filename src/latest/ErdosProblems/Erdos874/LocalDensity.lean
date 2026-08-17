/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.RestrictedSums

/-!
# Local density of restricted sums of an almost complete progression

This file isolates the elementary ``few holes'' proposition used by
Deshouillers--Freiman.  The definitions below deliberately keep the endpoints
as hypotheses: this avoids making the public statement depend on a choice of
proof that a restricted sumset is nonempty.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The `n` consecutive terms, starting at `z`, of a progression of difference
`q`. -/
def progressionBlock (z q : ℤ) (n : ℕ) : Finset ℤ :=
  Finset.image (fun i : ℕ ↦ z + q * (i : ℤ)) (Finset.range n)

@[simp] lemma mem_progressionBlock {x z q : ℤ} {n : ℕ} :
    x ∈ progressionBlock z q n ↔
      ∃ i < n, x = z + q * (i : ℤ) := by
  simp [progressionBlock, eq_comm]

lemma progressionBlock_card {z q : ℤ} (hq : q ≠ 0) (n : ℕ) :
    (progressionBlock z q n).card = n := by
  have hinj : Function.Injective (fun i : ℕ ↦ z + q * (i : ℤ)) := by
    intro i j hij
    have hmul : q * (i : ℤ) = q * (j : ℤ) := add_left_cancel hij
    have hcast : (i : ℤ) = (j : ℤ) := mul_left_cancel₀ hq hmul
    exact_mod_cast hcast
  simpa only [progressionBlock] using
    (Finset.card_image_of_injective (Finset.range n) hinj).trans (Finset.card_range n)

lemma progressionBlock_one_eq_Icc (z : ℤ) (n : ℕ) :
    progressionBlock z 1 n = Finset.Ico z (z + n) := by
  ext x
  simp only [mem_progressionBlock, one_mul, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi, rfl⟩
    constructor <;> omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨(x - z).toNat, ?_, ?_⟩
    · omega
    · omega

lemma progressionBlock_one_odd_eq_Icc (z : ℤ) (R : ℕ) :
    progressionBlock z 1 (2 * R + 1) = Finset.Icc z (z + 2 * R) := by
  rw [progressionBlock_one_eq_Icc]
  ext x
  simp
  omega

/-- `m` is the least member of `S`.  This relational formulation is convenient
for finite sets whose nonemptiness proof is available only locally. -/
def IsLeastMember (S : Finset ℤ) (m : ℤ) : Prop :=
  m ∈ S ∧ ∀ x ∈ S, m ≤ x

/-- `M` is the greatest member of `S`. -/
def IsGreatestMember (S : Finset ℤ) (M : ℤ) : Prop :=
  M ∈ S ∧ ∀ x ∈ S, x ≤ M

lemma IsLeastMember.unique {S : Finset ℤ} {m n : ℤ}
    (hm : IsLeastMember S m) (hn : IsLeastMember S n) : m = n := by
  exact le_antisymm (hm.2 n hn.1) (hn.2 m hm.1)

lemma IsGreatestMember.unique {S : Finset ℤ} {m n : ℤ}
    (hm : IsGreatestMember S m) (hn : IsGreatestMember S n) : m = n := by
  exact le_antisymm (hn.2 m hm.1) (hm.2 n hn.1)

lemma exists_least_member (S : Finset ℤ) (hS : S.Nonempty) :
    ∃ m, IsLeastMember S m := by
  classical
  refine ⟨S.min' hS, Finset.min'_mem S hS, ?_⟩
  intro x hx
  exact Finset.min'_le S x hx

lemma exists_greatest_member (S : Finset ℤ) (hS : S.Nonempty) :
    ∃ M, IsGreatestMember S M := by
  classical
  refine ⟨S.max' hS, Finset.max'_mem S hS, ?_⟩
  intro x hx
  exact Finset.le_max' S x hx

/-- A block-local formulation of density in one residue class.  The endpoint
inequalities say that all `2*R+1` terms of the block lie in `[m,M]`. -/
def HasLocalDensity (S : Finset ℤ) (m M residue q : ℤ) (R : ℕ) : Prop :=
  ∀ z : ℤ,
    z % q = residue % q →
    m ≤ z →
    z + q * (2 * R : ℕ) ≤ M →
    R + 1 ≤ ((progressionBlock z q (2 * R + 1)) ∩ S).card

/-- The exact conclusion of the Deshouillers--Freiman proposition, separated
from its structural hypotheses. -/
def RestrictedSumsetHasLocalDensity
    (D : Finset ℤ) (s R : ℕ) (a q m M : ℤ) : Prop :=
  HasLocalDensity (restrictedSumset s D) m M (s * a) q R

/-! ## The monotone-path counting lemma

The paper's sliding argument produces a finite increasing path of attainable
sums.  The only integers it can miss are those lying strictly between two
successive path values.  Keeping this elementary bookkeeping separate makes
the later token-sliding argument substantially less brittle. -/

/-- Integers skipped by successive steps of an integer path. -/
def pathHoles : List ℤ → Finset ℤ
  | [] => ∅
  | [_] => ∅
  | x :: y :: xs => Finset.Ioo x y ∪ pathHoles (y :: xs)

/-- Sum of the excesses of the successive positive steps of an integer path.
For a strictly increasing path this is exactly the sum of `(next-current-1)`. -/
def pathExcess : List ℤ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: xs => (y - x - 1).toNat + pathExcess (y :: xs)

lemma card_pathHoles_le_pathExcess : ∀ p : List ℤ,
    (pathHoles p).card ≤ pathExcess p := by
  intro p
  induction p with
  | nil => simp [pathHoles, pathExcess]
  | cons x xs ih =>
      cases xs with
      | nil => simp [pathHoles, pathExcess]
      | cons y ys =>
          rw [pathHoles, pathExcess]
          refine (Finset.card_union_le (Finset.Ioo x y) (pathHoles (y :: ys))).trans ?_
          have hcard : (Finset.Ioo x y).card = (y - x - 1).toNat := by
            simp
          rw [hcard]
          exact Nat.add_le_add_left (by simpa using ih) _

lemma mem_toFinset_or_pathHoles_of_between : ∀ {x y : ℤ} {xs : List ℤ} {z : ℤ},
    (x :: y :: xs).Pairwise (.<.) →
      x ≤ z → z ≤ (x :: y :: xs).getLast (by simp) →
      z ∈ (x :: y :: xs).toFinset ∨ z ∈ pathHoles (x :: y :: xs) := by
  intro x y xs
  induction xs generalizing x y with
  | nil =>
      intro z hp hxz hzlast
      by_cases hzy : z < y
      · by_cases hzx : z = x
        · left
          simp [hzx]
        · right
          simp [pathHoles]
          exact ⟨by omega, hzy⟩
      · left
        have hzy' : z = y := by
          change z ≤ y at hzlast
          omega
        simp [hzy']
  | cons w ws ih =>
      intro z hp hxz hzlast
      by_cases hzy : z < y
      · by_cases hzx : z = x
        · left
          simp [hzx]
        · right
          simp only [pathHoles, Finset.mem_union, Finset.mem_Ioo]
          exact Or.inl ⟨by omega, hzy⟩
      · have hyz : y ≤ z := by omega
        have hrec := ih hp.tail hyz (by simpa using hzlast)
        rcases hrec with hmem | hhole
        · left
          simp only [List.mem_toFinset] at hmem ⊢
          exact List.mem_cons_of_mem x hmem
        · right
          change z ∈ Finset.Ioo x y ∪ pathHoles (y :: w :: ws)
          exact Finset.mem_union.mpr (Or.inr hhole)

/-- Every missing integer between the endpoints of a strictly increasing path
is charged to a skipped integer of that path. -/
lemma interval_sdiff_subset_pathHoles {x y : ℤ} {xs : List ℤ}
    (hp : (x :: y :: xs).Pairwise (.<.))
    {S : Finset ℤ} (hpath : ∀ z ∈ (x :: y :: xs), z ∈ S) :
    Finset.Icc x ((x :: y :: xs).getLast (by simp)) \ S ⊆
      pathHoles (x :: y :: xs) := by
  intro z hz
  simp only [Finset.mem_sdiff, Finset.mem_Icc] at hz
  have hcover := mem_toFinset_or_pathHoles_of_between hp hz.1.1 hz.1.2
  rcases hcover with hpoint | hhole
  · have : z ∈ S := hpath z (by simpa using hpoint)
    exact (hz.2 this).elim
  · exact hhole

/-- Cardinal form of `interval_sdiff_subset_pathHoles`. -/
lemma card_interval_sdiff_le_pathExcess {x y : ℤ} {xs : List ℤ}
    (hp : (x :: y :: xs).Pairwise (.<.))
    {S : Finset ℤ} (hpath : ∀ z ∈ (x :: y :: xs), z ∈ S) :
    (Finset.Icc x ((x :: y :: xs).getLast (by simp)) \ S).card ≤
      pathExcess (x :: y :: xs) := by
  exact (Finset.card_le_card (interval_sdiff_subset_pathHoles hp hpath)).trans
    (card_pathHoles_le_pathExcess (x :: y :: xs))

/-- A convenient interface for the canonical sliding path: if every relevant
block is spanned by a strictly increasing path in `S` whose total excess is at
most `R`, then `S` has the desired local density (in the normalized residue
class of difference one). -/
theorem hasLocalDensity_one_of_spanning_paths {S : Finset ℤ} {m M residue : ℤ}
    {R : ℕ}
    (hpaths : ∀ z : ℤ, m ≤ z → z + (2 * R : ℕ) ≤ M →
      ∃ x y : ℤ, ∃ xs : List ℤ,
        (x :: y :: xs).Pairwise (.<.) ∧
        x ≤ z ∧ z + (2 * R : ℕ) ≤ (x :: y :: xs).getLast (by simp) ∧
        (∀ w ∈ (x :: y :: xs), w ∈ S) ∧
        pathExcess (x :: y :: xs) ≤ R) :
    HasLocalDensity S m M residue 1 R := by
  intro z hres hzlo hzhi
  obtain ⟨x, y, xs, hp, hxz, hzlast, hpath, hexcess⟩ := hpaths z hzlo (by simpa using hzhi)
  let p : List ℤ := x :: y :: xs
  let B : Finset ℤ := Finset.Icc z (z + 2 * R)
  have hBsub : B \ S ⊆ Finset.Icc x (p.getLast (by simp [p])) \ S := by
    intro w hw
    change w ∈ Finset.Icc z (z + 2 * R) \ S at hw
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hw ⊢
    exact ⟨⟨le_trans hxz hw.1.1, le_trans hw.1.2 hzlast⟩, hw.2⟩
  have hmiss : (B \ S).card ≤ R := by
    calc
      (B \ S).card ≤ (Finset.Icc x (p.getLast (by simp [p])) \ S).card :=
        Finset.card_le_card hBsub
      _ ≤ pathExcess p := by
        simpa [p] using card_interval_sdiff_le_pathExcess hp hpath
      _ ≤ R := hexcess
  have hBcard : B.card = 2 * R + 1 := by
    have hcast : z + 2 * (R : ℤ) + 1 - z = ((2 * R + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    simp [B, hcast]
    <;> omega
  rw [progressionBlock_one_odd_eq_Icc]
  change R + 1 ≤ (B ∩ S).card
  have hpartition := Finset.card_sdiff_add_card_inter B S
  omega

end

end Erdos874

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Affine transport from the normalized proposition -/

lemma progressionBlock_affine (z q c : ℤ) (n : ℕ) :
    progressionBlock (q * z + c) q n =
      (progressionBlock z 1 n).image (fun w ↦ q * w + c) := by
  ext x
  simp only [mem_progressionBlock, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨z + 1 * (i : ℤ), ⟨i, hi, rfl⟩, ?_⟩
    ring
  · rintro ⟨w, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨i, hi, ?_⟩
    ring

private lemma affine_injective_local {q c : ℤ} (hq : q ≠ 0) :
    Function.Injective (fun z : ℤ ↦ q * z + c) := by
  intro x y hxy
  apply mul_left_cancel₀ hq
  exact add_right_cancel hxy

theorem HasLocalDensity.image_affine
    {S : Finset ℤ} {m M residue : ℤ} {R : ℕ}
    (hS : HasLocalDensity S m M residue 1 R)
    (q c : ℤ) (hq : 0 < q) :
    HasLocalDensity (S.image fun z ↦ q * z + c)
      (q * m + c) (q * M + c) c q R := by
  intro z hzmod hzlo hzhi
  have hmodeq : Int.ModEq q z c := hzmod
  rw [Int.modEq_iff_dvd] at hmodeq
  obtain ⟨t, ht⟩ := hmodeq
  have hzrepr : z = q * (-t) + c := by
    rw [mul_neg]
    linarith
  let z₀ : ℤ := -t
  have hzrepr₀ : z = q * z₀ + c := by simpa [z₀] using hzrepr
  have hz₀lo : m ≤ z₀ := by
    rw [hzrepr₀] at hzlo
    nlinarith
  have hz₀hi : z₀ + (2 * R : ℕ) ≤ M := by
    rw [hzrepr₀] at hzhi
    have hscaled : q * (z₀ + (2 * R : ℕ)) + c ≤ q * M + c := by
      calc
        q * (z₀ + (2 * R : ℕ)) + c =
            q * z₀ + c + q * (2 * R : ℕ) := by ring
        _ ≤ q * M + c := hzhi
    nlinarith
  have hnorm := hS z₀ (by simp) hz₀lo (by simpa using hz₀hi)
  have himage : progressionBlock z q (2 * R + 1) =
      (progressionBlock z₀ 1 (2 * R + 1)).image (fun w ↦ q * w + c) := by
    rw [hzrepr₀]
    exact progressionBlock_affine z₀ q c (2 * R + 1)
  rw [himage, ← Finset.image_inter _ _ (affine_injective_local hq.ne'),
    Finset.card_image_of_injective _ (affine_injective_local hq.ne')]
  exact hnorm

theorem restrictedSumset_localDensity_of_affine_normalization
    {D V : Finset ℤ} {s R : ℕ} {m₀ M₀ residue₀ a c q : ℤ}
    (hq : 0 < q)
    (hV : V = D.image fun x ↦ q * x + c)
    (ha : Int.ModEq q a c)
    (hnorm : HasLocalDensity (restrictedSumset s D) m₀ M₀ residue₀ 1 R) :
    HasLocalDensity (restrictedSumset s V)
      (q * m₀ + (s : ℤ) * c) (q * M₀ + (s : ℤ) * c)
      ((s : ℤ) * a) q R := by
  have himage : restrictedSumset s V =
      (restrictedSumset s D).image (fun z ↦ q * z + (s : ℤ) * c) := by
    rw [hV, restrictedSumset_image_affine D s q c hq.ne']
  have hdense := hnorm.image_affine q ((s : ℤ) * c) hq
  rw [← himage] at hdense
  intro z hzmod hzlo hzhi
  apply hdense z
  · have hsa : Int.ModEq q ((s : ℤ) * a) ((s : ℤ) * c) := by
      exact ha.mul_left (s : ℤ)
    exact hzmod.trans hsa
  · exact hzlo
  · exact hzhi

/-- Divide one residue class by its positive step after translation. -/
def normalizedCarrier (V : Finset ℤ) (c q : ℤ) : Finset ℤ :=
  V.image fun x ↦ (x - c) / q

private lemma affine_normalize_eq_self {x c q : ℤ}
    (hx : Int.ModEq q x c) : q * ((x - c) / q) + c = x := by
  have hdvdneg : q ∣ c - x := Int.modEq_iff_dvd.mp hx
  have hdvd : q ∣ x - c := by
    obtain ⟨k, hk⟩ := hdvdneg
    refine ⟨-k, ?_⟩
    rw [mul_neg]
    linarith
  have hcancel := Int.ediv_mul_cancel hdvd
  calc
    q * ((x - c) / q) + c = ((x - c) / q) * q + c := by ring
    _ = (x - c) + c := by rw [hcancel]
    _ = x := by ring

theorem image_normalizedCarrier_affine {V : Finset ℤ} {c q : ℤ}
    (hV : ∀ x ∈ V, Int.ModEq q x c) :
    (normalizedCarrier V c q).image (fun x ↦ q * x + c) = V := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    simpa only [affine_normalize_eq_self (hV v hv)] using hv
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨(x - c) / q, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
    exact affine_normalize_eq_self (hV x hx)

theorem restrictedSumset_localDensity_of_canonical_normalizedCarrier
    {V : Finset ℤ} {s R : ℕ} {m₀ M₀ residue₀ a c q : ℤ}
    (hq : 0 < q)
    (hV : ∀ x ∈ V, Int.ModEq q x c)
    (ha : Int.ModEq q a c)
    (hnorm : HasLocalDensity
      (restrictedSumset s (normalizedCarrier V c q)) m₀ M₀ residue₀ 1 R) :
    HasLocalDensity (restrictedSumset s V)
      (q * m₀ + (s : ℤ) * c) (q * M₀ + (s : ℤ) * c)
      ((s : ℤ) * a) q R := by
  apply restrictedSumset_localDensity_of_affine_normalization hq
    (image_normalizedCarrier_affine hV).symm ha hnorm

end

end Erdos874

/- The checked copy of this source-order draft follows the canonical-value
definitions below. -/
/-
namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

private lemma exists_adjacent_straddling {f : ℕ → ℤ} {n : ℕ} {z : ℤ}
    (hstep : ∀ i < n, f i < f (i + 1))
    (hlo : f 0 ≤ z) (hhi : z ≤ f n)
    (hmiss : ∀ i ≤ n, z ≠ f i) :
    ∃ i < n, f i < z ∧ z < f (i + 1) := by
  induction n generalizing f with
  | zero => exact (hmiss 0 le_rfl (le_antisymm hhi hlo)).elim
  | succ n ih =>
      have hf0 : f 0 < z := lt_of_le_of_ne hlo (Ne.symm (hmiss 0 (by omega)))
      by_cases hz1 : z < f 1
      · exact ⟨0, by omega, hf0, hz1⟩
      · have hf1 : f 1 < z := by
          have hle : f 1 ≤ z := le_of_not_gt hz1
          exact lt_of_le_of_ne hle (hmiss 1 (by omega))
        obtain ⟨i, hi, hfi, hfis⟩ := ih
          (f := fun r ↦ f (r + 1))
          (fun i hi ↦ by simpa [Nat.add_assoc] using hstep (i + 1) (by omega))
          hf1 (by simpa using hhi)
          (fun i hi hEq ↦ hmiss (i + 1) (by omega) (by simpa using hEq))
        exact ⟨i + 1, by omega, by simpa [Nat.add_assoc] using hfi,
          by simpa [Nat.add_assoc] using hfis⟩

private def canonicalDFBoundary (d : ℕ → ℤ) (L s p : ℕ) : ℤ :=
  if p < s then
    canonicalDFValue d L s (s - 1 - p) (s - 1 - p)
  else
    canonicalDFValue d L s 0 L

private lemma canonicalDFValue_first (d : ℕ → ℤ) {L s : ℕ} (hs : 0 < s) :
    canonicalDFBoundary d L s 0 = canonicalDFValue d L s (s - 1) (s - 1) := by
  simp [canonicalDFBoundary, hs]

private lemma canonicalDFValue_last (d : ℕ → ℤ) (L s : ℕ) :
    canonicalDFBoundary d L s s = canonicalDFValue d L s 0 L := by
  simp [canonicalDFBoundary]

private lemma canonicalDFBoundary_step
    {d : ℕ → ℤ} {L s p : ℕ}
    (hL : 0 < L) (hp : p < s)
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < L + s → d i < d j) :
    canonicalDFBoundary d L s p < canonicalDFBoundary d L s (p + 1) := by
  let j := s - 1 - p
  have hjs : j < s := by dsimp [j]; omega
  have hjL : j < L + j := by omega
  have hLj : L + j < L + s := by omega
  have hv : canonicalDFValue d L s j j < canonicalDFValue d L s j (L + j) := by
    rw [canonicalDFValue_eq d hjs le_rfl (by omega),
      canonicalDFValue_eq d hjs (by omega) le_rfl]
    exact add_lt_add_right (add_lt_add_left (hmono hjL hLj) _) _
  rw [canonicalDFBoundary, if_pos hp]
  by_cases hps : p + 1 < s
  · rw [if_pos hps]
    have hj : 0 < j := by dsimp [j]; omega
    have hidx : s - 1 - (p + 1) = j - 1 := by dsimp [j]; omega
    rw [hidx, ← canonicalDFValue_boundary d hj hjs]
    exact hv
  · rw [if_neg hps]
    have hj0 : j = 0 := by dsimp [j]; omega
    simpa [hj0] using hv

private lemma canonicalDFEdge_exists
    {D : Finset ℤ} {d : ℕ → ℤ} {L s : ℕ} {z : ℤ}
    (hD : D = (Finset.range (L + s)).image d)
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < L + s → d i < d j)
    (hL : 0 < L) (hs : 0 < s)
    (hzlo : canonicalDFValue d L s (s - 1) (s - 1) ≤ z)
    (hzhi : z ≤ canonicalDFValue d L s 0 L)
    (hzmiss : z ∉ restrictedSumset s D) :
    ∃ j k : ℕ, j < s ∧ j ≤ k ∧ k < L + j ∧
      canonicalDFValue d L s j k < z ∧
      z < canonicalDFValue d L s j (k + 1) := by
  have hinj : Set.InjOn d (Finset.range (L + s)) := by
    intro i hi j hj hij
    rcases lt_trichotomy i j with hij' | hij' | hij'
    · exact (hmono hij' (Finset.mem_range.mp hj)).ne hij
    · exact hij'
    · exact ((hmono hij' (Finset.mem_range.mp hi)).ne hij.symm).elim
  have hboundaryMiss : ∀ p ≤ s, z ≠ canonicalDFBoundary d L s p := by
    intro p hp heq
    by_cases hps : p < s
    · have hj : s - 1 - p < s := by omega
      have hmem := canonicalDFValue_mem_restrictedSumset hD hinj hj le_rfl (by omega :
        s - 1 - p ≤ L + (s - 1 - p))
      exact hzmiss (heq ▸ hmem)
    · have hpEq : p = s := by omega
      subst p
      have hmem := canonicalDFValue_mem_restrictedSumset hD hinj (by omega : 0 < s)
        (by omega : 0 ≤ L) le_rfl
      exact hzmiss (canonicalDFValue_last d L s ▸ heq ▸ hmem)
  obtain ⟨p, hp, hpz, hzp⟩ := exists_adjacent_straddling
    (f := canonicalDFBoundary d L s) (n := s) (z := z)
    (fun p hp ↦ canonicalDFBoundary_step hL hp hmono)
    (by simpa [canonicalDFValue_first d hs] using hzlo)
    (by simpa [canonicalDFValue_last] using hzhi) hboundaryMiss
  let j := s - 1 - p
  have hj : j < s := by dsimp [j]; omega
  have hphaseEnd : canonicalDFBoundary d L s (p + 1) =
      canonicalDFValue d L s j (L + j) := by
    by_cases hps : p + 1 < s
    · rw [canonicalDFBoundary, if_pos hps]
      have hjpos : 0 < j := by dsimp [j]; omega
      have hidx : s - 1 - (p + 1) = j - 1 := by dsimp [j]; omega
      rw [hidx, ← canonicalDFValue_boundary d hjpos hj]
    · have hj0 : j = 0 := by dsimp [j]; omega
      rw [canonicalDFBoundary, if_neg hps, hj0]
  have hphaseStart : canonicalDFBoundary d L s p = canonicalDFValue d L s j j := by
    simp [canonicalDFBoundary, hp, j]
  have hpointMiss : ∀ r ≤ L, z ≠ canonicalDFValue d L s j (j + r) := by
    intro r hr heq
    have hmem := canonicalDFValue_mem_restrictedSumset hD hinj hj (by omega) (by omega)
    exact hzmiss (heq ▸ hmem)
  obtain ⟨r, hr, hrz, hzr⟩ := exists_adjacent_straddling
    (f := fun r ↦ canonicalDFValue d L s j (j + r)) (n := L) (z := z)
    (fun r hr ↦ by
      have hstep := canonicalDFValue_step d hj (by omega : j ≤ j + r)
        (by omega : j + r < L + j)
      have hdstep := hmono (show j + r < j + (r + 1) by omega)
        (show j + (r + 1) < L + s by omega)
      omega)
    (by simpa [hphaseStart] using hpz.le)
    (by simpa [hphaseEnd] using hzp.le) hpointMiss
  exact ⟨j, j + r, hj, by omega, by omega, hrz, by simpa [Nat.add_assoc] using hzr⟩

end

end Erdos874

-/

/-! ## The canonical Deshouillers--Freiman path

The following second section gives the ordered-index version of the sharp
local-density proposition.  Writing `T = L + s`, the hypothesis in the
paper implies `4 * R + 3 ≤ L`.  The point `canonicalDFValue d L s j k`
is the sum denoted `P(j,k)` in the proof: the first `j` entries, the moving
entry with index `k`, and the last `s-j-1` entries.
-/

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

private def canonicalDFIndices (L s j k : ℕ) : Finset ℕ :=
  (Finset.range j ∪ {k}) ∪ Finset.Ico (L + j + 1) (L + s)

private def canonicalDFValue (d : ℕ → ℤ) (L s j k : ℕ) : ℤ :=
  (canonicalDFIndices L s j k).sum d

private lemma canonicalDFIndices_card {L s j k : ℕ}
    (hj : j < s) (hjk : j ≤ k) (hk : k ≤ L + j) :
    (canonicalDFIndices L s j k).card = s := by
  have hkr : k ∉ Finset.range j := by simp; omega
  have hdisj₁ : Disjoint (Finset.range j ∪ {k})
      (Finset.Ico (L + j + 1) (L + s)) := by
    rw [Finset.disjoint_left]
    intro x hx hxIco
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico] at hxIco
    rcases hx with hx | rfl <;> omega
  rw [canonicalDFIndices, Finset.card_union_of_disjoint hdisj₁,
    Finset.card_union_of_disjoint]
  · simp only [Finset.card_range, Finset.card_singleton]
    simp
    omega
  · simpa [Finset.disjoint_singleton_right]

private lemma canonicalDFIndices_subset_range {L s j k : ℕ}
    (hj : j < s) (hjk : j ≤ k) (hk : k ≤ L + j) :
    canonicalDFIndices L s j k ⊆ Finset.range (L + s) := by
  intro x hx
  simp only [canonicalDFIndices, Finset.mem_union, Finset.mem_range,
    Finset.mem_singleton, Finset.mem_Ico] at hx ⊢
  rcases hx with (hx | rfl) | hx <;> omega

private lemma canonicalDFValue_mem_restrictedSumset
    {D : Finset ℤ} {d : ℕ → ℤ} {L s j k : ℕ}
    (hD : D = (Finset.range (L + s)).image d)
    (hinj : Set.InjOn d (Finset.range (L + s)))
    (hj : j < s) (hjk : j ≤ k) (hk : k ≤ L + j) :
    canonicalDFValue d L s j k ∈ restrictedSumset s D := by
  refine mem_restrictedSumset.mpr
    ⟨(canonicalDFIndices L s j k).image d, ?_, ?_, ?_⟩
  · rw [hD]
    exact Finset.image_mono _ (canonicalDFIndices_subset_range hj hjk hk)
  · rw [Finset.card_image_of_injOn]
    · exact canonicalDFIndices_card hj hjk hk
    · exact hinj.mono (canonicalDFIndices_subset_range hj hjk hk)
  · rw [canonicalDFValue, Finset.sum_image]
    intro x hx y hy hxy
    exact hinj (canonicalDFIndices_subset_range hj hjk hk hx)
      (canonicalDFIndices_subset_range hj hjk hk hy) hxy

private lemma canonicalDFValue_eq
    (d : ℕ → ℤ) {L s j k : ℕ} (hj : j < s)
    (hjk : j ≤ k) (hk : k ≤ L + j) :
    canonicalDFValue d L s j k =
      (∑ i ∈ Finset.range j, d i) + d k +
        ∑ i ∈ Finset.Ico (L + j + 1) (L + s), d i := by
  have hkr : k ∉ Finset.range j := by simp; omega
  have hdisj₁ : Disjoint (Finset.range j ∪ {k})
      (Finset.Ico (L + j + 1) (L + s)) := by
    rw [Finset.disjoint_left]
    intro x hx hxIco
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico] at hxIco
    rcases hx with hx | rfl <;> omega
  rw [canonicalDFValue, canonicalDFIndices, Finset.sum_union hdisj₁,
    Finset.sum_union]
  · simp
  · simpa [Finset.disjoint_singleton_right]

private lemma canonicalDFValue_step (d : ℕ → ℤ) {L s j k : ℕ}
    (hj : j < s) (hjk : j ≤ k) (hk : k < L + j) :
    canonicalDFValue d L s j (k + 1) - canonicalDFValue d L s j k =
      d (k + 1) - d k := by
  rw [canonicalDFValue_eq d hj (by omega) (by omega),
    canonicalDFValue_eq d hj hjk hk.le]
  ring

private lemma canonicalDFValue_boundary (d : ℕ → ℤ) {L s j : ℕ}
    (hj : 0 < j) (hjs : j < s) :
    canonicalDFValue d L s j (L + j) =
      canonicalDFValue d L s (j - 1) (j - 1) := by
  unfold canonicalDFValue
  congr 1
  ext x
  simp only [canonicalDFIndices, Finset.mem_union, Finset.mem_range,
    Finset.mem_singleton, Finset.mem_Ico]
  omega

end

end Erdos874

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Abstract labeled-path injection

This is the finite bookkeeping core of the canonical Deshouillers--Freiman
path.  A missing value chooses a labeled edge and is charged to a ground-set
hole.  Equal labels on different edges force their starts more than `3 * R`
apart, whereas every edge meeting the target block starts in a window of
diameter less than `3 * R`. -/

theorem localDensity_of_labeled_path
    {Edge Label Hole : Type*} [DecidableEq Edge] [DecidableEq Label] [DecidableEq Hole]
    (S : Finset ℤ) (H : Finset Hole) (R : ℕ) (y : ℤ)
    (edge : ℤ → Edge) (label : Edge → Label) (start : Edge → ℤ)
    (charge : ℤ → Hole)
    (hmap : ∀ z ∈ Finset.Icc y (y + (2 * R : ℕ)) \ S, charge z ∈ H)
    (hchargeLabel : ∀ z ∈ Finset.Icc y (y + (2 * R : ℕ)) \ S,
      ∀ w ∈ Finset.Icc y (y + (2 * R : ℕ)) \ S,
        charge z = charge w → label (edge z) = label (edge w))
    (hrepeat : ∀ e f : Edge, e ≠ f → label e = label f →
      start e + (3 * R : ℕ) < start f ∨ start f + (3 * R : ℕ) < start e)
    (hwindow : ∀ z ∈ Finset.Icc y (y + (2 * R : ℕ)) \ S,
      y - (R : ℕ) ≤ start (edge z) ∧
        start (edge z) ≤ y + (2 * R : ℕ) - 1)
    (hoffset : ∀ z ∈ Finset.Icc y (y + (2 * R : ℕ)) \ S,
      ∀ w ∈ Finset.Icc y (y + (2 * R : ℕ)) \ S,
        edge z = edge w → charge z = charge w → z = w)
    (hH : H.card ≤ R) :
    R + 1 ≤ (Finset.Icc y (y + (2 * R : ℕ)) ∩ S).card := by
  let B : Finset ℤ := Finset.Icc y (y + (2 * R : ℕ))
  have hinj : Set.InjOn charge ↑(B \ S) := by
    intro z hz w hw hzw
    have hz' : z ∈ Finset.Icc y (y + (2 * R : ℕ)) \ S := by simpa [B] using hz
    have hw' : w ∈ Finset.Icc y (y + (2 * R : ℕ)) \ S := by simpa [B] using hw
    have hlabel := hchargeLabel z hz' w hw' hzw
    have hedge : edge z = edge w := by
      by_contra hne
      rcases hrepeat (edge z) (edge w) hne hlabel with hsep | hsep
      · have hzwin := hwindow z hz'
        have hwwin := hwindow w hw'
        omega
      · have hzwin := hwindow z hz'
        have hwwin := hwindow w hw'
        omega
    exact hoffset z hz' w hw' hedge hzw
  have hmiss : (B \ S).card ≤ H.card := by
    apply Finset.card_le_card_of_injOn charge
    · intro z hz
      exact hmap z (by simpa [B] using hz)
    · exact hinj
  have hBcard : B.card = 2 * R + 1 := by
    rw [show B = Finset.Icc y (y + (2 * R : ℕ)) by rfl, Int.card_Icc]
    have heq : y + (2 * R : ℕ) + 1 - y = ((2 * R + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [heq]
    exact Int.toNat_natCast (2 * R + 1)
  change R + 1 ≤ (B ∩ S).card
  have hpartition := Finset.card_sdiff_add_card_inter B S
  omega

end

end Erdos874

/-
/-
namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

private lemma exists_adjacent_straddling_checked {f : ℕ → ℤ} {n : ℕ} {z : ℤ}
    (hstep : ∀ i < n, f i < f (i + 1))
    (hlo : f 0 ≤ z) (hhi : z ≤ f n)
    (hmiss : ∀ i ≤ n, z ≠ f i) :
    ∃ i < n, f i < z ∧ z < f (i + 1) := by
  induction n generalizing f with
  | zero => exact (hmiss 0 le_rfl (le_antisymm hhi hlo)).elim
  | succ n ih =>
      have hf0 : f 0 < z := lt_of_le_of_ne hlo (Ne.symm (hmiss 0 (by omega)))
      by_cases hz1 : z < f 1
      · exact ⟨0, by omega, hf0, hz1⟩
      · have hf1 : f 1 < z := by
          have hle : f 1 ≤ z := le_of_not_gt hz1
          exact lt_of_le_of_ne hle (Ne.symm (hmiss 1 (by omega)))
        obtain ⟨i, hi, hfi, hfis⟩ := ih
          (f := fun r ↦ f (r + 1))
          (fun i hi ↦ by simpa [Nat.add_assoc] using hstep (i + 1) (by omega))
          hf1.le (by simpa using hhi)
          (fun i hi hEq ↦ hmiss (i + 1) (by omega) (by simpa using hEq))
        exact ⟨i + 1, by omega, by simpa [Nat.add_assoc] using hfi,
          by simpa [Nat.add_assoc] using hfis⟩

private def canonicalDFBoundaryChecked (d : ℕ → ℤ) (L s p : ℕ) : ℤ :=
  if p < s then
    canonicalDFValue d L s (s - 1 - p) (s - 1 - p)
  else
    canonicalDFValue d L s 0 L

private lemma canonicalDFBoundaryChecked_step
    {d : ℕ → ℤ} {L s p : ℕ}
    (hL : 0 < L) (hp : p < s)
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < L + s → d i < d j) :
    canonicalDFBoundaryChecked d L s p < canonicalDFBoundaryChecked d L s (p + 1) := by
  let j := s - 1 - p
  have hjs : j < s := by dsimp [j]; omega
  have hv : canonicalDFValue d L s j j < canonicalDFValue d L s j (L + j) := by
    rw [canonicalDFValue_eq d hjs le_rfl (by omega),
      canonicalDFValue_eq d hjs (by omega) le_rfl]
    exact add_lt_add_right
      (add_lt_add_left (hmono (by omega) (by omega : L + j < L + s)) _) _
  rw [canonicalDFBoundaryChecked, if_pos hp]
  by_cases hps : p + 1 < s
  · rw [if_pos hps]
    have hj : 0 < j := by dsimp [j]; omega
    have hidx : s - 1 - (p + 1) = j - 1 := by dsimp [j]; omega
    rw [hidx, ← canonicalDFValue_boundary d hj hjs]
    exact hv
  · rw [if_neg hps]
    have hj0 : j = 0 := by dsimp [j]; omega
    simpa [hj0] using hv

end

end Erdos874

-/
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

def cdfIndices (L s j k : ℕ) : Finset ℕ :=
  (Finset.range j ∪ {k}) ∪ Finset.Ico (L + j + 1) (L + s)

def cdfValue (d : ℕ → ℤ) (L s j k : ℕ) : ℤ :=
  (cdfIndices L s j k).sum d

lemma cdfIndices_card {L s j k : ℕ}
    (hj : j < s) (hjk : j ≤ k) (hk : k ≤ L + j) :
    (cdfIndices L s j k).card = s := by
  have hdisj₁ : Disjoint (Finset.range j ∪ {k})
      (Finset.Ico (L + j + 1) (L + s)) := by
    rw [Finset.disjoint_left]
    intro x hx hxIco
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico] at hxIco
    rcases hx with hx | rfl <;> omega
  rw [cdfIndices, Finset.card_union_of_disjoint hdisj₁,
    Finset.card_union_of_disjoint]
  · simp only [Finset.card_range, Finset.card_singleton, Nat.card_Ico]
    omega
  · simpa [Finset.disjoint_singleton_right]

lemma cdfIndices_subset_range {L s j k : ℕ}
    (hj : j < s) (hjk : j ≤ k) (hk : k ≤ L + j) :
    cdfIndices L s j k ⊆ Finset.range (L + s) := by
  intro x hx
  simp only [cdfIndices, Finset.mem_union, Finset.mem_range,
    Finset.mem_singleton, Finset.mem_Ico] at hx ⊢
  rcases hx with (hx | rfl) | hx <;> omega

lemma cdfValue_mem
    {D : Finset ℤ} {d : ℕ → ℤ} {L s j k : ℕ}
    (hD : D = (Finset.range (L + s)).image d)
    (hinj : Set.InjOn d (Finset.range (L + s)))
    (hj : j < s) (hjk : j ≤ k) (hk : k ≤ L + j) :
    cdfValue d L s j k ∈ restrictedSumset s D := by
  refine mem_restrictedSumset.mpr ⟨(cdfIndices L s j k).image d, ?_, ?_, ?_⟩
  · rw [hD]
    exact Finset.image_mono _ (cdfIndices_subset_range hj hjk hk)
  · rw [Finset.card_image_of_injOn]
    · exact cdfIndices_card hj hjk hk
    · exact hinj.mono (cdfIndices_subset_range hj hjk hk)
  · rw [cdfValue, Finset.sum_image]
    intro x hx y hy hxy
    exact hinj (cdfIndices_subset_range hj hjk hk hx)
      (cdfIndices_subset_range hj hjk hk hy) hxy

lemma cdfValue_eq (d : ℕ → ℤ) {L s j k : ℕ} (hj : j < s)
    (hjk : j ≤ k) (hk : k ≤ L + j) :
    cdfValue d L s j k =
      (∑ i ∈ Finset.range j, d i) + d k +
        ∑ i ∈ Finset.Ico (L + j + 1) (L + s), d i := by
  have hdisj₁ : Disjoint (Finset.range j ∪ {k})
      (Finset.Ico (L + j + 1) (L + s)) := by
    rw [Finset.disjoint_left]
    intro x hx hxIco
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico] at hxIco
    rcases hx with hx | rfl <;> omega
  rw [cdfValue, cdfIndices, Finset.sum_union hdisj₁, Finset.sum_union]
  · simp
  · simpa [Finset.disjoint_singleton_right]

lemma cdfValue_step (d : ℕ → ℤ) {L s j k : ℕ}
    (hj : j < s) (hjk : j ≤ k) (hk : k < L + j) :
    cdfValue d L s j (k + 1) - cdfValue d L s j k = d (k + 1) - d k := by
  rw [cdfValue_eq d hj (by omega) (by omega), cdfValue_eq d hj hjk hk.le]
  ring

lemma cdfValue_boundary (d : ℕ → ℤ) {L s j : ℕ}
    (hj : 0 < j) (hjs : j < s) :
    cdfValue d L s j (L + j) = cdfValue d L s (j - 1) (j - 1) := by
  unfold cdfValue
  congr 1
  ext x
  simp only [cdfIndices, Finset.mem_union, Finset.mem_range,
    Finset.mem_singleton, Finset.mem_Ico]
  omega

lemma cdf_inj {d : ℕ → ℤ} {T : ℕ}
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < T → d i < d j) :
    Set.InjOn d (Finset.range T) := by
  intro i hi j hj heq
  rcases lt_trichotomy i j with hij | hij | hij
  · exact ((hmono hij (Finset.mem_range.mp hj)).ne heq).elim
  · exact hij
  · exact ((hmono hij (Finset.mem_range.mp hi)).ne heq.symm).elim

lemma cdf_rank_difference {d : ℕ → ℤ} {T : ℕ}
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < T → d i < d j)
    {i j : ℕ} (hij : i ≤ j) (hjT : j < T) :
    ((j - i : ℕ) : ℤ) ≤ d j - d i := by
  induction j generalizing i with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      simp
  | succ j ih =>
      by_cases hi : i = j + 1
      · subst i; simp
      · have hrank := ih (show i ≤ j by omega) (show j < T by omega)
        have hstep := hmono (show j < j + 1 by omega) hjT
        omega

lemma cdf_gap_le {d : ℕ → ℤ} {T R : ℕ}
    (hT : 0 < T)
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < T → d i < d j)
    (hspan : d (T - 1) - d 0 = ((T - 1 + R : ℕ) : ℤ))
    {k : ℕ} (hk : k + 1 < T) : d (k + 1) - d k ≤ (R + 1 : ℕ) := by
  have hleft := cdf_rank_difference hmono (i := 0) (j := k) (by omega) (by omega)
  have hright := cdf_rank_difference hmono (i := k + 1) (j := T - 1)
    (by omega) (by omega)
  push_cast at hleft hright ⊢
  omega

lemma cdf_holes_card {d : ℕ → ℤ} {T R : ℕ}
    (hT : 0 < T)
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < T → d i < d j)
    (hspan : d (T - 1) - d 0 = ((T - 1 + R : ℕ) : ℤ)) :
    (Finset.Icc (d 0) (d (T - 1)) \ (Finset.range T).image d).card = R := by
  let E := (Finset.range T).image d
  have hEcard : E.card = T := by
    dsimp [E]
    rw [Finset.card_image_of_injOn (cdf_inj hmono), Finset.card_range]
  have hsub : E ⊆ Finset.Icc (d 0) (d (T - 1)) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hiT := Finset.mem_range.mp hi
    simp only [Finset.mem_Icc]
    constructor
    · rcases eq_or_lt_of_le (Nat.zero_le i) with rfl | hi
      · exact le_rfl
      · exact (hmono hi hiT).le
    · rcases eq_or_lt_of_le (show i ≤ T - 1 by omega) with hi | hi
      · subst i; exact le_rfl
      · exact (hmono hi (by omega)).le
  have hIcard : (Finset.Icc (d 0) (d (T - 1))).card = T + R := by
    rw [Int.card_Icc]
    have heq : d (T - 1) + 1 - d 0 = ((T + R : ℕ) : ℤ) := by
      push_cast
      omega
    rw [heq, Int.toNat_natCast]
  have hp := Finset.card_sdiff_of_subset hsub
  change (Finset.Icc (d 0) (d (T - 1)) \ E).card = R
  omega

lemma exists_adjacent_straddling {f : ℕ → ℤ} {n : ℕ} {z : ℤ}
    (hstep : ∀ i < n, f i < f (i + 1))
    (hlo : f 0 ≤ z) (hhi : z ≤ f n)
    (hmiss : ∀ i ≤ n, z ≠ f i) :
    ∃ i < n, f i < z ∧ z < f (i + 1) := by
  induction n generalizing f with
  | zero => exact (hmiss 0 le_rfl (le_antisymm hhi hlo)).elim
  | succ n ih =>
      have hf0 : f 0 < z := lt_of_le_of_ne hlo (Ne.symm (hmiss 0 (by omega)))
      by_cases hz1 : z < f 1
      · exact ⟨0, by omega, hf0, hz1⟩
      · have hf1 : f 1 < z := by
          exact lt_of_le_of_ne (le_of_not_gt hz1) (Ne.symm (hmiss 1 (by omega)))
        obtain ⟨i, hi, hfi, hfis⟩ := ih
          (f := fun r ↦ f (r + 1))
          (fun i hi ↦ by simpa [Nat.add_assoc] using hstep (i + 1) (by omega))
          hf1.le (by simpa using hhi)
          (fun i hi hEq ↦ hmiss (i + 1) (by omega) (by simpa using hEq))
        exact ⟨i + 1, by omega, by simpa [Nat.add_assoc] using hfi,
          by simpa [Nat.add_assoc] using hfis⟩

def cdfBoundary (d : ℕ → ℤ) (L s p : ℕ) : ℤ :=
  if p < s then cdfValue d L s (s - 1 - p) (s - 1 - p)
  else cdfValue d L s 0 L

lemma cdfBoundary_step {d : ℕ → ℤ} {L s p : ℕ}
    (hL : 0 < L) (hp : p < s)
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < L + s → d i < d j) :
    cdfBoundary d L s p < cdfBoundary d L s (p + 1) := by
  let j := s - 1 - p
  have hjs : j < s := by dsimp [j]; omega
  have hd : d j < d (L + j) := hmono (i := j) (j := L + j) (by omega) (by omega)
  have hv : cdfValue d L s j j < cdfValue d L s j (L + j) := by
    rw [cdfValue_eq d hjs le_rfl (by omega), cdfValue_eq d hjs (by omega) le_rfl]
    omega
  simp only [cdfBoundary, hp, if_pos]
  by_cases hps : p + 1 < s
  · rw [if_pos hps]
    have hj : 0 < j := by dsimp [j]; omega
    have hidx : s - 1 - (p + 1) = j - 1 := by dsimp [j]; omega
    change cdfValue d L s j j < cdfValue d L s (j - 1) (j - 1)
    rw [← cdfValue_boundary d hj hjs]
    exact hv
  · rw [if_neg hps]
    have hj0 : j = 0 := by dsimp [j]; omega
    simpa [j, hj0] using hv

lemma cdfEdge_exists
    {D : Finset ℤ} {d : ℕ → ℤ} {L s : ℕ} {z : ℤ}
    (hD : D = (Finset.range (L + s)).image d)
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < L + s → d i < d j)
    (hL : 0 < L) (hs : 0 < s)
    (hzlo : cdfValue d L s (s - 1) (s - 1) ≤ z)
    (hzhi : z ≤ cdfValue d L s 0 L)
    (hzmiss : z ∉ restrictedSumset s D) :
    ∃ j k : ℕ, j < s ∧ j ≤ k ∧ k < L + j ∧
      cdfValue d L s j k < z ∧ z < cdfValue d L s j (k + 1) := by
  have hinj := cdf_inj hmono
  have hboundaryMiss : ∀ p ≤ s, z ≠ cdfBoundary d L s p := by
    intro p hp heq
    by_cases hps : p < s
    · have hj : s - 1 - p < s := by omega
      have hmem := cdfValue_mem hD hinj hj le_rfl (by omega :
        s - 1 - p ≤ L + (s - 1 - p))
      apply hzmiss
      rw [heq, cdfBoundary, if_pos hps]
      exact hmem
    · have hpEq : p = s := by omega
      subst p
      have hmem := cdfValue_mem hD hinj (by omega : 0 < s) (by omega : 0 ≤ L) le_rfl
      apply hzmiss
      rw [heq]
      simpa [cdfBoundary] using hmem
  obtain ⟨p, hp, hpz, hzp⟩ := exists_adjacent_straddling
    (f := cdfBoundary d L s) (n := s) (z := z)
    (fun p hp ↦ cdfBoundary_step hL hp hmono)
    (by simpa [cdfBoundary, hs] using hzlo)
    (by simpa [cdfBoundary] using hzhi) hboundaryMiss
  let j := s - 1 - p
  have hj : j < s := by dsimp [j]; omega
  have hphaseEnd : cdfBoundary d L s (p + 1) = cdfValue d L s j (L + j) := by
    by_cases hps : p + 1 < s
    · rw [cdfBoundary, if_pos hps]
      have hjpos : 0 < j := by dsimp [j]; omega
      have hidx : s - 1 - (p + 1) = j - 1 := by dsimp [j]; omega
      rw [hidx, ← cdfValue_boundary d hjpos hj]
    · have hj0 : j = 0 := by dsimp [j]; omega
      rw [cdfBoundary, if_neg hps, hj0, Nat.add_zero]
  have hphaseStart : cdfBoundary d L s p = cdfValue d L s j j := by
    simp [cdfBoundary, hp, j]
  have hpointMiss : ∀ r ≤ L, z ≠ cdfValue d L s j (j + r) := by
    intro r hr heq
    exact hzmiss (heq ▸ cdfValue_mem hD hinj hj (by omega) (by omega))
  obtain ⟨r, hr, hrz, hzr⟩ := exists_adjacent_straddling
    (f := fun r ↦ cdfValue d L s j (j + r)) (n := L) (z := z)
    (fun r hr ↦ by
      have heq := cdfValue_step d hj (by omega : j ≤ j + r) (by omega : j + r < L + j)
      have hlt := hmono (i := j + r) (j := j + r + 1) (by omega) (by omega)
      have : cdfValue d L s j (j + r) < cdfValue d L s j (j + r + 1) := by omega
      simpa [Nat.add_assoc] using this)
    (by simpa [hphaseStart] using hpz.le)
    (by simpa [hphaseEnd, Nat.add_comm] using hzp.le) hpointMiss
  exact ⟨j, j + r, hj, by omega, by omega, hrz, by simpa [Nat.add_assoc] using hzr⟩

lemma cdfValue_prev_diff (d : ℕ → ℤ) {L s j k : ℕ}
    (hj : 0 < j) (hjs : j < s)
    (hjk : j ≤ k) (hk : k < L + j - 1) :
    cdfValue d L s (j - 1) k - cdfValue d L s j k =
      d (L + j) - d (j - 1) := by
  have hsum : (∑ i ∈ Finset.range j, d i) =
      (∑ i ∈ Finset.range (j - 1), d i) + d (j - 1) := by
    have hjid : j - 1 + 1 = j := by omega
    conv_lhs => rw [← hjid, Finset.sum_range_succ]
  have hnot : L + j ∉ Finset.Ico (L + j + 1) (L + s) := by simp
  have hI : insert (L + j) (Finset.Ico (L + j + 1) (L + s)) =
      Finset.Ico (L + j) (L + s) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [cdfValue_eq d (by omega) (by omega) (by omega),
    cdfValue_eq d hjs hjk (by omega), hsum]
  have hjid : L + (j - 1) + 1 = L + j := by omega
  rw [hjid, ← hI, Finset.sum_insert hnot]
  ring

lemma cdf_same_label_separated
    {d : ℕ → ℤ} {L s j₁ j₂ k : ℕ}
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < L + s → d i < d j)
    (hj₁ : j₁ < s) (hj₂ : j₂ < s)
    (h₁lo : j₁ ≤ k) (h₁hi : k < L + j₁)
    (h₂lo : j₂ ≤ k) (h₂hi : k < L + j₂)
    (hlt : j₁ < j₂) :
    cdfValue d L s j₂ k + (L + 1 : ℕ) ≤ cdfValue d L s j₁ k := by
  induction j₂ generalizing j₁ with
  | zero => omega
  | succ j₂ ih =>
      by_cases heq : j₁ = j₂
      · subst j₁
        have he := cdfValue_prev_diff d (j := j₂ + 1) (k := k)
          (by omega) hj₂ h₂lo h₁hi
        have he' : cdfValue d L s j₂ k - cdfValue d L s (j₂ + 1) k =
            d (L + (j₂ + 1)) - d j₂ := by
          simpa only [Nat.succ_sub_one] using he
        have hrank := cdf_rank_difference hmono (i := j₂) (j := L + (j₂ + 1))
          (by omega) (by omega)
        have hnat : L + (j₂ + 1) - j₂ = L + 1 := by omega
        rw [hnat] at hrank
        push_cast at hrank ⊢
        linarith
      · have hj₁j₂ : j₁ < j₂ := by omega
        have hprev := ih (j₁ := j₁) hj₁ (by omega : j₂ < s) h₁lo h₁hi
          (by omega : j₂ ≤ k) (by omega : k < L + j₂) hj₁j₂
        have hinc : cdfValue d L s (j₂ + 1) k < cdfValue d L s j₂ k := by
          have hkj₂ : k < L + j₂ := by omega
          have he := cdfValue_prev_diff d (j := j₂ + 1) (k := k)
            (by omega) hj₂ h₂lo hkj₂
          have he' : cdfValue d L s j₂ k - cdfValue d L s (j₂ + 1) k =
              d (L + (j₂ + 1)) - d j₂ := by
            simpa only [Nat.succ_sub_one] using he
          have hpos : d j₂ < d (L + (j₂ + 1)) := hmono (by omega) (by omega)
          linarith
        linarith

/-- Normalized ordered-index form of the Deshouillers--Freiman local-density
proposition.  Here `L = T-s`; the hypotheses of Proposition 1 imply
`4*R+3 ≤ L`. -/
theorem canonicalDF_localDensity
    {D : Finset ℤ} {d : ℕ → ℤ} {L s R : ℕ}
    (hD : D = (Finset.range (L + s)).image d)
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < L + s → d i < d j)
    (hspan : d (L + s - 1) - d 0 = ((L + s - 1 + R : ℕ) : ℤ))
    (hL : 4 * R + 3 ≤ L) (hs : 0 < s) :
    HasLocalDensity (restrictedSumset s D)
      (cdfValue d L s (s - 1) (s - 1)) (cdfValue d L s 0 L) 0 1 R := by
  classical
  let S := restrictedSumset s D
  intro y _hyres hylo hyhi
  rw [progressionBlock_one_odd_eq_Icc]
  let B : Finset ℤ := Finset.Icc y (y + 2 * R)
  have hedgeExists : ∀ z ∈ B \ S, ∃ j k : ℕ,
      j < s ∧ j ≤ k ∧ k < L + j ∧
        cdfValue d L s j k < z ∧ z < cdfValue d L s j (k + 1) := by
    intro z hz
    have hzB : z ∈ B := (Finset.mem_sdiff.mp hz).1
    have hznot : z ∉ S := (Finset.mem_sdiff.mp hz).2
    exact cdfEdge_exists hD hmono (by omega) hs
      (hylo.trans (Finset.mem_Icc.mp hzB).1)
      ((Finset.mem_Icc.mp hzB).2.trans (by simpa using hyhi)) hznot
  have hedgeExists' : ∀ z : ℤ, ∃ j k : ℕ, z ∈ B \ S →
      j < s ∧ j ≤ k ∧ k < L + j ∧
        cdfValue d L s j k < z ∧ z < cdfValue d L s j (k + 1) := by
    intro z
    by_cases hz : z ∈ B \ S
    · obtain ⟨j, k, h⟩ := hedgeExists z hz
      exact ⟨j, k, fun _ ↦ h⟩
    · exact ⟨0, 0, fun h ↦ (hz h).elim⟩
  choose phase label hedge using hedgeExists'
  let Edge := {e : ℕ × ℕ // e.1 < s ∧ e.1 ≤ e.2 ∧ e.2 < L + e.1}
  let edge : ℤ → Edge := fun z ↦
    if hz : z ∈ B \ S then
      ⟨(phase z, label z), (hedge z hz).1, (hedge z hz).2.1, (hedge z hz).2.2.1⟩
    else ⟨(0, 0), hs, le_rfl, by omega⟩
  let edgeLabel : Edge → ℕ := fun e ↦ e.1.2
  let edgeStart : Edge → ℤ := fun e ↦ cdfValue d L s e.1.1 e.1.2
  let charge : ℤ → ℤ := fun z ↦
    d (edgeLabel (edge z)) + (z - edgeStart (edge z))
  let H : Finset ℤ := Finset.Icc (d 0) (d (L + s - 1)) \ D
  have hedge_spec : ∀ z ∈ B \ S,
      (edge z).1.1 < s ∧ (edge z).1.1 ≤ (edge z).1.2 ∧
      (edge z).1.2 < L + (edge z).1.1 ∧
      edgeStart (edge z) < z ∧
      z < cdfValue d L s (edge z).1.1 ((edge z).1.2 + 1) := by
    intro z hz
    simpa only [edge, dif_pos hz, edgeStart] using hedge z hz
  have hinj := cdf_inj hmono
  have hmap : ∀ z ∈ B \ S, charge z ∈ H := by
    intro z hz
    have he := hedge_spec z hz
    let j := (edge z).1.1
    let k := (edge z).1.2
    have hkT : k + 1 < L + s := by dsimp [j, k] at *; omega
    have hstep := cdfValue_step d he.1 he.2.1 he.2.2.1
    have hclo : d k < charge z := by dsimp [charge, edgeLabel, edgeStart, j, k] at *; omega
    have hchi : charge z < d (k + 1) := by
      dsimp [charge, edgeLabel, edgeStart, j, k] at *
      omega
    have hd0k : d 0 ≤ d k := by
      by_cases hk0 : k = 0
      · simpa [hk0]
      · exact (hmono (by omega) (by omega)).le
    have hdkLast : d (k + 1) ≤ d (L + s - 1) := by
      by_cases heq : k + 1 = L + s - 1
      · rw [heq]
      · exact (hmono (by omega) (by omega)).le
    rw [Finset.mem_sdiff, Finset.mem_Icc]
    refine ⟨⟨hd0k.trans hclo.le, hchi.le.trans hdkLast⟩, ?_⟩
    rw [hD]
    intro hmem
    obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp hmem
    have hiT := Finset.mem_range.mp hi
    by_cases hik : i ≤ k
    · have hdik : d i ≤ d k := by
        rcases eq_or_lt_of_le hik with rfl | hik
        · exact le_rfl
        · exact (hmono hik (by omega)).le
      rw [← hEq] at hclo
      exact (not_lt_of_ge hdik hclo).elim
    · have hdki : d (k + 1) ≤ d i := by
        rcases eq_or_lt_of_le (show k + 1 ≤ i by omega) with hEq' | hlt
        · rw [hEq']
        · exact (hmono hlt hiT).le
      rw [← hEq] at hchi
      exact (not_lt_of_ge hdki hchi).elim
  have hchargeLabel : ∀ z ∈ B \ S, ∀ w ∈ B \ S,
      charge z = charge w → edgeLabel (edge z) = edgeLabel (edge w) := by
    intro z hz w hw hcharge
    have hzspec := hedge_spec z hz
    have hwspec := hedge_spec w hw
    let kz := edgeLabel (edge z)
    let kw := edgeLabel (edge w)
    have hzstep := cdfValue_step d hzspec.1 hzspec.2.1 hzspec.2.2.1
    have hwstep := cdfValue_step d hwspec.1 hwspec.2.1 hwspec.2.2.1
    have hzlo : d kz < charge z := by dsimp [kz, charge, edgeLabel, edgeStart] at *; omega
    have hzhi : charge z < d (kz + 1) := by
      dsimp [kz, charge, edgeLabel, edgeStart] at *; omega
    have hwlo : d kw < charge w := by dsimp [kw, charge, edgeLabel, edgeStart] at *; omega
    have hwhi : charge w < d (kw + 1) := by
      dsimp [kw, charge, edgeLabel, edgeStart] at *; omega
    rcases lt_trichotomy kz kw with hlt | heq | hgt
    · have hdk : d (kz + 1) ≤ d kw := by
        rcases eq_or_lt_of_le (show kz + 1 ≤ kw by omega) with h | h
        · rw [h]
        · exact (hmono h (by dsimp [kw, edgeLabel]; omega)).le
      rw [hcharge] at hzhi
      exact (not_lt_of_ge (hdk.trans hwlo.le) hzhi).elim
    · exact heq
    · have hdk : d (kw + 1) ≤ d kz := by
        rcases eq_or_lt_of_le (show kw + 1 ≤ kz by omega) with h | h
        · rw [h]
        · exact (hmono h (by dsimp [kz, edgeLabel]; omega)).le
      rw [← hcharge] at hwhi
      exact (not_lt_of_ge (hdk.trans hzlo.le) hwhi).elim
  have hrepeat : ∀ e f : Edge, e ≠ f → edgeLabel e = edgeLabel f →
      edgeStart e + (3 * R : ℕ) < edgeStart f ∨
        edgeStart f + (3 * R : ℕ) < edgeStart e := by
    intro e f hef hlabel
    have hk : e.1.2 = f.1.2 := by simpa [edgeLabel] using hlabel
    have hjne : e.1.1 ≠ f.1.1 := by
      intro h
      apply hef
      apply Subtype.ext
      exact Prod.ext h hlabel
    rcases lt_trichotomy e.1.1 f.1.1 with hlt | heq | hgt
    · right
      have hflo : f.1.1 ≤ e.1.2 := by simpa only [hk] using f.2.2.1
      have hfhi : e.1.2 < L + f.1.1 := by simpa only [hk] using f.2.2.2
      have hsep := cdf_same_label_separated hmono e.2.1 f.2.1
        e.2.2.1 e.2.2.2 hflo hfhi hlt
      rw [hk] at hsep
      dsimp [edgeStart]
      calc
        cdfValue d L s f.1.1 f.1.2 + (3 * R : ℕ) <
            cdfValue d L s f.1.1 f.1.2 + (L + 1 : ℕ) := by
              push_cast
              omega
        _ ≤ cdfValue d L s e.1.1 f.1.2 := hsep
        _ = cdfValue d L s e.1.1 e.1.2 := by rw [hk]
    · exact (hjne heq).elim
    · left
      have helo : e.1.1 ≤ f.1.2 := by simpa only [← hk] using e.2.2.1
      have hehi : f.1.2 < L + e.1.1 := by simpa only [← hk] using e.2.2.2
      have hsep := cdf_same_label_separated hmono f.2.1 e.2.1
        f.2.2.1 f.2.2.2 helo hehi hgt
      dsimp [edgeStart]
      calc
        cdfValue d L s e.1.1 e.1.2 + (3 * R : ℕ) =
            cdfValue d L s e.1.1 f.1.2 + (3 * R : ℕ) := by rw [hk]
        _ < cdfValue d L s e.1.1 f.1.2 + (L + 1 : ℕ) := by
          push_cast
          omega
        _ ≤ cdfValue d L s f.1.1 f.1.2 := hsep
  have hwindow : ∀ z ∈ B \ S,
      y - (R : ℕ) ≤ edgeStart (edge z) ∧
        edgeStart (edge z) ≤ y + (2 * R : ℕ) - 1 := by
    intro z hz
    have hspez := hedge_spec z hz
    have hzB := (Finset.mem_sdiff.mp hz).1
    have hgap := cdf_gap_le (T := L + s) (R := R) (by omega) hmono hspan
      (show (edge z).1.2 + 1 < L + s by omega)
    have hstep := cdfValue_step d hspez.1 hspez.2.1 hspez.2.2.1
    change z ∈ Finset.Icc y (y + 2 * R) at hzB
    have hzmem := Finset.mem_Icc.mp hzB
    dsimp [edgeStart] at *
    push_cast at hgap
    constructor <;> omega
  have hoffset : ∀ z ∈ B \ S, ∀ w ∈ B \ S,
      edge z = edge w → charge z = charge w → z = w := by
    intro z hz w hw hedgeEq hcharge
    dsimp [charge] at hcharge
    rw [hedgeEq] at hcharge
    omega
  have hH : H.card ≤ R := by
    have hh := cdf_holes_card (T := L + s) (R := R) (by omega) hmono hspan
    simpa [H, hD] using hh.le
  have hchargeInj : Set.InjOn charge ↑(B \ S) := by
    intro z hz w hw hzw
    have hlabel := hchargeLabel z hz w hw hzw
    have hedgeEq : edge z = edge w := by
      by_contra hne
      rcases hrepeat (edge z) (edge w) hne hlabel with hsep | hsep
      · have hzwin := hwindow z hz
        have hwwin := hwindow w hw
        omega
      · have hzwin := hwindow z hz
        have hwwin := hwindow w hw
        omega
    exact hoffset z hz w hw hedgeEq hzw
  have hmiss : (B \ S).card ≤ H.card := by
    exact Finset.card_le_card_of_injOn charge (fun z hz ↦ hmap z hz) hchargeInj
  have hBcard : B.card = 2 * R + 1 := by
    dsimp [B]
    rw [Int.card_Icc]
    have heq : y + 2 * (R : ℤ) + 1 - y = ((2 * R + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [heq, Int.toNat_natCast]
  change R + 1 ≤ (B ∩ S).card
  have hpartition := Finset.card_sdiff_add_card_inter B S
  omega

end

end Erdos874

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The Deshouillers--Freiman local-density conclusion after affine
normalization, with all numerical hypotheses over `ℕ`. -/
theorem df99_localDensity_of_affine_normalization
    {D V : Finset ℤ} {d : ℕ → ℤ} {T s R q : ℕ} {a c : ℤ}
    (hq : 0 < q)
    (hT : 2 * s ≤ T + q)
    (hs : 4 * R + 3 + q ≤ s)
    (hD : D = (Finset.range T).image d)
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < T → d i < d j)
    (hspan : d (T - 1) - d 0 = ((T - 1 + R : ℕ) : ℤ))
    (hV : V = D.image fun x ↦ (q : ℤ) * x + c)
    (ha : Int.ModEq (q : ℤ) a c) :
    HasLocalDensity (restrictedSumset s V)
      ((q : ℤ) * cdfValue d (T - s) s (s - 1) (s - 1) + (s : ℤ) * c)
      ((q : ℤ) * cdfValue d (T - s) s 0 (T - s) + (s : ℤ) * c)
      ((s : ℤ) * a) (q : ℤ) R := by
  have hqle : q ≤ s := by omega
  have hsT : s ≤ T := by omega
  have hTs : T - s + s = T := Nat.sub_add_cancel hsT
  have hL : 4 * R + 3 ≤ T - s := by omega
  have hspos : 0 < s := by omega
  have hD' : D = (Finset.range (T - s + s)).image d := by
    simpa [hTs] using hD
  have hmono' : ∀ ⦃i j : ℕ⦄, i < j → j < T - s + s → d i < d j := by
    simpa [hTs] using hmono
  have hspan' : d (T - s + s - 1) - d 0 =
      (((T - s + s - 1) + R : ℕ) : ℤ) := by
    simpa [hTs] using hspan
  have hnorm := canonicalDF_localDensity hD' hmono' hspan' hL hspos
  exact restrictedSumset_localDensity_of_affine_normalization
    (by exact_mod_cast hq) hV ha hnorm

lemma cdfValue_lower_endpoint (d : ℕ → ℤ) {L s : ℕ} (hs : 0 < s) :
    cdfValue d L s (s - 1) (s - 1) = ∑ i ∈ Finset.range s, d i := by
  unfold cdfValue
  congr 1
  ext i
  simp only [cdfIndices, Finset.mem_union, Finset.mem_range,
    Finset.mem_singleton, Finset.mem_Ico]
  omega

lemma cdfValue_upper_endpoint (d : ℕ → ℤ) {L s : ℕ} (hs : 0 < s) :
    cdfValue d L s 0 L = ∑ i ∈ Finset.Ico L (L + s), d i := by
  unfold cdfValue
  congr 1
  ext i
  simp only [cdfIndices, Finset.mem_union, Finset.mem_range,
    Finset.mem_singleton, Finset.mem_Ico]
  omega

/-- Explicit-endpoint form of `df99_localDensity_of_affine_normalization`.
The endpoints are the sums of the first and last `s` entries of the affine
ordered carrier. -/
theorem df99_localDensity_of_affine_normalization_explicit
    {D V : Finset ℤ} {d : ℕ → ℤ} {T s R q : ℕ} {a c : ℤ}
    (hq : 0 < q)
    (hT : 2 * s ≤ T + q)
    (hs : 4 * R + 3 + q ≤ s)
    (hD : D = (Finset.range T).image d)
    (hmono : ∀ ⦃i j : ℕ⦄, i < j → j < T → d i < d j)
    (hspan : d (T - 1) - d 0 = ((T - 1 + R : ℕ) : ℤ))
    (hV : V = D.image fun x ↦ (q : ℤ) * x + c)
    (ha : Int.ModEq (q : ℤ) a c) :
    HasLocalDensity (restrictedSumset s V)
      (∑ i ∈ Finset.range s, ((q : ℤ) * d i + c))
      (∑ i ∈ Finset.Ico (T - s) T, ((q : ℤ) * d i + c))
      ((s : ℤ) * a) (q : ℤ) R := by
  have hspos : 0 < s := by omega
  have hsT : s ≤ T := by omega
  have hTs : T - s + s = T := Nat.sub_add_cancel hsT
  have hlo : (∑ i ∈ Finset.range s, ((q : ℤ) * d i + c)) =
      (q : ℤ) * cdfValue d (T - s) s (s - 1) (s - 1) + (s : ℤ) * c := by
    rw [cdfValue_lower_endpoint d hspos, Finset.sum_add_distrib]
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hhi : (∑ i ∈ Finset.Ico (T - s) T, ((q : ℤ) * d i + c)) =
      (q : ℤ) * cdfValue d (T - s) s 0 (T - s) + (s : ℤ) * c := by
    rw [cdfValue_upper_endpoint d hspos, Finset.sum_add_distrib]
    simp only [← Finset.mul_sum, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hdiff : T - (T - s) = s := by omega
    rw [hdiff, hTs]
  rw [hlo, hhi]
  exact df99_localDensity_of_affine_normalization hq hT hs hD hmono hspan hV ha

end

end Erdos874
