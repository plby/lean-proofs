/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.ModularDecomposition

/-!
# The endpoint-absorption step in the DF95 structure theorem

This file formalizes the last, easily missed, part of the 1995
Deshouillers--Freiman structure argument.  A common residue class modulo the
refined difference does not by itself put the regular set in a *short*
progression.  One must absorb its two extreme blocks into the exceptional set.

For `T` extreme points on either side, interpolate between the lower and upper
`T`-subsets by replacing one point at a time.  If the two inner endpoints are
`d * Δ` apart, consecutive interpolating sums are at least `d * Δ` apart.
Translating a long `d`-progression by those sums, and then by one fixed filler,
injects `T * min Δ L` points into one prescribed restricted layer.  A capacity
bound on that layer forces `Δ` to be small.  After the two extreme blocks are
absorbed, every remaining point lies between the inner endpoints and hence in
a short `d`-progression.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Consecutive blocks in the increasing enumeration of a finset -/

/-- The `length` consecutive elements of `D` whose ranks start at `offset`. -/
private noncomputable def orderedBlock (D : Finset ℤ) (offset length : ℕ)
    (h : offset + length ≤ D.card) : Finset ℤ :=
  Finset.univ.map
    { toFun := fun i : Fin length =>
        D.orderEmbOfFin rfl
          ⟨offset + i, by omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        have hidx := (D.orderEmbOfFin rfl).injective hij
        have hval := congrArg Fin.val hidx
        exact Nat.add_left_cancel hval }

@[simp] private lemma card_orderedBlock (D : Finset ℤ) (offset length : ℕ)
    (h : offset + length ≤ D.card) :
    (orderedBlock D offset length h).card = length := by
  simp [orderedBlock]

private lemma orderedBlock_subset (D : Finset ℤ) (offset length : ℕ)
    (h : offset + length ≤ D.card) :
    orderedBlock D offset length h ⊆ D := by
  intro x hx
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
  exact D.orderEmbOfFin_mem rfl _

private lemma mem_orderedBlock_iff (D : Finset ℤ) (offset length : ℕ)
    (h : offset + length ≤ D.card) (x : ℤ) :
    x ∈ orderedBlock D offset length h ↔
      ∃ i : Fin length,
        D.orderEmbOfFin rfl ⟨offset + i, by omega⟩ = x := by
  constructor
  · intro hx
    obtain ⟨i, _hi, hi⟩ := Finset.mem_map.mp hx
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    apply Finset.mem_map.mpr
    exact ⟨i, Finset.mem_univ _, rfl⟩

private lemma orderedBlock_disjoint_of_le
    (D : Finset ℤ) {o₁ l₁ o₂ l₂ : ℕ}
    (h₁ : o₁ + l₁ ≤ D.card) (h₂ : o₂ + l₂ ≤ D.card)
    (hsep : o₁ + l₁ ≤ o₂) :
    Disjoint (orderedBlock D o₁ l₁ h₁) (orderedBlock D o₂ l₂ h₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  obtain ⟨i, hi⟩ := (mem_orderedBlock_iff D o₁ l₁ h₁ x).mp hx₁
  obtain ⟨j, hj⟩ := (mem_orderedBlock_iff D o₂ l₂ h₂ x).mp hx₂
  have hij := (D.orderEmbOfFin rfl).injective (hi.trans hj.symm)
  have : o₁ + (i : ℕ) = o₂ + (j : ℕ) := congrArg Fin.val hij
  omega

private lemma orderedBlock_mono_length
    (D : Finset ℤ) (offset l₁ l₂ : ℕ)
    (h₁ : offset + l₁ ≤ D.card) (h₂ : offset + l₂ ≤ D.card)
    (hlen : l₁ ≤ l₂) :
    orderedBlock D offset l₁ h₁ ⊆ orderedBlock D offset l₂ h₂ := by
  intro x hx
  obtain ⟨i, rfl⟩ :=
    (mem_orderedBlock_iff D offset l₁ h₁ x).mp hx
  apply (mem_orderedBlock_iff D offset l₂ h₂ _).mpr
  exact ⟨⟨i, i.isLt.trans_le hlen⟩, rfl⟩

private lemma orderedBlock_eq_of_length_eq
    (D : Finset ℤ) (offset l₁ l₂ : ℕ)
    (h₁ : offset + l₁ ≤ D.card) (h₂ : offset + l₂ ≤ D.card)
    (hlen : l₁ = l₂) :
    orderedBlock D offset l₁ h₁ = orderedBlock D offset l₂ h₂ := by
  subst l₂
  rfl

private lemma orderedBlock_succ
    (D : Finset ℤ) (offset length : ℕ)
    (h : offset + (length + 1) ≤ D.card) :
    orderedBlock D offset (length + 1) h =
      insert (D.orderEmbOfFin rfl ⟨offset + length, by omega⟩)
        (orderedBlock D offset length (by omega)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ :=
      (mem_orderedBlock_iff D offset (length + 1) h x).mp hx
    by_cases hi : (i : ℕ) = length
    · apply Finset.mem_insert.mpr
      left
      have hind :
          (⟨offset + (i : ℕ), by omega⟩ : Fin D.card) =
            ⟨offset + length, by omega⟩ := by
        apply Fin.ext
        simpa [hi]
      exact congrArg (D.orderEmbOfFin rfl) hind
    · apply Finset.mem_insert.mpr
      right
      apply (mem_orderedBlock_iff D offset length (by omega) _).mpr
      exact ⟨⟨i, by omega⟩, rfl⟩
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · apply (mem_orderedBlock_iff D offset (length + 1) h _).mpr
      exact ⟨⟨length, by omega⟩, rfl⟩
    · obtain ⟨i, rfl⟩ :=
        (mem_orderedBlock_iff D offset length (by omega) _).mp hx
      apply (mem_orderedBlock_iff D offset (length + 1) h _).mpr
      exact ⟨⟨i, by omega⟩, rfl⟩

private lemma orderedBlock_last_not_mem
    (D : Finset ℤ) (offset length : ℕ)
    (h : offset + (length + 1) ≤ D.card) :
    D.orderEmbOfFin rfl ⟨offset + length, by omega⟩ ∉
      orderedBlock D offset length (by omega) := by
  intro hx
  obtain ⟨i, hi⟩ :=
    (mem_orderedBlock_iff D offset length (by omega) _).mp hx
  have hidx := (D.orderEmbOfFin rfl).injective hi
  have hval := congrArg Fin.val hidx
  have : offset + (i : ℕ) = offset + length := hval
  omega

private lemma sum_orderedBlock_succ
    (D : Finset ℤ) (offset length : ℕ)
    (h : offset + (length + 1) ≤ D.card) :
    (∑ x ∈ orderedBlock D offset (length + 1) h, x) =
      (∑ x ∈ orderedBlock D offset length (by omega), x) +
        D.orderEmbOfFin rfl ⟨offset + length, by omega⟩ := by
  rw [orderedBlock_succ D offset length h,
    Finset.sum_insert (orderedBlock_last_not_mem D offset length h)]
  ring

/-! ## The two extreme blocks and their interpolating subsets -/

private noncomputable def endpointExtremes (D : Finset ℤ) (T : ℕ)
    (h2T : 2 * T ≤ D.card) : Finset ℤ :=
  orderedBlock D 0 T (by omega) ∪
    orderedBlock D (D.card - T) T (by omega)

private noncomputable def endpointMix (D : Finset ℤ) (T : ℕ)
    (h2T : 2 * T ≤ D.card) (j : Fin (T + 1)) : Finset ℤ :=
  orderedBlock D 0 (T - (j : ℕ)) (by omega) ∪
    orderedBlock D (D.card - T) (j : ℕ) (by omega)

private lemma endpointExtremes_subset (D : Finset ℤ) (T : ℕ)
    (h2T : 2 * T ≤ D.card) : endpointExtremes D T h2T ⊆ D := by
  exact Finset.union_subset
    (orderedBlock_subset D 0 T (by omega))
    (orderedBlock_subset D (D.card - T) T (by omega))

@[simp] private lemma card_endpointExtremes (D : Finset ℤ) (T : ℕ)
    (h2T : 2 * T ≤ D.card) :
    (endpointExtremes D T h2T).card = 2 * T := by
  have hdisj : Disjoint
      (orderedBlock D 0 T (by omega))
      (orderedBlock D (D.card - T) T (by omega)) :=
    orderedBlock_disjoint_of_le D (by omega) (by omega) (by omega)
  rw [endpointExtremes, Finset.card_union_of_disjoint hdisj]
  simp
  omega

private lemma endpointMix_subset_extremes (D : Finset ℤ) (T : ℕ)
    (h2T : 2 * T ≤ D.card) (j : Fin (T + 1)) :
    endpointMix D T h2T j ⊆ endpointExtremes D T h2T := by
  apply Finset.union_subset
  · exact (orderedBlock_mono_length D 0 (T - (j : ℕ)) T
      (by omega) (by omega) (Nat.sub_le _ _)).trans Finset.subset_union_left
  · exact (orderedBlock_mono_length D (D.card - T) (j : ℕ) T
      (by omega) (by omega) (by omega)).trans Finset.subset_union_right

@[simp] private lemma card_endpointMix (D : Finset ℤ) (T : ℕ)
    (h2T : 2 * T ≤ D.card) (j : Fin (T + 1)) :
    (endpointMix D T h2T j).card = T := by
  have hdisj : Disjoint
      (orderedBlock D 0 (T - (j : ℕ)) (by omega))
      (orderedBlock D (D.card - T) (j : ℕ) (by omega)) :=
    orderedBlock_disjoint_of_le D (by omega) (by omega) (by omega)
  rw [endpointMix, Finset.card_union_of_disjoint hdisj]
  simp
  omega

private lemma sum_endpointMix_succ
    (D : Finset ℤ) (T : ℕ) (h2T : 2 * T ≤ D.card)
    (j : ℕ) (hj : j < T) :
    (∑ x ∈ endpointMix D T h2T ⟨j + 1, by omega⟩, x) =
      (∑ x ∈ endpointMix D T h2T ⟨j, by omega⟩, x) -
        D.orderEmbOfFin rfl ⟨T - j - 1, by omega⟩ +
        D.orderEmbOfFin rfl ⟨D.card - T + j, by omega⟩ := by
  have hdisj_j : Disjoint
      (orderedBlock D 0 (T - j) (by omega))
      (orderedBlock D (D.card - T) j (by omega)) :=
    orderedBlock_disjoint_of_le D (by omega) (by omega) (by omega)
  have hdisj_succ : Disjoint
      (orderedBlock D 0 (T - (j + 1)) (by omega))
      (orderedBlock D (D.card - T) (j + 1) (by omega)) :=
    orderedBlock_disjoint_of_le D (by omega) (by omega) (by omega)
  have hlowlen : T - j = (T - (j + 1)) + 1 := by omega
  have hlow := sum_orderedBlock_succ D 0 (T - (j + 1)) (by omega)
  have hhigh := sum_orderedBlock_succ D (D.card - T) j (by omega)
  have hlow' :
      (∑ x ∈ orderedBlock D 0 (T - j) (by omega), x) =
        (∑ x ∈ orderedBlock D 0 (T - (j + 1)) (by omega), x) +
          D.orderEmbOfFin rfl ⟨T - j - 1, by omega⟩ := by
    have hb :
        orderedBlock D 0 (T - j) (by omega) =
          orderedBlock D 0 (T - (j + 1) + 1) (by omega) :=
      orderedBlock_eq_of_length_eq D 0 _ _ (by omega) (by omega) hlowlen
    rw [hb]
    convert hlow using 1 <;>
      first
      | apply proof_irrel_heq
      | (congr 1; apply congrArg (D.orderEmbOfFin rfl); apply Fin.ext;
          change T - j - 1 = 0 + (T - (j + 1)); omega)
  simp only [endpointMix]
  rw [Finset.sum_union hdisj_j, Finset.sum_union hdisj_succ]
  rw [hlow', hhigh]
  ring

private lemma endpointMix_sum_gap
    (D : Finset ℤ) (T d Δ : ℕ) (h2T : 2 * T ≤ D.card)
    (hd : 0 < d) (hT : 0 < T) (hΔ :
      D.orderEmbOfFin rfl ⟨D.card - T, by omega⟩ -
          D.orderEmbOfFin rfl ⟨T - 1, by omega⟩ =
        (d : ℤ) * (Δ : ℤ))
    (j : ℕ) (hj : j < T) :
    (∑ x ∈ endpointMix D T h2T ⟨j, by omega⟩, x) +
        (d : ℤ) * (Δ : ℤ) ≤
      ∑ x ∈ endpointMix D T h2T ⟨j + 1, by omega⟩, x := by
  have hsum := sum_endpointMix_succ D T h2T j hj
  have hlow :
      D.orderEmbOfFin rfl ⟨T - j - 1, by omega⟩ ≤
        D.orderEmbOfFin rfl ⟨T - 1, by omega⟩ := by
    exact (D.orderEmbOfFin rfl).monotone (by apply Fin.mk_le_mk.mpr; omega)
  have hhigh :
      D.orderEmbOfFin rfl ⟨D.card - T, by omega⟩ ≤
        D.orderEmbOfFin rfl ⟨D.card - T + j, by omega⟩ := by
    exact (D.orderEmbOfFin rfl).monotone (by apply Fin.mk_le_mk.mpr; omega)
  rw [← hΔ]
  omega

/-! ## Packing separated translates of one progression -/

/-- `T` starts separated by at least `d*Δ` contribute
`T * min Δ L` distinct points when translated by an `L`-term
`d`-progression. -/
private theorem separated_progression_translates_card_le
    {S : Finset ℤ} {d Δ L T : ℕ} {a : ℤ}
    (hd : 0 < d) (starts : Fin T → ℤ)
    (hgap : ∀ i j : Fin T, i < j →
      starts i + (d : ℤ) * (Δ : ℤ) ≤ starts j)
    (hmem : ∀ i : Fin T,
      arithmeticProgression (a + starts i) (d : ℤ) (min Δ L) ⊆ S) :
    T * min Δ L ≤ S.card := by
  let F : Fin T × Fin (min Δ L) → ℤ := fun p =>
    a + starts p.1 + (d : ℤ) * (p.2 : ℕ)
  have hFmem : ∀ p, F p ∈ S := by
    rintro ⟨i, j⟩
    apply hmem i
    exact mem_arithmeticProgression.mpr ⟨j, j.isLt, by simp [F, add_assoc]⟩
  have hFinj : Function.Injective F := by
    rintro ⟨i, u⟩ ⟨j, v⟩ huv
    by_cases hij : i = j
    · subst j
      have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
      have : ((u : ℕ) : ℤ) = ((v : ℕ) : ℤ) := by
        apply mul_left_cancel₀ hdZ
        dsimp [F] at huv
        omega
      have huvFin : u = v := by
        apply Fin.ext
        exact_mod_cast this
      exact congrArg (fun w => (i, w)) huvFin
    · rcases lt_or_gt_of_ne hij with hij | hji
      · have hsep := hgap i j hij
        have hu : (u : ℕ) < Δ := u.isLt.trans_le (min_le_left _ _)
        have hdZ : 0 < (d : ℤ) := by exact_mod_cast hd
        dsimp [F] at huv
        have huvlt : a + starts i + (d : ℤ) * (u : ℕ) < a + starts j := by
          nlinarith
        have hvnonneg : 0 ≤ (d : ℤ) * (v : ℕ) := by positivity
        omega
      · have hsep := hgap j i hji
        have hv : (v : ℕ) < Δ := v.isLt.trans_le (min_le_left _ _)
        have hdZ : 0 < (d : ℤ) := by exact_mod_cast hd
        dsimp [F] at huv
        have hvult : a + starts j + (d : ℤ) * (v : ℕ) < a + starts i := by
          nlinarith
        have hunonneg : 0 ≤ (d : ℤ) * (u : ℕ) := by positivity
        omega
  let P : Finset ℤ := Finset.univ.image F
  have hPsub : P ⊆ S := by
    intro z hz
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hz
    exact hFmem p
  have hPcard : P.card = T * min Δ L := by
    rw [Finset.card_image_of_injective _ hFinj]
    simp
  rw [← hPcard]
  exact Finset.card_le_card hPsub

private lemma restrictedSumset_mono_regularSpan
    {r : ℕ} {B C : Finset ℤ} (hBC : B ⊆ C) :
    restrictedSumset r B ⊆ restrictedSumset r C := by
  intro z hz
  obtain ⟨S, hSB, hScard, hSsum⟩ := mem_restrictedSumset.mp hz
  exact mem_restrictedSumset.mpr ⟨S, hSB.trans hBC, hScard, hSsum⟩

/-! ## The finite DF95 endpoint-absorption theorem -/

/-- **Endpoint absorption.**

Suppose `C ⊆ A` already carries an `L`-term progression of difference `d`
in its `ell`-th restricted layer, and every element of `A \ C` lies in one
residue class modulo `d`.  Reserve the lowest and highest `T` regular
elements.  A common filler raises every interpolating translate to the
prescribed layer `s`.  If that layer is too small to contain
`T * min U L` points, the unreserved regular elements lie in a `d`-progression
of at most `U` terms.

The hypothesis on `filler` is deliberately stated using truncated natural
subtraction.  Thus it imposes no spurious condition in the branch
`(A \ C).card < 2*T`, where all regular elements are simply absorbed. -/
theorem exists_regular_span_after_absorbing_extremes
    {A C : Finset ℤ} {ell s d L T U filler : ℕ}
    (hCA : C ⊆ A) (hd : 0 < d) (hT : 0 < T)
    (hlayer : ell + (filler + T) = s)
    (hfiller : filler ≤ (A \ C).card - 2 * T)
    (hcapacity : (restrictedSumset s A).card < T * min U L)
    (hlong : ContainsAP (restrictedSumset ell C) (d : ℤ) L)
    (hregular : IsDifferenceDivisor d (A \ C)) :
    ∃ C' start,
      C ⊆ C' ∧
      C' ⊆ A ∧
      C'.card ≤ C.card + 2 * T ∧
      ContainsAP (restrictedSumset ell C') (d : ℤ) L ∧
      ContainedInAP (A \ C') start d U := by
  let D := A \ C
  by_cases h2T : 2 * T ≤ D.card
  · let E := endpointExtremes D T h2T
    have hED : E ⊆ D := endpointExtremes_subset D T h2T
    have hEcard : E.card = 2 * T := card_endpointExtremes D T h2T
    have hDEcard : (D \ E).card = D.card - 2 * T := by
      rw [Finset.card_sdiff_of_subset hED, hEcard]
    have hfillCard : filler ≤ (D \ E).card := by
      simpa [D, hDEcard] using hfiller
    obtain ⟨W, hW, hWcard⟩ := Finset.exists_subset_card_eq hfillCard
    have hWD : W ⊆ D := hW.trans Finset.sdiff_subset
    have hWE : Disjoint W E := by
      rw [Finset.disjoint_left]
      intro x hxW hxE
      exact (Finset.mem_sdiff.mp (hW hxW)).2 hxE

    let low : ℤ := D.orderEmbOfFin rfl ⟨T - 1, by omega⟩
    let high : ℤ := D.orderEmbOfFin rfl ⟨D.card - T, by omega⟩
    have hlowD : low ∈ D := D.orderEmbOfFin_mem rfl _
    have hhighD : high ∈ D := D.orderEmbOfFin_mem rfl _
    have hlowhigh : low < high := by
      apply (D.orderEmbOfFin rfl).strictMono
      apply Fin.mk_lt_mk.mpr
      omega
    obtain ⟨z, hz⟩ := hregular high hhighD low hlowD
    have hzpos : 0 < z := by
      have hdZ : 0 < (d : ℤ) := by exact_mod_cast hd
      dsimp [low, high] at hlowhigh
      nlinarith
    let Δ : ℕ := z.toNat
    have hzcast : (Δ : ℤ) = z := by
      exact Int.toNat_of_nonneg hzpos.le
    have hΔ : high - low = (d : ℤ) * (Δ : ℤ) := by
      simpa [hzcast] using hz

    let startsFull : Fin (T + 1) → ℤ := fun j =>
      (∑ x ∈ W, x) + ∑ x ∈ endpointMix D T h2T j, x
    have hstartsSucc : ∀ j : Fin T,
        startsFull j.castSucc + (d : ℤ) * (Δ : ℤ) ≤
          startsFull j.succ := by
      intro j
      dsimp [startsFull]
      have hgap := endpointMix_sum_gap D T d Δ h2T hd hT (by
        simpa [low, high] using hΔ) (j : ℕ) j.isLt
      have hjcast : j.castSucc = (⟨(j : ℕ), by omega⟩ : Fin (T + 1)) :=
        Fin.ext rfl
      have hjsucc : j.succ = (⟨(j : ℕ) + 1, by omega⟩ : Fin (T + 1)) :=
        Fin.ext rfl
      rw [hjcast, hjsucc]
      omega
    have hstartsMono : Monotone startsFull := by
      apply Fin.monotone_iff_le_succ.mpr
      intro j
      have h := hstartsSucc j
      have hnonneg : 0 ≤ (d : ℤ) * (Δ : ℤ) := by positivity
      omega
    let starts : Fin T → ℤ := fun j => startsFull j.castSucc
    have hstartsGap : ∀ i j : Fin T, i < j →
        starts i + (d : ℤ) * (Δ : ℤ) ≤ starts j := by
      intro i j hij
      have hadj := hstartsSucc i
      have hisucc : i.succ ≤ j.castSucc := by
        apply Fin.mk_le_mk.mpr
        omega
      exact hadj.trans (hstartsMono hisucc)

    obtain ⟨a, ha⟩ := hlong
    have htranslate : ∀ i : Fin T,
        arithmeticProgression (a + starts i) (d : ℤ) (min Δ L) ⊆
          restrictedSumset s A := by
      intro i y hy
      obtain ⟨n, hn, rfl⟩ := mem_arithmeticProgression.mp hy
      let j : Fin (T + 1) := i.castSucc
      let X := endpointMix D T h2T j
      have hXE : X ⊆ E := endpointMix_subset_extremes D T h2T j
      have hXD : X ⊆ D := hXE.trans hED
      have hWX : Disjoint W X := hWE.mono_right hXE
      let R := W ∪ X
      have hRD : R ⊆ D := Finset.union_subset hWD hXD
      have hRcard : R.card = filler + T := by
        dsimp [R]
        rw [Finset.card_union_of_disjoint hWX, hWcard,
          card_endpointMix]
      have hnL : n < L := hn.trans_le (min_le_right _ _)
      have hbase : a + (d : ℤ) * (n : ℕ) ∈ restrictedSumset ell C :=
        ha (mem_arithmeticProgression.mpr ⟨n, hnL, rfl⟩)
      have hadd := add_sum_mem_restrictedSumset_of_subset_sdiff
        hCA (by simpa [D] using hRD) hbase
      rw [hRcard, hlayer] at hadd
      have hRsum : (∑ x ∈ R, x) = starts i := by
        dsimp [R]
        rw [Finset.sum_union hWX]
      rw [hRsum] at hadd
      simpa [starts, startsFull, j, X, add_assoc, add_left_comm, add_comm]
        using hadd
    have hpack : T * min Δ L ≤ (restrictedSumset s A).card :=
      separated_progression_translates_card_le hd starts hstartsGap htranslate
    have hΔU : Δ < U := by
      by_contra hnot
      have hUΔ : U ≤ Δ := Nat.le_of_not_gt hnot
      have hmin : min U L ≤ min Δ L := min_le_min_right L hUΔ
      have hmul := Nat.mul_le_mul_left T hmin
      omega

    let C' := C ∪ E
    have hCC' : C ⊆ C' := Finset.subset_union_left
    have hC'A : C' ⊆ A := by
      apply Finset.union_subset hCA
      exact hED.trans (by simpa [D] using Finset.sdiff_subset)
    have hC'card : C'.card ≤ C.card + 2 * T := by
      calc
        C'.card ≤ C.card + E.card := by
          simpa [C'] using Finset.card_union_le C E
        _ = C.card + 2 * T := by rw [hEcard]
    have hlong' : ContainsAP (restrictedSumset ell C') (d : ℤ) L := by
      refine ⟨a, fun x hx => restrictedSumset_mono_regularSpan hCC' (ha hx)⟩
    have hshort : ContainedInAP (A \ C') low d U := by
      refine ⟨hd, ?_⟩
      intro x hx
      have hxA : x ∈ A := (Finset.mem_sdiff.mp hx).1
      have hxnotC' : x ∉ C' := (Finset.mem_sdiff.mp hx).2
      have hxC : x ∉ C := fun hxC => hxnotC' (Finset.mem_union_left E hxC)
      have hxE : x ∉ E := fun hxE => hxnotC' (Finset.mem_union_right C hxE)
      have hxD : x ∈ D := by simpa [D] using Finset.mem_sdiff.mpr ⟨hxA, hxC⟩
      have hxenum : x ∈ Finset.univ.map (D.orderEmbOfFin rfl).toEmbedding := by
        rw [D.map_orderEmbOfFin_univ rfl]
        exact hxD
      obtain ⟨i, _hi, hi⟩ := Finset.mem_map.mp hxenum
      have hiT : T ≤ (i : ℕ) := by
        by_contra hnot
        have hiLT : (i : ℕ) < T := Nat.lt_of_not_ge hnot
        have hxP : x ∈ orderedBlock D 0 T (by omega) := by
          apply (mem_orderedBlock_iff D 0 T (by omega) x).mpr
          exact ⟨⟨i, hiLT⟩, by simpa using hi⟩
        exact hxE (Finset.mem_union_left _ hxP)
      have hiHigh : (i : ℕ) < D.card - T := by
        by_contra hnot
        have hle : D.card - T ≤ (i : ℕ) := Nat.le_of_not_gt hnot
        let q : ℕ := (i : ℕ) - (D.card - T)
        have hqT : q < T := by dsimp [q]; omega
        have hxQ : x ∈ orderedBlock D (D.card - T) T (by omega) := by
          apply (mem_orderedBlock_iff D (D.card - T) T (by omega) x).mpr
          refine ⟨⟨q, hqT⟩, ?_⟩
          have hidx :
              (⟨D.card - T + q, by omega⟩ : Fin D.card) = i := by
            apply Fin.ext
            dsimp [q]
            omega
          simpa [hidx] using hi
        exact hxE (Finset.mem_union_right _ hxQ)
      have hlowx : low < x := by
        rw [← hi]
        dsimp [low]
        apply (D.orderEmbOfFin rfl).strictMono
        apply Fin.mk_lt_mk.mpr
        omega
      have hxhigh : x < high := by
        rw [← hi]
        dsimp [high]
        apply (D.orderEmbOfFin rfl).strictMono
        apply Fin.mk_lt_mk.mpr
        exact hiHigh
      obtain ⟨q, hq⟩ := hregular x hxD low hlowD
      have hqpos : 0 < q := by
        have hdZ : 0 < (d : ℤ) := by exact_mod_cast hd
        have hprod : 0 < (d : ℤ) * q := by
          calc
            0 < x - low := sub_pos.mpr hlowx
            _ = (d : ℤ) * q := hq
        rcases (mul_pos_iff.mp hprod) with h | h
        · exact h.2
        · exact (not_lt_of_ge hdZ.le h.1).elim
      let n : ℕ := q.toNat
      have hncast : (n : ℤ) = q := Int.toNat_of_nonneg hqpos.le
      have hxrep : x = low + (n : ℤ) * (d : ℤ) := by
        rw [hncast]
        nlinarith
      have hnΔ : n < Δ := by
        have hdZ : 0 < (d : ℤ) := by exact_mod_cast hd
        have hmul : (n : ℤ) * (d : ℤ) < (Δ : ℤ) * (d : ℤ) := by
          calc
            (n : ℤ) * (d : ℤ) = x - low := by rw [hxrep]; ring
            _ < high - low := sub_lt_sub_right hxhigh low
            _ = (d : ℤ) * (Δ : ℤ) := hΔ
            _ = (Δ : ℤ) * (d : ℤ) := mul_comm _ _
        have hnZ : (n : ℤ) < (Δ : ℤ) :=
          lt_of_mul_lt_mul_right hmul hdZ.le
        exact_mod_cast hnZ
      exact ⟨n, hnΔ.trans hΔU, hxrep⟩
    exact ⟨C', low, hCC', hC'A, hC'card, hlong', hshort⟩
  · have hDsmall : D.card < 2 * T := Nat.lt_of_not_ge h2T
    have hCAeq : C ∪ D = A := by
      simpa [D] using Finset.union_sdiff_of_subset hCA
    have hcardD : D.card + C.card = A.card := by
      simpa [D] using Finset.card_sdiff_add_card_eq_card hCA
    have hAcard : A.card ≤ C.card + 2 * T := by omega
    have hlongA : ContainsAP (restrictedSumset ell A) (d : ℤ) L :=
      ContainsAP.mono hlong (restrictedSumset_mono_regularSpan hCA)
    refine ⟨A, 0, hCA, Finset.Subset.rfl, hAcard, hlongA, ?_⟩
    simp [ContainedInAP, hd]

end

end Erdos874
