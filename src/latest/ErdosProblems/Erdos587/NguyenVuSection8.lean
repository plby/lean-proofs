import ErdosProblems.Erdos587.ResidueTrichotomy

open Filter MeasureTheory
open scoped BigOperators Pointwise

namespace Erdos587

/-!
# Nguyen--Vu Section 8: finite combinatorial preparation

The stopped rank-reduction theorem covers the unused reserve by boundedly
many translates of an iterated difference of the terminal rank-two GAP.
Nguyen--Vu's Section 8 is phrased for boundedly many translates of the GAP
itself.  The first lemmas below bridge these two formulations: an iterated
difference coefficient box is tiled by a rank-dependent constant number of
ordinary coefficient boxes.  This restores the exact coordinate fibers used
in Proposition 8.3 without paying a side-length factor.
-/

/-- Partition an integer coordinate in `[-K*L,K*L]` into a box of width
`L+1`, with a box index in `[-K,K]` and a remainder in `[0,L]`. -/
lemma exists_binned_coordinate (K L : ℕ) {k : ℤ}
    (hk : |k| ≤ (K * L : ℕ)) :
    ∃ b : ℤ, b ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) ∧
      ∃ r : ℕ, r ≤ L ∧ k = b * (L + 1 : ℕ) + r := by
  let d : ℤ := (L + 1 : ℕ)
  let b : ℤ := k / d
  let e : ℤ := k % d
  have hd : 0 < d := by simp [d]
  have he0 : 0 ≤ e := Int.emod_nonneg _ hd.ne'
  have hed : e < d := Int.emod_lt_of_pos _ hd
  have heL : e ≤ (L : ℤ) := by simp [d] at hed; omega
  have hdecomp : k = b * d + e := by
    have h := Int.emod_add_mul_ediv k d
    dsimp only [b, e]
    linarith
  have hkZ : |k| ≤ (K : ℤ) * (L : ℤ) := by exact_mod_cast hk
  have hk' : -(K : ℤ) * (L : ℤ) ≤ k ∧
      k ≤ (K : ℤ) * (L : ℤ) := by
    simpa only [neg_mul] using abs_le.mp hkZ
  have hlowRaw : (-(K : ℤ)) * d ≤ k := by
    dsimp only [d]
    push_cast
    nlinarith [hk'.1]
  have huppRaw : k ≤ (K : ℤ) * d := by
    dsimp only [d]
    push_cast
    nlinarith [hk'.2]
  have hbLow : -(K : ℤ) ≤ b := by
    have hdiv := Int.ediv_le_ediv hd hlowRaw
    have hcancel : ((-(K : ℤ)) * d) / d = -(K : ℤ) := by
      rw [mul_comm (-(K : ℤ)) d]
      exact Int.mul_ediv_cancel_left _ hd.ne'
    simpa only [b, hcancel] using hdiv
  have hbUpp : b ≤ (K : ℤ) := by
    have hdiv := Int.ediv_le_ediv hd huppRaw
    have hcancel : ((K : ℤ) * d) / d = (K : ℤ) := by
      rw [mul_comm (K : ℤ) d]
      exact Int.mul_ediv_cancel_left _ hd.ne'
    simpa only [b, hcancel] using hdiv
  refine ⟨b, Finset.mem_Icc.mpr ⟨hbLow, hbUpp⟩,
    e.toNat, ?_, ?_⟩
  · exact Int.toNat_le.mpr heL
  · rw [Int.toNat_of_nonneg he0]
    simpa only [d] using hdecomp

namespace GeneralizedAP

/-- Swap the two coordinates of the already-positive presentation of a
rank-two GAP.  This is used to run the Section 8 argument with either side
as the long arithmetic-progression direction. -/
def rankTwoSwap (R : GeneralizedAP) (hrank : R.rank = 2) : GeneralizedAP where
  rank := 2
  base := R.positiveForm.base
  step := Fin.cases
    (R.positiveForm.step
      ⟨1, by simpa [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (fun _ : Fin 1 ↦ R.positiveForm.step
      ⟨0, by simpa [GeneralizedAP.rank_positiveForm, hrank]⟩)
  length := Fin.cases
    (R.length ⟨1, by omega⟩)
    (fun _ : Fin 1 ↦ R.length ⟨0, by omega⟩)

@[simp] lemma rank_rankTwoSwap (R : GeneralizedAP) (hrank : R.rank = 2) :
    (R.rankTwoSwap hrank).rank = 2 := rfl

@[simp] lemma length_rankTwoSwap_zero
    (R : GeneralizedAP) (hrank : R.rank = 2) :
    (R.rankTwoSwap hrank).length ⟨0, by simp [rankTwoSwap]⟩ =
      R.length ⟨1, by omega⟩ := by rfl

@[simp] lemma length_rankTwoSwap_one
    (R : GeneralizedAP) (hrank : R.rank = 2) :
    (R.rankTwoSwap hrank).length ⟨1, by simp [rankTwoSwap]⟩ =
      R.length ⟨0, by omega⟩ := by rfl

@[simp] lemma positiveForm_base_rankTwoSwap
    (R : GeneralizedAP) (hrank : R.rank = 2) :
    (R.rankTwoSwap hrank).positiveForm.base = R.positiveForm.base := by
  unfold GeneralizedAP.positiveForm
  change R.positiveForm.base +
      (∑ i : Fin 2,
        if (R.rankTwoSwap hrank).step i < 0 then
          ((R.rankTwoSwap hrank).length i : ℤ) *
            (R.rankTwoSwap hrank).step i else 0) = R.positiveForm.base
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro i _hi
  have hstep : 0 ≤ (R.rankTwoSwap hrank).step i := by
    fin_cases i
    · exact R.step_positiveForm_nonneg _
    · exact R.step_positiveForm_nonneg _
  simp only [if_neg (not_lt_of_ge hstep)]

@[simp] lemma positiveForm_step_rankTwoSwap_zero
    (R : GeneralizedAP) (hrank : R.rank = 2) :
    (R.rankTwoSwap hrank).positiveForm.step
      ⟨0, by simp [rankTwoSwap]⟩ =
      R.positiveForm.step
        ⟨1, by simpa [GeneralizedAP.rank_positiveForm, hrank]⟩ := by
  change |R.positiveForm.step
    ⟨1, by simpa [GeneralizedAP.rank_positiveForm, hrank]⟩| = _
  apply abs_of_nonneg
  exact R.step_positiveForm_nonneg _

@[simp] lemma positiveForm_step_rankTwoSwap_one
    (R : GeneralizedAP) (hrank : R.rank = 2) :
    (R.rankTwoSwap hrank).positiveForm.step
      ⟨1, by simp [rankTwoSwap]⟩ =
      R.positiveForm.step
        ⟨0, by simpa [GeneralizedAP.rank_positiveForm, hrank]⟩ := by
  change |R.positiveForm.step
    ⟨0, by simpa [GeneralizedAP.rank_positiveForm, hrank]⟩| = _
  apply abs_of_nonneg
  exact R.step_positiveForm_nonneg _

/-- Every element of the `(n+1)`-fold iterated difference has a homogeneous
coefficient vector bounded coordinatewise by `2^n` times the original side
length. -/
lemma exists_bounded_coeff_of_mem_iteratedDifference_succ
    (R : GeneralizedAP) :
    ∀ n {z : ℤ}, z ∈ iteratedDifference (n + 1) R.carrier →
      ∃ k : R.CoeffVec,
        (∀ i, |k i| ≤ (2 ^ n * R.length i : ℕ)) ∧
        z = R.linearEval k := by
  intro n
  induction n with
  | zero =>
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
      obtain ⟨x, rfl⟩ := R.mem_carrier_iff.mp ha
      obtain ⟨y, rfl⟩ := R.mem_carrier_iff.mp hb
      let k : R.CoeffVec := fun i => (x i : ℤ) - (y i : ℤ)
      refine ⟨k, ?_, ?_⟩
      · intro i
        have hx : (x i : ℕ) ≤ R.length i := Nat.le_of_lt_succ (x i).isLt
        have hy : (y i : ℕ) ≤ R.length i := Nat.le_of_lt_succ (y i).isLt
        rw [abs_le]
        constructor <;> dsimp only [k] <;> norm_num <;> omega
      · rw [R.eval_eq_base_add_linearEval, R.eval_eq_base_add_linearEval]
        simp only [GeneralizedAP.linearEval, k]
        rw [show R.base + (∑ i, ((x i : ℕ) : ℤ) * R.step i) -
            (R.base + ∑ i, ((y i : ℕ) : ℤ) * R.step i) =
            (∑ i, ((x i : ℕ) : ℤ) * R.step i) -
              ∑ i, ((y i : ℕ) : ℤ) * R.step i by ring]
        rw [← Finset.sum_sub_distrib]
        congr 1
        funext i
        ring
  | succ n ih =>
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
      obtain ⟨x, hx, rfl⟩ := ih ha
      obtain ⟨y, hy, rfl⟩ := ih hb
      let k : R.CoeffVec := fun i => x i - y i
      refine ⟨k, ?_, ?_⟩
      · intro i
        calc
          |k i| ≤ |x i| + |y i| := by
            dsimp only [k]
            exact abs_sub _ _
          _ ≤ (2 ^ n * R.length i : ℕ) +
              (2 ^ n * R.length i : ℕ) := add_le_add (hx i) (hy i)
          _ = (2 ^ (n + 1) * R.length i : ℕ) := by
            norm_num
            rw [pow_succ]
            ring
      · simp only [GeneralizedAP.linearEval, k]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring

/-- The rectangular rank-two carrier contains every point obtained by
choosing one natural coordinate on each side. -/
lemma base_add_two_steps_mem_carrier
    (R : GeneralizedAP) (hrank : R.rank = 2) {x y : ℕ}
    (hx : x ≤ R.length ⟨0, by omega⟩)
    (hy : y ≤ R.length ⟨1, by omega⟩) :
    R.base + (x : ℤ) * R.step ⟨0, by omega⟩ +
        (y : ℤ) * R.step ⟨1, by omega⟩ ∈ R.carrier := by
  let i₀ : Fin R.rank := ⟨0, by omega⟩
  let i₁ : Fin R.rank := ⟨1, by omega⟩
  have hi01 : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  have hall (j : Fin R.rank) : j = i₀ ∨ j = i₁ := by
    have hjlt : j.val < 2 := by simpa [hrank] using j.isLt
    rcases (show j.val = 0 ∨ j.val = 1 by omega) with hj | hj
    · exact Or.inl (Fin.ext (by simpa [i₀] using hj))
    · exact Or.inr (Fin.ext (by simpa [i₁] using hj))
  have huniv : (Finset.univ : Finset (Fin R.rank)) = {i₀, i₁} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact hall j
  let v : R.Param := fun j ↦
    if hj : j = i₀ then
      ⟨x, by simpa [i₀, hj] using Nat.lt_succ_of_le hx⟩
    else
      ⟨y, by
        have hj₁ : j = i₁ := (hall j).resolve_left hj
        simpa [i₁, hj₁] using Nat.lt_succ_of_le hy⟩
  apply R.mem_carrier_iff.mpr
  refine ⟨v, ?_⟩
  simp only [GeneralizedAP.eval]
  rw [huniv]
  simp [v, hi01, hi01.symm]
  ring

/-- Origins of the ordinary rank-two boxes tiling the coefficient range
`[-K*L₁,K*L₁] × [-K*L₂,K*L₂]`. -/
noncomputable def rankTwoBoxOrigins
    (R : GeneralizedAP) (hrank : R.rank = 2) (K : ℕ) : Finset ℤ :=
  let I := Finset.Icc (-(K : ℤ)) (K : ℤ)
  (I ×ˢ I).image fun b ↦
    -R.positiveForm.base +
      b.1 * (R.length ⟨0, by omega⟩ + 1 : ℕ) *
        R.positiveForm.step
          ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ +
      b.2 * (R.length ⟨1, by omega⟩ + 1 : ℕ) *
        R.positiveForm.step
          ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩

lemma card_rankTwoBoxOrigins_le
    (R : GeneralizedAP) (hrank : R.rank = 2) (K : ℕ) :
    (R.rankTwoBoxOrigins hrank K).card ≤ (2 * K + 1) ^ 2 := by
  let I := Finset.Icc (-(K : ℤ)) (K : ℤ)
  calc
    (R.rankTwoBoxOrigins hrank K).card ≤ (I ×ˢ I).card :=
      Finset.card_image_le
    _ = I.card * I.card := Finset.card_product _ _
    _ = (2 * K + 1) ^ 2 := by
      have hI : I.card = 2 * K + 1 := by
        dsimp only [I]
        rw [Int.card_Icc]
        norm_num
        omega
      rw [hI]
      ring

/-- A rank-two iterated difference is covered by a side-length-independent
number of translates of the original carrier. -/
lemma iteratedDifference_rank_two_subset_boxOrigins_add_carrier
    (R : GeneralizedAP) (hrank : R.rank = 2) (n : ℕ) :
    iteratedDifference (n + 1) R.carrier ⊆
      R.rankTwoBoxOrigins hrank (2 ^ n) + R.carrier := by
  intro z hz
  let S := R.positiveForm
  have hSr : S.rank = 2 := by simpa [S] using hrank
  have hzS : z ∈ iteratedDifference (n + 1) S.carrier := by
    simpa only [S, R.carrier_positiveForm] using hz
  obtain ⟨k, hk, hzk⟩ :=
    S.exists_bounded_coeff_of_mem_iteratedDifference_succ n hzS
  let i₀ : Fin S.rank := ⟨0, by omega⟩
  let i₁ : Fin S.rank := ⟨1, by omega⟩
  obtain ⟨b₀, hb₀, x, hx, hk₀⟩ :=
    exists_binned_coordinate (2 ^ n) (R.length ⟨0, by omega⟩)
      (k := k i₀) (by simpa [S, i₀] using hk i₀)
  obtain ⟨b₁, hb₁, y, hy, hk₁⟩ :=
    exists_binned_coordinate (2 ^ n) (R.length ⟨1, by omega⟩)
      (k := k i₁) (by simpa [S, i₁] using hk i₁)
  let o : ℤ := -S.base +
      b₀ * (R.length ⟨0, by omega⟩ + 1 : ℕ) * S.step i₀ +
      b₁ * (R.length ⟨1, by omega⟩ + 1 : ℕ) * S.step i₁
  let c : ℤ := S.base + (x : ℤ) * S.step i₀ + (y : ℤ) * S.step i₁
  have ho : o ∈ R.rankTwoBoxOrigins hrank (2 ^ n) := by
    apply Finset.mem_image.mpr
    refine ⟨(b₀, b₁), Finset.mem_product.mpr ⟨hb₀, hb₁⟩, ?_⟩
    rfl
  have hcS : c ∈ S.carrier := by
    simpa only [c, i₀, i₁] using
      S.base_add_two_steps_mem_carrier hSr
        (by simpa [S] using hx) (by simpa [S] using hy)
  have hcR : c ∈ R.carrier := by
    rw [← R.carrier_positiveForm]
    exact hcS
  apply Finset.mem_add.mpr
  refine ⟨o, ho, c, hcR, ?_⟩
  have hall (j : Fin S.rank) : j = i₀ ∨ j = i₁ := by
    have hjlt : j.val < 2 := by simpa [hSr] using j.isLt
    rcases (show j.val = 0 ∨ j.val = 1 by omega) with hj | hj
    · exact Or.inl (Fin.ext (by simpa [i₀] using hj))
    · exact Or.inr (Fin.ext (by simpa [i₁] using hj))
  have hi01 : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  have huniv : (Finset.univ : Finset (Fin S.rank)) = {i₀, i₁} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact hall j
  rw [hzk]
  simp only [GeneralizedAP.linearEval]
  rw [huniv]
  simp [hi01, o, c, hk₀, hk₁]
  ring

end GeneralizedAP

/-- Compose the stopped iterated-difference cover with the rank-two box
tiling.  The resulting translation count depends only on the difference
depth and the previous cover count, not on either side length. -/
lemma exists_rank_two_carrier_translate_cover_of_iteratedDifference_cover
    {B : Finset ℕ} {Z : Finset ℤ} (R : GeneralizedAP)
    (hrank : R.rank = 2) (n : ℕ)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier) :
    ∃ Z' : Finset ℤ,
      Z'.card ≤ Z.card * (2 * (2 ^ n) + 1) ^ 2 ∧
      natToIntFinset B ⊆ Z' + R.carrier := by
  let O := R.rankTwoBoxOrigins hrank (2 ^ n)
  let Z' := Z + O
  refine ⟨Z', ?_, ?_⟩
  · calc
      Z'.card ≤ Z.card * O.card := Finset.card_add_le
      _ ≤ Z.card * (2 * (2 ^ n) + 1) ^ 2 :=
        Nat.mul_le_mul_left Z.card
          (R.card_rankTwoBoxOrigins_le hrank (2 ^ n))
  · intro a ha
    obtain ⟨z, hz, d, hd, hzd⟩ := Finset.mem_add.mp (hcover ha)
    have hd' := R.iteratedDifference_rank_two_subset_boxOrigins_add_carrier
      hrank n hd
    obtain ⟨o, ho, c, hc, hoc⟩ := Finset.mem_add.mp hd'
    apply Finset.mem_add.mpr
    refine ⟨z + o, Finset.mem_add.mpr ⟨z, hz, o, ho, rfl⟩,
      c, hc, ?_⟩
    omega

/-! ## Proposition 8.3: the essential coordinate -/

/-- A bounded-increment prefix chain covers its whole total interval after
adding one final remainder in `[0,L]`.  This is the finite form of (22). -/
lemma exists_take_sum_add_remainder_of_le_sum
    {L x : ℕ} {ds : List ℕ}
    (hD : ∀ d ∈ ds, d ≤ L) (hx : x ≤ ds.sum) :
    ∃ j ≤ ds.length, ∃ u ≤ L,
      x = (ds.take j).sum + u := by
  induction ds generalizing x with
  | nil =>
      simp only [List.sum_nil] at hx
      refine ⟨0, by simp, 0, by omega, ?_⟩
      simp
      omega
  | cons d ds ih =>
      have hd : d ≤ L := hD d (by simp)
      have htail : ∀ e ∈ ds, e ≤ L := by
        intro e he
        exact hD e (by simp [he])
      by_cases hxd : x ≤ d
      · refine ⟨0, by simp, x, hxd.trans hd, by simp⟩
      · have hxTail : x - d ≤ ds.sum := by
          simp only [List.sum_cons] at hx
          omega
        obtain ⟨j, hj, u, hu, heq⟩ := ih htail hxTail
        refine ⟨j + 1, by simp; omega, u, hu, ?_⟩
        simp only [List.take_succ_cons, List.sum_cons]
        omega

/-- The index of the `i`-th smallest term in a sorted family of length `m`. -/
def lowIndex {m l : ℕ} (h : l ≤ m) (i : Fin l) : Fin m :=
  ⟨i, lt_of_lt_of_le i.isLt h⟩

/-- The index of the `i`-th term among the `l` largest terms in a sorted
family of length `m`. -/
def highIndex {m l : ℕ} (h : l ≤ m) (i : Fin l) : Fin m :=
  ⟨m - l + i, by omega⟩

/-- If the total gap between the `l` largest and `l` smallest terms of a
monotone integer family is less than `l`, one corresponding pair agrees. -/
lemma exists_equal_low_high_of_monotone_sum_gap
    {m l : ℕ} (t : Fin m → ℤ) (ht : Monotone t)
    (hl : 0 < l) (h2l : 2 * l ≤ m)
    (hgap : (∑ i : Fin l,
      (t (highIndex (by omega) i) - t (lowIndex (by omega) i))) < l) :
    ∃ i : Fin l,
      t (lowIndex (by omega) i) = t (highIndex (by omega) i) := by
  have hlm : l ≤ m := by omega
  by_contra hno
  push Not at hno
  have hterm (i : Fin l) :
      (1 : ℤ) ≤ t (highIndex hlm i) -
        t (lowIndex hlm i) := by
    have hidx : (lowIndex hlm i : ℕ) ≤
        (highIndex hlm i : ℕ) := by
      change (i : ℕ) ≤ m - l + (i : ℕ)
      omega
    have hle := ht hidx
    have hne : t (lowIndex hlm i) ≠ t (highIndex hlm i) := by
      simpa using hno i
    omega
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset (Fin l)))
    (f := fun _i => (1 : ℤ))
    (g := fun i => t (highIndex hlm i) -
      t (lowIndex hlm i))
    (fun i _hi => hterm i)
  have hlower : (l : ℤ) ≤ ∑ i : Fin l,
      (t (highIndex (by omega) i) - t (lowIndex (by omega) i)) := by
    simpa using hsum
  exact (not_lt_of_ge hlower) hgap

/-- Nguyen--Vu Proposition 8.3 in a division-free finite form.  If the
restricted-sum gap is less than `l`, a single value occurs at all but at most
`l` positions. -/
lemma exists_essential_value_of_monotone_sum_gap
    {m l : ℕ} (t : Fin m → ℤ) (ht : Monotone t)
    (hl : 0 < l) (h2l : 2 * l ≤ m)
    (hgap : (∑ i : Fin l,
      (t (highIndex (by omega) i) - t (lowIndex (by omega) i))) < l) :
    ∃ c : ℤ,
      m ≤ ((Finset.univ : Finset (Fin m)).filter fun j => t j = c).card + l := by
  obtain ⟨i, hi⟩ :=
    exists_equal_low_high_of_monotone_sum_gap t ht hl h2l hgap
  have hlm : l ≤ m := by omega
  let a : Fin m := lowIndex hlm i
  let b : Fin m := highIndex hlm i
  let c : ℤ := t a
  have hab : a ≤ b := by
    apply Fin.mk_le_mk.mpr
    change (i : ℕ) ≤ m - l + (i : ℕ)
    omega
  have hinterval : Finset.Icc a b ⊆
      (Finset.univ : Finset (Fin m)).filter fun j => t j = c := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply le_antisymm
    · exact ht hj'.2 |>.trans_eq (by simpa only [a, b, c] using hi.symm)
    · exact ht hj'.1
  have hcard := Finset.card_le_card hinterval
  have hIcc : (Finset.Icc a b).card = m - l + 1 := by
    rw [Fin.card_Icc]
    simp only [a, b, lowIndex, highIndex]
    omega
  rw [hIcc] at hcard
  refine ⟨c, ?_⟩
  omega

/-! ## The exchange chain (equation (22)) -/

/-- The first `j` indices in `Fin l`, embedded without changing values. -/
def finHead (l j : ℕ) (hj : j ≤ l) : Finset (Fin l) :=
  (Finset.univ : Finset (Fin j)).image (Fin.castLE hj)

lemma card_finHead (l j : ℕ) (hj : j ≤ l) :
    (finHead l j hj).card = j := by
  rw [finHead, Finset.card_image_of_injective _ (Fin.castLE_injective hj)]
  simp

lemma finHead_eq_filter (l j : ℕ) (hj : j ≤ l) :
    finHead l j hj =
      (Finset.univ : Finset (Fin l)).filter fun i : Fin l => i.val < j := by
  ext i
  constructor
  · intro hi
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, k.isLt⟩
  · intro hi
    have hij := (Finset.mem_filter.mp hi).2
    apply Finset.mem_image.mpr
    let k : Fin j := ⟨i, hij⟩
    refine ⟨k, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl

/-- The `l`-element index set obtained after the first `j` exchanges: retain
the last `l-j` of the `l` smallest indices and insert the first `j` of the
`l` largest indices. -/
def exchangeIndices (m l j : ℕ) (h2l : 2 * l ≤ m) (hj : j ≤ l) :
    Finset (Fin m) :=
  (((Finset.univ : Finset (Fin l)) \ finHead l j hj).image
      (lowIndex (by omega))) ∪
    (finHead l j hj).image (highIndex (by omega))

lemma card_exchangeIndices (m l j : ℕ) (h2l : 2 * l ≤ m)
    (hj : j ≤ l) : (exchangeIndices m l j h2l hj).card = l := by
  have hlm : l ≤ m := by omega
  let H := finHead l j hj
  let A := ((Finset.univ : Finset (Fin l)) \ H).image
      (lowIndex hlm)
  let B := H.image (highIndex hlm)
  have hlowInj : Function.Injective (lowIndex hlm) := by
    intro a b hab
    apply Fin.ext
    simpa only [lowIndex] using congrArg Fin.val hab
  have hhighInj : Function.Injective (highIndex hlm) := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    simp only [highIndex] at hv
    omega
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr (by
    intro x hxA hxB
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hxA
    obtain ⟨b, _hb, hEq⟩ := Finset.mem_image.mp hxB
    have hv := congrArg Fin.val hEq
    simp only [lowIndex, highIndex] at hv
    have hb : (b : ℕ) < l := b.isLt
    omega)
  have hHsub : H ⊆ (Finset.univ : Finset (Fin l)) := by simp
  have hAcard : A.card = l - j := by
    dsimp only [A]
    rw [Finset.card_image_of_injective _ hlowInj,
      Finset.card_sdiff_of_subset hHsub, Finset.card_univ,
      Fintype.card_fin, show H.card = j by exact card_finHead l j hj]
  have hBcard : B.card = j := by
    dsimp only [B]
    rw [Finset.card_image_of_injective _ hhighInj,
      show H.card = j by exact card_finHead l j hj]
  dsimp only [exchangeIndices]
  change (A ∪ B).card = l
  rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard]
  omega

/-- The fixed set of the `l` smallest and `l` largest indices.  Every member
of the exchange chain lies in this set, so it can be reserved before the
quadratic congruence adjustment is performed. -/
def exchangeSupport (m l : ℕ) (h2l : 2 * l ≤ m) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin l)).image (lowIndex (by omega)) ∪
    (Finset.univ : Finset (Fin l)).image (highIndex (by omega))

lemma card_exchangeSupport_le (m l : ℕ) (h2l : 2 * l ≤ m) :
    (exchangeSupport m l h2l).card ≤ 2 * l := by
  have hlow : ((Finset.univ : Finset (Fin l)).image
      (lowIndex (m := m) (l := l) (by omega))).card ≤ l := by
    simpa using (Finset.card_image_le :
      ((Finset.univ : Finset (Fin l)).image
        (lowIndex (m := m) (l := l) (by omega))).card ≤
          (Finset.univ : Finset (Fin l)).card)
  have hhigh : ((Finset.univ : Finset (Fin l)).image
      (highIndex (m := m) (l := l) (by omega))).card ≤ l := by
    simpa using (Finset.card_image_le :
      ((Finset.univ : Finset (Fin l)).image
        (highIndex (m := m) (l := l) (by omega))).card ≤
          (Finset.univ : Finset (Fin l)).card)
  calc
    (exchangeSupport m l h2l).card ≤
        ((Finset.univ : Finset (Fin l)).image
            (lowIndex (m := m) (l := l) (by omega))).card +
          ((Finset.univ : Finset (Fin l)).image
            (highIndex (m := m) (l := l) (by omega))).card :=
      Finset.card_union_le _ _
    _ ≤ l + l := Nat.add_le_add hlow hhigh
    _ = 2 * l := by omega

lemma exchangeIndices_subset_exchangeSupport
    (m l j : ℕ) (h2l : 2 * l ≤ m) (hj : j ≤ l) :
    exchangeIndices m l j h2l hj ⊆ exchangeSupport m l h2l := by
  intro i hi
  rw [exchangeIndices, Finset.mem_union] at hi
  rw [exchangeSupport, Finset.mem_union]
  rcases hi with hi | hi
  · left
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · right
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

/-- Successive nonnegative increments in the exchange chain. -/
def exchangeDeltas {m l : ℕ} (t : Fin m → ℤ) (h : l ≤ m) : List ℕ :=
  List.ofFn fun i : Fin l =>
    Int.toNat (t (highIndex h i) - t (lowIndex h i))

lemma length_exchangeDeltas {m l : ℕ} (t : Fin m → ℤ) (h : l ≤ m) :
    (exchangeDeltas t h).length = l := by simp [exchangeDeltas]

lemma intCast_sum_exchangeDeltas {m l : ℕ} (t : Fin m → ℤ)
    (hlm : l ≤ m) (ht : Monotone t) :
    ((exchangeDeltas t hlm).sum : ℤ) =
      ∑ i : Fin l, (t (highIndex hlm i) -
        t (lowIndex hlm i)) := by
  rw [exchangeDeltas, List.sum_ofFn]
  push_cast
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Int.toNat_of_nonneg]
  have hidx : (lowIndex hlm i : ℕ) ≤
      (highIndex hlm i : ℕ) := by
    change (i : ℕ) ≤ m - l + (i : ℕ)
    omega
  exact sub_nonneg.mpr (ht hidx)

lemma intCast_sum_take_exchangeDeltas {m l j : ℕ} (t : Fin m → ℤ)
    (hlm : l ≤ m) (ht : Monotone t) (hj : j ≤ l) :
    (((exchangeDeltas t hlm).take j).sum : ℤ) =
      ∑ i ∈ finHead l j hj,
        (t (highIndex hlm i) - t (lowIndex hlm i)) := by
  rw [exchangeDeltas, List.sum_take_ofFn]
  push_cast
  rw [finHead_eq_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Int.toNat_of_nonneg]
  have hidx : (lowIndex hlm i : ℕ) ≤
      (highIndex hlm i : ℕ) := by
    change (i : ℕ) ≤ m - l + (i : ℕ)
    omega
  exact sub_nonneg.mpr (ht hidx)

lemma sum_exchangeIndices {m l j : ℕ} (t : Fin m → ℤ)
    (hlm : l ≤ m) (h2l : 2 * l ≤ m) (hj : j ≤ l)
    (ht : Monotone t) :
    (∑ k ∈ exchangeIndices m l j h2l hj, t k) =
      (∑ i : Fin l, t (lowIndex hlm i)) +
        (((exchangeDeltas t hlm).take j).sum : ℤ) := by
  let H := finHead l j hj
  let A := ((Finset.univ : Finset (Fin l)) \ H).image (lowIndex hlm)
  let B := H.image (highIndex hlm)
  have hlowInj : Function.Injective (lowIndex hlm) := by
    intro a b hab
    apply Fin.ext
    simpa only [lowIndex] using congrArg Fin.val hab
  have hhighInj : Function.Injective (highIndex hlm) := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    simp only [highIndex] at hv
    omega
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr (by
    intro x hxA hxB
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hxA
    obtain ⟨b, _hb, hEq⟩ := Finset.mem_image.mp hxB
    have hv := congrArg Fin.val hEq
    simp only [lowIndex, highIndex] at hv
    have hb : (b : ℕ) < l := b.isLt
    omega)
  have hHsub : H ⊆ (Finset.univ : Finset (Fin l)) := by simp
  have hA : (∑ k ∈ A, t k) =
      ∑ i ∈ (Finset.univ : Finset (Fin l)) \ H,
        t (lowIndex hlm i) := by
    dsimp only [A]
    exact Finset.sum_image hlowInj.injOn
  have hB : (∑ k ∈ B, t k) =
      ∑ i ∈ H, t (highIndex hlm i) := by
    dsimp only [B]
    exact Finset.sum_image hhighInj.injOn
  have hsplit := Finset.sum_sdiff hHsub
      (f := fun i : Fin l => t (lowIndex hlm i))
  have hdelta := intCast_sum_take_exchangeDeltas t hlm ht hj
  dsimp only [exchangeIndices]
  change (∑ k ∈ A ∪ B, t k) = _
  rw [Finset.sum_union hdisj, hA, hB]
  rw [Finset.sum_sub_distrib] at hdelta
  linarith

/-- The exact exchange-chain realization used in Nguyen--Vu equation (22).
Every integer shift up to the total exchange gap is realized by an
`l`-element index set, up to one remainder in `[0,L]`. -/
lemma exists_exchangeIndices_sum_add_remainder
    {m l L x : ℕ} (t : Fin m → ℤ)
    (hlm : l ≤ m) (h2l : 2 * l ≤ m) (ht : Monotone t)
    (hwidth : ∀ i : Fin l,
      t (highIndex hlm i) - t (lowIndex hlm i) ≤ (L : ℤ))
    (hx : x ≤ (exchangeDeltas t hlm).sum) :
    ∃ I : Finset (Fin m), I.card = l ∧
      I ⊆ exchangeSupport m l h2l ∧
      ∃ u ≤ L,
        (∑ k ∈ I, t k) =
          (∑ i : Fin l, t (lowIndex hlm i)) + (x : ℤ) - (u : ℤ) := by
  have hD : ∀ d ∈ exchangeDeltas t hlm, d ≤ L := by
    intro d hd
    rw [exchangeDeltas, List.mem_ofFn] at hd
    obtain ⟨i, rfl⟩ := hd
    exact Int.toNat_le.mpr (hwidth i)
  obtain ⟨j, hj, u, hu, hxu⟩ :=
    exists_take_sum_add_remainder_of_le_sum hD hx
  have hjl : j ≤ l := by simpa [exchangeDeltas] using hj
  let I := exchangeIndices m l j h2l hjl
  refine ⟨I, ?_, ?_, u, hu, ?_⟩
  · exact card_exchangeIndices m l j h2l hjl
  · exact exchangeIndices_subset_exchangeSupport m l j h2l hjl
  · have hsum := sum_exchangeIndices t hlm h2l hjl ht
    dsimp only [I]
    rw [hsum]
    have hxuZ : (x : ℤ) =
        ((List.take j (exchangeDeltas t hlm)).sum : ℤ) + (u : ℤ) := by
      exact_mod_cast hxu
    rw [hxuZ]
    ring

/-! ## Ordinary rank-two cover fibers -/

namespace GeneralizedAP

lemma eval_rank_two_eq_base_add_two_steps
    (R : GeneralizedAP) (hrank : R.rank = 2) (v : R.Param) :
    R.eval v = R.base +
      ((v ⟨0, by omega⟩ : ℕ) : ℤ) * R.step ⟨0, by omega⟩ +
      ((v ⟨1, by omega⟩ : ℕ) : ℤ) * R.step ⟨1, by omega⟩ := by
  let i₀ : Fin R.rank := ⟨0, by omega⟩
  let i₁ : Fin R.rank := ⟨1, by omega⟩
  have hi01 : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  have hall (j : Fin R.rank) : j = i₀ ∨ j = i₁ := by
    have hjlt : j.val < 2 := by simpa [hrank] using j.isLt
    rcases (show j.val = 0 ∨ j.val = 1 by omega) with hj | hj
    · exact Or.inl (Fin.ext (by simpa [i₀] using hj))
    · exact Or.inr (Fin.ext (by simpa [i₁] using hj))
  have huniv : (Finset.univ : Finset (Fin R.rank)) = {i₀, i₁} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact hall j
  simp only [GeneralizedAP.eval]
  rw [huniv]
  simp [i₀, i₁, hi01]
  ring

end GeneralizedAP

/-- A deterministic assignment of every covered reserve element to one
ordinary rank-two translate and to one coefficient pair in its positive
presentation.  No uniqueness of the cover is assumed; classical choice fixes
one witness for each element. -/
structure RankTwoCoverModel (B : Finset ℕ) (Z : Finset ℤ)
    (R : GeneralizedAP) (hrank : R.rank = 2) where
  origin : ↥B → ℤ
  first : ↥B → ℕ
  second : ↥B → ℕ
  origin_mem : ∀ a, origin a ∈ Z
  first_le : ∀ a, first a ≤ R.length ⟨0, by omega⟩
  second_le : ∀ a, second a ≤ R.length ⟨1, by omega⟩
  value_eq : ∀ a,
    ((a.val : ℕ) : ℤ) = origin a + R.positiveForm.base +
      (first a : ℤ) * R.positiveForm.step
        ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ +
      (second a : ℤ) * R.positiveForm.step
        ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩

theorem exists_rankTwoCoverModel
    {B : Finset ℕ} {Z : Finset ℤ} (R : GeneralizedAP)
    (hrank : R.rank = 2)
    (hcover : natToIntFinset B ⊆ Z + R.carrier) :
    Nonempty (RankTwoCoverModel B Z R hrank) := by
  classical
  let S := R.positiveForm
  have hSr : S.rank = 2 := by simpa [S] using hrank
  have haRep (a : ↥B) : ∃ z : ℤ, ∃ x y : ℕ,
      z ∈ Z ∧ x ≤ R.length ⟨0, by omega⟩ ∧
      y ≤ R.length ⟨1, by omega⟩ ∧
      ((a.val : ℕ) : ℤ) = z + S.base +
        (x : ℤ) * S.step ⟨0, by omega⟩ +
        (y : ℤ) * S.step ⟨1, by omega⟩ := by
    have haInt : ((a.val : ℕ) : ℤ) ∈ natToIntFinset B :=
      natCast_mem_natToIntFinset.mpr a.property
    obtain ⟨z, hz, c, hc, hzc⟩ := Finset.mem_add.mp (hcover haInt)
    have hcS : c ∈ S.carrier := by
      simpa only [S, R.carrier_positiveForm] using hc
    obtain ⟨v, hv⟩ := S.mem_carrier_iff.mp hcS
    let x : ℕ := v ⟨0, by omega⟩
    let y : ℕ := v ⟨1, by omega⟩
    refine ⟨z, x, y, hz, ?_, ?_, ?_⟩
    · exact Nat.le_of_lt_succ (by simpa [x, S] using
        (v ⟨0, by omega⟩).isLt)
    · exact Nat.le_of_lt_succ (by simpa [y, S] using
        (v ⟨1, by omega⟩).isLt)
    · rw [← hv, S.eval_rank_two_eq_base_add_two_steps hSr v] at hzc
      dsimp only [x, y]
      calc
        ((a.val : ℕ) : ℤ) = z +
            (S.base + ((v ⟨0, by omega⟩ : ℕ) : ℤ) * S.step ⟨0, by omega⟩ +
              ((v ⟨1, by omega⟩ : ℕ) : ℤ) * S.step ⟨1, by omega⟩) := hzc.symm
        _ = z + S.base + ((v ⟨0, by omega⟩ : ℕ) : ℤ) *
              S.step ⟨0, by omega⟩ +
              ((v ⟨1, by omega⟩ : ℕ) : ℤ) * S.step ⟨1, by omega⟩ := by ring
  choose origin first second horigin hfirst hsecond heq using haRep
  exact ⟨{
    origin := origin
    first := first
    second := second
    origin_mem := horigin
    first_le := hfirst
    second_le := hsecond
    value_eq := by simpa only [S] using heq }⟩

namespace RankTwoCoverModel

/-- The same rank-two cover, with its two positive coordinates exchanged. -/
noncomputable def swap {B : Finset ℕ} {Z : Finset ℤ}
    {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank) :
    RankTwoCoverModel B Z (R.rankTwoSwap hrank)
      (R.rank_rankTwoSwap hrank) where
  origin := M.origin
  first := M.second
  second := M.first
  origin_mem := M.origin_mem
  first_le := by
    intro a
    simpa only [GeneralizedAP.length_rankTwoSwap_zero] using M.second_le a
  second_le := by
    intro a
    simpa only [GeneralizedAP.length_rankTwoSwap_one] using M.first_le a
  value_eq := by
    intro a
    rw [GeneralizedAP.positiveForm_base_rankTwoSwap,
      GeneralizedAP.positiveForm_step_rankTwoSwap_zero,
      GeneralizedAP.positiveForm_step_rankTwoSwap_one]
    calc
      ((a.val : ℕ) : ℤ) = M.origin a + R.positiveForm.base +
          (M.first a : ℤ) * R.positiveForm.step
            ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ +
          (M.second a : ℤ) * R.positiveForm.step
            ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ := M.value_eq a
      _ = M.origin a + R.positiveForm.base +
          (M.second a : ℤ) * R.positiveForm.step
            ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ +
          (M.first a : ℤ) * R.positiveForm.step
            ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ := by ring

def fiber {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank) (z : ℤ) :
    Finset ↥B :=
  (Finset.univ : Finset ↥B).filter fun a => M.origin a = z

@[simp] lemma mem_fiber {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank)
    {z : ℤ} {a : ↥B} : a ∈ M.fiber z ↔ M.origin a = z := by
  simp [fiber]

lemma card_eq_sum_card_fiber {B : Finset ℕ} {Z : Finset ℤ}
    {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank) :
    B.card = ∑ z ∈ Z, (M.fiber z).card := by
  have hmap : ((Finset.univ : Finset ↥B) : Set ↥B).MapsTo M.origin Z := by
    intro a _ha
    exact M.origin_mem a
  simpa only [fiber, Finset.card_univ, Fintype.card_coe] using
    (Finset.card_eq_sum_card_fiberwise hmap)

noncomputable def sortedFiber {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank) (z : ℤ) :
    List ↥B :=
  (M.fiber z).toList.mergeSort fun a b => decide (M.first a ≤ M.first b)

@[simp] lemma length_sortedFiber {B : Finset ℕ} {Z : Finset ℤ}
    {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank) (z : ℤ) :
    (M.sortedFiber z).length = (M.fiber z).card := by
  simp [sortedFiber]

lemma nodup_sortedFiber {B : Finset ℕ} {Z : Finset ℤ}
    {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank) (z : ℤ) :
    (M.sortedFiber z).Nodup := by
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (M.fiber z).nodup_toList

noncomputable def sortedIndex {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank) (z : ℤ)
    (i : Fin (M.fiber z).card) : Fin (M.sortedFiber z).length :=
  ⟨i, by simpa using i.isLt⟩

noncomputable def fiberElement {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank) (z : ℤ)
    (i : Fin (M.fiber z).card) : ↥B :=
  (M.sortedFiber z).get (M.sortedIndex z i)

noncomputable def fiberFirst {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank) (z : ℤ)
    (i : Fin (M.fiber z).card) : ℤ :=
  M.first (M.fiberElement z i)

lemma fiberElement_mem_fiber {B : Finset ℕ} {Z : Finset ℤ}
    {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank) (z : ℤ)
    (i : Fin (M.fiber z).card) : M.fiberElement z i ∈ M.fiber z := by
  have hmem := List.get_mem (M.sortedFiber z) (M.sortedIndex z i)
  change (M.sortedFiber z).get (M.sortedIndex z i) ∈ M.fiber z
  simpa only [sortedFiber, List.mem_mergeSort, Finset.mem_toList] using hmem

lemma origin_fiberElement {B : Finset ℕ} {Z : Finset ℤ}
    {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank) (z : ℤ)
    (i : Fin (M.fiber z).card) : M.origin (M.fiberElement z i) = z := by
  exact M.mem_fiber.mp (M.fiberElement_mem_fiber z i)

lemma injective_fiberElement {B : Finset ℕ} {Z : Finset ℤ}
    {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank) (z : ℤ) :
    Function.Injective (M.fiberElement z) := by
  intro i j hij
  have hget : M.sortedIndex z i = M.sortedIndex z j :=
    (M.nodup_sortedFiber z).injective_get hij
  apply Fin.ext
  have hv := congrArg Fin.val hget
  simpa only [sortedIndex] using hv

lemma fiberFirst_nonneg {B : Finset ℕ} {Z : Finset ℤ}
    {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank) (z : ℤ)
    (i : Fin (M.fiber z).card) : 0 ≤ M.fiberFirst z i := by
  simp [fiberFirst]

lemma fiberFirst_le {B : Finset ℕ} {Z : Finset ℤ}
    {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank) (z : ℤ)
    (i : Fin (M.fiber z).card) :
    M.fiberFirst z i ≤ R.length ⟨0, by omega⟩ := by
  change (M.first (M.fiberElement z i) : ℤ) ≤
    (R.length ⟨0, by omega⟩ : ℤ)
  exact_mod_cast M.first_le (M.fiberElement z i)

lemma monotone_fiberFirst {B : Finset ℕ} {Z : Finset ℤ}
    {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank) (z : ℤ) :
    Monotone (M.fiberFirst z) := by
  have hpair : (M.sortedFiber z).Pairwise
      (fun a b => M.first a ≤ M.first b) := by
    exact List.pairwise_mergeSort' _ _
  intro i j hij
  obtain rfl | hijne := eq_or_ne i j
  · exact le_rfl
  have hijlt : i < j := lt_of_le_of_ne hij hijne
  have hidx : M.sortedIndex z i < M.sortedIndex z j := by
    exact_mod_cast hijlt
  have hfirst := (List.pairwise_iff_get.mp hpair) _ _ hidx
  change (M.first ((M.sortedFiber z).get (M.sortedIndex z i)) : ℤ) ≤
    (M.first ((M.sortedFiber z).get (M.sortedIndex z j)) : ℤ)
  exact_mod_cast hfirst

lemma fiberFirst_exchange_width {B : Finset ℕ} {Z : Finset ℤ}
    {R : GeneralizedAP} {hrank : R.rank = 2}
    (M : RankTwoCoverModel B Z R hrank) (z : ℤ)
    {l : ℕ} (hlm : l ≤ (M.fiber z).card) (i : Fin l) :
    M.fiberFirst z (highIndex hlm i) -
        M.fiberFirst z (lowIndex hlm i) ≤
      (R.length ⟨0, by omega⟩ : ℤ) := by
  have hhigh := M.fiberFirst_le z (highIndex hlm i)
  have hlow := M.fiberFirst_nonneg z (lowIndex hlm i)
  omega

/-- The actual reserve elements corresponding to the `l` lowest and `l`
highest first coordinates of a cover fiber. -/
noncomputable def fiberExchangeReserve
    {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank)
    (z : ℤ) (l : ℕ) (h2l : 2 * l ≤ (M.fiber z).card) : Finset ℕ :=
  (exchangeSupport (M.fiber z).card l h2l).image fun i ↦
    (M.fiberElement z i).val

lemma fiberExchangeReserve_subset
    {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank)
    (z : ℤ) (l : ℕ) (h2l : 2 * l ≤ (M.fiber z).card) :
    M.fiberExchangeReserve z l h2l ⊆ B := by
  intro a ha
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ha
  exact (M.fiberElement z i).property

lemma card_fiberExchangeReserve_le
    {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank)
    (z : ℤ) (l : ℕ) (h2l : 2 * l ≤ (M.fiber z).card) :
    (M.fiberExchangeReserve z l h2l).card ≤ 2 * l := by
  calc
    (M.fiberExchangeReserve z l h2l).card ≤
        (exchangeSupport (M.fiber z).card l h2l).card :=
      Finset.card_image_le
    _ ≤ 2 * l := card_exchangeSupport_le _ _ _

/-- Modulo a common divisor of both rank-two steps, every modeled reserve
element is determined by its translation origin. -/
lemma usedPositiveResidues_card_le_common_step
    {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank)
    {q : ℕ} (hq : 0 < q)
    (hstep₀ : (q : ℤ) ∣ R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hstep₁ : (q : ℤ) ∣ R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) :
    (usedPositiveResidues q B).card ≤ Z.card := by
  classical
  let residues : Finset ℕ := Z.image fun z ↦
    positiveIntResidue q (z + R.positiveForm.base)
  have hsub : usedPositiveResidues q B ⊆ residues := by
    intro g hg
    obtain ⟨a, haB, rfl⟩ := mem_usedPositiveResidues.mp hg
    let b : ↥B := ⟨a, haB⟩
    apply Finset.mem_image.mpr
    refine ⟨M.origin b, M.origin_mem b, ?_⟩
    have hmod : ((a : ℕ) : ℤ) ≡ M.origin b + R.positiveForm.base
        [ZMOD (q : ℤ)] := by
      rw [Int.modEq_iff_dvd, M.value_eq b]
      have hd₀ : (q : ℤ) ∣
          (M.first b : ℤ) * R.positiveForm.step
            ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ :=
        dvd_mul_of_dvd_right hstep₀ _
      have hd₁ : (q : ℤ) ∣
          (M.second b : ℤ) * R.positiveForm.step
            ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ :=
        dvd_mul_of_dvd_right hstep₁ _
      have heq :
          M.origin b + R.positiveForm.base -
              (M.origin b + R.positiveForm.base +
                (M.first b : ℤ) * R.positiveForm.step
                  ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ +
                (M.second b : ℤ) * R.positiveForm.step
                  ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) =
            -((M.first b : ℤ) * R.positiveForm.step
                ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ +
              (M.second b : ℤ) * R.positiveForm.step
                ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) := by
        ring
      rw [heq]
      exact dvd_neg.mpr (dvd_add hd₀ hd₁)
    exact (positiveResidue_eq_positiveIntResidue_of_modEq hq hmod).symm
  calc
    (usedPositiveResidues q B).card ≤ residues.card := Finset.card_le_card hsub
    _ ≤ Z.card := Finset.card_image_le

/-- Actual-element form of Nguyen--Vu (22)/(26): after exchanging `l`
elements inside one fiber, every admissible first-coordinate shift is
realized up to one first-side remainder; the untracked second coordinates
contribute an integer multiple of the second step. -/
lemma exists_fiber_exchange_sum
    {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank)
    (z : ℤ) {l x : ℕ} (hlm : l ≤ (M.fiber z).card)
    (h2l : 2 * l ≤ (M.fiber z).card)
    (hx : x ≤ (exchangeDeltas (M.fiberFirst z) hlm).sum) :
    ∃ T : Finset ℕ, T ⊆ M.fiberExchangeReserve z l h2l ∧
      T ⊆ B ∧ T.card = l ∧
      ∃ u ≤ R.length ⟨0, by omega⟩, ∃ v : ℤ,
        (((∑ a ∈ T, a : ℕ) : ℕ) : ℤ) +
            (u : ℤ) * R.positiveForm.step
              ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ =
          (l : ℤ) * (z + R.positiveForm.base) +
            ((∑ i : Fin l,
                M.fiberFirst z (lowIndex (by omega) i)) + (x : ℤ)) *
              R.positiveForm.step
                ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ +
            v * R.positiveForm.step
              ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ := by
  classical
  obtain ⟨I, hIcard, hIsub, u, hu, hcoord⟩ :=
    exists_exchangeIndices_sum_add_remainder
      (M.fiberFirst z) hlm h2l (M.monotone_fiberFirst z)
      (M.fiberFirst_exchange_width z hlm) hx
  let f : Fin (M.fiber z).card → ℕ := fun i => (M.fiberElement z i).val
  have hf : Function.Injective f := by
    intro i j hij
    apply M.injective_fiberElement z
    apply Subtype.ext
    exact hij
  let T : Finset ℕ := I.image f
  have hTB : T ⊆ B := by
    intro a ha
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ha
    exact (M.fiberElement z i).property
  have hTres : T ⊆ M.fiberExchangeReserve z l h2l := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_image.mpr
    exact ⟨i, hIsub hi, rfl⟩
  have hTcard : T.card = l := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ hf, hIcard]
  let v : ℤ := ∑ i ∈ I, (M.second (M.fiberElement z i) : ℤ)
  refine ⟨T, hTres, hTB, hTcard, u, hu, v, ?_⟩
  have hTsum : ∑ a ∈ T, a = ∑ i ∈ I, f i := by
    dsimp only [T]
    exact Finset.sum_image hf.injOn
  have hTsumZ : (((∑ a ∈ T, a : ℕ) : ℕ) : ℤ) =
      ∑ i ∈ I, ((M.fiberElement z i).val : ℤ) := by
    rw [hTsum]
    dsimp only [f]
    push_cast
    rfl
  have hvalue : (∑ i ∈ I, ((M.fiberElement z i).val : ℤ)) =
      ∑ i ∈ I,
        (z + R.positiveForm.base +
          (M.first (M.fiberElement z i) : ℤ) *
            R.positiveForm.step
              ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩ +
          (M.second (M.fiberElement z i) : ℤ) *
            R.positiveForm.step
              ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) := by
    apply Finset.sum_congr rfl
    intro i _hi
    simpa only [M.origin_fiberElement z i] using M.value_eq (M.fiberElement z i)
  rw [hTsumZ, hvalue]
  have hfirst : (∑ i ∈ I, (M.first (M.fiberElement z i) : ℤ)) =
      (∑ i : Fin l, M.fiberFirst z (lowIndex hlm i)) +
        (x : ℤ) - (u : ℤ) := by
    simpa only [fiberFirst] using hcoord
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hIcard]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hfirst]
  dsimp only [v]
  ring

/-- Assemble constant-first-coordinate pieces from all ordinary cover fibers.
The retained set loses at most `loss` elements per fiber and uses at most one
residue modulo the second step per translation origin. -/
theorem exists_global_subset_of_concentrated_fibers
    {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank)
    {q₂ loss : ℕ} (hq₂ : 0 < q₂)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (c : ℤ → ℤ) (K : ℤ → Finset ↥B)
    (hKsub : ∀ z ∈ Z, K z ⊆ M.fiber z)
    (hKfirst : ∀ z ∈ Z, ∀ a ∈ K z, (M.first a : ℤ) = c z)
    (hloss : ∀ z ∈ Z, (M.fiber z).card ≤ (K z).card + loss) :
    ∃ D : Finset ℕ, D ⊆ B ∧
      B.card ≤ D.card + Z.card * loss ∧
      (usedPositiveResidues q₂ D).card ≤ Z.card := by
  classical
  let U : Finset ↥B := Z.biUnion K
  let D : Finset ℕ := U.image Subtype.val
  have hdisj : (Z : Set ℤ).PairwiseDisjoint K := by
    intro z hz w hw hzw
    apply Finset.disjoint_left.mpr
    intro a haKz haKw
    have haz := M.mem_fiber.mp (hKsub z hz haKz)
    have haw := M.mem_fiber.mp (hKsub w hw haKw)
    exact hzw (haz.symm.trans haw)
  have hUcard : U.card = ∑ z ∈ Z, (K z).card := by
    exact Finset.card_biUnion hdisj
  have hDcard : D.card = U.card := by
    dsimp only [D]
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
  have hDB : D ⊆ B := by
    intro a ha
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp ha
    exact b.property
  have hcard : B.card ≤ D.card + Z.card * loss := by
    rw [M.card_eq_sum_card_fiber, hDcard, hUcard]
    calc
      (∑ z ∈ Z, (M.fiber z).card) ≤
          ∑ z ∈ Z, ((K z).card + loss) :=
        Finset.sum_le_sum fun z hz => hloss z hz
      _ = (∑ z ∈ Z, (K z).card) + Z.card * loss := by
        rw [Finset.sum_add_distrib]
        simp [mul_comm]
  let residues : Finset ℕ := Z.image fun z =>
    positiveIntResidue q₂
      (z + R.positiveForm.base + c z * R.positiveForm.step
        ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
  have hresSub : usedPositiveResidues q₂ D ⊆ residues := by
    intro g hg
    obtain ⟨a, haD, rfl⟩ := mem_usedPositiveResidues.mp hg
    obtain ⟨b, hbU, rfl⟩ := Finset.mem_image.mp haD
    obtain ⟨z, hz, hbK⟩ := Finset.mem_biUnion.mp hbU
    apply Finset.mem_image.mpr
    refine ⟨z, hz, ?_⟩
    have hvalue := M.value_eq b
    rw [M.mem_fiber.mp (hKsub z hz hbK), hKfirst z hz b hbK] at hvalue
    have hmod : ((b.val : ℕ) : ℤ) ≡
        z + R.positiveForm.base + c z * R.positiveForm.step
          ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩
        [ZMOD (q₂ : ℤ)] := by
      rw [Int.modEq_iff_dvd, hvalue, hq₂step]
      refine ⟨-(M.second b : ℤ), ?_⟩
      ring
    exact (positiveResidue_eq_positiveIntResidue_of_modEq hq₂ hmod).symm
  refine ⟨D, hDB, hcard, ?_⟩
  calc
    (usedPositiveResidues q₂ D).card ≤ residues.card :=
      Finset.card_le_card hresSub
    _ ≤ Z.card := Finset.card_image_le

/-- Global concentrated branch of Nguyen--Vu Proposition 8.3.  Small fibers
are discarded; every large fiber contributes all indices having its essential
first coordinate. -/
theorem exists_concentrated_core
    {B : Finset ℕ} {Z : Finset ℤ} {R : GeneralizedAP}
    {hrank : R.rank = 2} (M : RankTwoCoverModel B Z R hrank)
    {q₂ l : ℕ} (hq₂ : 0 < q₂)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hl : 0 < l)
    (hconcentrated : ∀ z ∈ Z, ∀ h2l : 2 * l ≤ (M.fiber z).card,
      (∑ i : Fin l,
        (M.fiberFirst z (highIndex (by omega) i) -
          M.fiberFirst z (lowIndex (by omega) i))) < l) :
    ∃ D : Finset ℕ, D ⊆ B ∧
      B.card ≤ D.card + Z.card * (2 * l) ∧
      (usedPositiveResidues q₂ D).card ≤ Z.card := by
  classical
  have hselect (z : ℤ) (hz : z ∈ Z) :
      ∃ c : ℤ, ∃ K : Finset ↥B,
        K ⊆ M.fiber z ∧
        (∀ a ∈ K, (M.first a : ℤ) = c) ∧
        (M.fiber z).card ≤ K.card + 2 * l := by
    by_cases h2l : 2 * l ≤ (M.fiber z).card
    · obtain ⟨c, hc⟩ := exists_essential_value_of_monotone_sum_gap
        (M.fiberFirst z) (M.monotone_fiberFirst z) hl h2l
        (hconcentrated z hz h2l)
      let J : Finset (Fin (M.fiber z).card) :=
        (Finset.univ : Finset (Fin (M.fiber z).card)).filter fun i =>
          M.fiberFirst z i = c
      let K : Finset ↥B := J.image (M.fiberElement z)
      have hKsub : K ⊆ M.fiber z := by
        intro a ha
        obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ha
        exact M.fiberElement_mem_fiber z i
      have hKfirst : ∀ a ∈ K, (M.first a : ℤ) = c := by
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        have hit := (Finset.mem_filter.mp hi).2
        simpa only [fiberFirst] using hit
      have hKcard : K.card = J.card := by
        dsimp only [K]
        rw [Finset.card_image_of_injective _ (M.injective_fiberElement z)]
      refine ⟨c, K, hKsub, hKfirst, ?_⟩
      rw [hKcard]
      dsimp only [J]
      omega
    · refine ⟨0, ∅, by simp, by simp, ?_⟩
      simp only [Finset.card_empty, zero_add]
      omega
  choose c K hKsub hKfirst hloss using hselect
  let c₀ : ℤ → ℤ := fun z => if hz : z ∈ Z then c z hz else 0
  let K₀ : ℤ → Finset ↥B := fun z => if hz : z ∈ Z then K z hz else ∅
  apply M.exists_global_subset_of_concentrated_fibers hq₂ hq₂step c₀ K₀
  · intro z hz
    simpa only [K₀, hz, dite_true] using hKsub z hz
  · intro z hz a ha
    have ha' : a ∈ K z hz := by simpa only [K₀, hz, dite_true] using ha
    simpa only [c₀, hz, dite_true] using hKfirst z hz a ha'
  · intro z hz
    simpa only [K₀, hz, dite_true] using hloss z hz

end RankTwoCoverModel

end Erdos587
