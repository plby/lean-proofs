import ErdosProblems.Erdos360.LevCompletion

/-!
# Lev's dense two-summand interval lemma

This file formalizes the elementary reflection proof of Lemma 1 in
V. F. Lev, *Optimal representations by sumsets and subset sums*, J. Number
Theory 130 (2010).  The nonemptiness hypotheses are indispensable (and are
automatic for the subset-sum sets occurring in `IsCFPLevFamily`).
-/

open scoped Pointwise

namespace Erdos360

attribute [local instance] Classical.propDecidable

private def intCastFinset (S : Finset ℕ) : Finset ℤ :=
  S.image (fun s : ℕ ↦ (s : ℤ))

private def reflectedIntFinset (x : ℕ) (S : Finset ℕ) : Finset ℤ :=
  S.image (fun s : ℕ ↦ (x : ℤ) - (s : ℤ))

private lemma card_intCastFinset (S : Finset ℕ) :
    (intCastFinset S).card = S.card := by
  rw [intCastFinset, Finset.card_image_iff.mpr]
  intro a _ b _ hab
  exact Int.ofNat_inj.mp hab

private lemma card_reflectedIntFinset (x : ℕ) (S : Finset ℕ) :
    (reflectedIntFinset x S).card = S.card := by
  rw [reflectedIntFinset, Finset.card_image_iff.mpr]
  intro a _ b _ hab
  have : (a : ℤ) = b := sub_right_inj.mp hab
  exact Int.ofNat_inj.mp this

private lemma intCastFinset_subset_Icc {S : Finset ℕ} {lo hi : ℕ}
    (hS : S ⊆ Finset.Icc lo hi) :
    intCastFinset S ⊆ Finset.Icc (lo : ℤ) hi := by
  intro z hz
  simp only [intCastFinset, Finset.mem_image] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  rw [Finset.mem_Icc]
  exact_mod_cast (Finset.mem_Icc.mp (hS hs))

private lemma reflectedIntFinset_subset_Icc
    {S : Finset ℕ} {x L : ℕ} (hS : S ⊆ Finset.Icc 0 L) :
    reflectedIntFinset x S ⊆
      Finset.Icc ((x : ℤ) - L) x := by
  intro z hz
  simp only [reflectedIntFinset, Finset.mem_image] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  have hsI := Finset.mem_Icc.mp (hS hs)
  rw [Finset.mem_Icc]
  constructor
  · exact sub_le_sub_left (Int.ofNat_le.mpr hsI.2) _
  · exact sub_le_self _ (Int.natCast_nonneg s)

private lemma reflectedIntFinset_subset_Icc_of_subset_Icc
    {S : Finset ℕ} {x lo hi : ℕ} (hS : S ⊆ Finset.Icc lo hi) :
    reflectedIntFinset x S ⊆
      Finset.Icc ((x : ℤ) - hi) ((x : ℤ) - lo) := by
  intro z hz
  simp only [reflectedIntFinset, Finset.mem_image] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  have hsI := Finset.mem_Icc.mp (hS hs)
  rw [Finset.mem_Icc]
  constructor
  · exact sub_le_sub_left (Int.ofNat_le.mpr hsI.2) _
  · exact sub_le_sub_left (Int.ofNat_le.mpr hsI.1) _

private lemma mem_add_of_reflected_inter
    {S₁ S₂ : Finset ℕ} {x : ℕ}
    (hinter : (intCastFinset S₁ ∩ reflectedIntFinset x S₂).Nonempty) :
    x ∈ S₁ + S₂ := by
  obtain ⟨z, hz⟩ := hinter
  rw [Finset.mem_inter] at hz
  simp only [intCastFinset, reflectedIntFinset, Finset.mem_image] at hz
  obtain ⟨a, ha, rfl⟩ := hz.1
  obtain ⟨b, hb, hab⟩ := hz.2
  rw [Finset.mem_add]
  refine ⟨a, ha, b, hb, ?_⟩
  have hab' : (a : ℤ) + b = x := by omega
  exact_mod_cast hab'

private lemma mem_add_of_common_int_interval
    {S₁ S₂ : Finset ℕ} {x : ℕ} {lo hi : ℤ}
    (h₁ : intCastFinset S₁ ⊆ Finset.Icc lo hi)
    (h₂ : reflectedIntFinset x S₂ ⊆ Finset.Icc lo hi)
    (hcard : (Finset.Icc lo hi).card < S₁.card + S₂.card) :
    x ∈ S₁ + S₂ := by
  apply mem_add_of_reflected_inter
  apply Finset.inter_nonempty_of_card_lt_card_add_card h₁ h₂
  simpa [card_intCastFinset, card_reflectedIntFinset] using hcard

/-- Lev's dense two-summand interval lemma.  The hypotheses say that two
nonempty sets lie in integer intervals of lengths `L₁` and `L₂`, and that
each of those lengths is at most the combined excess cardinality.  Then the
entire central interval occurs in the sumset. -/
theorem lev_dense_two_sum_interval
    {S₁ S₂ : Finset ℕ} {L₁ L₂ : ℕ}
    (hne₁ : S₁.Nonempty) (hne₂ : S₂.Nonempty)
    (hS₁ : S₁ ⊆ Finset.Icc 0 L₁)
    (hS₂ : S₂ ⊆ Finset.Icc 0 L₂)
    (hdense : max L₁ L₂ ≤ S₁.card + S₂.card - 2) :
    Finset.Icc
        (L₁ + L₂ - (S₁.card + S₂.card - 2))
        (S₁.card + S₂.card - 2) ⊆ S₁ + S₂ := by
  let K := S₁.card + S₂.card - 2
  have hcard₁ : 0 < S₁.card := Finset.card_pos.mpr hne₁
  have hcard₂ : 0 < S₂.card := Finset.card_pos.mpr hne₂
  have hK : K + 2 = S₁.card + S₂.card := by
    dsimp [K]
    omega
  have hL₁K : L₁ ≤ K := le_trans (le_max_left _ _) hdense
  have hL₂K : L₂ ≤ K := le_trans (le_max_right _ _) hdense
  have hcast₁ : intCastFinset S₁ ⊆ Finset.Icc (0 : ℤ) L₁ :=
    intCastFinset_subset_Icc hS₁
  intro x hx
  rw [Finset.mem_Icc] at hx
  have hxlow : L₁ + L₂ - K ≤ x := by simpa [K] using hx.1
  have hxhigh : x ≤ K := by simpa [K] using hx.2
  have href : reflectedIntFinset x S₂ ⊆
      Finset.Icc ((x : ℤ) - L₂) x :=
    reflectedIntFinset_subset_Icc hS₂
  by_cases hxL₁ : x ≤ L₁
  · by_cases hL₂x : L₂ ≤ x
    · apply mem_add_of_common_int_interval
          (lo := 0) (hi := L₁) hcast₁
      · exact href.trans (Finset.Icc_subset_Icc
          (sub_nonneg.mpr (Int.ofNat_le.mpr hL₂x)) (by exact_mod_cast hxL₁))
      · have hI := Int.card_Icc_of_le (a := (0 : ℤ)) (b := L₁) (by omega)
        omega
    · have hxL₂ : x < L₂ := Nat.lt_of_not_ge hL₂x
      apply mem_add_of_common_int_interval
          (lo := (x : ℤ) - L₂) (hi := L₁)
      · exact hcast₁.trans (Finset.Icc_subset_Icc (by omega) le_rfl)
      · exact href.trans (Finset.Icc_subset_Icc le_rfl (by exact_mod_cast hxL₁))
      · have hI := Int.card_Icc_of_le
            (a := (x : ℤ) - L₂) (b := L₁) (by omega)
        omega
  · have hL₁x : L₁ < x := Nat.lt_of_not_ge hxL₁
    by_cases hL₂x : L₂ ≤ x
    · apply mem_add_of_common_int_interval
          (lo := 0) (hi := x)
      · exact hcast₁.trans (Finset.Icc_subset_Icc le_rfl (by exact_mod_cast hL₁x.le))
      · exact href.trans (Finset.Icc_subset_Icc
          (sub_nonneg.mpr (Int.ofNat_le.mpr hL₂x)) le_rfl)
      · have hI := Int.card_Icc_of_le (a := (0 : ℤ)) (b := x) (by omega)
        omega
    · have hxL₂ : x < L₂ := Nat.lt_of_not_ge hL₂x
      apply mem_add_of_common_int_interval
          (lo := (x : ℤ) - L₂) (hi := x)
      · exact hcast₁.trans (Finset.Icc_subset_Icc (by omega) (by exact_mod_cast hL₁x.le))
      · exact href
      · have hI := Int.card_Icc_of_le
            (a := (x : ℤ) - L₂) (b := x) (by omega)
        omega

/-- Translated form of `lev_dense_two_sum_interval`.  Here the two input
intervals need not begin at zero.  The conclusion exhibits the standard
central interval, with `K = |S₁| + |S₂| - 2`, between
`b₁ + b₂ - K` and `a₁ + a₂ + K`. -/
theorem lev_dense_two_sum_interval_translated
    {S₁ S₂ : Finset ℕ} {a₁ b₁ a₂ b₂ : ℕ}
    (hne₁ : S₁.Nonempty) (hne₂ : S₂.Nonempty)
    (hS₁ : S₁ ⊆ Finset.Icc a₁ b₁)
    (hS₂ : S₂ ⊆ Finset.Icc a₂ b₂)
    (hdense : max (b₁ - a₁) (b₂ - a₂) ≤
      S₁.card + S₂.card - 2) :
    Finset.Icc
        (b₁ + b₂ - (S₁.card + S₂.card - 2))
        (a₁ + a₂ + (S₁.card + S₂.card - 2)) ⊆ S₁ + S₂ := by
  let K := S₁.card + S₂.card - 2
  have hcard₁ : 0 < S₁.card := Finset.card_pos.mpr hne₁
  have hcard₂ : 0 < S₂.card := Finset.card_pos.mpr hne₂
  have hK : K + 2 = S₁.card + S₂.card := by
    dsimp [K]
    omega
  obtain ⟨s₁, hs₁⟩ := hne₁
  obtain ⟨s₂, hs₂⟩ := hne₂
  have ha₁b₁ : a₁ ≤ b₁ :=
    (Finset.mem_Icc.mp (hS₁ hs₁)).1.trans
      (Finset.mem_Icc.mp (hS₁ hs₁)).2
  have ha₂b₂ : a₂ ≤ b₂ :=
    (Finset.mem_Icc.mp (hS₂ hs₂)).1.trans
      (Finset.mem_Icc.mp (hS₂ hs₂)).2
  have hdenseK : max (b₁ - a₁) (b₂ - a₂) ≤ K := by
    simpa only [K] using hdense
  have hD₁ : b₁ - a₁ ≤ K :=
    (le_max_left _ _).trans hdenseK
  have hD₂ : b₂ - a₂ ≤ K :=
    (le_max_right _ _).trans hdenseK
  have hcast₁ : intCastFinset S₁ ⊆ Finset.Icc (a₁ : ℤ) b₁ :=
    intCastFinset_subset_Icc hS₁
  intro x hx
  rw [Finset.mem_Icc] at hx
  have hxlow : b₁ + b₂ - K ≤ x := by simpa [K] using hx.1
  have hxhigh : x ≤ a₁ + a₂ + K := by simpa [K] using hx.2
  have hxlowZ : (b₁ : ℤ) + b₂ - K ≤ x := by omega
  have hxhighZ : (x : ℤ) ≤ a₁ + a₂ + K := by exact_mod_cast hxhigh
  have href : reflectedIntFinset x S₂ ⊆
      Finset.Icc ((x : ℤ) - b₂) ((x : ℤ) - a₂) :=
    reflectedIntFinset_subset_Icc_of_subset_Icc hS₂
  by_cases hupp : (x : ℤ) - a₂ ≤ b₁
  · by_cases hlow : (a₁ : ℤ) ≤ (x : ℤ) - b₂
    · apply mem_add_of_common_int_interval
          (lo := a₁) (hi := b₁) hcast₁
      · exact href.trans (Finset.Icc_subset_Icc hlow hupp)
      · have hI := Int.card_Icc_of_le
            (a := (a₁ : ℤ)) (b := b₁) (by omega)
        omega
    · have hlow' : (x : ℤ) - b₂ < a₁ := lt_of_not_ge hlow
      apply mem_add_of_common_int_interval
          (lo := (x : ℤ) - b₂) (hi := b₁)
      · exact hcast₁.trans (Finset.Icc_subset_Icc hlow'.le le_rfl)
      · exact href.trans (Finset.Icc_subset_Icc le_rfl hupp)
      · have hI := Int.card_Icc_of_le
            (a := (x : ℤ) - b₂) (b := b₁) (by omega)
        omega
  · have hupp' : (b₁ : ℤ) < (x : ℤ) - a₂ := lt_of_not_ge hupp
    by_cases hlow : (a₁ : ℤ) ≤ (x : ℤ) - b₂
    · apply mem_add_of_common_int_interval
          (lo := a₁) (hi := (x : ℤ) - a₂)
      · exact hcast₁.trans (Finset.Icc_subset_Icc le_rfl hupp'.le)
      · exact href.trans (Finset.Icc_subset_Icc hlow le_rfl)
      · have hI := Int.card_Icc_of_le
            (a := (a₁ : ℤ)) (b := (x : ℤ) - a₂) (by omega)
        omega
    · have hlow' : (x : ℤ) - b₂ < a₁ := lt_of_not_ge hlow
      apply mem_add_of_common_int_interval
          (lo := (x : ℤ) - b₂) (hi := (x : ℤ) - a₂)
      · exact hcast₁.trans (Finset.Icc_subset_Icc hlow'.le hupp'.le)
      · exact href
      · have hI := Int.card_Icc_of_le
            (a := (x : ℤ) - b₂) (b := (x : ℤ) - a₂) (by omega)
        omega

/-- Two-member specialization in the exact interface of `IsCFPLevFamily`.
The extra room inequality is the quantitative condition that makes the
central interval long enough for `HasCFPLevInterval`. -/
theorem hasCFPLevInterval_pair_of_room
    {P Q : Finset ℕ} {n₀ q : ℕ}
    (hfamily : IsCFPLevFamily [P, Q] 2 n₀ q)
    (hroom : q + (n₀ - 1) ≤
      P.subsetSum.card + Q.subsetSum.card - 2) :
    HasCFPLevInterval [P, Q] 2 n₀ := by
  obtain ⟨_hlen, _hpair, hord⟩ := hfamily
  have hP := hord P (by simp)
  have hQ := hord Q (by simp)
  let K := P.subsetSum.card + Q.subsetSum.card - 2
  have hPK : P.subsetSum.card ≤ q + 1 := by
    calc
      P.subsetSum.card ≤ (Finset.Icc 0 q).card :=
        Finset.card_le_card hP.2.1
      _ = q + 1 := by simp
  have hq_n₀ : n₀ - 1 ≤ q := by omega
  have hqK : q ≤ K := by simpa [K] using hroom.trans' (Nat.le_add_right q (n₀ - 1))
  have hcentral := lev_dense_two_sum_interval
    (S₁ := P.subsetSum) (S₂ := Q.subsetSum) (L₁ := q) (L₂ := q)
    ⟨0, by simp⟩ ⟨0, by simp⟩ hP.2.1 hQ.2.1 (by
      simpa [K] using hqK)
  have hQzero : Q.subsetSum + ({0} : Finset ℕ) = Q.subsetSum := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_add] at hy
      obtain ⟨u, hu, v, hv, rfl⟩ := hy
      simp only [Finset.mem_singleton] at hv
      subst v
      simpa using hu
    · intro hy
      rw [Finset.mem_add]
      exact ⟨y, hy, 0, by simp, by simp⟩
  refine ⟨2 * q - K, K, ?_, ?_, ?_⟩
  · omega
  · simpa [levIteratedSubsetSum, K, hQzero, two_mul] using hcentral
  · dsimp [K] at hroom ⊢
    omega

end Erdos360
