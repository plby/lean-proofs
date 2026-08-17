/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos305.Scale
import PrimeNumberTheoremAnd.Consequences

/-!
# Final two-block assembly for Erdős 305
-/

open Filter Real
open scoped Topology

namespace Erdos305.Assembly

noncomputable section

attribute [local instance] Classical.propDecidable

def dilate (c : ℕ) (E : Finset ℕ) : Finset ℕ :=
  E.image fun n ↦ c * n

lemma rec_sum_dilate {c : ℕ} (hc : 0 < c) (E : Finset ℕ) :
    UnitFractions.rec_sum (dilate c E) = UnitFractions.rec_sum E / c := by
  simp only [UnitFractions.rec_sum]
  rw [dilate, Finset.sum_image]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    field_simp
  · intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left (by omega) hxy

lemma zero_not_mem_dilate {c : ℕ} (hc : 0 < c) {E : Finset ℕ}
    (hE : 0 ∉ E) : 0 ∉ dilate c E := by
  simp [dilate, hc.ne', hE]

lemma mem_dilate_bound {c N : ℕ} {E : Finset ℕ}
    (hE : ∀ n ∈ E, n ≤ N) {m : ℕ} (hm : m ∈ dilate c E) :
    m ≤ c * N := by
  rw [dilate, Finset.mem_image] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  exact Nat.mul_le_mul_left c (hE n hn)

private lemma disjoint_dilate_of_prime
    {b p N : ℕ} {E F : Finset ℕ}
    (hp : Nat.Prime p) (hpb : ¬p ∣ b) (hNp : N < p)
    (hE0 : 0 ∉ E) (hE : ∀ n ∈ E, n ≤ N) :
    Disjoint (dilate b E) (dilate p F) := by
  rw [Finset.disjoint_left]
  intro m hmE hmF
  rw [dilate, Finset.mem_image] at hmE hmF
  obtain ⟨n, hnE, rfl⟩ := hmE
  obtain ⟨k, _, hkn⟩ := hmF
  have hpDvd : p ∣ b * n := ⟨k, by simpa [Nat.mul_comm] using hkn.symm⟩
  have hpn : p ∣ n := (hp.dvd_mul.mp hpDvd).resolve_left hpb
  have hnpos : 0 < n := Nat.pos_of_ne_zero (by
    intro hn
    subst n
    exact hE0 hnE)
  have hpLeN := Nat.le_of_dvd hnpos hpn
  have hnN := hE n hnE
  omega

private lemma disjoint_dilate_of_separation
    {b y N : ℕ} {E F : Finset ℕ}
    (hb : y * N < b) (hE0 : 0 ∉ E) (hF : ∀ n ∈ F, n ≤ N) :
    Disjoint (dilate b E) (dilate y F) := by
  rw [Finset.disjoint_left]
  intro m hmE hmF
  rw [dilate, Finset.mem_image] at hmE hmF
  obtain ⟨n, hnE, rfl⟩ := hmE
  obtain ⟨k, hkF, hkn⟩ := hmF
  have hnpos : 0 < n := Nat.pos_of_ne_zero (by
    intro hn
    subst n
    exact hE0 hnE)
  have hleft : b ≤ b * n := by nlinarith
  have hright : y * k ≤ y * N := Nat.mul_le_mul_left y (hF k hkF)
  omega

private lemma smooth_div_initialLcm {S s : ℕ}
    (_hS : 1 ≤ S) :
    UnitFractions.is_smooth (S : ℝ)
      (((s : ℚ) / Erdos285.PrimePowers.initialLcm S).den) := by
  let Q := Erdos285.PrimePowers.initialLcm S
  have hQ0 : Q ≠ 0 := by simp [Q, Erdos285.PrimePowers.initialLcm]
  have hdenZ : ((((s : ℚ) / Q).den : ℕ) : ℤ) ∣ (Q : ℤ) := by
    simpa [Rat.natCast_div_eq_divInt] using Rat.den_dvd (s : ℤ) (Q : ℤ)
  have hden : (((s : ℚ) / Q).den : ℕ) ∣ Q := by
    exact_mod_cast hdenZ
  intro q hqpp hqden
  have hqQ : q ∣ Q := hqden.trans hden
  exact_mod_cast Erdos285.Lemma16.isPrimePow_le_of_dvd_initialLcm hqpp hqQ

private lemma representation_of_le_one
    {N : ℕ}
    (hN : 1 ≤ N)
    (hrep : ∀ r : ℚ, (1 / 3 : ℝ) ≤ (r : ℝ) → (r : ℝ) < 1 →
      UnitFractions.is_smooth (Erdos285.proposition6MainCutoff N) r.den →
      ∃ E : Finset ℕ,
        UnitFractions.rec_sum E = r ∧ 0 ∉ E ∧ ∀ n ∈ E, n ≤ N)
    (r : ℚ) (hrLower : (1 / 3 : ℝ) ≤ (r : ℝ))
    (hrUpper : (r : ℝ) ≤ 1)
    (hrsmooth : UnitFractions.is_smooth
      (Erdos285.proposition6MainCutoff N) r.den) :
    ∃ E : Finset ℕ,
      UnitFractions.rec_sum E = r ∧ 0 ∉ E ∧ ∀ n ∈ E, n ≤ N := by
  rcases hrUpper.eq_or_lt with hr | hr
  · have hrQ : r = 1 := by exact_mod_cast hr
    subst r
    refine ⟨{1}, by simp [UnitFractions.rec_sum], by simp, ?_⟩
    intro n hn
    simp only [Finset.mem_singleton] at hn
    subst n
    exact hN
  · exact hrep r hrLower hr hrsmooth

private lemma exists_prime_not_dvd_in_third
    {Z z : ℝ} {b : ℕ}
    (hZ : ∀ t : ℝ, Z ≤ t →
      ∃ p : ℕ, Nat.Prime p ∧ t < p ∧ p < (1 + (1 / 4 : ℝ)) * t)
    (hb : 0 < b) (hzpos : 0 < z) (hzZ : Z ≤ z / 3)
    (hzsq : 6 * (b : ℝ) < z ^ 2) :
    ∃ p : ℕ, Nat.Prime p ∧ ¬p ∣ b ∧ z / 3 < p ∧ (p : ℝ) < z := by
  obtain ⟨p₁, hp₁, hp₁lo, hp₁hi⟩ := hZ (z / 3) hzZ
  obtain ⟨p₂, hp₂, hp₂lo, hp₂hi⟩ := hZ (z / 2) (by linarith)
  norm_num at hp₁hi hp₂hi
  have hp₁half : (p₁ : ℝ) < z / 2 := by linarith
  have hp₁z : (p₁ : ℝ) < z := by linarith
  have hp₂z : (p₂ : ℝ) < z := by linarith
  have hpne : p₁ ≠ p₂ := by
    intro h
    subst p₂
    linarith
  by_cases hp₁b : p₁ ∣ b
  · by_cases hp₂b : p₂ ∣ b
    · have hprodDvd : p₁ * p₂ ∣ b :=
        hp₁.dvd_mul_of_dvd_ne hpne hp₂ hp₁b hp₂b
      have hprodLe : p₁ * p₂ ≤ b := Nat.le_of_dvd hb hprodDvd
      have hprodLeR : (p₁ : ℝ) * p₂ ≤ b := by exact_mod_cast hprodLe
      have hp₁lo' : z / 3 < (p₁ : ℝ) := hp₁lo
      have hp₂lo' : z / 2 < (p₂ : ℝ) := hp₂lo
      have hp₁pos : 0 < (p₁ : ℝ) := by exact_mod_cast hp₁.pos
      have hp₂pos : 0 < (p₂ : ℝ) := by exact_mod_cast hp₂.pos
      nlinarith [mul_pos (sub_pos.mpr hp₁lo') (sub_pos.mpr hp₂lo')]
    · exact ⟨p₂, hp₂, hp₂b, by linarith, hp₂z⟩
  · exact ⟨p₁, hp₁, hp₁b, hp₁lo, hp₁z⟩

/-- Uniform finite-set form of the Liu--Sawhney/Yokota construction. -/
theorem eventually_uniform_expansion :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℕ, 1 ≤ a → a < b →
      ∃ E : Finset ℕ,
        UnitFractions.rec_sum E = (a : ℚ) / b ∧
        0 ∉ E ∧
        ∀ n ∈ E, n ≤ 4 * b * Scale.cutoff b := by
  have hrep := Scale.cutoff_tendsto_atTop.eventually
    SmoothInterval.eventually_smooth_target_representation
  have hprime := prime_between (ε := (1 / 4 : ℝ)) (by norm_num)
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp hprime
  let Aconst : ℝ := max 25 (6 * max Z 1)
  have hAconst : 0 < Aconst := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  filter_upwards [hrep, Scale.eventually_six_mul_lt_initialLcm,
    Scale.eventually_mul_cutoff_sq_lt Aconst hAconst,
    Scale.cutoff_tendsto_atTop.eventually (eventually_ge_atTop 1),
    Scale.mainCutoffNat_cutoff_tendsto_atTop.eventually (eventually_ge_atTop 1)]
      with b hrepB hQlarge hbScale hNpos hSpos
  intro a ha hab
  let N := Scale.cutoff b
  let S := Erdos285.mainCutoffNat N
  let Q := Erdos285.PrimePowers.initialLcm S
  let u := a * Q - Q / 2
  let x := u / b
  let s := a * Q - x * b
  have hbpos : 0 < b := lt_of_lt_of_le Nat.zero_lt_one ha |>.trans hab
  have hQ : 6 * b < Q := by simpa [Q, S, N] using hQlarge
  have hQpos : 0 < Q := lt_trans (Nat.mul_pos (by norm_num) hbpos) hQ
  have hhalfQ : Q / 2 ≤ a * Q := by
    exact (Nat.div_le_self Q 2).trans (Nat.le_mul_of_pos_left Q ha)
  have huEq : u = a * Q - Q / 2 := rfl
  have hxMulLe : x * b ≤ u := by
    exact Nat.div_mul_le_self u b
  have huLt : u < x * b + b := by
    simpa [Nat.mul_comm] using Nat.lt_div_mul_add (a := u) (b := b) hbpos
  have hQhalfGtB : b < Q / 2 := by omega
  have hupos : 0 < u := by
    rw [huEq, Nat.sub_pos_iff_lt]
    exact (Nat.div_lt_self hQpos (by norm_num)).trans_le
      (Nat.le_mul_of_pos_left Q ha)
  have hbLeU : b ≤ u := by
    rw [huEq]
    apply Nat.le_sub_of_add_le
    have hbHalfLeQ : b + Q / 2 ≤ Q := by omega
    exact hbHalfLeQ.trans (Nat.le_mul_of_pos_left Q ha)
  have hxpos : 0 < x := (Nat.le_div_iff_mul_le hbpos).2 (by simpa using hbLeU)
  have hxQ : x < Q := by
    have hxb : x * b < Q * b := by
      calc
        x * b ≤ u := hxMulLe
        _ ≤ a * Q := Nat.sub_le _ _
        _ < b * Q := Nat.mul_lt_mul_of_pos_right hab hQpos
        _ = Q * b := Nat.mul_comm _ _
    exact (Nat.mul_lt_mul_right hbpos).mp (by simpa [Nat.mul_comm] using hxb)
  have hsEq : s + x * b = a * Q := by
    dsimp [s]
    omega
  have hsLowerNat : Q / 2 ≤ s := by
    rw [huEq] at hxMulLe
    omega
  have hsUpperNat : 3 * s < 2 * Q := by
    rw [huEq] at huLt
    omega
  have hSsmooth : UnitFractions.is_smooth
      (Erdos285.proposition6MainCutoff N) (((s : ℚ) / Q).den) := by
    have hsmoothNat := smooth_div_initialLcm (S := S) (s := s) hSpos
    intro q hq hqd
    exact (hsmoothNat q hq hqd).trans (Nat.floor_le
      (Erdos285.proposition6MainCutoff_nonneg N))
  have hr1Lower : (1 / 3 : ℝ) ≤ (((s : ℚ) / Q : ℚ) : ℝ) := by
    push_cast
    rw [le_div_iff₀ (by exact_mod_cast hQpos)]
    have hsThird : (Q : ℝ) ≤ 3 * (s : ℝ) := by
      exact_mod_cast (by omega : Q ≤ 3 * s)
    linarith
  have hr1Upper : ((((s : ℚ) / Q : ℚ) : ℝ)) < 1 := by
    push_cast
    rw [div_lt_one (by exact_mod_cast hQpos)]
    exact_mod_cast (by omega : s < Q)
  obtain ⟨EA, hEAsum, hEA0, hEAbound⟩ :=
    hrepB ((s : ℚ) / Q) hr1Lower hr1Upper hSsmooth
  have hbScaleN : Aconst * (N : ℝ) ^ 2 < b := by
    simpa [N] using hbScale
  have hxbLtAQ : x * b < a * Q := by
    calc
      x * b ≤ u := hxMulLe
      _ < a * Q := by
        rw [huEq, Nat.sub_lt_iff_lt_add hhalfQ]
        omega
  have hQlt3xb : Q < 3 * (x * b) := by
    have hQleAQ : Q ≤ a * Q := Nat.le_mul_of_pos_left Q ha
    omega
  obtain ⟨y, hypos, hyLower, hyUpper, hyB,
      hyDisj : (Nat.Prime y ∧ ¬y ∣ b ∧ N < y) ∨ y * N < b⟩ :
      ∃ y : ℕ, 0 < y ∧ Q ≤ 3 * (y * x) ∧ y * x ≤ Q ∧ y ≤ 3 * b ∧
        ((Nat.Prime y ∧ ¬y ∣ b ∧ N < y) ∨ y * N < b) := by
    by_cases haSmall : a ≤ 2 * N
    · let z : ℝ := (Q : ℝ) / x
      have hxposR : (0 : ℝ) < x := by exact_mod_cast hxpos
      have hQposR : (0 : ℝ) < Q := by exact_mod_cast hQpos
      have hzpos : 0 < z := div_pos hQposR hxposR
      have hbaLtZ : (b : ℝ) / a < z := by
        dsimp [z]
        rw [div_lt_div_iff₀ (by exact_mod_cast ha) hxposR]
        exact_mod_cast (by simpa [Nat.mul_comm] using hxbLtAQ)
      let M : ℝ := max Z 1
      have hM : 1 ≤ M := le_max_right _ _
      have hNposR : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
      have haSmallR : (a : ℝ) ≤ 2 * N := by exact_mod_cast haSmall
      have haPosR : (0 : ℝ) < a := by exact_mod_cast ha
      have hA25 : (25 : ℝ) ≤ Aconst := le_max_left _ _
      have hAM : 6 * M ≤ Aconst := by
        dsimp [M, Aconst]
        exact le_max_right _ _
      have hb25 : 25 * (N : ℝ) ^ 2 < b :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hA25 (sq_nonneg (N : ℝ))) hbScaleN
      have hb6M : 6 * M * (N : ℝ) ^ 2 < b :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hAM (sq_nonneg (N : ℝ))) hbScaleN
      have h3Ma : 3 * M * (a : ℝ) < b := by
        have hmulA : 0 ≤ 3 * M * (2 * N - a) :=
          mul_nonneg (by positivity) (sub_nonneg.mpr haSmallR)
        have hmulN : 0 ≤ 6 * M * N * (N - 1) :=
          mul_nonneg (by positivity) (sub_nonneg.mpr hNposR)
        nlinarith only [hmulA, hmulN, hb6M]
      have h3Na : 3 * (N : ℝ) * (a : ℝ) < b := by
        have hmulA : 0 ≤ (3 : ℝ) * (N : ℝ) * (2 * (N : ℝ) - (a : ℝ)) :=
          mul_nonneg (by positivity) (sub_nonneg.mpr haSmallR)
        nlinarith only [hmulA, hb25, sq_nonneg (N : ℝ)]
      have h6a : 6 * (a : ℝ) ^ 2 < b := by
        have hsq : 0 ≤ (2 * (N : ℝ) - (a : ℝ)) *
            (2 * (N : ℝ) + (a : ℝ)) :=
          mul_nonneg (sub_nonneg.mpr haSmallR) (by positivity)
        nlinarith only [hsq, hb25]
      have h3Mba : 3 * M < (b : ℝ) / a :=
        (lt_div_iff₀ haPosR).2 (by simpa [mul_assoc] using h3Ma)
      have h3Nba : 3 * (N : ℝ) < (b : ℝ) / a :=
        (lt_div_iff₀ haPosR).2 (by simpa [mul_assoc] using h3Na)
      have hzZ : Z ≤ z / 3 := by
        have hZM : Z ≤ M := by exact le_max_left _ _
        linarith
      have hz3N : 3 * (N : ℝ) < z := h3Nba.trans hbaLtZ
      have hsqBA : 6 * (b : ℝ) < ((b : ℝ) / a) ^ 2 := by
        rw [div_pow, lt_div_iff₀ (sq_pos_of_pos haPosR)]
        nlinarith
      have hzsq : 6 * (b : ℝ) < z ^ 2 := by
        have hbaPos : 0 < (b : ℝ) / a := div_pos (by exact_mod_cast hbpos) haPosR
        nlinarith [mul_pos (sub_pos.mpr hbaLtZ) (add_pos_of_pos_of_nonneg hbaPos hzpos.le)]
      obtain ⟨p, hp, hpb, hplo, hpz⟩ :=
        exists_prime_not_dvd_in_third hZ hbpos hzpos hzZ hzsq
      have hNp : N < p := by
        exact_mod_cast (show (N : ℝ) < p by linarith)
      have hzMul : z * (x : ℝ) = Q := by
        dsimp [z]
        field_simp
      have hQlowerR : (Q : ℝ) < 3 * ((p : ℝ) * x) := by
        nlinarith [mul_pos (sub_pos.mpr hplo) hxposR]
      have hpUpperR : (p : ℝ) * x < Q := by
        nlinarith [mul_pos (sub_pos.mpr hpz) hxposR]
      have hQlower : Q ≤ 3 * (p * x) := by exact_mod_cast hQlowerR.le
      have hpUpper : p * x ≤ Q := by exact_mod_cast hpUpperR.le
      have hpB : p ≤ 3 * b := by
        have : p * x < 3 * b * x := by
          calc
            p * x < Q := by exact_mod_cast hpUpperR
            _ < 3 * (x * b) := hQlt3xb
            _ = 3 * b * x := by ring
        exact (Nat.mul_lt_mul_right hxpos).mp (by simpa [Nat.mul_comm] using this) |>.le
      exact ⟨p, hp.pos, hQlower, hpUpper, hpB, Or.inl ⟨hp, hpb, hNp⟩⟩
    · have haLarge : 2 * N < a := lt_of_not_ge haSmall
      let y := Q / x
      have hypos : 0 < y :=
        (Nat.le_div_iff_mul_le hxpos).2 (by simpa using hxQ.le)
      have hyUpper : y * x ≤ Q := Nat.div_mul_le_self Q x
      have hQlt : Q < y * x + x := by
        simpa [y, Nat.mul_comm] using Nat.lt_div_mul_add (a := Q) (b := x) hxpos
      have hxLe : x ≤ y * x := by
        simpa using Nat.mul_le_mul_right x (show 1 ≤ y by omega)
      have hyLower : Q ≤ 3 * (y * x) := by omega
      have hyB : y ≤ 3 * b := by
        have : y * x < 3 * b * x := by
          calc
            y * x ≤ Q := hyUpper
            _ < 3 * (x * b) := hQlt3xb
            _ = 3 * b * x := by ring
        exact (Nat.mul_lt_mul_right hxpos).mp (by simpa [Nat.mul_comm] using this) |>.le
      have haDecomp : a * Q = (a - 1) * Q + Q := by
        calc
          a * Q = ((a - 1) + 1) * Q := by rw [Nat.sub_add_cancel ha]
          _ = (a - 1) * Q + Q := by ring
      have hAmulLt : (a - 1) * Q < x * b := by
        rw [huEq, haDecomp] at huLt
        omega
      have hySep : y * N < b := by
        have hyNx : (y * N) * x < b * x := by
          calc
            (y * N) * x = N * (y * x) := by ring
            _ ≤ N * Q := Nat.mul_le_mul_left N hyUpper
            _ ≤ (a - 1) * Q := Nat.mul_le_mul_right Q (by omega)
            _ < x * b := hAmulLt
            _ = b * x := Nat.mul_comm _ _
        exact (Nat.mul_lt_mul_right hxpos).mp hyNx
      exact ⟨y, hypos, hyLower, hyUpper, hyB, Or.inr hySep⟩
  have hYsmooth : UnitFractions.is_smooth
      (Erdos285.proposition6MainCutoff N) ((((y * x : ℕ) : ℚ) / Q).den) := by
    have hsmoothNat := smooth_div_initialLcm (S := S) (s := y * x) hSpos
    intro q hq hqd
    exact (hsmoothNat q hq hqd).trans (Nat.floor_le
      (Erdos285.proposition6MainCutoff_nonneg N))
  have hr2Lower : (1 / 3 : ℝ) ≤ (((((y * x : ℕ) : ℚ) / Q : ℚ) : ℝ)) := by
    push_cast
    rw [le_div_iff₀ (by exact_mod_cast hQpos)]
    have hLowerR : (Q : ℝ) ≤ 3 * ((y * x : ℕ) : ℝ) := by exact_mod_cast hyLower
    push_cast at hLowerR
    calc
      (1 / 3 : ℝ) * Q ≤ (1 / 3 : ℝ) * (3 * ((y : ℝ) * x)) :=
        mul_le_mul_of_nonneg_left hLowerR (by norm_num)
      _ = (y : ℝ) * x := by ring
  have hr2Upper : (((((y * x : ℕ) : ℚ) / Q : ℚ) : ℝ)) ≤ 1 := by
    push_cast
    rw [div_le_one (by exact_mod_cast hQpos)]
    exact_mod_cast hyUpper
  obtain ⟨EB, hEBsum, hEB0, hEBbound⟩ :=
    representation_of_le_one hNpos hrepB (((y * x : ℕ) : ℚ) / Q)
      hr2Lower hr2Upper hYsmooth
  have hdisj : Disjoint (dilate b EA) (dilate y EB) := by
    rcases hyDisj with ⟨hp, hpb, hNp⟩ | hySep
    · exact disjoint_dilate_of_prime hp hpb hNp hEA0 hEAbound
    · exact disjoint_dilate_of_separation hySep hEA0 hEBbound
  refine ⟨dilate b EA ∪ dilate y EB, ?_, ?_, ?_⟩
  · rw [UnitFractions.rec_sum_disjoint hdisj, rec_sum_dilate hbpos,
      rec_sum_dilate hypos, hEAsum, hEBsum]
    push_cast
    field_simp
    exact_mod_cast (by simpa [Nat.mul_comm] using hsEq)
  · simp only [Finset.mem_union, not_or]
    exact ⟨zero_not_mem_dilate hbpos hEA0, zero_not_mem_dilate hypos hEB0⟩
  · intro n hn
    simp only [Finset.mem_union] at hn
    rcases hn with hn | hn
    · have hn' := mem_dilate_bound hEAbound hn
      exact hn'.trans (Nat.mul_le_mul_right N (by omega : b ≤ 4 * b))
    · have hn' := mem_dilate_bound hEBbound hn
      have hy4b : y ≤ 4 * b := hyB.trans (by omega)
      exact hn'.trans (Nat.mul_le_mul_right N hy4b)

end

end Erdos305.Assembly
