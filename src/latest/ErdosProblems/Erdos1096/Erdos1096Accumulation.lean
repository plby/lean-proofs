import ErdosProblems.Erdos1096.Erdos1096UnitCircle

open Filter Set Polynomial
open scoped BigOperators Pointwise Topology ComplexConjugate

noncomputable section

namespace Erdos1096

lemma signedSpectrum_mem_as_spectrum_difference {q y : ℝ}
    (hy : y ∈ SignedSpectrum q) :
    ∃ a ∈ Spectrum q, ∃ b ∈ Spectrum q, y = a - b := by
  rcases hy with ⟨p, hp, rfl⟩
  let A : Finset ℕ := p.support.filter fun i ↦ p.coeff i = 1
  let B : Finset ℕ := p.support.filter fun i ↦ p.coeff i = -1
  have hcases (i : ℕ) : p.coeff i = -1 ∨ p.coeff i = 0 ∨ p.coeff i = 1 := by
    have hi := abs_le.mp (hp i)
    omega
  have hpoly : p = (∑ i ∈ A, X ^ i) - ∑ i ∈ B, X ^ i := by
    ext i
    rcases hcases i with hi | hi | hi
    · simp [A, B, Polynomial.coeff_X_pow, hi]
    · have hisupp : i ∉ p.support := by simp [Polynomial.mem_support_iff, hi]
      simp [A, B, Polynomial.coeff_X_pow, hi, hisupp]
    · simp [A, B, Polynomial.coeff_X_pow, hi]
  refine ⟨∑ i ∈ A, q ^ i, ⟨A, rfl⟩,
    ∑ i ∈ B, q ^ i, ⟨B, rfl⟩, ?_⟩
  rw [hpoly, Polynomial.eval₂_sub, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_finsetSum]
  simp

private def residueZeroSupport3 (S : Finset ℕ) : Finset ℕ :=
  S.image (fun i ↦ 3 * i)

private def residueOneSupport3 (S : Finset ℕ) : Finset ℕ :=
  S.image (fun i ↦ 3 * i + 1)

private lemma residueZeroSupport3_disjoint_residueOneSupport3 (S T : Finset ℕ) :
    Disjoint (residueZeroSupport3 S) (residueOneSupport3 T) := by
  rw [Finset.disjoint_left]
  intro k hkS hkT
  rcases Finset.mem_image.mp hkS with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hkT with ⟨j, hj, h⟩
  omega

private lemma sum_residueZeroSupport3 (q : ℝ) (S : Finset ℕ) :
    (∑ k ∈ residueZeroSupport3 S, q ^ k) = ∑ i ∈ S, (q ^ 3) ^ i := by
  rw [residueZeroSupport3, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [pow_mul]
  · intro i hi j hj hij
    change 3 * i = 3 * j at hij
    omega

private lemma sum_residueOneSupport3 (q : ℝ) (S : Finset ℕ) :
    (∑ k ∈ residueOneSupport3 S, q ^ k) = q * ∑ i ∈ S, (q ^ 3) ^ i := by
  rw [residueOneSupport3, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ, pow_mul]
    ring
  · intro i hi j hj hij
    change 3 * i + 1 = 3 * j + 1 at hij
    omega

lemma add_scaleSet_cube_subset_spectrum (q : ℝ) :
    ∀ u ∈ Spectrum (q ^ 3), ∀ v ∈ scaleSet q (Spectrum (q ^ 3)),
      u + v ∈ Spectrum q := by
  intro u hu v hv
  rcases hu with ⟨S, rfl⟩
  rcases hv with ⟨a, ⟨T, rfl⟩, rfl⟩
  refine ⟨residueZeroSupport3 S ∪ residueOneSupport3 T, ?_⟩
  rw [Finset.sum_union (residueZeroSupport3_disjoint_residueOneSupport3 S T)]
  rw [sum_residueZeroSupport3, sum_residueOneSupport3]

private lemma abs_sub_lt_of_floor_eq {x y L ε : ℝ} (hε : 0 < ε)
    (hx : 0 ≤ x - L) (hy : 0 ≤ y - L)
    (hfloor : ⌊(x - L) / ε⌋₊ = ⌊(y - L) / ε⌋₊) :
    |x - y| < ε := by
  let k : ℕ := ⌊(x - L) / ε⌋₊
  have hxlo : (k : ℝ) ≤ (x - L) / ε := by
    exact Nat.floor_le (div_nonneg hx hε.le)
  have hxhi : (x - L) / ε < (k : ℝ) + 1 := by
    exact Nat.lt_floor_add_one ((x - L) / ε)
  have hylo : (k : ℝ) ≤ (y - L) / ε := by
    rw [show k = ⌊(y - L) / ε⌋₊ by exact hfloor]
    exact Nat.floor_le (div_nonneg hy hε.le)
  have hyhi : (y - L) / ε < (k : ℝ) + 1 := by
    rw [show k = ⌊(y - L) / ε⌋₊ by exact hfloor]
    exact Nat.lt_floor_add_one ((y - L) / ε)
  rw [abs_lt]
  constructor
  · have haux : (y - L) / ε - (x - L) / ε < 1 := by linarith
    have hdiv : (y - x) / ε < 1 := by
      convert haux using 1
      all_goals ring
    have := (div_lt_iff₀ hε).mp hdiv
    linarith
  · have haux : (x - L) / ε - (y - L) / ε < 1 := by linarith
    have hdiv : (x - y) / ε < 1 := by
      convert haux using 1
      all_goals ring
    simpa using (div_lt_iff₀ hε).mp hdiv

/-- Akiyama--Komornik's finite sumset pigeonhole lemma in the special form
needed here.  An accumulation point of the signed spectrum in base `q³`
produces arbitrarily close distinct binary spectrum values in base `q`. -/
lemma smallSpectrumDifferences_of_cube_accumulation {q : ℝ}
    (hq1 : 1 < q) (hqcube2 : q ^ 3 ≤ 2)
    (hacc : HasAccumulation (SignedSpectrum (q ^ 3))) :
    SmallSpectrumDifferences q := by
  classical
  intro ε hε
  rcases hacc with ⟨c, hc⟩
  have hlocalAcc : AccPt c
      (Filter.principal (Metric.ball c 1 ∩ SignedSpectrum (q ^ 3))) :=
    hc.nhds_inter (Metric.ball_mem_nhds c zero_lt_one)
  have hlocalInf : (Metric.ball c 1 ∩ SignedSpectrum (q ^ 3)).Infinite :=
    Set.Infinite.of_accPt hlocalAcc
  have hq0 : 0 < q := by linarith
  have hcube1 : 1 < q ^ 3 := one_lt_pow₀ hq1 (by omega)
  obtain ⟨C, hC⟩ :=
    scaleSet_spectrum_eventuallyLeftDense hq0 hcube1 hqcube2
  let R : ℝ := q + |c| + 2
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 2 * R / ε < K := exists_nat_gt (2 * R / ε)
  have hKpos : 0 < K := by
    have hquot : 0 < 2 * R / ε := by positivity
    exact_mod_cast (lt_trans hquot hK)
  obtain ⟨Dset, hDsub, hDcard⟩ :=
    hlocalInf.exists_subset_card_eq (K * K + 1)
  let D := {d : ℝ // d ∈ Dset}
  have hrep (d : D) :
      ∃ ab : ℝ × ℝ, ab.1 ∈ Spectrum (q ^ 3) ∧
        ab.2 ∈ Spectrum (q ^ 3) ∧ (d : ℝ) = ab.1 - ab.2 := by
    obtain ⟨a, ha, b, hb, hd⟩ :=
      signedSpectrum_mem_as_spectrum_difference
        (show (d : ℝ) ∈ SignedSpectrum (q ^ 3) from (hDsub d.property).2)
    exact ⟨(a, b), ha, hb, hd⟩
  let rep : D → ℝ × ℝ := fun d ↦ Classical.choose (hrep d)
  have hrepSpec (d : D) :
      (rep d).1 ∈ Spectrum (q ^ 3) ∧
        (rep d).2 ∈ Spectrum (q ^ 3) ∧ (d : ℝ) = (rep d).1 - (rep d).2 :=
    Classical.choose_spec (hrep d)
  let a : D → ℝ := fun d ↦ (rep d).1
  let b : D → ℝ := fun d ↦ (rep d).2
  have ha (d : D) : a d ∈ Spectrum (q ^ 3) := (hrepSpec d).1
  have hb (d : D) : b d ∈ Spectrum (q ^ 3) := (hrepSpec d).2.1
  have hdab (d : D) : (d : ℝ) = a d - b d := (hrepSpec d).2.2
  let T : ℝ := C + ∑ d : D, |b d| + 1
  have htarget (d : D) : C ≤ T - b d := by
    have hbabs : b d ≤ |b d| := le_abs_self (b d)
    have habssum : |b d| ≤ ∑ e : D, |b e| := by
      exact Finset.single_le_sum (fun e _ ↦ abs_nonneg (b e)) (Finset.mem_univ d)
    dsimp [T]
    linarith
  have hvExists (d : D) : ∃ v ∈ scaleSet q (Spectrum (q ^ 3)),
      (T - b d) - q < v ∧ v ≤ T - b d :=
    hC (T - b d) (htarget d)
  let v : D → ℝ := fun d ↦ Classical.choose (hvExists d)
  have hvSpec (d : D) : v d ∈ scaleSet q (Spectrum (q ^ 3)) ∧
      (T - b d) - q < v d ∧ v d ≤ T - b d :=
    Classical.choose_spec (hvExists d)
  let A : D → ℝ := fun d ↦ a d + v d
  let B : D → ℝ := fun d ↦ b d + v d
  have hAZ (d : D) : A d ∈ Spectrum q :=
    add_scaleSet_cube_subset_spectrum q (a d) (ha d) (v d) (hvSpec d).1
  have hBZ (d : D) : B d ∈ Spectrum q :=
    add_scaleSet_cube_subset_spectrum q (b d) (hb d) (v d) (hvSpec d).1
  have hAdiffB (d : D) : A d - B d = (d : ℝ) := by
    dsimp [A, B]
    linarith [hdab d]
  have hdBound (d : D) : |(d : ℝ)| < |c| + 1 := by
    have hball : dist (d : ℝ) c < 1 := Metric.mem_ball.mp (hDsub d.property).1
    rw [Real.dist_eq] at hball
    calc
      |(d : ℝ)| = |((d : ℝ) - c) + c| := by ring_nf
      _ ≤ |(d : ℝ) - c| + |c| := abs_add_le _ _
      _ < |c| + 1 := by linarith
  have hBbounds (d : D) : T - R ≤ B d ∧ B d ≤ T + R := by
    have hlo := (hvSpec d).2.1
    have hhi := (hvSpec d).2.2
    dsimp [B, R]
    constructor <;> linarith [abs_nonneg c]
  have hAbounds (d : D) : T - R ≤ A d ∧ A d ≤ T + R := by
    have hBlo : T - q < B d := by
      have hlo := (hvSpec d).2.1
      dsimp [B]
      linarith
    have hBhi : B d ≤ T := by
      have hhi := (hvSpec d).2.2
      dsimp [B]
      linarith
    have hd := hdBound d
    rw [abs_lt] at hd
    have hrel := hAdiffB d
    dsimp [R]
    constructor <;> linarith
  let bin : ℝ → ℕ := fun x ↦ ⌊(x - (T - R)) / ε⌋₊
  have hbinRange {x : ℝ} (hx : T - R ≤ x ∧ x ≤ T + R) : bin x < K := by
    have hx0 : 0 ≤ x - (T - R) := by linarith
    apply (Nat.floor_lt (div_nonneg hx0 hε.le)).mpr
    calc
      (x - (T - R)) / ε ≤ (2 * R) / ε := by
        apply div_le_div_of_nonneg_right _ hε.le
        linarith
      _ < K := hK
  let code : D → Fin K × Fin K := fun d ↦
    (⟨bin (A d), hbinRange (hAbounds d)⟩,
      ⟨bin (B d), hbinRange (hBbounds d)⟩)
  have hcard : Fintype.card (Fin K × Fin K) < Fintype.card D := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [show Fintype.card D = Dset.card by simp [D], hDcard]
    omega
  obtain ⟨d, e, hde, hcode⟩ := Fintype.exists_ne_map_eq_of_card_lt code hcard
  have hfloorA : bin (A d) = bin (A e) :=
    congrArg (fun z : Fin K × Fin K ↦ z.1.1) hcode
  have hfloorB : bin (B d) = bin (B e) :=
    congrArg (fun z : Fin K × Fin K ↦ z.2.1) hcode
  have hcloseA : |A d - A e| < ε :=
    abs_sub_lt_of_floor_eq hε (by linarith [hAbounds d])
      (by linarith [hAbounds e]) hfloorA
  have hcloseB : |B d - B e| < ε :=
    abs_sub_lt_of_floor_eq hε (by linarith [hBbounds d])
      (by linarith [hBbounds e]) hfloorB
  have hdistinct : A d ≠ A e ∨ B d ≠ B e := by
    by_contra hnot
    push Not at hnot
    apply hde
    apply Subtype.ext
    have hdrel := hAdiffB d
    have herel := hAdiffB e
    linarith
  rcases hdistinct with hAne | hBne
  · rcases hAZ d with ⟨Sd, hSd⟩
    rcases hAZ e with ⟨Se, hSe⟩
    refine ⟨Se, Sd, ?_, ?_⟩
    · simpa [hSd, hSe] using abs_pos.mpr (sub_ne_zero.mpr hAne)
    · simpa [hSd, hSe] using hcloseA
  · rcases hBZ d with ⟨Sd, hSd⟩
    rcases hBZ e with ⟨Se, hSe⟩
    refine ⟨Se, Sd, ?_, ?_⟩
    · simpa [hSd, hSe] using abs_pos.mpr (sub_ne_zero.mpr hBne)
    · simpa [hSd, hSe] using hcloseB

/-- A rational interval on which the spectral small-difference input needed
by the even/odd bridge is now unconditional. -/
lemma smallSpectrumDifferences_below_one_hundred_one_hundredths {q : ℝ}
    (hq1 : 1 < q) (hqsmall : q < 101 / 100) :
    SmallSpectrumDifferences q := by
  have hq0 : 0 ≤ q := by linarith
  have hpow : q ^ 3 < (101 / 100 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hqsmall hq0 (by omega)
  have hcubeSmall : q ^ 3 < 11 / 10 := by
    calc
      q ^ 3 < (101 / 100 : ℝ) ^ 3 := hpow
      _ < 11 / 10 := by norm_num
  have hcubeTwo : q ^ 3 ≤ 2 := hcubeSmall.le.trans (by norm_num)
  exact smallSpectrumDifferences_of_cube_accumulation hq1 hcubeTwo
    (signedSpectrum_hasAccumulation_below_eleven_tenths
      (one_lt_pow₀ hq1 (by omega)) hcubeSmall)

end Erdos1096
