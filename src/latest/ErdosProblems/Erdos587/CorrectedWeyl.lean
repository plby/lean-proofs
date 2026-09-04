import ErdosProblems.Erdos587.NVDevelopment
import ErdosProblems.Erdos439.PowerSums

open Filter MeasureTheory
open scoped Pointwise

namespace Erdos587

/-- A fixed subpower envelope for the divisor-count term introduced by the
composite-modulus repair.  The exponent `1/8` is far more than the final
argument needs, but is convenient and already available from the explicit
Erdos--Tenenbaum divisor estimate formalized in `Erdos439`. -/
theorem exists_card_divisors_le_eighth_rpow :
    ∃ Q₀ : ℕ, ∀ q : ℕ, Q₀ ≤ q →
      (q.divisors.card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ) := by
  obtain ⟨Q₀, hQ₀⟩ :=
    Erdos439.PowerDecay.exists_uniform_divisor_power_le_subpower 1 (by omega)
  refine ⟨max 1 Q₀, ?_⟩
  intro q hq
  have hq1 : 1 ≤ q := (le_max_left 1 Q₀).trans hq
  have hqQ₀ : Q₀ ≤ q := (le_max_right 1 Q₀).trans hq
  have hmem : q ∈ Finset.Icc 1 (q ^ 1) := by
    simpa using (show 1 ≤ q ∧ q ≤ q from ⟨hq1, le_rfl⟩)
  have h := hQ₀ q hqQ₀ q hmem
  simpa [Erdos439.PowerDecay.divisorSubpowerEnvelope] using h

lemma gcd_two_mul_le_two_mul_gcd (q m : ℕ) (hq : 0 < q) :
    q.gcd (2 * m) ≤ 2 * q.gcd m := by
  apply Nat.le_of_dvd
  · positivity
  exact (gcd_mul_dvd_mul_gcd q 2 m).trans
    (mul_dvd_mul_right (Nat.gcd_dvd_right q 2) (q.gcd m))

lemma sum_gcd_Icc_le_mul_card_divisors (q M : ℕ) (hq : 0 < q) :
    ∑ m ∈ Finset.Icc 1 M, q.gcd m ≤ M * q.divisors.card := by
  classical
  have hq0 : q ≠ 0 := hq.ne'
  have hmajor (m : ℕ) : q.gcd m ≤
      ∑ d ∈ q.divisors, if d ∣ m then d else 0 := by
    let g := q.gcd m
    have hgMem : g ∈ q.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q m, hq0⟩
    have hgDvd : g ∣ m := Nat.gcd_dvd_right q m
    have hsingle := Finset.single_le_sum
      (fun d hd ↦ by positivity : ∀ d ∈ q.divisors,
        0 ≤ (if d ∣ m then d else 0)) hgMem
    simpa only [g, if_pos hgDvd] using hsingle
  calc
    (∑ m ∈ Finset.Icc 1 M, q.gcd m) ≤
        ∑ m ∈ Finset.Icc 1 M,
          ∑ d ∈ q.divisors, if d ∣ m then d else 0 := by
      exact Finset.sum_le_sum fun m hm ↦ hmajor m
    _ = ∑ d ∈ q.divisors,
          d * ((Finset.Icc 1 M).filter fun m ↦ d ∣ m).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp [Nat.mul_comm]
    _ ≤ ∑ _d ∈ q.divisors, M := by
      apply Finset.sum_le_sum
      intro d hd
      have hcard : ((Finset.Icc 1 M).filter fun m => d ∣ m).card ≤ M / d := by
        have heq : (Finset.Icc 1 M).filter (fun m => d ∣ m) =
            (Finset.range (M + 1)).filter (fun m => m ≠ 0 ∧ d ∣ m) := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
          omega
        rw [heq, Nat.card_multiples']
      calc
        d * ((Finset.Icc 1 M).filter fun m ↦ d ∣ m).card ≤
            d * (M / d) := Nat.mul_le_mul_left d hcard
        _ ≤ M := Nat.mul_div_le M d
    _ = M * q.divisors.card := by
      simp [Nat.mul_comm]

lemma sum_gcd_two_mul_Icc_le (q M : ℕ) (hq : 0 < q) :
    ∑ m ∈ Finset.Icc 1 M, q.gcd (2 * m) ≤
      2 * M * q.divisors.card := by
  calc
    (∑ m ∈ Finset.Icc 1 M, q.gcd (2 * m)) ≤
        ∑ m ∈ Finset.Icc 1 M, 2 * q.gcd m := by
      exact Finset.sum_le_sum fun m hm ↦ gcd_two_mul_le_two_mul_gcd q m hq
    _ = 2 * (∑ m ∈ Finset.Icc 1 M, q.gcd m) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (M * q.divisors.card) :=
      Nat.mul_le_mul_left 2 (sum_gcd_Icc_le_mul_card_divisors q M hq)
    _ = 2 * M * q.divisors.card := by ring

lemma twistedResiduePairCount_zero_le_divisor_envelope
    {a q M N : ℕ} (haq : a.Coprime q) (hq : 0 < q) :
    (twistedResiduePairCount a q 0 M N : ℝ) ≤
      ((N : ℝ) / q) * (2 * M * q.divisors.card : ℕ) := by
  have hzero := twistedResiduePairCount_zero_le_gcd_sum
    (M := M) (N := N) haq hq
  have hzeroR : (twistedResiduePairCount a q 0 M N : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 M,
        ((N / (q / q.gcd (2 * m)) : ℕ) : ℝ) := by
    exact_mod_cast hzero
  calc
    (twistedResiduePairCount a q 0 M N : ℝ) ≤
        ∑ m ∈ Finset.Icc 1 M,
          ((N / (q / q.gcd (2 * m)) : ℕ) : ℝ) := hzeroR
    _ ≤ ∑ m ∈ Finset.Icc 1 M,
          ((N : ℝ) / q) * q.gcd (2 * m) := by
      apply Finset.sum_le_sum
      intro m hm
      let g := q.gcd (2 * m)
      let d := q / g
      have hg : 0 < g := Nat.gcd_pos_of_pos_left (2 * m) hq
      have hd : 0 < d := Nat.div_pos (Nat.gcd_le_left (2 * m) hq) hg
      have hqeq : d * g = q := Nat.div_mul_cancel (Nat.gcd_dvd_left q (2 * m))
      calc
        ((N / (q / q.gcd (2 * m)) : ℕ) : ℝ) = ((N / d : ℕ) : ℝ) := by rfl
        _ ≤ (N : ℝ) / d := Nat.cast_div_le
        _ = ((N : ℝ) / q) * g := by
          have hd0 : (d : ℝ) ≠ 0 := by positivity
          have hg0 : (g : ℝ) ≠ 0 := by positivity
          have hq0 : (q : ℝ) ≠ 0 := by positivity
          have hqeqR : (q : ℝ) = (d : ℝ) * g := by
            exact_mod_cast hqeq.symm
          rw [hqeqR]
          field_simp
        _ = ((N : ℝ) / q) * q.gcd (2 * m) := by rfl
    _ = ((N : ℝ) / q) *
          (∑ m ∈ Finset.Icc 1 M, q.gcd (2 * m)) := by
      push_cast
      rw [Finset.mul_sum]
    _ ≤ ((N : ℝ) / q) * (2 * M * q.divisors.card : ℕ) := by
      gcongr
      exact_mod_cast sum_gcd_two_mul_Icc_le q M hq

lemma complementary_twisted_residue
    (a q v : ℕ) (hq : 0 < q) (hpos : 0 < (a * v) % q) :
    ((q - a % q) * v) % q = q - (a * v) % q := by
  let : NeZero q := ⟨hq.ne'⟩
  have hamod : a % q ≤ q := (Nat.mod_lt a hq).le
  have hbar : ((q - a % q : ℕ) : ZMod q) = -(a : ZMod q) := by
    rw [Nat.cast_sub hamod, ZMod.natCast_self, ZMod.natCast_mod]
    simp
  have hrlt : (a * v) % q < q := Nat.mod_lt _ hq
  have hcast : ((((q - a % q) * v) % q : ℕ) : ZMod q) =
      ((q - (a * v) % q : ℕ) : ZMod q) := by
    rw [ZMod.natCast_mod]
    rw [Nat.cast_mul, hbar]
    rw [Nat.cast_sub hrlt.le, ZMod.natCast_self, ZMod.natCast_mod]
    rw [Nat.cast_mul]
    ring
  have hval := congrArg ZMod.val hcast
  simpa [ZMod.val_mul, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Nat.sub_lt hq hpos)] using hval

lemma complementary_numerator_coprime
    {a q : ℕ} (hq : 0 < q) (haq : a.Coprime q) :
    (q - a % q).Coprime q := by
  have hamod : a % q ≤ q := (Nat.mod_lt a hq).le
  rw [Nat.coprime_self_sub_left hamod]
  exact (ZMod.coprime_mod_iff_coprime a q).mpr haq

lemma complementary_twisted_residue_zero_of_zero
    (a q v : ℕ) (hq : 0 < q) (ha0 : (a * v) % q = 0) :
    ((q - a % q) * v) % q = 0 := by
  let : NeZero q := ⟨hq.ne'⟩
  have hamod : a % q ≤ q := (Nat.mod_lt a hq).le
  have hbar : ((q - a % q : ℕ) : ZMod q) = -(a : ZMod q) := by
    rw [Nat.cast_sub hamod, ZMod.natCast_self, ZMod.natCast_mod]
    simp
  have hprod : (((q - a % q) * v : ℕ) : ZMod q) =
      -((a * v : ℕ) : ZMod q) := by
    rw [Nat.cast_mul, hbar, Nat.cast_mul]
    ring
  have hacast : ((a * v : ℕ) : ZMod q) = 0 := by
    rw [← ZMod.natCast_mod]
    rw [ha0]
    simp
  have hbarcast : (((q - a % q) * v : ℕ) : ZMod q) = 0 := by
    rw [hprod, hacast]
    simp
  have hval := congrArg ZMod.val hbarcast
  simpa [ZMod.val_mul, ZMod.val_natCast] using hval

lemma complementary_twisted_residue_zero_iff
    (a q v : ℕ) (hq : 0 < q) :
    ((q - a % q) * v) % q = 0 ↔ (a * v) % q = 0 := by
  constructor
  · intro hbar0
    by_contra ha0
    have hapos : 0 < (a * v) % q := Nat.pos_of_ne_zero ha0
    have hcomp := complementary_twisted_residue a q v hq hapos
    have hrlt := Nat.mod_lt (a * v) hq
    omega
  · exact complementary_twisted_residue_zero_of_zero a q v hq

lemma complementary_twisted_residue_eq_iff
    (a q v r : ℕ) (hq : 0 < q) (hr : r ∈ Finset.Icc 1 (q - 1)) :
    ((q - a % q) * v) % q = r ↔ (a * v) % q = q - r := by
  have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
  have hrle : r ≤ q - 1 := (Finset.mem_Icc.mp hr).2
  have hrlt : r < q := by omega
  constructor
  · intro hbar
    have hapos : 0 < (a * v) % q := by
      by_contra hnot
      have ha0 : (a * v) % q = 0 := by omega
      have hbar0 := complementary_twisted_residue_zero_of_zero a q v hq ha0
      omega
    have hcomp := complementary_twisted_residue a q v hq hapos
    omega
  · intro ha
    have hapos : 0 < (a * v) % q := by omega
    rw [complementary_twisted_residue a q v hq hapos, ha]
    omega

lemma twistedResiduePairCount_complement
    (a q r M N : ℕ) (hq : 0 < q) (hr : r ∈ Finset.Icc 1 (q - 1)) :
    twistedResiduePairCount (q - a % q) q r M N =
      twistedResiduePairCount a q (q - r) M N := by
  unfold twistedResiduePairCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, (complementary_twisted_residue_eq_iff
      a q (2 * x.1 * x.2) r hq hr).mp h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, (complementary_twisted_residue_eq_iff
      a q (2 * x.1 * x.2) r hq hr).mpr h⟩

lemma twistedResiduePairCount_complement_zero
    (a q M N : ℕ) (hq : 0 < q) :
    twistedResiduePairCount (q - a % q) q 0 M N =
      twistedResiduePairCount a q 0 M N := by
  unfold twistedResiduePairCount
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, (complementary_twisted_residue_zero_iff
      a q (2 * x.1 * x.2) hq).mp h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, (complementary_twisted_residue_zero_iff
      a q (2 * x.1 * x.2) hq).mpr h⟩

noncomputable def twistedPairMajorant
    (a q L m h : ℕ) : ℝ :=
  let r := (a * (2 * m * h)) % q
  if r = 0 then L else (q : ℝ) / r

lemma rationalMajorant_le_twistedPairMajorants
    (a q L m h : ℕ) (hq : 0 < q) :
    Erdos438.QuadraticWeyl.rationalMajorant (a * m) q L h ≤
      twistedPairMajorant a q L m h +
        twistedPairMajorant (q - a % q) q L m h := by
  let r := (a * (2 * m * h)) % q
  have hrlt : r < q := Nat.mod_lt _ hq
  have hres : (2 * (a * m) * h) % q = r := by
    dsimp [r]
    congr 1
    ring
  by_cases hr0 : r = 0
  · have hdist0 : Erdos438.QuadraticWeyl.residueDistance (a * m) q h = 0 := by
      simp [Erdos438.QuadraticWeyl.residueDistance, hres, hr0]
    have hz : (a * (2 * m * h)) % q = 0 := by simpa [r] using hr0
    have hcomp0 := complementary_twisted_residue_zero_of_zero
      a q (2 * m * h) hq hz
    rw [Erdos438.QuadraticWeyl.rationalMajorant, if_pos hdist0]
    simp only [twistedPairMajorant, hz, hcomp0, if_pos]
    exact le_add_of_nonneg_right (Nat.cast_nonneg L)
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hz : (a * (2 * m * h)) % q ≠ 0 := by simpa [r] using hr0
    have hcomp := complementary_twisted_residue a q (2 * m * h) hq hrpos
    have hcompPos : 0 < ((q - a % q) * (2 * m * h)) % q := by
      rw [hcomp]
      omega
    have hdistNe : Erdos438.QuadraticWeyl.residueDistance (a * m) q h ≠ 0 := by
      simp only [Erdos438.QuadraticWeyl.residueDistance, hres]
      omega
    rw [Erdos438.QuadraticWeyl.rationalMajorant, if_neg hdistNe]
    simp only [twistedPairMajorant, hz, hcompPos.ne', if_false]
    rw [hcomp]
    simp only [Erdos438.QuadraticWeyl.residueDistance, hres]
    change (q : ℝ) / (min r (q - r) : ℕ) ≤
      (q : ℝ) / r + (q : ℝ) / (q - r : ℕ)
    by_cases hle : r ≤ q - r
    · rw [min_eq_left hle]
      have hnonneg : 0 ≤ (q : ℝ) / (q - r : ℕ) := by positivity
      linarith
    · rw [min_eq_right (Nat.le_of_not_ge hle)]
      have hnonneg : 0 ≤ (q : ℝ) / r := by positivity
      linarith

lemma sum_twistedPairMajorant_eq
    (a q L M N : ℕ) (hq : 0 < q) :
    (∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 N,
        twistedPairMajorant a q L m h) =
      (twistedResiduePairCount a q 0 M N : ℝ) * L +
        ∑ r ∈ Finset.Icc 1 (q - 1),
          (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r) := by
  classical
  let box := (Finset.Icc 1 M).product (Finset.Icc 1 N)
  let f : ℕ × ℕ → ℕ := fun x ↦ (a * (2 * x.1 * x.2)) % q
  have hmaps : (box : Set (ℕ × ℕ)).MapsTo f (Finset.range q) := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
  have hfiber :
      (∑ r ∈ Finset.range q,
          ∑ x ∈ box with f x = r,
            twistedPairMajorant a q L x.1 x.2) =
        ∑ x ∈ box, twistedPairMajorant a q L x.1 x.2 := by
    exact Finset.sum_fiberwise_of_maps_to hmaps _
  have hrange : Finset.range q = insert 0 (Finset.Icc 1 (q - 1)) := by
    ext r
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    constructor
    · intro hrq
      by_cases hr0 : r = 0
      · exact Or.inl hr0
      · right
        omega
    · rintro (rfl | ⟨hr1, hrq⟩)
      · exact hq
      · omega
  have hzero :
      (∑ x ∈ box with f x = 0,
          twistedPairMajorant a q L x.1 x.2) =
        (twistedResiduePairCount a q 0 M N : ℝ) * L := by
    calc
      (∑ x ∈ box with f x = 0,
          twistedPairMajorant a q L x.1 x.2) =
          ∑ _x ∈ box.filter (fun x ↦ f x = 0), (L : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx0 : f x = 0 := (Finset.mem_filter.mp hx).2
        simp only [twistedPairMajorant]
        rw [if_pos]
        simpa [f] using hx0
      _ = (twistedResiduePairCount a q 0 M N : ℝ) * L := by
        rw [Finset.sum_const]
        simp [box, f, twistedResiduePairCount]
  have hnonzero (r : ℕ) (hr : r ∈ Finset.Icc 1 (q - 1)) :
      (∑ x ∈ box with f x = r,
          twistedPairMajorant a q L x.1 x.2) =
        (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r) := by
    have hr0 : r ≠ 0 := (Nat.ne_of_gt (Finset.mem_Icc.mp hr).1)
    calc
      (∑ x ∈ box with f x = r,
          twistedPairMajorant a q L x.1 x.2) =
          ∑ _x ∈ box.filter (fun x ↦ f x = r), ((q : ℝ) / r) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxr : f x = r := (Finset.mem_filter.mp hx).2
        simp only [twistedPairMajorant]
        rw [if_neg]
        · have heq : (a * (2 * x.1 * x.2)) % q = r := by
            simpa [f] using hxr
          rw [heq]
        · simpa [f, hxr] using hr0
      _ = (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r) := by
        rw [Finset.sum_const]
        simp [box, f, twistedResiduePairCount]
  calc
    (∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 N,
        twistedPairMajorant a q L m h) =
        ∑ x ∈ box, twistedPairMajorant a q L x.1 x.2 := by
      simpa [box] using
        (Finset.sum_product (Finset.Icc 1 M) (Finset.Icc 1 N)
          (fun x ↦ twistedPairMajorant a q L x.1 x.2)).symm
    _ = ∑ r ∈ Finset.range q,
          ∑ x ∈ box with f x = r,
            twistedPairMajorant a q L x.1 x.2 := hfiber.symm
    _ = (∑ x ∈ box with f x = 0,
          twistedPairMajorant a q L x.1 x.2) +
        ∑ r ∈ Finset.Icc 1 (q - 1),
          ∑ x ∈ box with f x = r,
            twistedPairMajorant a q L x.1 x.2 := by
      rw [hrange, Finset.sum_insert]
      simp
    _ = _ := by
      rw [hzero]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      exact hnonzero r hr

lemma sum_rationalMajorant_mul_frequency_le
    (a q L M N : ℕ) (hq : 0 < q) :
    (∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 N,
        Erdos438.QuadraticWeyl.rationalMajorant (a * m) q L h) ≤
      2 * (twistedResiduePairCount a q 0 M N : ℝ) * L +
        (∑ r ∈ Finset.Icc 1 (q - 1),
          (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r)) +
        (∑ r ∈ Finset.Icc 1 (q - 1),
          (twistedResiduePairCount (q - a % q) q r M N : ℝ) *
            ((q : ℝ) / r)) := by
  calc
    (∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 N,
        Erdos438.QuadraticWeyl.rationalMajorant (a * m) q L h) ≤
        ∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 N,
          (twistedPairMajorant a q L m h +
            twistedPairMajorant (q - a % q) q L m h) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro h hh
      exact rationalMajorant_le_twistedPairMajorants a q L m h hq
    _ = (∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 N,
          twistedPairMajorant a q L m h) +
        (∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 N,
          twistedPairMajorant (q - a % q) q L m h) := by
      simp_rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_twistedPairMajorant_eq a q L M N hq,
        sum_twistedPairMajorant_eq (q - a % q) q L M N hq,
        twistedResiduePairCount_complement_zero a q M N hq]
      ring

lemma norm_quadraticSum_rational_mul_sq_le_majorants
    (a q L m : ℕ) (beta : ℝ) (hq : 0 < q) :
    ‖quadraticSum (((a * m : ℕ) : ℝ) / q) beta L‖ ^ 2 ≤
      L + 2 * ∑ h ∈ Finset.Icc 1 L,
        Erdos438.QuadraticWeyl.rationalMajorant (a * m) q L h := by
  calc
    ‖quadraticSum (((a * m : ℕ) : ℝ) / q) beta L‖ ^ 2 ≤
        L + 2 * ∑ h ∈ Finset.range L,
          Erdos438.QuadraticWeyl.correlationMajorant
            (((a * m : ℕ) : ℝ) / q) L (h + 1) :=
      Erdos438.QuadraticWeyl.norm_quadraticSum_sq_le _ _ _
    _ = L + 2 * ∑ h ∈ Finset.Icc 1 L,
          Erdos438.QuadraticWeyl.correlationMajorant
            (((a * m : ℕ) : ℝ) / q) L h := by
      rw [Erdos438.QuadraticWeyl.sum_range_correlationMajorant_succ]
    _ ≤ L + 2 * ∑ h ∈ Finset.Icc 1 L,
          Erdos438.QuadraticWeyl.rationalMajorant (a * m) q L h := by
      gcongr with h hh
      apply Erdos438.QuadraticWeyl.correlationMajorant_le_rationalMajorant
        ((((a * m : ℕ) : ℝ) / q)) (a * m) q (4 * L) L h hq
      · exact (Finset.mem_Icc.mp hh).1
      · exact (Finset.mem_Icc.mp hh).2
      · omega
      · simp only [Nat.cast_mul, sub_self, abs_zero, Nat.cast_ofNat, one_div, mul_inv_rev]
        positivity

lemma sum_norm_quadraticSum_rational_mul_sq_le
    (a q L M : ℕ) (beta : ℕ → ℝ) (hq : 0 < q) :
    ∑ m ∈ Finset.Icc 1 M,
        ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖ ^ 2 ≤
      (M : ℝ) * L +
        2 * ∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 L,
          Erdos438.QuadraticWeyl.rationalMajorant (a * m) q L h := by
  calc
    (∑ m ∈ Finset.Icc 1 M,
        ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖ ^ 2) ≤
        ∑ m ∈ Finset.Icc 1 M,
          ((L : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 L,
            Erdos438.QuadraticWeyl.rationalMajorant (a * m) q L h) := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_quadraticSum_rational_mul_sq_le_majorants
        a q L m (beta m) hq
    _ = (M : ℝ) * L +
        2 * ∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 L,
          Erdos438.QuadraticWeyl.rationalMajorant (a * m) q L h := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      simp

lemma sum_norm_quadraticSum_rational_mul_sq_le_residues
    (a q L M : ℕ) (beta : ℕ → ℝ) (hq : 0 < q) :
    ∑ m ∈ Finset.Icc 1 M,
        ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖ ^ 2 ≤
      (M : ℝ) * L +
        4 * (twistedResiduePairCount a q 0 M L : ℝ) * L +
        2 * (∑ r ∈ Finset.Icc 1 (q - 1),
          (twistedResiduePairCount a q r M L : ℝ) * ((q : ℝ) / r)) +
        2 * (∑ r ∈ Finset.Icc 1 (q - 1),
          (twistedResiduePairCount (q - a % q) q r M L : ℝ) *
            ((q : ℝ) / r)) := by
  calc
    (∑ m ∈ Finset.Icc 1 M,
        ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖ ^ 2) ≤
        (M : ℝ) * L +
          2 * ∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 L,
            Erdos438.QuadraticWeyl.rationalMajorant (a * m) q L h :=
      sum_norm_quadraticSum_rational_mul_sq_le a q L M beta hq
    _ ≤ _ := by
      have hres := sum_rationalMajorant_mul_frequency_le a q L M L hq
      nlinarith

/-- Corrected finite form of Nguyen--Vu Lemma 4.2.  The published zero
residue estimate is replaced by the explicit divisor envelope. -/
theorem exists_sum_norm_quadraticSum_rational_mul_sq_le_corrected :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ a q L M : ℕ, ∀ beta : ℕ → ℝ,
        let X := 2 * M * L
        let D := Nat.sqrt (Nat.sqrt X)
        a.Coprime q → 0 < q → 3 ≤ D → q - 1 ≤ X → q * D ≤ X →
        (∑ m ∈ Finset.Icc 1 M,
          ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖ ^ 2) ≤
          (M : ℝ) * L +
            8 * ((M : ℝ) * L ^ 2 * q.divisors.card / q) +
            4 * K * (X : ℝ) * Real.log (X : ℝ) ^ O := by
  obtain ⟨K, hK, O, hO, hweighted⟩ :=
    exists_weighted_twistedResiduePairCount_polylog_bound
  refine ⟨K, hK, O, hO, ?_⟩
  intro a q L M beta
  dsimp only
  let X := 2 * M * L
  let D := Nat.sqrt (Nat.sqrt X)
  intro haq hq hD hqX hqD
  have hcompCop := complementary_numerator_coprime hq haq
  have hzero := twistedResiduePairCount_zero_le_divisor_envelope
    (M := M) (N := L) haq hq
  have hnonzero := hweighted a q M L (q - 1) haq hq hD hqX hqD
  have hnonzeroComp := hweighted (q - a % q) q M L (q - 1)
    hcompCop hq hD hqX hqD
  have hraw := sum_norm_quadraticSum_rational_mul_sq_le_residues
    a q L M beta hq
  let Z : ℝ := (twistedResiduePairCount a q 0 M L : ℝ)
  let W : ℝ := ∑ r ∈ Finset.Icc 1 (q - 1),
    (twistedResiduePairCount a q r M L : ℝ) * ((q : ℝ) / r)
  let W' : ℝ := ∑ r ∈ Finset.Icc 1 (q - 1),
    (twistedResiduePairCount (q - a % q) q r M L : ℝ) * ((q : ℝ) / r)
  have hzero' : 4 * Z * L ≤
      8 * ((M : ℝ) * L ^ 2 * q.divisors.card / q) := by
    calc
      4 * Z * L ≤
          4 * (((L : ℝ) / q) * (2 * M * q.divisors.card : ℕ)) * L := by
        gcongr
      _ = 8 * ((M : ℝ) * L ^ 2 * q.divisors.card / q) := by
        push_cast
        ring
  have hW : W ≤ K * (X : ℝ) * Real.log (X : ℝ) ^ O := by
    simpa [W, X, D] using hnonzero
  have hW' : W' ≤ K * (X : ℝ) * Real.log (X : ℝ) ^ O := by
    simpa [W', X, D] using hnonzeroComp
  change
    (∑ m ∈ Finset.Icc 1 M,
      ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖ ^ 2) ≤ _
  change
    (∑ m ∈ Finset.Icc 1 M,
      ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖ ^ 2) ≤ _ at hraw
  change Z ≤ _ at hzero
  change _ ≤ (M : ℝ) * L + 4 * Z * L + 2 * W + 2 * W' at hraw
  nlinarith

theorem exists_sum_norm_quadraticSum_rational_mul_le_corrected :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ a q L M : ℕ, ∀ beta : ℕ → ℝ,
        let X := 2 * M * L
        let D := Nat.sqrt (Nat.sqrt X)
        a.Coprime q → 0 < q → 3 ≤ D → q - 1 ≤ X → q * D ≤ X →
        (∑ m ∈ Finset.Icc 1 M,
          ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖) ^ 2 ≤
          (M : ℝ) *
            ((M : ℝ) * L +
              8 * ((M : ℝ) * L ^ 2 * q.divisors.card / q) +
              4 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) := by
  obtain ⟨K, hK, O, hO, hsq⟩ :=
    exists_sum_norm_quadraticSum_rational_mul_sq_le_corrected
  refine ⟨K, hK, O, hO, ?_⟩
  intro a q L M beta
  dsimp only
  let X := 2 * M * L
  let D := Nat.sqrt (Nat.sqrt X)
  intro haq hq hD hqX hqD
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 M)
    (fun _m ↦ (1 : ℝ))
    (fun m ↦ ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖)
  have hsq' := hsq a q L M beta haq hq hD hqX hqD
  calc
    (∑ m ∈ Finset.Icc 1 M,
      ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖) ^ 2 ≤
        (M : ℝ) *
          (∑ m ∈ Finset.Icc 1 M,
            ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖ ^ 2) := by
      simpa using hcs
    _ ≤ (M : ℝ) *
        ((M : ℝ) * L +
          8 * ((M : ℝ) * L ^ 2 * q.divisors.card / q) +
          4 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) := by
      gcongr

/-- The corrected first-moment estimate in the exact strict form needed by
the low-frequency half of the Nguyen--Vu smoothing argument.  All
asymptotic work is isolated in the displayed numerical budget. -/
theorem exists_sum_norm_quadraticSum_rational_mul_lt_quarter_of_budget :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ a q L M : ℕ, ∀ beta : ℕ → ℝ,
        let X := 2 * M * L
        let D := Nat.sqrt (Nat.sqrt X)
        a.Coprime q → 0 < q → 0 < L →
        3 ≤ D → q - 1 ≤ X → q * D ≤ X →
        16 * (M : ℝ) *
            ((M : ℝ) * L +
              8 * ((M : ℝ) * L ^ 2 * q.divisors.card / q) +
              4 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) <
          (L : ℝ) ^ 2 →
        4 * (∑ m ∈ Finset.Icc 1 M,
          ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖) < L := by
  obtain ⟨K, hK, O, hO, hfirst⟩ :=
    exists_sum_norm_quadraticSum_rational_mul_le_corrected
  refine ⟨K, hK, O, hO, ?_⟩
  intro a q L M beta
  dsimp only
  let X := 2 * M * L
  let D := Nat.sqrt (Nat.sqrt X)
  intro haq hq hL hD hqX hqD hbudget
  let S : ℝ := ∑ m ∈ Finset.Icc 1 M,
    ‖quadraticSum (((a * m : ℕ) : ℝ) / q) (beta m) L‖
  have hS : 0 ≤ S := by
    dsimp only [S]
    positivity
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hfirst' := hfirst a q L M beta haq hq hD hqX hqD
  change S ^ 2 ≤ (M : ℝ) *
      ((M : ℝ) * L +
        8 * ((M : ℝ) * L ^ 2 * q.divisors.card / q) +
        4 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) at hfirst'
  change 16 * (M : ℝ) *
      ((M : ℝ) * L +
        8 * ((M : ℝ) * L ^ 2 * q.divisors.card / q) +
        4 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) <
      (L : ℝ) ^ 2 at hbudget
  change 4 * S < (L : ℝ)
  nlinarith [sq_nonneg (4 * S + (L : ℝ))]

/-- The corrected first-moment budget split into the three numerical
contributions that occur in the Nguyen--Vu application.  Keeping the
zero-residue term separate is essential: unlike the other two terms, it
cannot be hidden in a fixed logarithmic loss for arbitrary composite
moduli. -/
lemma corrected_weyl_budget_of_three_bounds
    {K : ℝ} {O q L M X : ℕ}
    (hmain : 48 * (M : ℝ) ^ 2 * L < (L : ℝ) ^ 2)
    (hzero :
      384 * (M : ℝ) ^ 2 * (L : ℝ) ^ 2 * q.divisors.card / q <
        (L : ℝ) ^ 2)
    (hnonzero :
      192 * K * (M : ℝ) * X * Real.log (X : ℝ) ^ O <
        (L : ℝ) ^ 2) :
    16 * (M : ℝ) *
        ((M : ℝ) * L +
          8 * ((M : ℝ) * L ^ 2 * q.divisors.card / q) +
          4 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) <
      (L : ℝ) ^ 2 := by
  let A : ℝ := (M : ℝ) ^ 2 * L
  let B : ℝ :=
    (M : ℝ) ^ 2 * (L : ℝ) ^ 2 * q.divisors.card / q
  let C : ℝ := K * (M : ℝ) * X * Real.log (X : ℝ) ^ O
  have hmain' : 48 * A < (L : ℝ) ^ 2 := by
    simpa only [A, mul_assoc] using hmain
  have hzero' : 384 * B < (L : ℝ) ^ 2 := by
    convert hzero using 1 <;> simp only [B] <;> ring
  have hnonzero' : 192 * C < (L : ℝ) ^ 2 := by
    simpa only [C, mul_assoc] using hnonzero
  have hsum : 48 * A + 384 * B + 192 * C <
      3 * (L : ℝ) ^ 2 := by
    nlinarith [hmain', hzero', hnonzero']
  calc
    16 * (M : ℝ) *
          ((M : ℝ) * L +
            8 * ((M : ℝ) * L ^ 2 * q.divisors.card / q) +
            4 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) =
        (48 * A + 384 * B + 192 * C) / 3 := by
          dsimp only [A, B, C]
          ring
    _ < (3 * (L : ℝ) ^ 2) / 3 :=
      div_lt_div_of_pos_right hsum (by norm_num)
    _ = (L : ℝ) ^ 2 := by ring

end Erdos587
