import ErdosProblems.Erdos587.CorrectedWeyl

namespace Erdos587

open scoped BigOperators ComplexConjugate

noncomputable def nvCyclicIntervalCoeff
    (q U : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  ∑ u : Fin U, ZMod.stdAddChar (-(h * (u : ZMod q)))

noncomputable def nvQuadraticIntervalSum
    (q A B C X Z L : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  ∑ j ∈ Finset.range L,
    ZMod.stdAddChar
      (h * ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
        h * (X : ZMod q))

/-- Multiplication by a unit modulo `q` preserves the gcd of a natural
coefficient with `q`, even after choosing the least natural representative. -/
lemma gcd_val_unit_mul_nat
    (q a : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    Nat.gcd (((u : ZMod q) * (a : ZMod q)).val) q = Nat.gcd a q := by
  have huCoprime : Nat.Coprime u.val.val q := ZMod.val_coe_unit_coprime u
  have hprod : (((u : ZMod q) * (a : ZMod q)).val) ≡
      u.val.val * a [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
  calc
    Nat.gcd (((u : ZMod q) * (a : ZMod q)).val) q =
        Nat.gcd (u.val.val * a) q := hprod.gcd_eq
    _ = Nat.gcd a q := huCoprime.gcd_mul_left_cancel a

lemma stdAddChar_int_eq_phase {q : ℕ} [NeZero q] (n : ℤ) :
    ZMod.stdAddChar (n : ZMod q) = phase ((n : ℝ) / q) := by
  rw [ZMod.stdAddChar_coe, phase, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

lemma norm_quadraticSum_neg (α β : ℝ) (L : ℕ) :
    ‖quadraticSum (-α) (-β) L‖ = ‖quadraticSum α β L‖ := by
  have hconj : quadraticSum (-α) (-β) L =
      starRingEnd ℂ (quadraticSum α β L) := by
    unfold quadraticSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← phase_neg]
    congr 1
    ring
  rw [hconj]
  exact norm_star _

lemma norm_nvQuadraticIntervalSum_eq
    (q A B C X Z L : ℕ) [NeZero q] (h : ZMod q) :
    ‖nvQuadraticIntervalSum q A B C X Z L h‖ =
      ‖quadraticSum
        (((A * h.valMinAbs.natAbs : ℕ) : ℝ) / q)
        (((h.valMinAbs.natAbs * (2 * A * Z + B) : ℕ) : ℝ) / q) L‖ := by
  let s : ℤ := h.valMinAbs
  let d : ℕ := h.valMinAbs.natAbs
  have hh : h = (s : ZMod q) := by
    dsimp only [s]
    exact (ZMod.coe_valMinAbs h).symm
  have hd : (d : ℤ) = |s| := by simp [d, s]
  have hterm (j : ℕ) :
      ZMod.stdAddChar
          (h * ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
            h * (X : ZMod q)) =
        phase (((s : ℝ) / q) *
          (((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ℤ) - X)) := by
    rw [hh]
    have hcast :
        (s : ZMod q) *
              ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
            (s : ZMod q) * (X : ZMod q) =
          ((s * (((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ℤ) - X) : ℤ) :
            ZMod q) := by
      push_cast
      ring
    rw [hcast, stdAddChar_int_eq_phase]
    congr 1
    push_cast
    field_simp
  have hfactor : nvQuadraticIntervalSum q A B C X Z L h =
      phase (((s : ℝ) / q) *
          (((A * Z ^ 2 + B * Z + C : ℕ) : ℤ) - X)) *
        quadraticSum
          (((s : ℝ) * A) / q)
          (((s : ℝ) * (2 * A * Z + B)) / q) L := by
    unfold nvQuadraticIntervalSum quadraticSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hterm, ← phase_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [hfactor, norm_mul, norm_phase, one_mul]
  change
    ‖quadraticSum (((s : ℝ) * A) / q)
        (((s : ℝ) * (2 * A * Z + B)) / q) L‖ =
      ‖quadraticSum (((A * d : ℕ) : ℝ) / q)
        (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) L‖
  rcases le_total 0 s with hs | hs
  · have hsabs : (s : ℤ) = d := by
      rw [← abs_of_nonneg hs, ← hd]
    rw [hsabs]
    push_cast
    congr 3 <;> ring
  · have hsabs : (s : ℤ) = -(d : ℤ) := by
      have habs := abs_of_nonpos hs
      rw [← hd] at habs
      omega
    rw [hsabs]
    push_cast
    rw [show (-(d : ℝ) * A) / q = -(((A * d : ℕ) : ℝ) / q) by
      push_cast; ring]
    rw [show (-(d : ℝ) * (2 * A * Z + B)) / q =
        -(((d * (2 * A * Z + B) : ℕ) : ℝ) / q) by
      push_cast; ring]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
      (norm_quadraticSum_neg
        (((A * d : ℕ) : ℝ) / q)
        (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) L)

/-- The low signed frequencies occur in fibres of size at most two.  After
reducing the leading coefficient, their total quadratic mass is therefore
bounded by twice the positive-frequency first moment used in the corrected
Nguyen--Vu Weyl estimate. -/
lemma sum_low_norm_nvQuadraticIntervalSum_le
    (q A B C X Z L M : ℕ) [NeZero q] (hMhalf : M ≤ q / 2) :
    let r := A.gcd q
    let A' := A / r
    let q' := q / r
    (∑ h ∈ (Finset.univ.erase (0 : ZMod q)).filter
        (fun h ↦ h.valMinAbs.natAbs ≤ M),
        ‖nvQuadraticIntervalSum q A B C X Z L h‖) ≤
      2 * ∑ d ∈ Finset.Icc 1 M,
        ‖quadraticSum
          (((A' * d : ℕ) : ℝ) / q')
          (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) L‖ := by
  dsimp only
  let low := (Finset.univ.erase (0 : ZMod q)).filter
    (fun h : ZMod q ↦ h.valMinAbs.natAbs ≤ M)
  let ds := Finset.Icc 1 M
  let f : ZMod q → ℕ := fun h ↦ h.valMinAbs.natAbs
  let r := A.gcd q
  let A' := A / r
  let q' := q / r
  have hq : 0 < q := NeZero.pos q
  have hr : 0 < r := Nat.gcd_pos_of_pos_right A hq
  have hq' : 0 < q' := Nat.div_pos (Nat.gcd_le_right A hq) hr
  have hmaps : (low : Set (ZMod q)).MapsTo f ds := by
    intro h hh
    have hh' := Finset.mem_filter.mp hh
    have hh0 := (Finset.mem_erase.mp hh'.1).1
    have hdpos : 1 ≤ h.valMinAbs.natAbs := by
      have hne : h.valMinAbs ≠ 0 := by
        intro hz
        exact hh0 ((ZMod.valMinAbs_eq_zero h).mp hz)
      omega
    exact Finset.mem_Icc.mpr ⟨hdpos, hh'.2⟩
  have hratio (d : ℕ) : (((A * d : ℕ) : ℝ) / q) =
      (((A' * d : ℕ) : ℝ) / q') := by
    have hbase := reduced_frequency_ratio (a := 1) (m := A) hq
    dsimp only [A', q', r]
    calc
      (((A * d : ℕ) : ℝ) / q) =
          (d : ℝ) * (((1 * A : ℕ) : ℝ) / q) := by
        push_cast
        ring
      _ = (d : ℝ) *
          (((1 * (A / A.gcd q) : ℕ) : ℝ) /
            ((q / A.gcd q : ℕ) : ℝ)) := by rw [hbase]
      _ = (((A / A.gcd q * d : ℕ) : ℝ) /
          ((q / A.gcd q : ℕ) : ℝ)) := by
        push_cast
        ring
  have hfiber (d : ℕ) (hd : d ∈ ds) :
      ((low.filter fun h ↦ f h = d).card : ℝ) ≤ 2 := by
    have hsub : low.filter (fun h ↦ f h = d) ⊆
        Waring.Analytic.leastResidueFiber q d := by
      intro h hh
      have hhd : f h = d := (Finset.mem_filter.mp hh).2
      simpa [f, Waring.Analytic.leastResidueFiber] using hhd
    have hdq : d ≤ q / 2 :=
      (Finset.mem_Icc.mp hd).2.trans hMhalf
    have hcard : (Waring.Analytic.leastResidueFiber q d).card ≤ 2 := by
      apply Waring.Analytic.card_leastResidueFiber_le_two
      exact hdq
    exact_mod_cast (Finset.card_le_card hsub |>.trans hcard)
  have hterm (d : ℕ) (hd : d ∈ ds) :
      (∑ h ∈ low with f h = d,
          ‖nvQuadraticIntervalSum q A B C X Z L h‖) ≤
        2 * ‖quadraticSum
          (((A' * d : ℕ) : ℝ) / q')
          (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) L‖ := by
    let Q : ℝ := ‖quadraticSum
      (((A' * d : ℕ) : ℝ) / q')
      (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) L‖
    calc
      (∑ h ∈ low with f h = d,
          ‖nvQuadraticIntervalSum q A B C X Z L h‖) =
          ∑ _h ∈ low.filter (fun h ↦ f h = d), Q := by
        apply Finset.sum_congr rfl
        intro h hh
        have hhd : h.valMinAbs.natAbs = d := by
          simpa [f] using (Finset.mem_filter.mp hh).2
        rw [norm_nvQuadraticIntervalSum_eq, hhd, hratio]
      _ = ((low.filter fun h ↦ f h = d).card : ℝ) * Q := by simp
      _ ≤ 2 * Q := by
        gcongr
        exact hfiber d hd
  change (∑ h ∈ low, ‖nvQuadraticIntervalSum q A B C X Z L h‖) ≤ _
  calc
    (∑ h ∈ low, ‖nvQuadraticIntervalSum q A B C X Z L h‖) =
        ∑ d ∈ ds, ∑ h ∈ low with f h = d,
          ‖nvQuadraticIntervalSum q A B C X Z L h‖ := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ d ∈ ds, 2 * ‖quadraticSum
          (((A' * d : ℕ) : ℝ) / q')
          (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) L‖ := by
      exact Finset.sum_le_sum fun d hd ↦ hterm d hd
    _ = 2 * ∑ d ∈ Finset.Icc 1 M,
        ‖quadraticSum
          (((A' * d : ℕ) : ℝ) / q')
          (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) L‖ := by
      rw [Finset.mul_sum]

/-- Correct reduced-denominator Weyl estimate for a signed cyclic frequency. -/
lemma norm_nvQuadraticIntervalSum_sq_le
    (q A B C X Z L : ℕ) [NeZero q] (h : ZMod q) :
    let r := A.gcd q
    let A' := A / r
    let q' := q / r
    let d := h.valMinAbs.natAbs
    ‖nvQuadraticIntervalSum q A B C X Z L h‖ ^ 2 ≤
      L + 4 * ((L : ℝ) / ((q' / d.gcd q' : ℕ) : ℝ) + 1) * L +
        8 * (L + ((q' / d.gcd q' : ℕ) : ℝ)) *
          (1 + Real.log ((q' / d.gcd q' : ℕ) : ℝ)) := by
  dsimp only
  have hq : 0 < q := NeZero.pos q
  let r := A.gcd q
  let A' := A / r
  let q' := q / r
  let d := h.valMinAbs.natAbs
  have hr : 0 < r := Nat.gcd_pos_of_pos_right A hq
  have hq' : 0 < q' := Nat.div_pos (Nat.gcd_le_right A hq) hr
  have hcop : A'.Coprime q' := by
    exact Nat.coprime_div_gcd_div_gcd hr
  have hratio : (((A * d : ℕ) : ℝ) / q) =
      (((A' * d : ℕ) : ℝ) / q') := by
    have hbase := reduced_frequency_ratio (a := 1) (m := A) hq
    dsimp only [A', q', r]
    calc
      (((A * d : ℕ) : ℝ) / q) = (d : ℝ) * (((1 * A : ℕ) : ℝ) / q) := by
        push_cast
        ring
      _ = (d : ℝ) *
          (((1 * (A / A.gcd q) : ℕ) : ℝ) / ((q / A.gcd q : ℕ) : ℝ)) := by
        rw [hbase]
      _ = (((A / A.gcd q * d : ℕ) : ℝ) / ((q / A.gcd q : ℕ) : ℝ)) := by
        push_cast
        ring
  rw [norm_nvQuadraticIntervalSum_eq, hratio]
  exact norm_quadraticSum_rational_frequency_sq_le
    A' d q' L (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) hq' hcop

lemma norm_nvQuadraticIntervalSum_sq_le_coarse
    (q A B C X Z L M : ℕ) [NeZero q] {h : ZMod q}
    (hh : h ≠ 0) (hdM : h.valMinAbs.natAbs ≤ M) :
    let r := A.gcd q
    let q' := q / r
    ‖nvQuadraticIntervalSum q A B C X Z L h‖ ^ 2 ≤
      L + 4 * ((L : ℝ) * M / q' + 1) * L +
        8 * (L + q') * (1 + Real.log q') := by
  dsimp only
  have hq : 0 < q := NeZero.pos q
  let r := A.gcd q
  let A' := A / r
  let q' := q / r
  let d := h.valMinAbs.natAbs
  have hr : 0 < r := Nat.gcd_pos_of_pos_right A hq
  have hq' : 0 < q' := Nat.div_pos (Nat.gcd_le_right A hq) hr
  have hcop : A'.Coprime q' := Nat.coprime_div_gcd_div_gcd hr
  have hd : 1 ≤ d := by
    have hne : h.valMinAbs ≠ 0 := by
      intro hz
      exact hh ((ZMod.valMinAbs_eq_zero h).mp hz)
    dsimp only [d]
    omega
  have hratio : (((A * d : ℕ) : ℝ) / q) =
      (((A' * d : ℕ) : ℝ) / q') := by
    have hbase := reduced_frequency_ratio (a := 1) (m := A) hq
    dsimp only [A', q', r]
    calc
      (((A * d : ℕ) : ℝ) / q) = (d : ℝ) * (((1 * A : ℕ) : ℝ) / q) := by
        push_cast
        ring
      _ = (d : ℝ) *
          (((1 * (A / A.gcd q) : ℕ) : ℝ) / ((q / A.gcd q : ℕ) : ℝ)) := by
        rw [hbase]
      _ = (((A / A.gcd q * d : ℕ) : ℝ) / ((q / A.gcd q : ℕ) : ℝ)) := by
        push_cast
        ring
  rw [norm_nvQuadraticIntervalSum_eq, hratio]
  exact (norm_quadraticSum_rational_frequency_sq_le_coarse
    A' d q' L (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) hd hq' hcop).trans
      (by gcongr)

lemma nvCyclicIntervalCoeff_zero (q U : ℕ) [NeZero q] :
    nvCyclicIntervalCoeff q U 0 = U := by
  simp [nvCyclicIntervalCoeff]

lemma nvQuadraticIntervalSum_zero (q A B C X Z L : ℕ) [NeZero q] :
    nvQuadraticIntervalSum q A B C X Z L 0 = L := by
  simp [nvQuadraticIntervalSum]

lemma nvCyclicIntervalCoeff_eq_intervalFourierCoefficient
    (q U : ℕ) [NeZero q] (h : ZMod q) :
    nvCyclicIntervalCoeff q U h =
      Waring.Analytic.intervalFourierCoefficient (-1) U h := by
  unfold nvCyclicIntervalCoeff Waring.Analytic.intervalFourierCoefficient
  apply Finset.sum_bij (fun (u : Fin U) _hu ↦ (u : ℤ))
  · intro u hu
    rw [Finset.mem_Ioc]
    constructor
    · omega
    · have hu' := u.isLt
      push_cast
      omega
  · intro u hu v hv huv
    exact Fin.ext (by exact_mod_cast huv)
  · intro x hx
    rw [Finset.mem_Ioc] at hx
    have hx0 : 0 ≤ x := by omega
    have hxU : x.toNat < U := by omega
    refine ⟨⟨x.toNat, hxU⟩, Finset.mem_univ _, ?_⟩
    simp [Int.toNat_of_nonneg hx0]
  · intro u hu
    congr 2
    simp

lemma norm_nvCyclicIntervalCoeff_le_length
    (q U : ℕ) [NeZero q] (h : ZMod q) :
    ‖nvCyclicIntervalCoeff q U h‖ ≤ U := by
  rw [nvCyclicIntervalCoeff_eq_intervalFourierCoefficient]
  exact Waring.Analytic.norm_intervalFourierCoefficient_le_length (-1) U h

lemma norm_nvCyclicIntervalCoeff_le_leastResidue
    (q U : ℕ) [NeZero q] {h : ZMod q} (hh : h ≠ 0) :
    ‖nvCyclicIntervalCoeff q U h‖ ≤
      (q : ℝ) / (2 * (h.valMinAbs.natAbs : ℝ)) := by
  rw [nvCyclicIntervalCoeff_eq_intervalFourierCoefficient]
  exact Waring.Analytic.norm_intervalFourierCoefficient_le_leastResidue (-1) U hh

lemma norm_nvQuadraticIntervalSum_le_length
    (q A B C X Z L : ℕ) [NeZero q] (h : ZMod q) :
    ‖nvQuadraticIntervalSum q A B C X Z L h‖ ≤ L := by
  unfold nvQuadraticIntervalSum
  calc
    ‖∑ j ∈ Finset.range L,
        ZMod.stdAddChar
          (h * ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
            h * (X : ZMod q))‖ ≤
        ∑ _j ∈ Finset.range L, (1 : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      gcongr with j hj
      simp
    _ = L := by simp

lemma nv_tuple_character_sum
    (q U k : ℕ) [NeZero q] (h : ZMod q) :
    (∑ v : Fin k → Fin U,
        ZMod.stdAddChar
          (-(h * ((∑ i, (v i : ℕ) : ℕ) : ZMod q)))) =
      nvCyclicIntervalCoeff q U h ^ k := by
  calc
    (∑ v : Fin k → Fin U,
        ZMod.stdAddChar
          (-(h * ((∑ i, (v i : ℕ) : ℕ) : ZMod q)))) =
        ∑ v : Fin k → Fin U,
          ∏ i : Fin k, ZMod.stdAddChar (-(h * (v i : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [show -(h * ((∑ i, (v i : ℕ) : ℕ) : ZMod q)) =
          ∑ i : Fin k, -(h * (v i : ZMod q)) by
        push_cast
        rw [Finset.mul_sum, Finset.sum_neg_distrib]]
      exact addChar_map_sum_eq_prod ZMod.stdAddChar
        (fun i : Fin k ↦ -(h * (v i : ZMod q)))
    _ = ∏ _i : Fin k, nvCyclicIntervalCoeff q U h := by
      symm
      exact Fintype.prod_sum
        (fun _i : Fin k ↦ fun u : Fin U ↦ ZMod.stdAddChar (-(h * (u : ZMod q))))
    _ = nvCyclicIntervalCoeff q U h ^ k := by simp

lemma nv_smoothed_frequency_factorization
    (q A B C X Z L U k : ℕ) [NeZero q] (h : ZMod q) :
    (∑ v : Fin k → Fin U, ∑ j ∈ Finset.range L,
        ZMod.stdAddChar
          (h * (((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
            ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q)))) =
      nvCyclicIntervalCoeff q U h ^ k *
        nvQuadraticIntervalSum q A B C X Z L h := by
  rw [Finset.sum_comm]
  unfold nvQuadraticIntervalSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ v : Fin k → Fin U,
        ZMod.stdAddChar
          (h * (((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
            ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q)))) =
        ∑ v : Fin k → Fin U,
          ZMod.stdAddChar
              (-(h * ((∑ i, (v i : ℕ) : ℕ) : ZMod q))) *
            ZMod.stdAddChar
              (h * ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
                h * (X : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← ZMod.stdAddChar.map_add_eq_mul]
      congr 2
      push_cast
      ring
    _ = (∑ v : Fin k → Fin U,
          ZMod.stdAddChar (-(h * ((∑ i, (v i : ℕ) : ℕ) : ZMod q)))) *
        ZMod.stdAddChar
          (h * ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
            h * (X : ZMod q)) := by rw [Finset.sum_mul]
    _ = nvCyclicIntervalCoeff q U h ^ k *
        ZMod.stdAddChar
          (h * ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
            h * (X : ZMod q)) := by rw [nv_tuple_character_sum]

lemma card_nv_low_frequencies_le
    (q M : ℕ) [NeZero q] (hM : M ≤ q / 2) :
    ((Finset.univ.erase (0 : ZMod q)).filter
      (fun h ↦ h.valMinAbs.natAbs ≤ M)).card ≤ 2 * M := by
  let low := (Finset.univ.erase (0 : ZMod q)).filter
    (fun h : ZMod q ↦ h.valMinAbs.natAbs ≤ M)
  let ds := Finset.Icc 1 M
  let fibers : ℕ → Finset (ZMod q) := fun d ↦
    Waring.Analytic.leastResidueFiber q d
  have hsub : low ⊆ ds.biUnion fibers := by
    intro h hh
    have hh' := Finset.mem_filter.mp hh
    have hh0 := (Finset.mem_erase.mp hh'.1).1
    have hdpos : 1 ≤ h.valMinAbs.natAbs := by
      have hne : h.valMinAbs ≠ 0 := by
        intro hz
        exact hh0 ((ZMod.valMinAbs_eq_zero h).mp hz)
      omega
    exact Finset.mem_biUnion.mpr
      ⟨h.valMinAbs.natAbs, Finset.mem_Icc.mpr ⟨hdpos, hh'.2⟩,
        by simp [fibers, Waring.Analytic.leastResidueFiber]⟩
  calc
    low.card ≤ (ds.biUnion fibers).card := Finset.card_le_card hsub
    _ ≤ ∑ d ∈ ds, (fibers d).card := Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ ds, 2 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Waring.Analytic.card_leastResidueFiber_le_two
      exact (Finset.mem_Icc.mp hd).2.trans hM
    _ = 2 * M := by simp [ds, mul_comm]

theorem exists_smoothed_quadratic_rectangle_of_low_sum
    {q A B C X Z L U k M : ℕ} {E : ℝ}
    [NeZero q] (hU : 0 < U) (hL : 0 < L)
    (hMhalf : M ≤ q / 2)
    (hE : 0 ≤ E)
    (hlow :
      (∑ h ∈ (Finset.univ.erase (0 : ZMod q)).filter
        (fun h ↦ h.valMinAbs.natAbs ≤ M),
        ‖nvQuadraticIntervalSum q A B C X Z L h‖) ≤ E)
    (hdom :
      (U : ℝ) ^ k * E +
          (q : ℝ) * ((q : ℝ) / (2 * (M + 1))) ^ k * L <
        (U : ℝ) ^ k * L) :
    ∃ v : Fin k → Fin U, ∃ j < L,
      (A * (Z + j) ^ 2 + B * (Z + j) + C : ZMod q) =
        (X + ∑ i, (v i : ℕ) : ℕ) := by
  let low := (Finset.univ.erase (0 : ZMod q)).filter
    (fun h : ZMod q ↦ h.valMinAbs.natAbs ≤ M)
  let high := (Finset.univ.erase (0 : ZMod q)).filter
    (fun h : ZMod q ↦ ¬ h.valMinAbs.natAbs ≤ M)
  by_contra hnone
  push Not at hnone
  have hfreqZero :
      (∑ h : ZMod q,
          nvCyclicIntervalCoeff q U h ^ k *
            nvQuadraticIntervalSum q A B C X Z L h) = 0 := by
    calc
      (∑ h : ZMod q,
          nvCyclicIntervalCoeff q U h ^ k *
            nvQuadraticIntervalSum q A B C X Z L h) =
          ∑ h : ZMod q, ∑ v : Fin k → Fin U, ∑ j ∈ Finset.range L,
            ZMod.stdAddChar
              (h * (((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
                ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q))) := by
        apply Finset.sum_congr rfl
        intro h hh
        exact (nv_smoothed_frequency_factorization q A B C X Z L U k h).symm
      _ = ∑ v : Fin k → Fin U, ∑ j ∈ Finset.range L, ∑ h : ZMod q,
            ZMod.stdAddChar
              (h * (((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) -
                ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.sum_comm]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        apply Finset.sum_eq_zero
        intro j hj
        rw [Erdos387.AdditiveOrthogonality.sum_stdAddChar_mul]
        rw [if_neg]
        intro heq
        apply hnone v j (Finset.mem_range.mp hj)
        rw [← sub_eq_zero]
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sum] using heq
  have hzeroTerm :
      nvCyclicIntervalCoeff q U 0 ^ k *
          nvQuadraticIntervalSum q A B C X Z L 0 =
        ((U : ℕ) ^ k * L : ℕ) := by
    rw [nvCyclicIntervalCoeff_zero, nvQuadraticIntervalSum_zero]
    norm_num
  have hmain : (U : ℝ) ^ k * L ≤
      ∑ h ∈ (Finset.univ.erase (0 : ZMod q)),
        ‖nvCyclicIntervalCoeff q U h ^ k *
          nvQuadraticIntervalSum q A B C X Z L h‖ := by
    have hmem : (0 : ZMod q) ∈ (Finset.univ : Finset (ZMod q)) := by simp
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (ZMod q))
      (fun h ↦ nvCyclicIntervalCoeff q U h ^ k *
        nvQuadraticIntervalSum q A B C X Z L h) hmem
    rw [hfreqZero, hzeroTerm] at hsplit
    have hcast : ‖(((U : ℕ) ^ k * L : ℕ) : ℂ)‖ =
        (U : ℝ) ^ k * L := by
      rw [Complex.norm_natCast]
      push_cast
      rfl
    have heq :
        (∑ x ∈ Finset.univ.erase (0 : ZMod q),
          nvCyclicIntervalCoeff q U x ^ k *
            nvQuadraticIntervalSum q A B C X Z L x) =
          -((((U : ℕ) ^ k * L : ℕ) : ℂ)) := by
      linear_combination hsplit
    calc
      (U : ℝ) ^ k * L = ‖-((((U : ℕ) ^ k * L : ℕ) : ℂ))‖ := by
        rw [norm_neg, hcast]
      _ = ‖∑ x ∈ Finset.univ.erase (0 : ZMod q),
          nvCyclicIntervalCoeff q U x ^ k *
            nvQuadraticIntervalSum q A B C X Z L x‖ := by rw [heq]
      _ ≤ _ := norm_sum_le _ _
  have herase : (Finset.univ.erase (0 : ZMod q)) = low ∪ high := by
    ext h
    constructor
    · intro hh
      have hh0 : h ≠ 0 := (Finset.mem_erase.mp hh).1
      by_cases hd : h.valMinAbs.natAbs ≤ M
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hh, hd⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hh, hd⟩)
    · intro hh
      rcases Finset.mem_union.mp hh with hl | hh
      · exact (Finset.mem_filter.mp hl).1
      · exact (Finset.mem_filter.mp hh).1
  have hdisj : Disjoint low high := by
    rw [Finset.disjoint_left]
    intro h hl hh
    exact (Finset.mem_filter.mp hh).2 (Finset.mem_filter.mp hl).2
  have hpartition :
      (∑ h ∈ (Finset.univ.erase (0 : ZMod q)),
        ‖nvCyclicIntervalCoeff q U h ^ k *
          nvQuadraticIntervalSum q A B C X Z L h‖) =
      (∑ h ∈ low,
        ‖nvCyclicIntervalCoeff q U h ^ k *
          nvQuadraticIntervalSum q A B C X Z L h‖) +
      (∑ h ∈ high,
        ‖nvCyclicIntervalCoeff q U h ^ k *
          nvQuadraticIntervalSum q A B C X Z L h‖) := by
    rw [herase, Finset.sum_union hdisj]
  have hlowSum :
      (∑ h ∈ low,
        ‖nvCyclicIntervalCoeff q U h ^ k *
          nvQuadraticIntervalSum q A B C X Z L h‖) ≤
        (U : ℝ) ^ k * E := by
    calc
      (∑ h ∈ low,
          ‖nvCyclicIntervalCoeff q U h ^ k *
            nvQuadraticIntervalSum q A B C X Z L h‖) ≤
          ∑ h ∈ low, (U : ℝ) ^ k *
            ‖nvQuadraticIntervalSum q A B C X Z L h‖ := by
        apply Finset.sum_le_sum
        intro h hh
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _)
            (norm_nvCyclicIntervalCoeff_le_length q U h) k)
          (norm_nonneg _)
      _ = (U : ℝ) ^ k *
          ∑ h ∈ low, ‖nvQuadraticIntervalSum q A B C X Z L h‖ := by
        rw [Finset.mul_sum]
      _ ≤ (U : ℝ) ^ k * E := by
        gcongr
  have hhighSum :
      (∑ h ∈ high,
        ‖nvCyclicIntervalCoeff q U h ^ k *
          nvQuadraticIntervalSum q A B C X Z L h‖) ≤
        (q : ℝ) * ((q : ℝ) / (2 * (M + 1))) ^ k * L := by
    calc
      (∑ h ∈ high,
          ‖nvCyclicIntervalCoeff q U h ^ k *
            nvQuadraticIntervalSum q A B C X Z L h‖) ≤
          ∑ _h ∈ high,
            ((q : ℝ) / (2 * (M + 1))) ^ k * L := by
        apply Finset.sum_le_sum
        intro h hh
        have hh' := Finset.mem_filter.mp hh
        have hh0 : h ≠ 0 := (Finset.mem_erase.mp hh'.1).1
        have hd : (M + 1 : ℝ) ≤ h.valMinAbs.natAbs := by
          exact_mod_cast (by omega : M + 1 ≤ h.valMinAbs.natAbs)
        have hden : (0 : ℝ) < 2 * (M + 1) := by positivity
        have hden' : (0 : ℝ) < 2 * (h.valMinAbs.natAbs : ℝ) := by
          have : 0 < h.valMinAbs.natAbs := by omega
          positivity
        have hcoeff : ‖nvCyclicIntervalCoeff q U h‖ ≤
            (q : ℝ) / (2 * (M + 1)) := by
          calc
            ‖nvCyclicIntervalCoeff q U h‖ ≤
                (q : ℝ) / (2 * (h.valMinAbs.natAbs : ℝ)) :=
              norm_nvCyclicIntervalCoeff_le_leastResidue q U hh0
            _ ≤ (q : ℝ) / (2 * (M + 1)) := by
              apply div_le_div_of_nonneg_left (by positivity) hden
              nlinarith
        rw [norm_mul, norm_pow]
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hcoeff k)
          (norm_nvQuadraticIntervalSum_le_length q A B C X Z L h)
          (by positivity) (by positivity)
      _ = (high.card : ℝ) *
          (((q : ℝ) / (2 * (M + 1))) ^ k * L) := by simp
      _ ≤ (q : ℝ) * (((q : ℝ) / (2 * (M + 1))) ^ k * L) := by
        gcongr
        exact_mod_cast (show high.card ≤ q by simpa using high.card_le_univ)
      _ = (q : ℝ) * ((q : ℝ) / (2 * (M + 1))) ^ k * L := by ring
  rw [hpartition] at hmain
  have := hmain.trans (add_le_add hlowSum hhighSum)
  exact (not_lt_of_ge this) hdom

/-- Pointwise wrapper for the aggregate low-frequency smoothing criterion. -/
theorem exists_smoothed_quadratic_rectangle
    {q A B C X Z L U k M : ℕ} {E : ℝ}
    [NeZero q] (hU : 0 < U) (hL : 0 < L)
    (hMhalf : M ≤ q / 2)
    (hE : 0 ≤ E)
    (hlow : ∀ h : ZMod q, h ≠ 0 → h.valMinAbs.natAbs ≤ M →
      ‖nvQuadraticIntervalSum q A B C X Z L h‖ ≤ E)
    (hdom :
      (2 * M : ℕ) * (U : ℝ) ^ k * E +
          (q : ℝ) * ((q : ℝ) / (2 * (M + 1))) ^ k * L <
        (U : ℝ) ^ k * L) :
    ∃ v : Fin k → Fin U, ∃ j < L,
      (A * (Z + j) ^ 2 + B * (Z + j) + C : ZMod q) =
        (X + ∑ i, (v i : ℕ) : ℕ) := by
  apply exists_smoothed_quadratic_rectangle_of_low_sum
      (E := (2 * M : ℕ) * E) hU hL hMhalf
  · positivity
  · let low := (Finset.univ.erase (0 : ZMod q)).filter
      (fun h : ZMod q ↦ h.valMinAbs.natAbs ≤ M)
    change (∑ h ∈ low, ‖nvQuadraticIntervalSum q A B C X Z L h‖) ≤ _
    calc
      (∑ h ∈ low, ‖nvQuadraticIntervalSum q A B C X Z L h‖) ≤
          ∑ _h ∈ low, E := by
        apply Finset.sum_le_sum
        intro h hh
        have hh' := Finset.mem_filter.mp hh
        exact hlow h (Finset.mem_erase.mp hh'.1).1 hh'.2
      _ = (low.card : ℝ) * E := by simp
      _ ≤ (2 * M : ℕ) * E := by
        gcongr
        exact_mod_cast card_nv_low_frequencies_le q M hMhalf
  · convert hdom using 1 <;> push_cast <;> ring

/-- The finite smoothing criterion with its low-frequency input discharged by the
correct reduced-denominator quadratic Weyl estimate. -/
theorem exists_smoothed_quadratic_rectangle_of_reduced_weyl
    {q A B C X Z L U k M : ℕ} [NeZero q]
    (hU : 0 < U) (hL : 0 < L)
    (hMhalf : M ≤ q / 2)
    (hdom :
      let q' := q / A.gcd q
      (2 * M : ℕ) * (U : ℝ) ^ k *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) +
          (q : ℝ) * ((q : ℝ) / (2 * (M + 1))) ^ k * L <
        (U : ℝ) ^ k * L) :
    ∃ v : Fin k → Fin U, ∃ j < L,
      (A * (Z + j) ^ 2 + B * (Z + j) + C : ZMod q) =
        (X + ∑ i, (v i : ℕ) : ℕ) := by
  let q' := q / A.gcd q
  let D : ℝ :=
    L + 4 * ((L : ℝ) * M / q' + 1) * L +
      8 * (L + q') * (1 + Real.log q')
  have hq : 0 < q := NeZero.pos q
  have hr : 0 < A.gcd q := Nat.gcd_pos_of_pos_right A hq
  have hq' : 0 < q' := Nat.div_pos (Nat.gcd_le_right A hq) hr
  have hlog : 0 ≤ Real.log (q' : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q' by omega))
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  apply exists_smoothed_quadratic_rectangle hU hL hMhalf
      (Real.sqrt_nonneg D)
  · intro h hh hdM
    have hsquare := norm_nvQuadraticIntervalSum_sq_le_coarse
      q A B C X Z L M hh hdM
    change ‖nvQuadraticIntervalSum q A B C X Z L h‖ ≤ Real.sqrt D
    dsimp only [D, q'] at hsquare
    exact Real.le_sqrt_of_sq_le hsquare
  · simpa only [D, q'] using hdom

/-- A convenient split form of the smoothing criterion.  The first strict
inequality gives the low frequencies less than half of the zero mode, and
the second does the same for the high frequencies. -/
theorem exists_smoothed_quadratic_rectangle_of_split_bounds
    {q A B C X Z L U k M : ℕ} [NeZero q]
    (hU : 0 < U) (hL : 0 < L)
    (hMhalf : M ≤ q / 2)
    (hlow :
      let q' := q / A.gcd q
      4 * (M : ℝ) *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) < L)
    (hhigh :
      2 * (q : ℝ) * ((q : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ v : Fin k → Fin U, ∃ j < L,
      (A * (Z + j) ^ 2 + B * (Z + j) + C : ZMod q) =
        (X + ∑ i, (v i : ℕ) : ℕ) := by
  let q' := q / A.gcd q
  let D : ℝ :=
    L + 4 * ((L : ℝ) * M / q' + 1) * L +
      8 * (L + q') * (1 + Real.log q')
  apply exists_smoothed_quadratic_rectangle_of_reduced_weyl
    hU hL hMhalf
  dsimp only
  have hP : 0 < (U : ℝ) ^ k := pow_pos (by positivity) k
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hlow' :
      2 * ((2 * M : ℕ) * (U : ℝ) ^ k * Real.sqrt D) <
        (U : ℝ) ^ k * L := by
    have hmul := mul_lt_mul_of_pos_left
      (show 4 * (M : ℝ) * Real.sqrt D < L by
        simpa only [D, q'] using hlow) hP
    push_cast
    nlinarith
  have hhigh' :
      2 * ((q : ℝ) * ((q : ℝ) / (2 * (M + 1))) ^ k * L) <
        (U : ℝ) ^ k * L := by
    have hmul := mul_lt_mul_of_pos_right hhigh hLreal
    nlinarith
  nlinarith

/-- Aggregate version of the split smoothing criterion.  It uses the
Nguyen--Vu first moment over the positive frequencies, rather than replacing
every low frequency by a pointwise maximum. -/
theorem exists_smoothed_quadratic_rectangle_of_aggregate_split_bounds
    {q A B C X Z L U k M : ℕ} [NeZero q]
    (hU : 0 < U) (hL : 0 < L)
    (hMhalf : M ≤ q / 2)
    (hlow :
      let r := A.gcd q
      let A' := A / r
      let q' := q / r
      4 * (∑ d ∈ Finset.Icc 1 M,
        ‖quadraticSum
          (((A' * d : ℕ) : ℝ) / q')
          (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) L‖) < L)
    (hhigh :
      2 * (q : ℝ) * ((q : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ v : Fin k → Fin U, ∃ j < L,
      (A * (Z + j) ^ 2 + B * (Z + j) + C : ZMod q) =
        (X + ∑ i, (v i : ℕ) : ℕ) := by
  let r := A.gcd q
  let A' := A / r
  let q' := q / r
  let S : ℝ := ∑ d ∈ Finset.Icc 1 M,
    ‖quadraticSum
      (((A' * d : ℕ) : ℝ) / q')
      (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) L‖
  have hS : 0 ≤ S := by
    dsimp only [S]
    positivity
  apply exists_smoothed_quadratic_rectangle_of_low_sum
      (E := 2 * S) hU hL hMhalf (by positivity)
  · exact (sum_low_norm_nvQuadraticIntervalSum_le
      q A B C X Z L M hMhalf).trans (le_refl _)
  · have hP : 0 < (U : ℝ) ^ k := pow_pos (by positivity) k
    have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
    have hlow' :
        2 * ((U : ℝ) ^ k * (2 * S)) < (U : ℝ) ^ k * L := by
      have hmul := mul_lt_mul_of_pos_left
        (show 4 * S < (L : ℝ) by
          simpa only [S, A', q', r] using hlow) hP
      nlinarith
    have hhigh' :
        2 * ((q : ℝ) * ((q : ℝ) / (2 * (M + 1))) ^ k * L) <
          (U : ℝ) ^ k * L := by
      have hmul := mul_lt_mul_of_pos_right hhigh hLreal
      nlinarith
    nlinarith

/-- Uniform low-frequency consequence of the corrected Nguyen--Vu Weyl
estimate, after reducing the leading coefficient by its gcd with the
modulus.  The linear coefficient is arbitrary, exactly as required by the
rank-two rectangle. -/
theorem exists_aggregate_low_bound_of_corrected_weyl_budget :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ q A B Z L M : ℕ,
        let r := A.gcd q
        let A' := A / r
        let q' := q / r
        let X := 2 * M * L
        let D := Nat.sqrt (Nat.sqrt X)
        0 < q → 0 < L → 3 ≤ D → q' - 1 ≤ X → q' * D ≤ X →
        16 * (M : ℝ) *
            ((M : ℝ) * L +
              8 * ((M : ℝ) * L ^ 2 * q'.divisors.card / q') +
              4 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) <
          (L : ℝ) ^ 2 →
        4 * (∑ d ∈ Finset.Icc 1 M,
          ‖quadraticSum
            (((A' * d : ℕ) : ℝ) / q')
            (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) L‖) < L := by
  obtain ⟨K, hK, O, hO, hweyl⟩ :=
    exists_sum_norm_quadraticSum_rational_mul_lt_quarter_of_budget
  refine ⟨K, hK, O, hO, ?_⟩
  intro q A B Z L M
  dsimp only
  let r := A.gcd q
  let A' := A / r
  let q' := q / r
  let X := 2 * M * L
  let D := Nat.sqrt (Nat.sqrt X)
  intro hq hL hD hqX hqD hbudget
  have hr : 0 < r := by
    dsimp only [r]
    exact Nat.gcd_pos_of_pos_right A hq
  have hq' : 0 < q' := by
    dsimp only [q']
    exact Nat.div_pos (Nat.gcd_le_right A hq) hr
  have hcop : A'.Coprime q' := by
    dsimp only [A', q', r]
    exact Nat.coprime_div_gcd_div_gcd hr
  let beta : ℕ → ℝ := fun d ↦
    ((d * (2 * A * Z + B) : ℕ) : ℝ) / q
  have hresult := hweyl A' q' L M beta hcop hq' hL hD hqX hqD
    (by simpa only [X, q'] using hbudget)
  simpa only [beta, A', q'] using hresult

/-- Short-variable branch of the rank-two Nguyen--Vu congruence.  Multiplying
by the inverse of the primitive coefficient `q₁` turns the first coordinate
into an ordinary interval; finite convolution smoothing then keeps that
coordinate and the quadratic variable inside their prescribed intervals. -/
theorem exists_rank_two_congruence_smoothed_of_reduced_weyl
    {a b q₁ q₂ X Hx Z L U k M : ℕ} {t : ℤ}
    (hq₂ : 0 < q₂) (hcop : q₁.Coprime q₂)
    (hU : 0 < U) (hL : 0 < L) (hMhalf : M ≤ q₂ / 2)
    (hsupport : k * (U - 1) ≤ Hx)
    (hdom :
      let u : (ZMod q₂)ˣ := ZMod.unitOfCoprime q₁ hcop
      let A : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * a).val
      let q' := q₂ / A.gcd q₂
      (2 * M : ℕ) * (U : ℝ) ^ k *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) +
          (q₂ : ℝ) * ((q₂ : ℝ) / (2 * (M + 1))) ^ k * L <
        (U : ℝ) ^ k * L) :
    ∃ x : ℕ, X ≤ x ∧ x ≤ X + Hx ∧
      ∃ z : ℕ, Z ≤ z ∧ z < Z + L ∧
        (q₂ : ℤ) ∣
          (a : ℤ) * z ^ 2 + (b : ℤ) * z - (q₁ : ℤ) * x - t := by
  let : NeZero q₂ := ⟨hq₂.ne'⟩
  let u : (ZMod q₂)ˣ := ZMod.unitOfCoprime q₁ hcop
  let A : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * a).val
  let B : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * b).val
  let C : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * (-(t : ZMod q₂))).val
  obtain ⟨v, j, hjL, hvj⟩ :=
    exists_smoothed_quadratic_rectangle_of_reduced_weyl
      (q := q₂) (A := A) (B := B) (C := C) (X := X)
      (Z := Z) (L := L) (U := U) (k := k) (M := M)
      hU hL hMhalf (by simpa only [A] using hdom)
  let y : ℕ := ∑ i, (v i : ℕ)
  have hy : y ≤ k * (U - 1) := by
    dsimp only [y]
    calc
      (∑ i, (v i : ℕ)) ≤ ∑ _i : Fin k, (U - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hvi := (v i).isLt
        omega
      _ = k * (U - 1) := by simp
  let x := X + y
  let z := Z + j
  have hxupper : x ≤ X + Hx := by
    dsimp only [x]
    omega
  have hzupper : z < Z + L := by
    dsimp only [z]
    omega
  have hAval : (A : ZMod q₂) =
      (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * a) :=
    ZMod.natCast_zmod_val _
  have hBval : (B : ZMod q₂) =
      (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * b) :=
    ZMod.natCast_zmod_val _
  have hCval : (C : ZMod q₂) =
      (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * (-(t : ZMod q₂))) :=
    ZMod.natCast_zmod_val _
  have hu : (q₁ : ZMod q₂) * (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂)) = 1 := by
    rw [show (q₁ : ZMod q₂) = (u : ZMod q₂) by
      exact (ZMod.coe_unitOfCoprime q₁ hcop).symm]
    rw [← Units.val_mul]
    simp
  have horig : (a : ZMod q₂) * z ^ 2 + (b : ZMod q₂) * z =
      (q₁ : ZMod q₂) * x + t := by
    rw [hAval, hBval, hCval] at hvj
    have hvj' : (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) *
        ((a : ZMod q₂) * z ^ 2 + (b : ZMod q₂) * z - t)) = x := by
      dsimp only [x, y, z]
      push_cast
      simp only [Nat.cast_add, Nat.cast_sum] at hvj ⊢
      linear_combination hvj
    calc
      (a : ZMod q₂) * z ^ 2 + (b : ZMod q₂) * z =
          (q₁ : ZMod q₂) *
            ((((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) *
              ((a : ZMod q₂) * z ^ 2 + (b : ZMod q₂) * z - t))) + t := by
                rw [← mul_assoc, hu, one_mul]
                ring
      _ = (q₁ : ZMod q₂) * x + t := by rw [hvj']
  refine ⟨x, by simp [x], hxupper, z, by simp [z], hzupper, ?_⟩
  have hmodeq :
      (a : ℤ) * (z : ℤ) ^ 2 + (b : ℤ) * z ≡
        (q₁ : ℤ) * x + t [ZMOD (q₂ : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact horig
  rw [Int.modEq_iff_dvd] at hmodeq
  obtain ⟨w, hw⟩ := hmodeq
  refine ⟨-w, ?_⟩
  linarith

/-- Split-bound interface for the short-variable rank-two congruence. -/
theorem exists_rank_two_congruence_smoothed_of_split_bounds
    {a b q₁ q₂ X Hx Z L U k M : ℕ} {t : ℤ}
    (hq₂ : 0 < q₂) (hcop : q₁.Coprime q₂)
    (hU : 0 < U) (hL : 0 < L) (hMhalf : M ≤ q₂ / 2)
    (hsupport : k * (U - 1) ≤ Hx)
    (hlow :
      let u : (ZMod q₂)ˣ := ZMod.unitOfCoprime q₁ hcop
      let A : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * a).val
      let q' := q₂ / A.gcd q₂
      4 * (M : ℝ) *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) < L)
    (hhigh :
      2 * (q₂ : ℝ) * ((q₂ : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ x : ℕ, X ≤ x ∧ x ≤ X + Hx ∧
      ∃ z : ℕ, Z ≤ z ∧ z < Z + L ∧
        (q₂ : ℤ) ∣
          (a : ℤ) * z ^ 2 + (b : ℤ) * z - (q₁ : ℤ) * x - t := by
  apply exists_rank_two_congruence_smoothed_of_reduced_weyl
    hq₂ hcop hU hL hMhalf hsupport
  let u : (ZMod q₂)ˣ := ZMod.unitOfCoprime q₁ hcop
  let A : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * a).val
  let q' := q₂ / A.gcd q₂
  let D : ℝ :=
    L + 4 * ((L : ℝ) * M / q' + 1) * L +
      8 * (L + q') * (1 + Real.log q')
  dsimp only
  have hP : 0 < (U : ℝ) ^ k := pow_pos (by positivity) k
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hlow' :
      2 * ((2 * M : ℕ) * (U : ℝ) ^ k * Real.sqrt D) <
        (U : ℝ) ^ k * L := by
    have hmul := mul_lt_mul_of_pos_left
      (show 4 * (M : ℝ) * Real.sqrt D < L by
        simpa only [D, q', A, u] using hlow) hP
    push_cast
    nlinarith
  have hhigh' :
      2 * ((q₂ : ℝ) * ((q₂ : ℝ) / (2 * (M + 1))) ^ k * L) <
        (U : ℝ) ^ k * L := by
    have hmul := mul_lt_mul_of_pos_right hhigh hLreal
    nlinarith
  nlinarith

/-- Aggregate first-moment interface for the short-variable rank-two
congruence. -/
theorem exists_rank_two_congruence_smoothed_of_aggregate_bounds
    {a b q₁ q₂ X Hx Z L U k M : ℕ} {t : ℤ}
    (hq₂ : 0 < q₂) (hcop : q₁.Coprime q₂)
    (hU : 0 < U) (hL : 0 < L) (hMhalf : M ≤ q₂ / 2)
    (hsupport : k * (U - 1) ≤ Hx)
    (hlow :
      let u : (ZMod q₂)ˣ := ZMod.unitOfCoprime q₁ hcop
      let A : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * a).val
      let B : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * b).val
      let r := A.gcd q₂
      let A' := A / r
      let q' := q₂ / r
      4 * (∑ d ∈ Finset.Icc 1 M,
        ‖quadraticSum
          (((A' * d : ℕ) : ℝ) / q')
          (((d * (2 * A * Z + B) : ℕ) : ℝ) / q₂) L‖) < L)
    (hhigh :
      2 * (q₂ : ℝ) * ((q₂ : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ x : ℕ, X ≤ x ∧ x ≤ X + Hx ∧
      ∃ z : ℕ, Z ≤ z ∧ z < Z + L ∧
        (q₂ : ℤ) ∣
          (a : ℤ) * z ^ 2 + (b : ℤ) * z - (q₁ : ℤ) * x - t := by
  let : NeZero q₂ := ⟨hq₂.ne'⟩
  let u : (ZMod q₂)ˣ := ZMod.unitOfCoprime q₁ hcop
  let A : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * a).val
  let B : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * b).val
  let C : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * (-(t : ZMod q₂))).val
  obtain ⟨v, j, hjL, hvj⟩ :=
    exists_smoothed_quadratic_rectangle_of_aggregate_split_bounds
      (q := q₂) (A := A) (B := B) (C := C) (X := X)
      (Z := Z) (L := L) (U := U) (k := k) (M := M)
      hU hL hMhalf (by simpa only [A, B, u] using hlow) hhigh
  let y : ℕ := ∑ i, (v i : ℕ)
  have hy : y ≤ k * (U - 1) := by
    dsimp only [y]
    calc
      (∑ i, (v i : ℕ)) ≤ ∑ _i : Fin k, (U - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hvi := (v i).isLt
        omega
      _ = k * (U - 1) := by simp
  let x := X + y
  let z := Z + j
  have hxupper : x ≤ X + Hx := by
    dsimp only [x]
    omega
  have hzupper : z < Z + L := by
    dsimp only [z]
    omega
  have hAval : (A : ZMod q₂) =
      (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * a) :=
    ZMod.natCast_zmod_val _
  have hBval : (B : ZMod q₂) =
      (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * b) :=
    ZMod.natCast_zmod_val _
  have hCval : (C : ZMod q₂) =
      (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * (-(t : ZMod q₂))) :=
    ZMod.natCast_zmod_val _
  have hu : (q₁ : ZMod q₂) * (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂)) = 1 := by
    rw [show (q₁ : ZMod q₂) = (u : ZMod q₂) by
      exact (ZMod.coe_unitOfCoprime q₁ hcop).symm]
    rw [← Units.val_mul]
    simp
  have horig : (a : ZMod q₂) * z ^ 2 + (b : ZMod q₂) * z =
      (q₁ : ZMod q₂) * x + t := by
    rw [hAval, hBval, hCval] at hvj
    have hvj' : (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) *
        ((a : ZMod q₂) * z ^ 2 + (b : ZMod q₂) * z - t)) = x := by
      dsimp only [x, y, z]
      push_cast
      simp only [Nat.cast_add, Nat.cast_sum] at hvj ⊢
      linear_combination hvj
    calc
      (a : ZMod q₂) * z ^ 2 + (b : ZMod q₂) * z =
          (q₁ : ZMod q₂) *
            ((((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) *
              ((a : ZMod q₂) * z ^ 2 + (b : ZMod q₂) * z - t))) + t := by
                rw [← mul_assoc, hu, one_mul]
                ring
      _ = (q₁ : ZMod q₂) * x + t := by rw [hvj']
  refine ⟨x, by simp [x], hxupper, z, by simp [z], hzupper, ?_⟩
  have hmodeq :
      (a : ℤ) * (z : ℤ) ^ 2 + (b : ℤ) * z ≡
        (q₁ : ℤ) * x + t [ZMOD (q₂ : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact horig
  rw [Int.modEq_iff_dvd] at hmodeq
  obtain ⟨w, hw⟩ := hmodeq
  refine ⟨-w, ?_⟩
  linarith

/-- The same split criterion, with the reduced denominator written in its
original Nguyen--Vu form `q₂ / gcd(a,q₂)`.  The preceding unit-gcd lemma
shows that inversion of `q₁` does not change it. -/
theorem exists_rank_two_congruence_smoothed
    {a b q₁ q₂ X Hx Z L U k M : ℕ} {t : ℤ}
    (hq₂ : 0 < q₂) (hcop : q₁.Coprime q₂)
    (hU : 0 < U) (hL : 0 < L) (hMhalf : M ≤ q₂ / 2)
    (hsupport : k * (U - 1) ≤ Hx)
    (hlow :
      let q' := q₂ / a.gcd q₂
      4 * (M : ℝ) *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) < L)
    (hhigh :
      2 * (q₂ : ℝ) * ((q₂ : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ x : ℕ, X ≤ x ∧ x ≤ X + Hx ∧
      ∃ z : ℕ, Z ≤ z ∧ z < Z + L ∧
        (q₂ : ℤ) ∣
          (a : ℤ) * z ^ 2 + (b : ℤ) * z - (q₁ : ℤ) * x - t := by
  apply exists_rank_two_congruence_smoothed_of_split_bounds
    hq₂ hcop hU hL hMhalf hsupport
  · let : NeZero q₂ := ⟨hq₂.ne'⟩
    dsimp only
    rw [gcd_val_unit_mul_nat q₂ a]
    simpa only using hlow
  · exact hhigh

/-- Archimedean completion of the smoothed congruence.  If the chosen
rectangle lies inside the strip between quotient coordinates `0` and `L₂`,
the modular solution supplies an actual natural second coordinate. -/
theorem exists_rank_two_quadratic_eq_smoothed
    {a b q₁ q₂ L₁ L₂ X Hx Z L U k M : ℕ} {t : ℤ}
    (hq₂ : 0 < q₂) (hcop : q₁.Coprime q₂)
    (hU : 0 < U) (hL : 0 < L) (hMhalf : M ≤ q₂ / 2)
    (hsupport : k * (U - 1) ≤ Hx)
    (hxside : X + Hx ≤ L₁)
    (hstrip : ∀ x z : ℕ,
      X ≤ x → x ≤ X + Hx → Z ≤ z → z < Z + L →
      0 ≤ (a : ℤ) * z ^ 2 + (b : ℤ) * z - (q₁ : ℤ) * x - t ∧
      (a : ℤ) * z ^ 2 + (b : ℤ) * z - (q₁ : ℤ) * x - t ≤
        (q₂ : ℤ) * L₂)
    (hlow :
      let q' := q₂ / a.gcd q₂
      4 * (M : ℝ) *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) < L)
    (hhigh :
      2 * (q₂ : ℝ) * ((q₂ : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ z : ℕ,
      Z ≤ z ∧ z < Z + L ∧
      (a : ℤ) * z ^ 2 + (b : ℤ) * z =
        (q₁ : ℤ) * x + (q₂ : ℤ) * y + t := by
  obtain ⟨x, hxX, hxupper, z, hzZ, hzupper, hdvd⟩ :=
    exists_rank_two_congruence_smoothed hq₂ hcop hU hL hMhalf
      hsupport hlow hhigh
  obtain ⟨y, hyL₂, heq⟩ := exists_rank_two_y_of_dvd hq₂
    (hstrip x z hxX hxupper hzZ hzupper).1
    (hstrip x z hxX hxupper hzZ hzupper).2 hdvd
  exact ⟨x, hxupper.trans hxside, y, hyL₂, z, hzZ, hzupper, heq⟩

/-- Archimedean completion of the aggregate first-moment rank-two
congruence.  This is the form used by the corrected Nguyen--Vu Weyl
estimate: the low Fourier modes are controlled only after summation. -/
theorem exists_rank_two_quadratic_eq_smoothed_of_aggregate_bounds
    {a b q₁ q₂ L₁ L₂ X Hx Z L U k M : ℕ} {t : ℤ}
    (hq₂ : 0 < q₂) (hcop : q₁.Coprime q₂)
    (hU : 0 < U) (hL : 0 < L) (hMhalf : M ≤ q₂ / 2)
    (hsupport : k * (U - 1) ≤ Hx)
    (hxside : X + Hx ≤ L₁)
    (hstrip : ∀ x z : ℕ,
      X ≤ x → x ≤ X + Hx → Z ≤ z → z < Z + L →
      0 ≤ (a : ℤ) * z ^ 2 + (b : ℤ) * z - (q₁ : ℤ) * x - t ∧
      (a : ℤ) * z ^ 2 + (b : ℤ) * z - (q₁ : ℤ) * x - t ≤
        (q₂ : ℤ) * L₂)
    (hlow :
      let u : (ZMod q₂)ˣ := ZMod.unitOfCoprime q₁ hcop
      let A : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * a).val
      let B : ℕ := (((u⁻¹ : (ZMod q₂)ˣ) : ZMod q₂) * b).val
      let r := A.gcd q₂
      let A' := A / r
      let q' := q₂ / r
      4 * (∑ d ∈ Finset.Icc 1 M,
        ‖quadraticSum
          (((A' * d : ℕ) : ℝ) / q')
          (((d * (2 * A * Z + B) : ℕ) : ℝ) / q₂) L‖) < L)
    (hhigh :
      2 * (q₂ : ℝ) * ((q₂ : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ z : ℕ,
      Z ≤ z ∧ z < Z + L ∧
      (a : ℤ) * z ^ 2 + (b : ℤ) * z =
        (q₁ : ℤ) * x + (q₂ : ℤ) * y + t := by
  obtain ⟨x, hxX, hxupper, z, hzZ, hzupper, hdvd⟩ :=
    exists_rank_two_congruence_smoothed_of_aggregate_bounds
      hq₂ hcop hU hL hMhalf hsupport hlow hhigh
  obtain ⟨y, hyL₂, heq⟩ := exists_rank_two_y_of_dvd hq₂
    (hstrip x z hxX hxupper hzZ hzupper).1
    (hstrip x z hxX hxupper hzZ hzupper).2 hdvd
  exact ⟨x, hxupper.trans hxside, y, hyL₂, z, hzZ, hzupper, heq⟩

end Erdos587
