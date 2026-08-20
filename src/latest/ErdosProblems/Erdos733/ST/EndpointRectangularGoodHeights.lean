import ErdosProblems.Erdos733.ST.PolygonalArc
import Mathlib.Order.Interval.Set.Infinite

open Classical
noncomputable section

set_option linter.unusedVariables false

-- [TABLET NODE: EndpointRectangularGoodHeights]
lemma EndpointRectangularGoodHeights {ι : Type*} [Fintype ι]
    (ε H : ℝ) (L R : ι → EuclideanSpace ℝ (Fin 2))
    (hε : 0 < ε) (hH : 0 < H)
    (hLx : ∀ i, (L i) 0 = -ε)
    (hRx : ∀ i, (R i) 0 = ε)
    (hLy : ∀ i, |(L i) 1| < H)
    (hRy : ∀ i, |(R i) 1| < H)
    (hLinj : Function.Injective L)
    (hRinj : Function.Injective R)
    (horder : ∀ i j, (L i) 1 < (L j) 1 ↔ (R j) 1 < (R i) 1) :
    ∃ η : ι → ℝ,
      let middleFromHeights : (ι → ℝ) → ι → EuclideanSpace ℝ (Fin 2) :=
        fun η i => WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then 0 else η i)
      (∀ i, |η i| < H) ∧
        (∀ i j, η i < η j ↔ (L i) 1 < (L j) 1) ∧
          (∀ ⦃i j : ι⦄, i ≠ j →
            line[ℝ, L i, middleFromHeights η i] ≠
                line[ℝ, L j, middleFromHeights η j] ∧
              line[ℝ, L i, middleFromHeights η i] ≠
                  line[ℝ, middleFromHeights η j, R j] ∧
                line[ℝ, middleFromHeights η i, R i] ≠
                    line[ℝ, L j, middleFromHeights η j] ∧
                  line[ℝ, middleFromHeights η i, R i] ≠
                    line[ℝ, middleFromHeights η j, R j]) ∧
            (∀ ⦃i j : ι⦄, i ≠ j →
              ¬ ∃ t : ℝ,
                R j - middleFromHeights η j =
                  t • (R i - middleFromHeights η i)) ∧
              (∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                i ≠ j → i ≠ k → j ≠ k →
                  p ∈ openSegment ℝ (middleFromHeights η i) (R i) →
                    p ∈ openSegment ℝ (middleFromHeights η j) (R j) →
                      p ∈ openSegment ℝ (middleFromHeights η k) (R k) → False) := by
-- BODY
  let lam : ι → ℝ := fun i => (L i) 1
  let ρ : ι → ℝ := fun i => (R i) 1
  let φ : ι → ℝ := fun i => H ^ 2 - (lam i) ^ 2
  let ηOf : ℝ → ι → ℝ := fun c i => lam i + c * φ i
  let middle : (ι → ℝ) → ι → EuclideanSpace ℝ (Fin 2) :=
    fun η i => WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then 0 else η i)
  let pairs : Finset (ι × ι) := Finset.univ.product Finset.univ
  let triples : Finset ((ι × ι) × ι) := pairs.product Finset.univ
  let tripleNum : ι → ι → ι → ℝ :=
    fun i j k => (lam j - lam i) * (ρ k - ρ i) - (lam k - lam i) * (ρ j - ρ i)
  let tripleDen : ι → ι → ι → ℝ :=
    fun i j k => (φ j - φ i) * (ρ k - ρ i) - (φ k - φ i) * (ρ j - ρ i)
  let badLR : Finset ℝ :=
    pairs.image (fun ij : ι × ι => (ρ ij.2 - lam ij.1) / (2 * φ ij.1))
  let badRL : Finset ℝ :=
    pairs.image (fun ij : ι × ι => (ρ ij.1 - lam ij.2) / (2 * φ ij.2))
  let badPar : Finset ℝ :=
    pairs.image (fun ij : ι × ι =>
      if h : φ ij.2 = φ ij.1 then 0
      else ((ρ ij.2 - lam ij.2) - (ρ ij.1 - lam ij.1)) / (φ ij.2 - φ ij.1))
  let badTri : Finset ℝ :=
    triples.image (fun ijk : (ι × ι) × ι =>
      if h : tripleDen ijk.1.1 ijk.1.2 ijk.2 = 0 then 0
      else -tripleNum ijk.1.1 ijk.1.2 ijk.2 /
        tripleDen ijk.1.1 ijk.1.2 ijk.2)
  let bad : Finset ℝ := badLR ∪ badRL ∪ badPar ∪ badTri
  have hlaminj : Function.Injective lam := by
    intro i j hij
    apply hLinj
    ext k
    fin_cases k
    · simp [hLx]
    · exact hij
  have hρinj : Function.Injective ρ := by
    intro i j hij
    apply hRinj
    ext k
    fin_cases k
    · simp [hRx]
    · exact hij
  have hlam_ne : ∀ ⦃i j : ι⦄, i ≠ j → lam i ≠ lam j := by
    intro i j hij h
    exact hij (hlaminj h)
  have hρ_ne : ∀ ⦃i j : ι⦄, i ≠ j → ρ i ≠ ρ j := by
    intro i j hij h
    exact hij (hρinj h)
  have hφpos : ∀ i, 0 < φ i := by
    intro i
    have hb := abs_lt.mp (hLy i)
    simp [φ, lam]
    nlinarith [hH, hb.1, hb.2]
  have hnot_both_triple :
      ∀ ⦃i j k : ι⦄, i ≠ j → i ≠ k → j ≠ k →
        ¬ (tripleNum i j k = 0 ∧ tripleDen i j k = 0) := by
    intro i j k hij hik hjk hboth
    rcases hboth with ⟨hA, hB⟩
    have hprod : (lam j - lam k) * (lam k - lam i) * (ρ j - ρ i) = 0 := by
      calc
        (lam j - lam k) * (lam k - lam i) * (ρ j - ρ i)
            =
              -(tripleDen i j k + (lam j + lam i) * tripleNum i j k) := by
                simp [tripleNum, tripleDen, φ]
                ring
        _ = 0 := by rw [hA, hB]; ring
    have h1 : lam j - lam k ≠ 0 := sub_ne_zero.mpr (hlam_ne hjk)
    have h2 : lam k - lam i ≠ 0 := sub_ne_zero.mpr (hlam_ne (Ne.symm hik))
    have h3 : ρ j - ρ i ≠ 0 := sub_ne_zero.mpr (hρ_ne (Ne.symm hij))
    rcases mul_eq_zero.mp hprod with h12 | h3zero
    · rcases mul_eq_zero.mp h12 with h1zero | h2zero
      · exact h1 h1zero
      · exact h2 h2zero
    · exact h3 h3zero
  let δ : ℝ := 1 / (4 * H)
  have hδpos : 0 < δ := by
    simp [δ]
    positivity
  have hδord : -δ < δ := by linarith
  have hinterval_inf : (Set.Ioo (-δ) δ : Set ℝ).Infinite :=
    Set.Ioo_infinite hδord
  have hbad_fin : (bad : Set ℝ).Finite := bad.finite_toSet
  obtain ⟨c, hc⟩ := (hinterval_inf.diff hbad_fin).nonempty
  have hc_interval : c ∈ Set.Ioo (-δ) δ := hc.1
  have hc_not_bad : c ∉ (bad : Set ℝ) := hc.2
  have hc_abs : |c| < δ := by
    exact abs_lt.mpr ⟨by linarith [hc_interval.1], by linarith [hc_interval.2]⟩
  let η : ι → ℝ := ηOf c
  let M : ι → EuclideanSpace ℝ (Fin 2) := middle η
  have hη_bound : ∀ i, |η i| < H := by
    intro i
    have hc_small : |c| < 1 / (4 * H) := by simpa [δ] using hc_abs
    have hx : |lam i| < H := by simpa [lam] using hLy i
    have hHpos4 : 0 < 4 * H := by positivity
    have hcabs : |c| * (H + |lam i|) < 1 := by
      have hxH : H + |lam i| < 2 * H := by
        linarith [abs_nonneg (lam i), hx]
      have hmul : |c| * (H + |lam i|) < (1 / (4 * H)) * (2 * H) := by
        exact mul_lt_mul'' hc_small hxH (abs_nonneg c) (by positivity)
      have hcalc : (1 / (4 * H)) * (2 * H) = (1 : ℝ) / 2 := by
        field_simp [ne_of_gt hH]
        ring
      linarith
    have hfactor : H ^ 2 - (lam i) ^ 2 = (H - |lam i|) * (H + |lam i|) := by
      rw [← sq_abs (lam i)]
      ring
    have hmargin_pos : 0 < H - |lam i| := sub_pos.mpr hx
    have hpert_abs : |c * (H ^ 2 - (lam i) ^ 2)| < H - |lam i| := by
      rw [abs_mul, hfactor, abs_mul, abs_of_pos hmargin_pos,
        abs_of_nonneg (by positivity : 0 ≤ H + |lam i|)]
      have : |c| * ((H - |lam i|) * (H + |lam i|)) =
          (H - |lam i|) * (|c| * (H + |lam i|)) := by ring
      rw [this]
      nlinarith
    calc
      |η i| = |lam i + c * (H ^ 2 - (lam i) ^ 2)| := by simp [η, ηOf, φ]
      _ ≤ |lam i| + |c * (H ^ 2 - (lam i) ^ 2)| := abs_add_le _ _
      _ < |lam i| + (H - |lam i|) := add_lt_add_right hpert_abs _
      _ = H := by ring
  have hη_order : ∀ i j, η i < η j ↔ lam i < lam j := by
    intro i j
    have hc_small : |c| < 1 / (4 * H) := by simpa [δ] using hc_abs
    have hxi : |lam i| < H := by simpa [lam] using hLy i
    have hxj : |lam j| < H := by simpa [lam] using hLy j
    have hcabs : |c| * |lam i + lam j| < 1 := by
      have hxy : |lam i + lam j| < 2 * H := by
        calc
          |lam i + lam j| ≤ |lam i| + |lam j| := abs_add_le _ _
          _ < H + H := add_lt_add hxi hxj
          _ = 2 * H := by ring
      have hmul : |c| * |lam i + lam j| < (1 / (4 * H)) * (2 * H) := by
        exact mul_lt_mul'' hc_small hxy (abs_nonneg c) (by positivity)
      have hcalc : (1 / (4 * H)) * (2 * H) = (1 : ℝ) / 2 := by
        field_simp [ne_of_gt hH]
        ring
      linarith
    have hfacpos : 0 < 1 - c * (lam i + lam j) := by
      have hle : |c * (lam i + lam j)| < 1 := by
        simpa [abs_mul] using hcabs
      have hlt : c * (lam i + lam j) < 1 := lt_of_le_of_lt (le_abs_self _) hle
      linarith
    have hdiff :
        η j - η i = (lam j - lam i) * (1 - c * (lam i + lam j)) := by
      simp [η, ηOf, φ]
      ring
    constructor
    · intro h
      have hpos : 0 < η j - η i := sub_pos.mpr h
      have : 0 < lam j - lam i := by nlinarith
      linarith
    · intro h
      have : 0 < η j - η i := by
        rw [hdiff]
        exact mul_pos (sub_pos.mpr h) hfacpos
      exact sub_pos.mp this
  have hbadLR_mem :
      ∀ i j, (ρ j - lam i) / (2 * φ i) ∈ (bad : Set ℝ) := by
    intro i j
    have hmem : (ρ j - lam i) / (2 * φ i) ∈ badLR := by
      refine Finset.mem_image.mpr ?_
      exact ⟨(i, j), by simp [pairs], rfl⟩
    simp [bad, hmem]
  have hbadRL_mem :
      ∀ i j, (ρ i - lam j) / (2 * φ j) ∈ (bad : Set ℝ) := by
    intro i j
    have hmem : (ρ i - lam j) / (2 * φ j) ∈ badRL := by
      refine Finset.mem_image.mpr ?_
      exact ⟨(i, j), by simp [pairs], rfl⟩
    simp [bad, hmem]
  have hbadPar_mem :
      ∀ i j, (if h : φ j = φ i then 0
        else ((ρ j - lam j) - (ρ i - lam i)) / (φ j - φ i)) ∈ (bad : Set ℝ) := by
    intro i j
    have hmem :
        (if h : φ j = φ i then 0
          else ((ρ j - lam j) - (ρ i - lam i)) / (φ j - φ i)) ∈ badPar := by
      refine Finset.mem_image.mpr ?_
      exact ⟨(i, j), by simp [pairs], rfl⟩
    change (if h : φ j = φ i then 0
        else ((ρ j - lam j) - (ρ i - lam i)) / (φ j - φ i)) ∈ bad
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inr hmem)))
  have hbadTri_mem :
      ∀ i j k, (if h : tripleDen i j k = 0 then 0
        else -tripleNum i j k / tripleDen i j k) ∈ (bad : Set ℝ) := by
    intro i j k
    have hmem :
        (if h : tripleDen i j k = 0 then 0
          else -tripleNum i j k / tripleDen i j k) ∈ badTri := by
      refine Finset.mem_image.mpr ?_
      exact ⟨((i, j), k), by simp [triples, pairs], rfl⟩
    change (if h : tripleDen i j k = 0 then 0
        else -tripleNum i j k / tripleDen i j k) ∈ bad
    exact Finset.mem_union.mpr (Or.inr hmem)
  have hsupport :
      ∀ ⦃i j : ι⦄, i ≠ j →
        line[ℝ, L i, M i] ≠ line[ℝ, L j, M j] ∧
          line[ℝ, L i, M i] ≠ line[ℝ, M j, R j] ∧
            line[ℝ, M i, R i] ≠ line[ℝ, L j, M j] ∧
              line[ℝ, M i, R i] ≠ line[ℝ, M j, R j] := by
    intro i j hij
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hline
      have hmem : L i ∈ line[ℝ, L j, M j] := by
        rw [← hline]
        exact left_mem_affineSpan_pair ℝ (L i) (M i)
      rcases (mem_affineSpan_pair_iff_exists_lineMap_eq.mp hmem) with ⟨t, ht⟩
      have hx : (1 - t) * (-ε) + t * 0 = -ε := by
        have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) ht
        simpa [M, middle, hLx i, hLx j, AffineMap.lineMap_apply_module] using hx'
      have ht0 : t = 0 := by nlinarith [hε, hx]
      have hLi : L j = L i := by
        simpa [ht0] using ht
      exact hij (hLinj hLi).symm
    · intro hline
      have hmem : R j ∈ line[ℝ, L i, M i] := by
        rw [hline]
        exact right_mem_affineSpan_pair ℝ (M j) (R j)
      rcases (mem_affineSpan_pair_iff_exists_lineMap_eq.mp hmem) with ⟨t, ht⟩
      have hx : (1 - t) * (-ε) + t * 0 = ε := by
        have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) ht
        simpa [M, middle, hLx i, hRx j, AffineMap.lineMap_apply_module] using hx'
      have ht2 : t = 2 := by nlinarith [hε, hx]
      have hy : (1 - t) * lam i + t * η i = ρ j := by
        have hy' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) ht
        simpa [M, middle, lam, ρ, AffineMap.lineMap_apply_module] using hy'
      have hc_eq : c = (ρ j - lam i) / (2 * φ i) := by
        rw [ht2] at hy
        simp [η, ηOf] at hy
        have hlin : 2 * c * φ i = ρ j - lam i := by nlinarith
        have hφne : 2 * φ i ≠ 0 := by nlinarith [hφpos i]
        rw [eq_div_iff hφne]
        nlinarith
      exact hc_not_bad (by simpa [hc_eq] using hbadLR_mem i j)
    · intro hline
      have hmem : R i ∈ line[ℝ, L j, M j] := by
        rw [← hline]
        exact right_mem_affineSpan_pair ℝ (M i) (R i)
      rcases (mem_affineSpan_pair_iff_exists_lineMap_eq.mp hmem) with ⟨t, ht⟩
      have hx : (1 - t) * (-ε) + t * 0 = ε := by
        have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) ht
        simpa [M, middle, hLx j, hRx i, AffineMap.lineMap_apply_module] using hx'
      have ht2 : t = 2 := by nlinarith [hε, hx]
      have hy : (1 - t) * lam j + t * η j = ρ i := by
        have hy' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) ht
        simpa [M, middle, lam, ρ, AffineMap.lineMap_apply_module] using hy'
      have hc_eq : c = (ρ i - lam j) / (2 * φ j) := by
        rw [ht2] at hy
        simp [η, ηOf] at hy
        have hlin : 2 * c * φ j = ρ i - lam j := by nlinarith
        have hφne : 2 * φ j ≠ 0 := by nlinarith [hφpos j]
        rw [eq_div_iff hφne]
        nlinarith
      exact hc_not_bad (by simpa [hc_eq] using hbadRL_mem i j)
    · intro hline
      have hmem : R i ∈ line[ℝ, M j, R j] := by
        rw [← hline]
        exact right_mem_affineSpan_pair ℝ (M i) (R i)
      rcases (mem_affineSpan_pair_iff_exists_lineMap_eq.mp hmem) with ⟨t, ht⟩
      have hx : (1 - t) * 0 + t * ε = ε := by
        have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) ht
        simpa [M, middle, hRx i, hRx j, AffineMap.lineMap_apply_module] using hx'
      have ht1 : t = 1 := by nlinarith [hε, hx]
      have hRi : R j = R i := by
        simpa [ht1] using ht
      exact hij (hRinj hRi).symm
  have hright_nonparallel :
      ∀ ⦃i j : ι⦄, i ≠ j →
        ¬ ∃ t : ℝ, R j - M j = t • (R i - M i) := by
    intro i j hij hpar
    rcases hpar with ⟨t, ht⟩
    have hx : ε = t * ε := by
      have hx' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) ht
      simpa [M, middle, hRx i, hRx j, Pi.smul_apply] using hx'
    have ht1 : t = 1 := by nlinarith [hε, hx]
    have hy : ρ j - η j = t * (ρ i - η i) := by
      have hy' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) ht
      simpa [M, middle, ρ, Pi.smul_apply] using hy'
    rw [ht1] at hy
    have hslope : (ρ j - lam j) - c * φ j = (ρ i - lam i) - c * φ i := by
      simp [η, ηOf] at hy ⊢
      ring_nf at hy ⊢
      exact hy
    by_cases hden : φ j = φ i
    · have hslope0 : ρ j - lam j = ρ i - lam i := by
        rw [hden] at hslope
        linarith
      have hlamne' : lam i ≠ lam j := hlam_ne hij
      rcases lt_or_gt_of_ne hlamne' with hlt | hgt
      · have hρlt : ρ j < ρ i := by
          simpa [lam, ρ] using (horder i j).1 (by simpa [lam] using hlt)
        nlinarith
      · have hρlt : ρ i < ρ j := by
          simpa [lam, ρ] using (horder j i).1 (by simpa [lam] using hgt)
        nlinarith
    · have hc_eq :
          c = ((ρ j - lam j) - (ρ i - lam i)) / (φ j - φ i) := by
        have hφne : φ j - φ i ≠ 0 := sub_ne_zero.mpr hden
        field_simp [hφne]
        nlinarith
      have hmem := hbadPar_mem i j
      have hmem' : ((ρ j - lam j) - (ρ i - lam i)) / (φ j - φ i) ∈ (bad : Set ℝ) := by
        simpa [hden] using hmem
      exact hc_not_bad (by simpa [hc_eq] using hmem')
  have hno_triple :
      ∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → i ≠ k → j ≠ k →
          p ∈ openSegment ℝ (M i) (R i) →
            p ∈ openSegment ℝ (M j) (R j) →
              p ∈ openSegment ℝ (M k) (R k) → False := by
    intro i j k p hij hik hjk hpi hpj hpk
    rw [openSegment_eq_image_lineMap] at hpi hpj hpk
    rcases hpi with ⟨ti, hti, hti_eq⟩
    rcases hpj with ⟨tj, htj, htj_eq⟩
    rcases hpk with ⟨tk, htk, htk_eq⟩
    have hxi : ti * ε = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hti_eq
      simpa [M, middle, hRx i, AffineMap.lineMap_apply_module] using hx'
    have hxj : tj * ε = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) htj_eq
      simpa [M, middle, hRx j, AffineMap.lineMap_apply_module] using hx'
    have hxk : tk * ε = p 0 := by
      have hx' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) htk_eq
      simpa [M, middle, hRx k, AffineMap.lineMap_apply_module] using hx'
    have htji : tj = ti := by nlinarith [hε, hxi, hxj]
    have htki : tk = ti := by nlinarith [hε, hxi, hxk]
    have hyi : (1 - ti) * η i + ti * ρ i = p 1 := by
      have hy' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 1) hti_eq
      simpa [M, middle, ρ, AffineMap.lineMap_apply_module] using hy'
    have hyj : (1 - ti) * η j + ti * ρ j = p 1 := by
      have hy' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 1) htj_eq
      rw [htji] at hy'
      simpa [M, middle, ρ, AffineMap.lineMap_apply_module] using hy'
    have hyk : (1 - ti) * η k + ti * ρ k = p 1 := by
      have hy' := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 1) htk_eq
      rw [htki] at hy'
      simpa [M, middle, ρ, AffineMap.lineMap_apply_module] using hy'
    have heqj : (1 - ti) * (η j - η i) + ti * (ρ j - ρ i) = 0 := by
      nlinarith
    have heqk : (1 - ti) * (η k - η i) + ti * (ρ k - ρ i) = 0 := by
      nlinarith
    have hdet_prod :
        (1 - ti) *
          ((η j - η i) * (ρ k - ρ i) - (η k - η i) * (ρ j - ρ i)) = 0 := by
      calc
        (1 - ti) *
            ((η j - η i) * (ρ k - ρ i) - (η k - η i) * (ρ j - ρ i))
            =
              ((1 - ti) * (η j - η i) + ti * (ρ j - ρ i)) * (ρ k - ρ i) -
                ((1 - ti) * (η k - η i) + ti * (ρ k - ρ i)) * (ρ j - ρ i) := by
                ring
        _ = 0 := by rw [heqj, heqk]; ring
    have hti_ne : 1 - ti ≠ 0 := by
      have : ti < 1 := hti.2
      linarith
    have hdet :
        (η j - η i) * (ρ k - ρ i) - (η k - η i) * (ρ j - ρ i) = 0 := by
      exact (mul_eq_zero.mp hdet_prod).resolve_left hti_ne
    have hdet_c : tripleNum i j k + c * tripleDen i j k = 0 := by
      simp [tripleNum, tripleDen, η, ηOf] at hdet ⊢
      ring_nf at hdet ⊢
      exact hdet
    by_cases hden : tripleDen i j k = 0
    · have hnum : tripleNum i j k = 0 := by
        rw [hden] at hdet_c
        linarith
      exact hnot_both_triple hij hik hjk ⟨hnum, hden⟩
    · have hc_eq : c = -tripleNum i j k / tripleDen i j k := by
        apply (eq_div_iff hden).2
        exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hdet_c)
      have hmem := hbadTri_mem i j k
      rw [dif_neg hden] at hmem
      exact hc_not_bad (hc_eq.symm ▸ hmem)
  refine ⟨η, ?_⟩
  dsimp only
  refine ⟨hη_bound, ?_, hsupport, hright_nonparallel, hno_triple⟩
  intro i j
  simpa [lam] using hη_order i j
