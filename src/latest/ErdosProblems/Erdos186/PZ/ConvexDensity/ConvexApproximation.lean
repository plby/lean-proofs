import ErdosProblems.Erdos186.PZ.ConvexDensity.Subgradient

open scoped BigOperators
open Set

namespace Erdos186.PZ.ConvexDensity.Subgradient

set_option autoImplicit false

noncomputable section

def pzExpandedBox (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) :=
  Set.Icc (fun _ ↦ -c) (fun _ ↦ 1 + c)

def pzGridPoint {n : ℕ} (m : ℕ) (v : Fin n → ℕ) : Fin n → ℝ :=
  fun i ↦ (v i : ℝ) / (m : ℝ)

def pzFinGridPoint {n m : ℕ} (v : Fin n → Fin m) : Fin n → ℝ :=
  pzGridPoint m fun i ↦ v i

def pzGridCell {n m : ℕ} (v : Fin n → Fin m) : Set (Fin n → ℝ) :=
  Set.Icc (pzFinGridPoint v) (fun i ↦ pzFinGridPoint v i + 1 / (m : ℝ))

abbrev pzTransverseKey {n m : ℕ} (i : Fin n) :=
  {j : Fin n // j ≠ i} → Fin m

def pzTransverse {n m : ℕ} (i : Fin n) (v : Fin n → Fin m) :
    pzTransverseKey (m := m) i :=
  fun j ↦ v j.1

def pzLineIndex {n m : ℕ} (i : Fin n)
    (t : pzTransverseKey (m := m) i) (a : ℕ) : Fin n → ℕ :=
  fun j ↦ if h : j = i then a else t ⟨j, h⟩

@[simp]
theorem card_pzTransverseKey {n m : ℕ} (i : Fin n) :
    Fintype.card (pzTransverseKey (m := m) i) = m ^ (n - 1) := by
  classical
  simp [pzTransverseKey, Fintype.card_subtype_compl]

theorem pzLineIndex_transverse {n m : ℕ} (i : Fin n)
    (v : Fin n → Fin m) :
    pzLineIndex i (pzTransverse i v) (v i) = fun j ↦ (v j : ℕ) := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [pzLineIndex]
  · simp [pzLineIndex, pzTransverse, h]

theorem pzLineIndex_add_axis {n m : ℕ} (i : Fin n)
    (t : pzTransverseKey (m := m) i) (a q : ℕ) :
    pzGridPoint m (pzLineIndex i t (a + q)) =
      pzGridPoint m (pzLineIndex i t a) +
        ((q : ℝ) / (m : ℝ)) • Pi.single i 1 := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [pzGridPoint, pzLineIndex]
    ring
  · simp [pzGridPoint, pzLineIndex, Pi.single_apply, h]

theorem pzFinGridPoint_mem_cell {n m : ℕ} (hm : 0 < m)
    (v : Fin n → Fin m) : pzFinGridPoint v ∈ pzGridCell v := by
  constructor
  · exact le_rfl
  · intro i
    exact le_add_of_nonneg_right (one_div_nonneg.mpr (by positivity))

theorem pzGridCell_coord {n m : ℕ} (hm : 0 < m)
    {v : Fin n → Fin m} {x : Fin n → ℝ} (hx : x ∈ pzGridCell v) (i : Fin n) :
    0 ≤ x i - pzFinGridPoint v i ∧
      x i - pzFinGridPoint v i ≤ 1 / (m : ℝ) := by
  constructor <;> linarith [hx.1 i, hx.2 i]

theorem pzFinGridPoint_cell_le_one {n m : ℕ} (hm : 0 < m)
    {v : Fin n → Fin m} {x : Fin n → ℝ} (hx : x ∈ pzGridCell v)
    (i : Fin n) : 0 ≤ x i ∧ x i ≤ 1 := by
  have hvlt : (v i : ℕ) < m := (v i).isLt
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hvnonneg : (0 : ℝ) ≤ v i := by positivity
  have hvle : ((v i : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast (show (v i : ℕ) + 1 ≤ m by omega)
  constructor
  · exact le_trans (div_nonneg hvnonneg hmreal.le) (hx.1 i)
  · calc
      x i ≤ pzFinGridPoint v i + 1 / (m : ℝ) := hx.2 i
      _ = (((v i : ℕ) : ℝ) + 1) / (m : ℝ) := by
        simp [pzFinGridPoint, pzGridPoint]
        ring
      _ ≤ 1 := (div_le_one hmreal).2 hvle

theorem mem_interior_pzExpandedBox_of_bounds {n : ℕ} {c : ℝ}
    {x : Fin n → ℝ} (hx : ∀ i, -c < x i ∧ x i < 1 + c) :
    x ∈ interior (pzExpandedBox n c) := by
  rw [pzExpandedBox, ← Set.pi_univ_Icc,
    interior_pi_set Set.finite_univ]
  intro i _hi
  simpa only [interior_Icc, Set.mem_Ioo] using hx i

theorem pzGridPoint_bounded_interior {n m K : ℕ} (hm : 0 < m)
    {c : ℝ} (hc : 2 * ((n : ℝ) + 1) / (m : ℝ) < c)
    (i : Fin n) (t : pzTransverseKey (m := m) i) (a : ℕ)
    (ha : a ≤ m + n) :
    pzGridPoint m (pzLineIndex i t a) ∈ interior (pzExpandedBox n c) := by
  apply mem_interior_pzExpandedBox_of_bounds
  intro j
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hcpos : 0 < c := lt_trans (by positivity) hc
  constructor
  · have : 0 ≤ pzGridPoint m (pzLineIndex i t a) j := by
      exact div_nonneg (by positivity) hmreal.le
    linarith
  · by_cases hji : j = i
    · subst j
      simp only [pzGridPoint, pzLineIndex, dif_pos]
      have hareal : (a : ℝ) ≤ (m : ℝ) + n := by exact_mod_cast ha
      have hqpos : 0 < ((n : ℝ) + 1) / (m : ℝ) :=
        div_pos (by positivity) hmreal
      have hqc : ((n : ℝ) + 1) / (m : ℝ) < c := by
        have hlt : ((n : ℝ) + 1) / (m : ℝ) <
            2 * ((n : ℝ) + 1) / (m : ℝ) := by
          rw [div_lt_div_iff_of_pos_right hmreal]
          nlinarith
        exact hlt.trans hc
      have hnmc : (n : ℝ) / (m : ℝ) < c :=
        lt_of_le_of_lt
          (div_le_div_of_nonneg_right (by norm_num) hmreal.le) hqc
      have : (a : ℝ) / (m : ℝ) ≤ 1 + (n : ℝ) / (m : ℝ) := by
        calc
          (a : ℝ) / (m : ℝ) ≤ ((m : ℝ) + n) / (m : ℝ) :=
            div_le_div_of_nonneg_right hareal hmreal.le
          _ = 1 + (n : ℝ) / (m : ℝ) := by
            field_simp
      linarith
    · simp only [pzGridPoint, pzLineIndex, dif_neg hji]
      have htlt : ((t ⟨j, hji⟩ : Fin m) : ℕ) < m := (t ⟨j, hji⟩).isLt
      have htlt' : ((((t ⟨j, hji⟩ : Fin m) : ℕ) : ℝ) / (m : ℝ)) < 1 := by
        rw [div_lt_one hmreal]
        exact_mod_cast htlt
      linarith

theorem pzGridCell_subset_interior {n m : ℕ} (hm : 0 < m)
    {c : ℝ} (hc : 0 < c) (v : Fin n → Fin m) :
    pzGridCell v ⊆ interior (pzExpandedBox n c) := by
  intro x hx
  apply mem_interior_pzExpandedBox_of_bounds
  intro i
  have hxi := pzFinGridPoint_cell_le_one hm hx i
  constructor <;> linarith

theorem pzFinGridPoint_axis_interior {n m : ℕ} (hm : 0 < m)
    {c : ℝ} (hc : 2 * ((n : ℝ) + 1) / (m : ℝ) < c)
    (v : Fin n → Fin m) (i : Fin n) :
    pzFinGridPoint v + (((n : ℝ) + 1) / (m : ℝ)) • Pi.single i 1 ∈
      interior (pzExpandedBox n c) := by
  let t := pzTransverse i v
  have ha : (v i : ℕ) + (n + 1) ≤ m + n := by
    have := (v i).isLt
    omega
  have hmem := pzGridPoint_bounded_interior (K := 0) hm hc i t
    ((v i : ℕ) + (n + 1)) ha
  have hb : pzGridPoint m (pzLineIndex i t (v i)) = pzFinGridPoint v := by
    rw [pzLineIndex_transverse]
    rfl
  have hadd := pzLineIndex_add_axis i t (v i : ℕ) (n + 1)
  rw [hadd, hb] at hmem
  norm_num only [Nat.cast_add, Nat.cast_one] at hmem
  exact hmem

theorem pzFinGridPoint_interior {n m : ℕ} (hm : 0 < m)
    {c : ℝ} (hc : 0 < c) (v : Fin n → Fin m) :
    pzFinGridPoint v ∈ interior (pzExpandedBox n c) := by
  exact pzGridCell_subset_interior hm hc v (pzFinGridPoint_mem_cell hm v)

theorem pzGridPoint_bounded_coord {n m : ℕ} (hm : 0 < m)
    (i : Fin n) (t : pzTransverseKey (m := m) i) (a : ℕ)
    (ha : a ≤ m + n) (j : Fin n) :
    pzGridPoint m (pzLineIndex i t a) j ∈
      Set.Icc (0 : ℝ) (1 + (n : ℝ) / (m : ℝ)) := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · exact div_nonneg (by positivity) hmreal.le
  · by_cases hji : j = i
    · subst j
      simp only [pzGridPoint, pzLineIndex, dif_pos]
      have hareal : (a : ℝ) ≤ (m : ℝ) + n := by exact_mod_cast ha
      calc
        (a : ℝ) / (m : ℝ) ≤ ((m : ℝ) + n) / (m : ℝ) :=
          div_le_div_of_nonneg_right hareal hmreal.le
        _ = 1 + (n : ℝ) / (m : ℝ) := by field_simp
    · simp only [pzGridPoint, pzLineIndex, dif_neg hji]
      have htlt : ((t ⟨j, hji⟩ : Fin m) : ℕ) < m := (t ⟨j, hji⟩).isLt
      have htle : ((((t ⟨j, hji⟩ : Fin m) : ℕ) : ℝ) / (m : ℝ)) ≤ 1 := by
        exact (div_le_one hmreal).2 (by exact_mod_cast (Nat.le_of_lt htlt))
      exact htle.trans (by
        have : 0 ≤ (n : ℝ) / (m : ℝ) := by positivity
        linarith)

theorem pzGridPoint_halfShift_mem {n m : ℕ} (hm : 0 < m)
    {c : ℝ} (hc : 2 * ((n : ℝ) + 1) / (m : ℝ) < c)
    (i : Fin n) (t : pzTransverseKey (m := m) i) (a : ℕ)
    (ha : a ≤ m + n) :
    pzGridPoint m (pzLineIndex i t a) - (c / 2) • Pi.single i 1 ∈
        pzExpandedBox n c ∧
      pzGridPoint m (pzLineIndex i t a) + (c / 2) • Pi.single i 1 ∈
        pzExpandedBox n c := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hcpos : 0 < c := lt_trans (by positivity) hc
  have hnHalf : (n : ℝ) / (m : ℝ) < c / 2 := by
    have hle : 2 * (n : ℝ) / (m : ℝ) ≤
        2 * ((n : ℝ) + 1) / (m : ℝ) := by
      exact div_le_div_of_nonneg_right (by nlinarith) hmreal.le
    have : 2 * (n : ℝ) / (m : ℝ) < c := hle.trans_lt hc
    have heq : 2 * (n : ℝ) / (m : ℝ) =
        2 * ((n : ℝ) / (m : ℝ)) := by ring
    rw [heq] at this
    nlinarith
  have hminusCoord (j : Fin n) :
      -c ≤ pzGridPoint m (pzLineIndex i t a) j -
        (c / 2) * (Pi.single i (1 : ℝ) : Fin n → ℝ) j ∧
      pzGridPoint m (pzLineIndex i t a) j -
        (c / 2) * (Pi.single i (1 : ℝ) : Fin n → ℝ) j ≤ 1 + c := by
    have hx := pzGridPoint_bounded_coord hm i t a ha j
    by_cases hji : j = i
    · subst j
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      constructor <;> nlinarith [hx.1, hx.2]
    · simp [Pi.single_apply, hji]
      constructor <;> nlinarith [hx.1, hx.2]
  have hplusCoord (j : Fin n) :
      -c ≤ pzGridPoint m (pzLineIndex i t a) j +
        (c / 2) * (Pi.single i (1 : ℝ) : Fin n → ℝ) j ∧
      pzGridPoint m (pzLineIndex i t a) j +
        (c / 2) * (Pi.single i (1 : ℝ) : Fin n → ℝ) j ≤ 1 + c := by
    have hx := pzGridPoint_bounded_coord hm i t a ha j
    by_cases hji : j = i
    · subst j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      constructor <;> nlinarith [hx.1, hx.2]
    · simp [Pi.single_apply, hji]
      constructor <;> nlinarith [hx.1, hx.2]
  exact ⟨⟨fun j ↦ by simpa using (hminusCoord j).1,
      fun j ↦ by simpa using (hminusCoord j).2⟩,
    ⟨fun j ↦ by simpa using (hplusCoord j).1,
      fun j ↦ by simpa using (hplusCoord j).2⟩⟩

theorem pzFinGridPoint_halfShift_mem {n m : ℕ} (hm : 0 < m)
    {c : ℝ} (hc : 2 * ((n : ℝ) + 1) / (m : ℝ) < c)
    (v : Fin n → Fin m) (i : Fin n) :
    pzFinGridPoint v - (c / 2) • Pi.single i 1 ∈ pzExpandedBox n c ∧
      pzFinGridPoint v + (c / 2) • Pi.single i 1 ∈ pzExpandedBox n c := by
  let t := pzTransverse i v
  have ha : (v i : ℕ) ≤ m + n := by omega
  have h := pzGridPoint_halfShift_mem hm hc i t (v i) ha
  have hb : pzGridPoint m (pzLineIndex i t (v i)) = pzFinGridPoint v := by
    rw [pzLineIndex_transverse]
    rfl
  simpa [hb] using h

/-- The finite-dimensional convex approximation lemma in the grid
normalization used by Pham--Zakharov. -/
theorem exists_gridCell_tangentAffine_approximation {n m : ℕ}
    (hn : 2 ≤ n) (hm : 0 < m) {c : ℝ}
    (hc : 2 * ((n : ℝ) + 1) / (m : ℝ) < c)
    {f : (Fin n → ℝ) → ℝ}
    (hf : ConvexOn ℝ (pzExpandedBox n c) f)
    (hrange : ∀ x ∈ pzExpandedBox n c, f x ∈ Set.Icc (0 : ℝ) 1)
    (I : Finset (Fin n → Fin m)) (hI : I.Nonempty) :
    ∃ v ∈ I, ∃ p : Fin n → ℝ,
      (∀ z ∈ pzExpandedBox n c,
        ConvexApproxND.tangentAffine f (pzFinGridPoint v) p z ≤ f z) ∧
      ∀ x ∈ pzGridCell v,
        |f x - ConvexApproxND.tangentAffine f (pzFinGridPoint v) p x| ≤
          4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
            (c * (I.card : ℝ)) := by
  classical
  let s := pzExpandedBox n c
  let delta : ℝ :=
    4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
      (c * (I.card : ℝ))
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hnpos : 0 < n := lt_of_lt_of_le (by omega) hn
  have hqnat : 0 < n + 1 := by omega
  have hcpos : 0 < c := by
    have : 0 < 2 * ((n : ℝ) + 1) / (m : ℝ) := by positivity
    linarith
  have hIcard : 0 < I.card := Finset.card_pos.mpr hI
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  let P : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) := fun x ↦
    if hx : x ∈ interior s then
      Classical.choose (exists_continuousLinear_subgradient_of_mem_interior hf hx)
    else 0
  have hPsupport (x : Fin n → ℝ) (hx : x ∈ interior s) :
      ∀ z ∈ s, f x + P x (z - x) ≤ f z := by
    simp only [P, dif_pos hx]
    exact Classical.choose_spec
      (exists_continuousLinear_subgradient_of_mem_interior hf hx)
  have hbaseInt (v : Fin n → Fin m) : pzFinGridPoint v ∈ interior s := by
    exact pzFinGridPoint_interior hm hcpos v
  have hcellInt (v : Fin n → Fin m) : pzGridCell v ⊆ interior s := by
    exact pzGridCell_subset_interior hm hcpos v
  have haxisInt (v : Fin n → Fin m) (i : Fin n) :
      pzFinGridPoint v + (((n : ℝ) + 1) / (m : ℝ)) • Pi.single i 1 ∈
        interior s := by
    exact pzFinGridPoint_axis_interior hm hc v i
  by_contra hgood
  have hbadPoint (v : Fin n → Fin m) (hv : v ∈ I) :
      ∃ y ∈ pzGridCell v,
        delta < supportError f (pzFinGridPoint v) (P (pzFinGridPoint v)) y := by
    let p := subgradientCoordinates (P (pzFinGridPoint v))
    have hsupp : ∀ z ∈ s,
        ConvexApproxND.tangentAffine f (pzFinGridPoint v) p z ≤ f z := by
      intro z hz
      have h := hPsupport (pzFinGridPoint v) (hbaseInt v) z hz
      rw [continuousLinear_eq_sum_subgradientCoordinates] at h
      simpa [p, ConvexApproxND.tangentAffine, Pi.sub_apply] using h
    have hnotGood : ¬ ∀ x ∈ pzGridCell v,
        |f x - ConvexApproxND.tangentAffine f (pzFinGridPoint v) p x| ≤ delta := by
      intro hg
      apply hgood
      exact ⟨v, hv, p, hsupp, hg⟩
    push_neg at hnotGood
    obtain ⟨y, hycell, hybad⟩ := hnotGood
    refine ⟨y, hycell, ?_⟩
    have hsupportY := hsupp y (interior_subset (hcellInt v hycell))
    rw [abs_of_nonneg (sub_nonneg.mpr hsupportY)] at hybad
    have heq : supportError f (pzFinGridPoint v) (P (pzFinGridPoint v)) y =
        f y - ConvexApproxND.tangentAffine f (pzFinGridPoint v) p y := by
      simp [supportError, ConvexApproxND.tangentAffine,
        continuousLinear_eq_sum_subgradientCoordinates, p, Pi.sub_apply]
    rwa [heq]
  have haxisExists (v : Fin n → Fin m) : ∃ i : Fin n, v ∈ I →
      P (pzFinGridPoint v) (Pi.single i 1) +
          delta / (((n : ℝ) + 1) / (m : ℝ)) <
        P (pzFinGridPoint v +
          (((n : ℝ) + 1) / (m : ℝ)) • Pi.single i 1) (Pi.single i 1) := by
    by_cases hv : v ∈ I
    · obtain ⟨y, hycell, hybad⟩ := hbadPoint v hv
      have hax := exists_axial_supportError_gt_of_bad hf
        (pzFinGridPoint v) y (P (pzFinGridPoint v)) (1 / (m : ℝ)) delta
        (one_div_pos.mpr hmreal) hdelta.le
        (fun i ↦ pzGridCell_coord hm hycell i)
        (fun i ↦ by
          simpa [div_eq_mul_inv] using interior_subset (haxisInt v i))
        (interior_subset (hbaseInt v)) hybad
      obtain ⟨i, hi⟩ := hax
      refine ⟨i, fun _hv ↦ ?_⟩
      have hq := hPsupport _ (haxisInt v i)
        (pzFinGridPoint v) (interior_subset (hbaseInt v))
      have hj := subgradient_coordinate_jump_of_axial_error f
        (pzFinGridPoint v) (P (pzFinGridPoint v))
        (P (pzFinGridPoint v +
          (((n : ℝ) + 1) / (m : ℝ)) • Pi.single i 1)) i
        (((n : ℝ) + 1) / (m : ℝ)) delta
        (div_pos (by positivity) hmreal) hq
      have hscale : ((n : ℝ) + 1) * (1 / (m : ℝ)) =
          ((n : ℝ) + 1) / (m : ℝ) := by ring
      rw [hscale] at hi
      exact hj hi
    · exact ⟨⟨0, hnpos⟩, fun h ↦ (hv h).elim⟩
  choose axis haxis using haxisExists
  obtain ⟨i, hiCount⟩ :=
    ConvexApproxND.exists_large_fiber I hI axis
  let A := I.filter fun v ↦ axis v = i
  have hAcard : I.card ≤ n * A.card := by simpa [A] using hiCount
  have hA : A.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hz
    have : A.card = 0 := Nat.eq_zero_of_not_pos hz
    rw [this, Nat.mul_zero] at hAcard
    omega
  let key : (Fin n → Fin m) →
      pzTransverseKey (m := m) i × Fin (n + 1) := fun v ↦
    (pzTransverse i v, ⟨(v i : ℕ) % (n + 1), Nat.mod_lt _ hqnat⟩)
  obtain ⟨⟨tr, r⟩, hkeyCount⟩ :=
    ConvexApproxND.exists_large_fiber A hA key
  let J := A.filter fun v ↦ key v = (tr, r)
  have hJCount : A.card ≤ (m ^ (n - 1) * (n + 1)) * J.card := by
    simpa [key, J, Fintype.card_prod] using hkeyCount
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hz
    have : J.card = 0 := Nat.eq_zero_of_not_pos hz
    rw [this, Nat.mul_zero] at hJCount
    have hAc : 0 < A.card := Finset.card_pos.mpr hA
    omega
  let positions : Finset ℕ := J.image fun v ↦ (v i : ℕ)
  have hposInj : Set.InjOn (fun v : Fin n → Fin m ↦ (v i : ℕ)) J := by
    intro v hv w hw heq
    have hvkey : key v = (tr, r) := (Finset.mem_filter.mp hv).2
    have hwkey : key w = (tr, r) := (Finset.mem_filter.mp hw).2
    apply funext
    intro j
    by_cases hji : j = i
    · subst j
      exact Fin.ext heq
    · have ht : pzTransverse i v = pzTransverse i w := by
        simpa [key] using congrArg Prod.fst (hvkey.trans hwkey.symm)
      exact congrFun ht ⟨j, hji⟩
  have hpositionsCard : positions.card = J.card := by
    exact Finset.card_image_of_injOn hposInj
  have hpositions : positions.Nonempty := hJ.image _
  let K := m + n
  let line : ℕ → Fin n → ℝ := fun a ↦
    pzGridPoint m (pzLineIndex i tr (min a K))
  let g : ℕ → ℝ := fun a ↦ P (line a) (Pi.single i 1)
  let Delta := delta / (((n : ℝ) + 1) / (m : ℝ))
  have hlineInt (a : ℕ) : line a ∈ interior s := by
    exact pzGridPoint_bounded_interior (K := 0) hm hc i tr (min a K)
      (by simp [K])
  have hgmono : Monotone g := by
    intro a b hab
    have hminle : min a K ≤ min b K := min_le_min hab le_rfl
    by_cases heq : min a K = min b K
    · simp [g, line, heq]
    · have hminlt : min a K < min b K := lt_of_le_of_ne hminle heq
      let d := min b K - min a K
      have hd : 0 < d := Nat.sub_pos_of_lt hminlt
      have ht : (0 : ℝ) < (d : ℝ) / (m : ℝ) := by positivity
      have hlineEq : line b = line a +
          ((d : ℝ) / (m : ℝ)) • Pi.single i 1 := by
        have hadd := pzLineIndex_add_axis i tr (min a K) d
        have hnat : min a K + d = min b K := by omega
        rw [hnat] at hadd
        exact hadd
      have hp := hPsupport (line a) (hlineInt a) (line b)
        (interior_subset (hlineInt b))
      have hq := hPsupport (line b) (hlineInt b) (line a)
        (interior_subset (hlineInt a))
      rw [hlineEq] at hp hq
      have hmono := subgradient_coordinate_mono f (line a) (P (line a))
        (P (line a + ((d : ℝ) / (m : ℝ)) • Pi.single i 1))
        i ((d : ℝ) / (m : ℝ)) ht hp hq
      simpa [g, hlineEq] using hmono
  have hjump (a : ℕ) (ha : a ∈ positions) :
      g a + Delta ≤ g (a + (n + 1)) := by
    obtain ⟨v, hvJ, rfl⟩ := Finset.mem_image.mp ha
    have hvA : v ∈ A := (Finset.mem_filter.mp hvJ).1
    have hvI : v ∈ I := (Finset.mem_filter.mp hvA).1
    have haxisEq : axis v = i := (Finset.mem_filter.mp hvA).2
    have hvkey : key v = (tr, r) := (Finset.mem_filter.mp hvJ).2
    have htr : pzTransverse i v = tr := by
      simpa [key] using congrArg Prod.fst hvkey
    have hva : (v i : ℕ) ≤ K := by
      dsimp [K]
      omega
    have hvaq : (v i : ℕ) + (n + 1) ≤ K := by
      dsimp [K]
      have := (v i).isLt
      omega
    have hbaseLine : pzGridPoint m (pzLineIndex i tr (v i)) =
        pzFinGridPoint v := by
      rw [← htr, pzLineIndex_transverse]
      rfl
    have hendLine : pzGridPoint m (pzLineIndex i tr ((v i : ℕ) + (n + 1))) =
        pzFinGridPoint v +
          (((n : ℝ) + 1) / (m : ℝ)) • Pi.single i 1 := by
      rw [pzLineIndex_add_axis, hbaseLine]
      norm_num only [Nat.cast_add, Nat.cast_one]
    have hj := haxis v hvI
    rw [haxisEq] at hj
    apply le_of_lt
    simpa [g, line, Delta, Nat.min_eq_left hva,
      Nat.min_eq_left hvaq, hbaseLine, hendLine] using hj
  have hresidue (a : ℕ) (ha : a ∈ positions) : a % (n + 1) = r := by
    obtain ⟨v, hvJ, rfl⟩ := Finset.mem_image.mp ha
    have hvkey : key v = (tr, r) := (Finset.mem_filter.mp hvJ).2
    have h := congrArg (fun z ↦ z.2.val) hvkey
    simpa [key] using h
  have hgBound (a : ℕ) (ha : a ≤ K) :
      g a ∈ Set.Icc (-2 / c) (2 / c) := by
    have hshift := pzGridPoint_halfShift_mem hm hc i tr a ha
    have hlineEq : line a = pzGridPoint m (pzLineIndex i tr a) := by
      simp [line, Nat.min_eq_left ha]
    have hb := subgradient_coordinate_mem_Icc (f := f) (s := s)
      (line a) (P (line a)) i
      (c / 2) (half_pos hcpos) hrange (interior_subset (hlineInt a))
      (by simpa [hlineEq] using hshift.1)
      (by simpa [hlineEq] using hshift.2)
      (hPsupport (line a) (hlineInt a))
    constructor
    · have := hb.1
      dsimp [g]
      convert this using 1 <;> field_simp [hcpos.ne']
    · have := hb.2
      dsimp [g]
      convert this using 1 <;> field_simp [hcpos.ne']
  have hlower (a : ℕ) (ha : a ∈ positions) : -2 / c ≤ g a := by
    obtain ⟨v, _hvJ, rfl⟩ := Finset.mem_image.mp ha
    exact (hgBound (v i) (by dsimp [K]; omega)).1
  have hupper (a : ℕ) (ha : a ∈ positions) :
      g (a + (n + 1)) ≤ 2 / c := by
    obtain ⟨v, _hvJ, rfl⟩ := Finset.mem_image.mp ha
    exact (hgBound ((v i : ℕ) + (n + 1)) (by
      dsimp [K]
      have := (v i).isLt
      omega)).2
  have hosc := card_mul_jump_le_oscillation hqnat positions hpositions r
    g Delta (-2 / c) (2 / c) hresidue hgmono hjump hlower hupper
  have hosc' : (positions.card : ℝ) * Delta ≤ 4 / c := by
    convert hosc using 1 <;> field_simp [hcpos.ne'] <;> ring
  have hcountNat : I.card ≤
      (n * (m ^ (n - 1) * (n + 1))) * positions.card := by
    calc
      I.card ≤ n * A.card := hAcard
      _ ≤ n * ((m ^ (n - 1) * (n + 1)) * J.card) :=
        Nat.mul_le_mul_left n hJCount
      _ = (n * (m ^ (n - 1) * (n + 1))) * positions.card := by
        rw [← hpositionsCard]
        simp [Nat.mul_assoc]
  have hcountReal : (I.card : ℝ) ≤
      ((n : ℝ) * ((m : ℝ) ^ (n - 1) * ((n : ℝ) + 1))) *
        (positions.card : ℝ) := by
    exact_mod_cast hcountNat
  have hpow : (m : ℝ) ^ (n - 1) = (m : ℝ) ^ (n - 2) * (m : ℝ) := by
    have hnsub : n - 1 = (n - 2) + 1 := by omega
    rw [hnsub, pow_succ]
  have hDelta : Delta = delta * (m : ℝ) / ((n : ℝ) + 1) := by
    dsimp [Delta]
    field_simp
  rw [hDelta] at hosc'
  have hposDelta : 0 ≤ (positions.card : ℝ) * delta := by positivity
  have hoscMul : (positions.card : ℝ) * delta * (m : ℝ) ≤
      4 * ((n : ℝ) + 1) / c := by
    have hqreal : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc
      (positions.card : ℝ) * delta * (m : ℝ) =
          ((positions.card : ℝ) *
            (delta * (m : ℝ) / ((n : ℝ) + 1))) *
              ((n : ℝ) + 1) := by field_simp
      _ ≤ (4 / c) * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hosc' hqreal.le
      _ = 4 * ((n : ℝ) + 1) / c := by ring
  have hdeltaCount : (I.card : ℝ) * delta ≤
      4 * (n : ℝ) * ((n : ℝ) + 1) ^ 2 *
        (m : ℝ) ^ (n - 2) / c := by
    have hmul := mul_le_mul_of_nonneg_right hcountReal hdelta.le
    rw [hpow] at hmul
    have hfactor : 0 ≤ (n : ℝ) * (m : ℝ) ^ (n - 2) *
        ((n : ℝ) + 1) := by positivity
    have hoscScaled := mul_le_mul_of_nonneg_left hoscMul hfactor
    calc
      (I.card : ℝ) * delta ≤
          ((n : ℝ) *
            ((m : ℝ) ^ (n - 2) * (m : ℝ) * ((n : ℝ) + 1))) *
              (positions.card : ℝ) * delta := hmul
      _ = ((n : ℝ) * (m : ℝ) ^ (n - 2) * ((n : ℝ) + 1)) *
          ((positions.card : ℝ) * delta * (m : ℝ)) := by ring
      _ ≤ ((n : ℝ) * (m : ℝ) ^ (n - 2) * ((n : ℝ) + 1)) *
          (4 * ((n : ℝ) + 1) / c) := hoscScaled
      _ = 4 * (n : ℝ) * ((n : ℝ) + 1) ^ 2 *
          (m : ℝ) ^ (n - 2) / c := by ring
  have hdeltaExact : (I.card : ℝ) * delta =
      4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) / c := by
    dsimp [delta]
    have hIc : (I.card : ℝ) ≠ 0 := by exact_mod_cast hIcard.ne'
    field_simp [hcpos.ne', hIc]
  rw [hdeltaExact] at hdeltaCount
  have hpowpos : 0 < (m : ℝ) ^ (n - 2) := by positivity
  have hqgap : (n : ℝ) < ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hcommon : 0 < 4 * ((n : ℝ) + 1) ^ 2 *
      (m : ℝ) ^ (n - 2) / c := by positivity
  have hleft : 4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) / c =
      ((n : ℝ) + 1) ^ 2 *
        (4 * ((n : ℝ) + 1) ^ 2 * (m : ℝ) ^ (n - 2) / c) := by ring
  have hright : 4 * (n : ℝ) * ((n : ℝ) + 1) ^ 2 *
      (m : ℝ) ^ (n - 2) / c =
      (n : ℝ) *
        (4 * ((n : ℝ) + 1) ^ 2 * (m : ℝ) ^ (n - 2) / c) := by ring
  rw [hleft, hright] at hdeltaCount
  have hstrict := mul_lt_mul_of_pos_right hqgap hcommon
  linarith

/-- The same approximation with the coefficient bound used in the PZ
iteration.  The bound follows directly from support at the two coordinate
test points at distance `c / 2`. -/
theorem exists_gridCell_tangentAffine_approximation_with_coeff_bound
    {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) {c : ℝ}
    (hc : 2 * ((n : ℝ) + 1) / (m : ℝ) < c)
    {f : (Fin n → ℝ) → ℝ}
    (hf : ConvexOn ℝ (pzExpandedBox n c) f)
    (hrange : ∀ x ∈ pzExpandedBox n c, f x ∈ Set.Icc (0 : ℝ) 1)
    (I : Finset (Fin n → Fin m)) (hI : I.Nonempty) :
    ∃ v ∈ I, ∃ p : Fin n → ℝ,
      (∀ z ∈ pzExpandedBox n c,
        ConvexApproxND.tangentAffine f (pzFinGridPoint v) p z ≤ f z) ∧
      (∀ i, |p i| ≤ 2 / c) ∧
      ∀ x ∈ pzGridCell v,
        |f x - ConvexApproxND.tangentAffine f (pzFinGridPoint v) p x| ≤
          4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
            (c * (I.card : ℝ)) := by
  obtain ⟨v, hvI, p, hsupp, hgood⟩ :=
    exists_gridCell_tangentAffine_approximation hn hm hc hf hrange I hI
  refine ⟨v, hvI, p, hsupp, ?_, hgood⟩
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hcpos : 0 < c := by
    have : 0 < 2 * ((n : ℝ) + 1) / (m : ℝ) := by positivity
    linarith
  have hbmem : pzFinGridPoint v ∈ pzExpandedBox n c :=
    interior_subset (pzFinGridPoint_interior hm hcpos v)
  have hfb := hrange (pzFinGridPoint v) hbmem
  intro i
  have hshift := pzFinGridPoint_halfShift_mem hm hc v i
  have hminus := hsupp
    (pzFinGridPoint v - (c / 2) •
      (Pi.single i (1 : ℝ) : Fin n → ℝ)) hshift.1
  have hplus := hsupp
    (pzFinGridPoint v + (c / 2) •
      (Pi.single i (1 : ℝ) : Fin n → ℝ)) hshift.2
  have hfminus := hrange _ hshift.1
  have hfplus := hrange _ hshift.2
  have hsumMinus :
      ∑ j, p j *
        ((pzFinGridPoint v - (c / 2) •
          (Pi.single i (1 : ℝ) : Fin n → ℝ)) j -
          pzFinGridPoint v j) = -p i * (c / 2) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      simp [hji]
    · simp
  have hsumPlus :
      ∑ j, p j *
        ((pzFinGridPoint v + (c / 2) •
          (Pi.single i (1 : ℝ) : Fin n → ℝ)) j -
          pzFinGridPoint v j) = p i * (c / 2) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      simp [hji]
    · simp
  have hminus' : f (pzFinGridPoint v) - p i * (c / 2) ≤
      f (pzFinGridPoint v - (c / 2) •
        (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    rw [ConvexApproxND.tangentAffine, hsumMinus] at hminus
    simpa [sub_eq_add_neg] using hminus
  have hplus' : f (pzFinGridPoint v) + p i * (c / 2) ≤
      f (pzFinGridPoint v + (c / 2) •
        (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    rw [ConvexApproxND.tangentAffine, hsumPlus] at hplus
    exact hplus
  rw [abs_le]
  constructor
  · rw [show -(2 / c) = (-2) / c by ring]
    apply (div_le_iff₀ hcpos).2
    nlinarith [hminus', hfb.1, hfminus.2]
  · apply (le_div_iff₀ hcpos).2
    nlinarith [hplus', hfb.1, hfplus.2]

/-- Concave form of the PZ grid approximation lemma, suited to upper
boundary graphs.  It is obtained by applying the convex theorem to `1 - h`.
-/
theorem exists_gridCell_tangentAffine_approximation_concave
    {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) {c : ℝ}
    (hc : 2 * ((n : ℝ) + 1) / (m : ℝ) < c)
    {h : (Fin n → ℝ) → ℝ}
    (hh : ConcaveOn ℝ (pzExpandedBox n c) h)
    (hrange : ∀ x ∈ pzExpandedBox n c, h x ∈ Set.Icc (0 : ℝ) 1)
    (I : Finset (Fin n → Fin m)) (hI : I.Nonempty) :
    ∃ v ∈ I, ∃ q : Fin n → ℝ,
      (∀ z ∈ pzExpandedBox n c,
        h z ≤ ConvexApproxND.tangentAffine h (pzFinGridPoint v) q z) ∧
      (∀ i, |q i| ≤ 2 / c) ∧
      ∀ x ∈ pzGridCell v,
        |h x - ConvexApproxND.tangentAffine h (pzFinGridPoint v) q x| ≤
          4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
            (c * (I.card : ℝ)) := by
  let f : (Fin n → ℝ) → ℝ := fun x ↦ 1 - h x
  have hf : ConvexOn ℝ (pzExpandedBox n c) f := by
    refine ⟨hh.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hconc := hh.2 hx hy ha hb hab
    dsimp [f]
    norm_num only [smul_eq_mul] at hconc ⊢
    nlinarith
  have hfrange : ∀ x ∈ pzExpandedBox n c, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    have hr := hrange x hx
    dsimp [f]
    constructor <;> linarith [hr.1, hr.2]
  obtain ⟨v, hvI, p, hsupp, hpbound, hgood⟩ :=
    exists_gridCell_tangentAffine_approximation_with_coeff_bound
      hn hm hc hf hfrange I hI
  let q : Fin n → ℝ := fun i ↦ -p i
  refine ⟨v, hvI, q, ?_, ?_, ?_⟩
  · intro z hz
    have hs := hsupp z hz
    have haff : ConvexApproxND.tangentAffine f (pzFinGridPoint v) p z =
        1 - ConvexApproxND.tangentAffine h (pzFinGridPoint v) q z := by
      simp only [ConvexApproxND.tangentAffine, f, q]
      simp_rw [neg_mul]
      rw [Finset.sum_neg_distrib]
      ring
    rw [haff] at hs
    dsimp [f] at hs
    linarith
  · intro i
    simpa [q] using hpbound i
  · intro x hx
    have hg := hgood x hx
    have haff : ConvexApproxND.tangentAffine f (pzFinGridPoint v) p x =
        1 - ConvexApproxND.tangentAffine h (pzFinGridPoint v) q x := by
      simp only [ConvexApproxND.tangentAffine, f, q]
      simp_rw [neg_mul]
      rw [Finset.sum_neg_distrib]
      ring
    have herr :
        f x - ConvexApproxND.tangentAffine f (pzFinGridPoint v) p x =
          -(h x - ConvexApproxND.tangentAffine h (pzFinGridPoint v) q x) := by
      rw [haff]
      dsimp [f]
      ring
    rw [herr, abs_neg] at hg
    exact hg

end

end Erdos186.PZ.ConvexDensity.Subgradient
