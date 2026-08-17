import ErdosProblems.Erdos874.Foundations

open scoped BigOperators

namespace Erdos874

noncomputable section

@[gcongr]
lemma restrictedSumset_mono {r : ℕ} {A B : Finset ℤ} (hAB : A ⊆ B) :
    restrictedSumset r A ⊆ restrictedSumset r B := by
  intro z hz
  obtain ⟨C, hCA, hCr, rfl⟩ := mem_restrictedSumset.mp hz
  exact mem_restrictedSumset.mpr ⟨C, hCA.trans hAB, hCr, rfl⟩

/-- Admissibility is inherited by subsets. -/
lemma IsAdmissible.mono {A B : Finset ℤ} (hA : IsAdmissible A) (hBA : B ⊆ A) :
    IsAdmissible B := by
  intro r s hr hs hrs
  exact (hA hr hs hrs).mono (restrictedSumset_mono hBA) (restrictedSumset_mono hBA)

private def affinePullback (u c : ℤ) (A B : Finset ℤ) : Finset ℤ :=
  A.filter fun x ↦ u * x + c ∈ B

private lemma affine_injective {u c : ℤ} (hu : u ≠ 0) :
    Function.Injective fun x : ℤ ↦ u * x + c := by
  intro x y hxy
  apply mul_left_cancel₀ hu
  exact add_right_cancel hxy

private lemma image_affinePullback {u c : ℤ} {A B : Finset ℤ} (hu : u ≠ 0)
    (hB : B ⊆ A.image fun x ↦ u * x + c) :
    (affinePullback u c A B).image (fun x ↦ u * x + c) = B := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hx).2
  · intro y hy
    obtain ⟨x, hxA, hxy⟩ := Finset.mem_image.mp (hB hy)
    subst y
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxA, hy⟩, rfl⟩

private lemma sum_image_affine (u c : ℤ) (hu : u ≠ 0) (C : Finset ℤ) :
    ∑ y ∈ C.image (fun x ↦ u * x + c), y =
      u * (∑ x ∈ C, x) + (C.card : ℤ) * c := by
  rw [Finset.sum_image]
  · rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp
  · exact (affine_injective hu).injOn

/-- Exact affine covariance of restricted sum layers.  The nonzero slope
hypothesis is precisely what ensures that distinct elements stay distinct. -/
theorem restrictedSumset_image_affine (A : Finset ℤ) (r : ℕ) (u c : ℤ) (hu : u ≠ 0) :
    restrictedSumset r (A.image fun x ↦ u * x + c) =
      (restrictedSumset r A).image fun z ↦ u * z + (r : ℤ) * c := by
  ext z
  constructor
  · intro hz
    obtain ⟨B, hBsub, hBcard, hBsum⟩ := mem_restrictedSumset.mp hz
    let C := affinePullback u c A B
    have himage : C.image (fun x ↦ u * x + c) = B :=
      image_affinePullback hu hBsub
    have hCsub : C ⊆ A := Finset.filter_subset _ _
    have hCcard : C.card = r := by
      rw [← hBcard, ← himage, Finset.card_image_of_injective _ (affine_injective hu)]
    apply Finset.mem_image.mpr
    refine ⟨∑ x ∈ C, x, mem_restrictedSumset.mpr ⟨C, hCsub, hCcard, rfl⟩, ?_⟩
    calc
      u * (∑ x ∈ C, x) + (r : ℤ) * c = ∑ y ∈ B, y := by
        rw [← himage, sum_image_affine u c hu, hCcard]
      _ = z := hBsum
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨C, hCsub, hCcard, hCsum⟩ := mem_restrictedSumset.mp hw
    refine mem_restrictedSumset.mpr
      ⟨C.image (fun x ↦ u * x + c), Finset.image_mono _ hCsub, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (affine_injective hu), hCcard]
    · rw [sum_image_affine u c hu, hCcard, hCsum]

/-- Translation changes every `r`-sum by exactly `r c`. -/
theorem restrictedSumset_image_add (A : Finset ℤ) (r : ℕ) (c : ℤ) :
    restrictedSumset r (A.image fun x ↦ x + c) =
      (restrictedSumset r A).image fun z ↦ z + (r : ℤ) * c := by
  simpa using restrictedSumset_image_affine A r 1 c one_ne_zero

/-- Nonzero dilation commutes with taking a restricted sum layer. -/
theorem restrictedSumset_image_mul (A : Finset ℤ) (r : ℕ) (u : ℤ) (hu : u ≠ 0) :
    restrictedSumset r (A.image fun x ↦ u * x) =
      (restrictedSumset r A).image fun z ↦ u * z := by
  simpa using restrictedSumset_image_affine A r u 0 hu

/-- Reflection negates every restricted sum. -/
theorem restrictedSumset_image_neg (A : Finset ℤ) (r : ℕ) :
    restrictedSumset r (A.image fun x ↦ -x) =
      (restrictedSumset r A).image fun z ↦ -z := by
  simpa using restrictedSumset_image_affine A r (-1) 0 (by omega)

/-- Nonzero dilation preserves and reflects admissibility. -/
theorem isAdmissible_image_mul_iff (A : Finset ℤ) (u : ℤ) (hu : u ≠ 0) :
    IsAdmissible (A.image fun x ↦ u * x) ↔ IsAdmissible A := by
  have hmul : Function.Injective fun z : ℤ ↦ u * z := by
    simpa using affine_injective (c := 0) hu
  constructor
  · intro h r s hr hs hrs
    rw [← Finset.disjoint_image hmul, ← restrictedSumset_image_mul A r u hu,
      ← restrictedSumset_image_mul A s u hu]
    exact h hr hs hrs
  · intro h r s hr hs hrs
    rw [restrictedSumset_image_mul A r u hu, restrictedSumset_image_mul A s u hu,
      Finset.disjoint_image hmul]
    exact h hr hs hrs

/-- Reflection preserves and reflects admissibility. -/
@[simp] theorem isAdmissible_image_neg_iff (A : Finset ℤ) :
    IsAdmissible (A.image fun x ↦ -x) ↔ IsAdmissible A := by
  simpa using isAdmissible_image_mul_iff A (-1) (by omega)

/-- Coarse endpoint bounds for every restricted sum.  They are sharp when
the chosen `lo` and `hi` are simultaneously attained by all selected terms. -/
theorem restrictedSumset_mem_bounds {A : Finset ℤ} {r : ℕ} {lo hi z : ℤ}
    (hlo : ∀ x ∈ A, lo ≤ x) (hhi : ∀ x ∈ A, x ≤ hi)
    (hz : z ∈ restrictedSumset r A) :
    (r : ℤ) * lo ≤ z ∧ z ≤ (r : ℤ) * hi := by
  obtain ⟨B, hBsub, hBcard, rfl⟩ := mem_restrictedSumset.mp hz
  constructor
  · calc
      (r : ℤ) * lo = ∑ x ∈ B, lo := by simp [hBcard]
      _ ≤ ∑ x ∈ B, x := Finset.sum_le_sum fun x hx ↦ hlo x (hBsub hx)
  · calc
      ∑ x ∈ B, x ≤ ∑ x ∈ B, hi := Finset.sum_le_sum fun x hx ↦ hhi x (hBsub hx)
      _ = (r : ℤ) * hi := by simp [hBcard]

private lemma add_index_le_of_strictMono {r : ℕ} (f : Fin r → ℤ) (hf : StrictMono f)
    (j : ℕ) (hj : j < r) : f ⟨0, Nat.zero_lt_of_lt hj⟩ + j ≤ f ⟨j, hj⟩ := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hj' : j < r := (Nat.lt_succ_self j).trans hj
      have hstep : f ⟨j, hj'⟩ + 1 ≤ f ⟨j + 1, hj⟩ := by
        exact_mod_cast hf (show (⟨j, hj'⟩ : Fin r) < ⟨j + 1, hj⟩ by simp)
      have ih' := ih hj'
      omega

/-- Sharp lower endpoint bound for `r` distinct integers bounded below by
`lo`.  The finite sum on the left is `0 + 1 + ⋯ + (r-1)`. -/
theorem restrictedSumset_mem_sharp_lower {A : Finset ℤ} {r : ℕ} {lo z : ℤ}
    (hlo : ∀ x ∈ A, lo ≤ x) (hz : z ∈ restrictedSumset r A) :
    (r : ℤ) * lo + ∑ j : Fin r, (j : ℕ) ≤ z := by
  obtain ⟨B, hBsub, hBcard, hBsum⟩ := mem_restrictedSumset.mp hz
  by_cases hr : r = 0
  · have hB : B = ∅ := Finset.card_eq_zero.mp (hBcard.trans hr)
    subst B
    have hz0 : z = 0 := by simpa using hBsum.symm
    subst z
    clear hBcard hz
    subst r
    simp
  · let e : Fin r ↪o ℤ := B.orderEmbOfFin hBcard
    have he0 : lo ≤ e ⟨0, Nat.pos_of_ne_zero hr⟩ :=
      hlo _ (hBsub (B.orderEmbOfFin_mem hBcard _))
    have he : ∀ j : Fin r, lo + (j : ℕ) ≤ e j := by
      intro j
      have hj := add_index_le_of_strictMono e e.strictMono j j.isLt
      calc
        lo + (j : ℕ) ≤ e ⟨0, Nat.pos_of_ne_zero hr⟩ + (j : ℕ) :=
          by simpa [add_comm] using add_le_add_right he0 ((j : ℕ) : ℤ)
        _ ≤ e j := by simpa using hj
    have henum : ∑ x ∈ B, x = ∑ j : Fin r, e j := by
      calc
        ∑ x ∈ B, x =
            ∑ x ∈ Finset.map (B.orderEmbOfFin hBcard).toEmbedding Finset.univ, x := by
              rw [B.map_orderEmbOfFin_univ hBcard]
        _ = ∑ j : Fin r, e j := by
          rw [Finset.sum_map]
          rfl
    calc
      (r : ℤ) * lo + ∑ j : Fin r, (j : ℕ) =
          ∑ j : Fin r, (lo + (j : ℕ)) := by
            rw [Finset.sum_add_distrib]
            simp
      _ ≤ ∑ j : Fin r, e j := Finset.sum_le_sum fun j _ ↦ he j
      _ = z := henum.symm.trans hBsum

/-- Sharp upper endpoint bound for `r` distinct integers bounded above by
`hi`. -/
theorem restrictedSumset_mem_sharp_upper {A : Finset ℤ} {r : ℕ} {hi z : ℤ}
    (hhi : ∀ x ∈ A, x ≤ hi) (hz : z ∈ restrictedSumset r A) :
    z ≤ (r : ℤ) * hi - ∑ j : Fin r, (j : ℕ) := by
  have hzneg : -z ∈ restrictedSumset r (A.image fun x ↦ -x) := by
    rw [restrictedSumset_image_neg]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hlo : ∀ y ∈ A.image (fun x ↦ -x), -hi ≤ y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact neg_le_neg (hhi x hx)
  have h := restrictedSumset_mem_sharp_lower hlo hzneg
  rw [mul_neg] at h
  linarith

/-! Auxiliary index path used in the elementary proof of the restricted-sum lower bound. -/

private def chainIndex (n r q s j : ℕ) : ℕ :=
  if j < r - q - 1 then j
  else if j = r - q - 1 then j + s
  else n - r + j

private lemma chainIndex_lt {n r q s j : ℕ} (hrn : r ≤ n) (hq : q < r)
    (hs : s < n - r) (hj : j < r) : chainIndex n r q s j < n := by
  unfold chainIndex
  split_ifs <;> omega

private lemma chainIndex_strictMono {n r q s : ℕ} (hrn : r ≤ n) (hq : q < r)
    (hs : s < n - r) : StrictMono fun j : Fin r ↦ chainIndex n r q s j := by
  intro i j hij
  simp only [chainIndex]
  split_ifs <;> omega

private lemma chainIndex_le_of_lex {n r q₁ q₂ s₁ s₂ j : ℕ}
    (hrn : r ≤ n) (hq₁ : q₁ < r) (hq₂ : q₂ < r)
    (hs₁ : s₁ < n - r) (hs₂ : s₂ < n - r) (hj : j < r)
    (hlex : q₁ < q₂ ∨ q₁ = q₂ ∧ s₁ ≤ s₂) :
    chainIndex n r q₁ s₁ j ≤ chainIndex n r q₂ s₂ j := by
  have hd : 0 < n - r := by omega
  unfold chainIndex
  split_ifs <;> omega

private lemma chainIndex_exists_lt_of_lex {n r q₁ q₂ s₁ s₂ : ℕ}
    (hrn : r ≤ n) (hq₁ : q₁ < r) (hq₂ : q₂ < r)
    (hs₁ : s₁ < n - r) (hs₂ : s₂ < n - r)
    (hlex : q₁ < q₂ ∨ q₁ = q₂ ∧ s₁ < s₂) :
    ∃ j : Fin r, chainIndex n r q₁ s₁ j < chainIndex n r q₂ s₂ j := by
  rcases hlex with hq | ⟨rfl, hs⟩
  · let j : Fin r := ⟨r - q₂, by omega⟩
    refine ⟨j, ?_⟩
    change chainIndex n r q₁ s₁ (r - q₂) < chainIndex n r q₂ s₂ (r - q₂)
    simp only [chainIndex]
    split_ifs <;> omega
  · let j : Fin r := ⟨r - q₁ - 1, by omega⟩
    refine ⟨j, ?_⟩
    change chainIndex n r q₁ s₁ (r - q₁ - 1) <
      chainIndex n r q₁ s₂ (r - q₁ - 1)
    simp only [chainIndex]
    split_ifs <;> omega

private def chainValue {n r : ℕ} (a : Fin n → ℤ) (hrn : r ≤ n)
    (q s : ℕ) (hq : q < r) (hs : s < n - r) : ℤ :=
  ∑ j : Fin r, a ⟨chainIndex n r q s j, chainIndex_lt hrn hq hs j.2⟩

private lemma chainValue_lt_of_lex {n r q₁ q₂ s₁ s₂ : ℕ}
    (a : Fin n ↪o ℤ) (hrn : r ≤ n) (hq₁ : q₁ < r) (hq₂ : q₂ < r)
    (hs₁ : s₁ < n - r) (hs₂ : s₂ < n - r)
    (hlex : q₁ < q₂ ∨ q₁ = q₂ ∧ s₁ < s₂) :
    chainValue a hrn q₁ s₁ hq₁ hs₁ < chainValue a hrn q₂ s₂ hq₂ hs₂ := by
  apply Finset.sum_lt_sum
  · intro j hj
    exact a.monotone (chainIndex_le_of_lex hrn hq₁ hq₂ hs₁ hs₂ j.2
      (hlex.elim Or.inl fun h ↦ Or.inr ⟨h.1, h.2.le⟩))
  · obtain ⟨j, hj⟩ := chainIndex_exists_lt_of_lex hrn hq₁ hq₂ hs₁ hs₂ hlex
    exact ⟨j, Finset.mem_univ j, a.strictMono hj⟩

private def chainValueAt {n r : ℕ} (a : Fin n → ℤ) (hrn : r ≤ n) (p : ℕ × ℕ) : ℤ :=
  if hq : p.1 < r then
    if hs : p.2 < n - r then chainValue a hrn p.1 p.2 hq hs else 0
  else 0

private lemma chainValueAt_injective {n r : ℕ} (a : Fin n ↪o ℤ) (hrn : r ≤ n) :
    Set.InjOn (chainValueAt a hrn) (Finset.range r ×ˢ Finset.range (n - r)) := by
  rintro ⟨q₁, s₁⟩ h₁ ⟨q₂, s₂⟩ h₂ heq
  change q₁ ∈ Finset.range r ∧ s₁ ∈ Finset.range (n - r) at h₁
  change q₂ ∈ Finset.range r ∧ s₂ ∈ Finset.range (n - r) at h₂
  simp only [Finset.mem_range] at h₁ h₂
  simp only [chainValueAt, dif_pos h₁.1, dif_pos h₁.2, dif_pos h₂.1,
    dif_pos h₂.2] at heq
  rcases lt_trichotomy q₁ q₂ with hq | hq | hq
  · exact ((chainValue_lt_of_lex a hrn h₁.1 h₂.1 h₁.2 h₂.2 (Or.inl hq)).ne heq).elim
  · subst q₂
    rcases lt_trichotomy s₁ s₂ with hs | hs | hs
    · exact ((chainValue_lt_of_lex a hrn h₁.1 h₂.1 h₁.2 h₂.2
        (Or.inr ⟨rfl, hs⟩)).ne heq).elim
    · simpa [hs]
    · exact ((chainValue_lt_of_lex a hrn h₂.1 h₁.1 h₂.2 h₁.2
        (Or.inr ⟨rfl, hs⟩)).ne heq.symm).elim
  · exact ((chainValue_lt_of_lex a hrn h₂.1 h₁.1 h₂.2 h₁.2
      (Or.inl hq)).ne heq.symm).elim

private def chainSubset {n r : ℕ} (a : Fin n ↪o ℤ) (hrn : r ≤ n)
    (q s : ℕ) (hq : q < r) (hs : s < n - r) : Finset ℤ :=
  Finset.univ.image fun j : Fin r ↦
    a ⟨chainIndex n r q s j, chainIndex_lt hrn hq hs j.2⟩

private lemma card_chainSubset {n r : ℕ} (a : Fin n ↪o ℤ) (hrn : r ≤ n)
    (q s : ℕ) (hq : q < r) (hs : s < n - r) :
    (chainSubset a hrn q s hq hs).card = r := by
  rw [chainSubset, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact (chainIndex_strictMono hrn hq hs).injective
      (congrArg Fin.val (a.injective hij))

private lemma sum_chainSubset {n r : ℕ} (a : Fin n ↪o ℤ) (hrn : r ≤ n)
    (q s : ℕ) (hq : q < r) (hs : s < n - r) :
    ∑ x ∈ chainSubset a hrn q s hq hs, x = chainValue a hrn q s hq hs := by
  rw [chainSubset, Finset.sum_image]
  · rfl
  · intro i hi j hj hij
    exact (chainIndex_strictMono hrn hq hs).injective
      (congrArg Fin.val (a.injective hij))

private lemma chainValue_mem_restrictedSumset {A : Finset ℤ} {r : ℕ} (hr : r ≤ A.card)
    (q s : ℕ) (hq : q < r) (hs : s < A.card - r) :
    chainValue (A.orderEmbOfFin rfl) hr q s hq hs ∈ restrictedSumset r A := by
  apply mem_restrictedSumset.mpr
  refine ⟨chainSubset (A.orderEmbOfFin rfl) hr q s hq hs, ?_,
    card_chainSubset _ _ _ _ _ _, sum_chainSubset _ _ _ _ _ _⟩
  intro x hx
  simp only [chainSubset, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨j, rfl⟩ := hx
  exact A.orderEmbOfFin_mem rfl _

private def terminalValue {n r : ℕ} (a : Fin n → ℤ) (hrn : r ≤ n) : ℤ :=
  ∑ j : Fin r, a ⟨n - r + j, by omega⟩

private lemma chainIndex_le_terminal {n r q s j : ℕ} (hrn : r ≤ n) (hq : q < r)
    (hs : s < n - r) (hj : j < r) : chainIndex n r q s j ≤ n - r + j := by
  unfold chainIndex
  split_ifs <;> omega

private lemma chainIndex_lt_terminal_at_pivot {n r q s : ℕ} (hrn : r ≤ n)
    (hq : q < r) (hs : s < n - r) :
    chainIndex n r q s (r - q - 1) < n - r + (r - q - 1) := by
  unfold chainIndex
  split_ifs <;> omega

private lemma chainValue_lt_terminal {n r q s : ℕ} (a : Fin n ↪o ℤ)
    (hrn : r ≤ n) (hq : q < r) (hs : s < n - r) :
    chainValue a hrn q s hq hs < terminalValue a hrn := by
  apply Finset.sum_lt_sum
  · intro j hj
    exact a.monotone (chainIndex_le_terminal hrn hq hs j.2)
  · let j : Fin r := ⟨r - q - 1, by omega⟩
    exact ⟨j, Finset.mem_univ j, a.strictMono (chainIndex_lt_terminal_at_pivot hrn hq hs)⟩

private def terminalSubset {n r : ℕ} (a : Fin n ↪o ℤ) (hrn : r ≤ n) : Finset ℤ :=
  Finset.univ.image fun j : Fin r ↦ a ⟨n - r + j, by omega⟩

private lemma terminalValue_mem_restrictedSumset {A : Finset ℤ} {r : ℕ} (hr : r ≤ A.card) :
    terminalValue (A.orderEmbOfFin rfl) hr ∈ restrictedSumset r A := by
  apply mem_restrictedSumset.mpr
  refine ⟨terminalSubset (A.orderEmbOfFin rfl) hr, ?_, ?_, ?_⟩
  · intro x hx
    simp only [terminalSubset, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    exact A.orderEmbOfFin_mem rfl _
  · rw [terminalSubset, Finset.card_image_of_injective]
    · simp
    · intro i j hij
      apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val ((A.orderEmbOfFin rfl).injective hij))
  · rw [terminalSubset, Finset.sum_image]
    · rfl
    · intro i hi j hj hij
      apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val ((A.orderEmbOfFin rfl).injective hij))

/-- The elementary sharp lower bound for sums of `r` distinct integers. -/
theorem card_restrictedSumset_lower_bound (A : Finset ℤ) (r : ℕ) (hr : r ≤ A.card) :
    r * (A.card - r) + 1 ≤ (restrictedSumset r A).card := by
  by_cases hd : A.card - r = 0
  · have hmem := terminalValue_mem_restrictedSumset (A := A) hr
    simpa [hd] using Finset.card_pos.mpr ⟨_, hmem⟩
  · let P := Finset.range r ×ˢ Finset.range (A.card - r)
    let f : ℕ × ℕ → ℤ := chainValueAt (A.orderEmbOfFin rfl) hr
    let C := P.image f
    have hCcard : C.card = r * (A.card - r) := by
      change (P.image f).card = _
      have hinj : Set.InjOn f P := by
        simpa [f, P] using chainValueAt_injective (A.orderEmbOfFin rfl) hr
      rw [Finset.card_image_of_injOn hinj]
      simp [P]
    have hCsub : C ⊆ restrictedSumset r A := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      simp only [P, Finset.mem_product, Finset.mem_range] at hp
      simpa [f, chainValueAt, hp.1, hp.2] using
        chainValue_mem_restrictedSumset hr p.1 p.2 hp.1 hp.2
    have htmem : terminalValue (A.orderEmbOfFin rfl) hr ∈ restrictedSumset r A :=
      terminalValue_mem_restrictedSumset hr
    have htC : terminalValue (A.orderEmbOfFin rfl) hr ∉ C := by
      intro ht
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp ht
      simp only [P, Finset.mem_product, Finset.mem_range] at hp
      exact (chainValue_lt_terminal (A.orderEmbOfFin rfl) hr hp.1 hp.2).ne
        (by simpa [f, chainValueAt, hp.1, hp.2] using heq)
    calc
      r * (A.card - r) + 1 = (insert (terminalValue (A.orderEmbOfFin rfl) hr) C).card := by
        rw [Finset.card_insert_of_notMem htC, hCcard]
      _ ≤ (restrictedSumset r A).card := Finset.card_le_card (Finset.insert_subset htmem hCsub)

end

end Erdos874
