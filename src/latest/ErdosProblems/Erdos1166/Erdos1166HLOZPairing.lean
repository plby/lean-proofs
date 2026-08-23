import ErdosProblems.Erdos1166.Erdos1166HLOZEventIdentity

namespace Erdos1166.HLOZPairing


abbrev Dir := Fin 4

def east : Dir := 0
def north : Dir := 1
def west : Dir := 2
def south : Dir := 3

def vec (d : Dir) : Site := ![(1, 0), (0, 1), (-1, 0), (0, -1)] d

def shift (x v : Site) : Site := (x.1 + v.1, x.2 + v.2)

def chessEven (x : Site) : Prop := Even (x.1 + x.2)

/-- The chessboard-parity domino tiling oriented from even sites in direction `d`. -/
def XPair (d : Dir) (x y : Site) : Prop :=
  (chessEven x ∧ y = shift x (vec d)) ∨
    (chessEven y ∧ x = shift y (vec d))

/-- The horizontal domino tiling whose left endpoints have even first coordinate. -/
def YPair (x y : Site) : Prop :=
  (Even x.1 ∧ y = shift x (vec east)) ∨
    (Even y.1 ∧ x = shift y (vec east))

/-- The horizontal domino tiling whose left endpoints have odd first coordinate. -/
def YPair' (x y : Site) : Prop :=
  (Odd x.1 ∧ y = shift x (vec east)) ∨
    (Odd y.1 ∧ x = shift y (vec east))

/-- No domino of the pairing `r` contains two sites of `A`. -/
def PairFree (r : Site → Site → Prop) (A : Finset Site) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ r x y

lemma vec_injective : Function.Injective vec := by
  intro d e h
  fin_cases d <;> fin_cases e <;> simp [vec] at h ⊢

lemma shift_vec_chessOdd (d : Dir) {x : Site} (hx : chessEven x) :
    ¬ chessEven (shift x (vec d)) := by
  rcases hx with ⟨k, hk⟩
  rintro ⟨l, hl⟩
  fin_cases d <;> simp [shift, vec] at hk hl ⊢ <;> omega

lemma shift_vec_chessEven_iff (d : Dir) (x : Site) :
    chessEven (shift x (vec d)) ↔ ¬ chessEven x := by
  constructor
  · intro hs hx
    exact shift_vec_chessOdd d hx hs
  · intro hx
    change ¬ Even (x.1 + x.2) at hx
    fin_cases d
    · change Even ((x.1 + 1) + (x.2 + 0))
      convert (Int.even_add_one (n := x.1 + x.2)).2 hx using 1 <;> ring
    · change Even ((x.1 + 0) + (x.2 + 1))
      convert (Int.even_add_one (n := x.1 + x.2)).2 hx using 1 <;> ring
    · change Even ((x.1 + -1) + (x.2 + 0))
      convert (Int.even_sub_one (n := x.1 + x.2)).2
        hx using 1 <;> ring
    · change Even ((x.1 + 0) + (x.2 + -1))
      convert (Int.even_sub_one (n := x.1 + x.2)).2
        hx using 1 <;> ring

lemma not_pairFree_X_iff (d : Dir) (A : Finset Site) :
    ¬ PairFree (XPair d) A ↔
      ∃ x ∈ A, chessEven x ∧ shift x (vec d) ∈ A := by
  constructor
  · intro h
    unfold PairFree at h
    simp only [not_forall, not_not] at h
    rcases h with ⟨x, hx, y, hy, hxy, hpair⟩
    rcases hpair with hpair | hpair
    · exact ⟨x, hx, hpair.1, hpair.2 ▸ hy⟩
    · exact ⟨y, hy, hpair.1, hpair.2 ▸ hx⟩
  · rintro ⟨x, hx, he, hxs⟩ hfree
    have hne : x ≠ shift x (vec d) := by
      intro h
      have := shift_vec_chessOdd d he
      exact this (h ▸ he)
    exact hfree x hx (shift x (vec d)) hxs hne (Or.inl ⟨he, rfl⟩)

lemma not_pairFree_Y_iff (A : Finset Site) :
    ¬ PairFree YPair A ↔
      ∃ x ∈ A, Even x.1 ∧ shift x (vec east) ∈ A := by
  constructor
  · intro h
    unfold PairFree at h
    simp only [not_forall, not_not] at h
    rcases h with ⟨x, hx, y, hy, hxy, hpair⟩
    rcases hpair with hpair | hpair
    · exact ⟨x, hx, hpair.1, hpair.2 ▸ hy⟩
    · exact ⟨y, hy, hpair.1, hpair.2 ▸ hx⟩
  · rintro ⟨x, hx, he, hxs⟩ hfree
    have hne : x ≠ shift x (vec east) := by
      intro h
      have := congrArg Prod.fst h
      simp [shift, vec, east] at this
    exact hfree x hx (shift x (vec east)) hxs hne (Or.inl ⟨he, rfl⟩)

lemma not_pairFree_Y'_iff (A : Finset Site) :
    ¬ PairFree YPair' A ↔
      ∃ x ∈ A, Odd x.1 ∧ shift x (vec east) ∈ A := by
  constructor
  · intro h
    unfold PairFree at h
    simp only [not_forall, not_not] at h
    rcases h with ⟨x, hx, y, hy, hxy, hpair⟩
    rcases hpair with hpair | hpair
    · exact ⟨x, hx, hpair.1, hpair.2 ▸ hy⟩
    · exact ⟨y, hy, hpair.1, hpair.2 ▸ hx⟩
  · rintro ⟨x, hx, he, hxs⟩ hfree
    have hne : x ≠ shift x (vec east) := by
      intro h
      have := congrArg Prod.fst h
      simp [shift, vec, east] at this
    exact hfree x hx (shift x (vec east)) hxs hne (Or.inl ⟨he, rfl⟩)

/-- Among the four chessboard-oriented and two column-oriented domino tilings,
one separates every four-element set of lattice sites. -/
theorem six_pairing_cover (A : Finset Site) (hA : A.card = 4) :
    (∃ d : Dir, PairFree (XPair d) A) ∨ PairFree YPair A ∨ PairFree YPair' A := by
  classical
  by_contra hcover
  have hX : ∀ d : Dir, ¬ PairFree (XPair d) A := by
    intro d hd
    exact hcover (Or.inl ⟨d, hd⟩)
  have hY : ¬ PairFree YPair A := by
    intro hy
    exact hcover (Or.inr (Or.inl hy))
  have hY' : ¬ PairFree YPair' A := by
    intro hy
    exact hcover (Or.inr (Or.inr hy))

  have hex : ∀ d : Dir, ∃ x ∈ A, chessEven x ∧ shift x (vec d) ∈ A :=
    fun d ↦ (not_pairFree_X_iff d A).mp (hX d)
  choose e heA heEven heTarget using hex

  let evenA := A.filter chessEven
  let oddA := A.filter (fun x ↦ ¬ chessEven x)
  let edge : Dir → Site × Site := fun d ↦ (e d, shift (e d) (vec d))

  have hedge_mem (d : Dir) : edge d ∈ evenA ×ˢ oddA := by
    simp only [Finset.mem_product]
    constructor
    · change e d ∈ A.filter chessEven
      simp only [Finset.mem_filter]
      exact ⟨heA d, heEven d⟩
    · change shift (e d) (vec d) ∈ A.filter (fun x ↦ ¬ chessEven x)
      simp only [Finset.mem_filter]
      exact ⟨heTarget d, shift_vec_chessOdd d (heEven d)⟩

  have hedge_inj : Function.Injective edge := by
    intro d₁ d₂ hedges
    have heq : e d₁ = e d₂ := congrArg Prod.fst hedges
    have htar : shift (e d₁) (vec d₁) = shift (e d₂) (vec d₂) :=
      congrArg Prod.snd hedges
    apply vec_injective
    apply Prod.ext
    · have h := congrArg Prod.fst htar
      simp only [shift] at h
      have hb := congrArg Prod.fst heq
      omega
    · have h := congrArg Prod.snd htar
      simp only [shift] at h
      have hb := congrArg Prod.snd heq
      omega

  have himage_sub : Finset.univ.image edge ⊆ evenA ×ˢ oddA := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with ⟨d, rfl⟩
    exact hedge_mem d

  have himage_card : (Finset.univ.image edge).card = 4 := by
    rw [Finset.card_image_of_injective _ hedge_inj]
    decide

  have hprod_ge : 4 ≤ evenA.card * oddA.card := by
    rw [← Finset.card_product]
    rw [← himage_card]
    exact Finset.card_le_card himage_sub

  have hpartition : evenA.card + oddA.card = 4 := by
    change (A.filter chessEven).card + (A.filter fun x ↦ ¬ chessEven x).card = 4
    rw [Finset.card_filter_add_card_filter_not]
    exact hA

  have heven_le : evenA.card ≤ 4 := by omega
  have heven_card : evenA.card = 2 := by
    have hc : evenA.card = 0 ∨ evenA.card = 1 ∨ evenA.card = 2 ∨
        evenA.card = 3 ∨ evenA.card = 4 := by omega
    rcases hc with h | h | h | h | h
    · rw [h] at hprod_ge
      norm_num at hprod_ge
    · rw [h] at hprod_ge hpartition
      omega
    · exact h
    · rw [h] at hprod_ge hpartition
      omega
    · rw [h] at hprod_ge
      norm_num at hprod_ge
      have hpos : 0 < oddA.card := Finset.card_pos.mpr hprod_ge
      omega
  have hodd_card : oddA.card = 2 := by omega

  have himage_eq : Finset.univ.image edge = evenA ×ˢ oddA := by
    apply Finset.eq_of_subset_of_card_le himage_sub
    rw [Finset.card_product, heven_card, hodd_card, himage_card]

  have complete {x y : Site} (hx : x ∈ evenA) (hy : y ∈ oddA) :
      ∃ d : Dir, e d = x ∧ shift (e d) (vec d) = y := by
    have hxy : (x, y) ∈ Finset.univ.image edge := by
      rw [himage_eq]
      exact Finset.mem_product.2 ⟨hx, hy⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxy
    rcases hxy with ⟨d, hd⟩
    exact ⟨d, congrArg Prod.fst hd, congrArg Prod.snd hd⟩

  clear hprod_ge heven_le hpartition

  have another {S : Finset Site} (hcard : S.card = 2) {x : Site} (hx : x ∈ S) :
      ∃ y ∈ S, y ≠ x := by
    by_contra hnone
    simp only [not_exists, not_and] at hnone
    have hsub : S ⊆ {x} := by
      intro y hy
      simp only [Finset.mem_singleton]
      by_contra hne
      exact hnone y hy hne
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega

  let a := e east
  let b := e west
  let r := shift a (vec east)
  let l := shift b (vec west)

  have ha : a ∈ evenA := (Finset.mem_product.mp (hedge_mem east)).1
  have hb : b ∈ evenA := (Finset.mem_product.mp (hedge_mem west)).1
  have hr : r ∈ oddA := (Finset.mem_product.mp (hedge_mem east)).2
  have hl : l ∈ oddA := (Finset.mem_product.mp (hedge_mem west)).2

  have hab : a ≠ b := by
    intro habeq
    rcases another heven_card ha with ⟨c, hc, hca⟩
    rcases complete hc hr with ⟨d₁, hd₁e, hd₁t⟩
    rcases complete hc hl with ⟨d₂, hd₂e, hd₂t⟩
    rw [hd₁e] at hd₁t
    rw [hd₂e] at hd₂t
    have hab₁ := congrArg Prod.fst habeq
    have hab₂ := congrArg Prod.snd habeq
    have h₁₁ := congrArg Prod.fst hd₁t
    have h₁₂ := congrArg Prod.snd hd₁t
    have h₂₁ := congrArg Prod.fst hd₂t
    have h₂₂ := congrArg Prod.snd hd₂t
    fin_cases d₁ <;> fin_cases d₂ <;>
      simp [a, b, r, l, shift, vec, east, west] at hab₁ hab₂ h₁₁ h₁₂ h₂₁ h₂₂ ⊢ <;>
      try omega
    apply hca
    apply Prod.ext
    · simpa [a, east] using h₁₁
    · simpa [a, east] using h₁₂

  have hrl : r ≠ l := by
    intro hrleq
    rcases another hodd_card hr with ⟨q, hq, hqr⟩
    rcases complete ha hq with ⟨d₁, hd₁e, hd₁t⟩
    rcases complete hb hq with ⟨d₂, hd₂e, hd₂t⟩
    rw [hd₁e] at hd₁t
    rw [hd₂e] at hd₂t
    have hrl₁ := congrArg Prod.fst hrleq
    have hrl₂ := congrArg Prod.snd hrleq
    have h₁₁ := congrArg Prod.fst hd₁t
    have h₁₂ := congrArg Prod.snd hd₁t
    have h₂₁ := congrArg Prod.fst hd₂t
    have h₂₂ := congrArg Prod.snd hd₂t
    fin_cases d₁ <;> fin_cases d₂ <;>
      simp [a, b, r, l, shift, vec, east, west] at hrl₁ hrl₂ h₁₁ h₁₂ h₂₁ h₂₂ ⊢ <;>
      try omega
    apply hqr
    apply Prod.ext
    · simpa [r, a, shift, vec, east] using h₁₁.symm
    · simpa [r, a, shift, vec, east] using h₁₂.symm

  have hleft : l.1 = a.1 := by
    rcases complete ha hl with ⟨d, hde, hdt⟩
    rw [hde] at hdt
    fin_cases d
    · exfalso
      apply hrl
      simpa [r, east] using hdt
    · have h := congrArg Prod.fst hdt
      simp [a, b, l, shift, vec, east, west] at h ⊢
      omega
    · exfalso
      apply hab
      apply Prod.ext
      · have h := congrArg Prod.fst hdt
        simp [a, b, l, shift, vec, east, west] at h ⊢
        omega
      · have h := congrArg Prod.snd hdt
        simp [a, b, l, shift, vec, east, west] at h ⊢
        omega
    · have h := congrArg Prod.fst hdt
      simp [a, b, l, shift, vec, east, west] at h ⊢
      omega

  have horizontal_left {z : Site} (hz : z ∈ A)
      (hzt : shift z (vec east) ∈ A) : z.1 = a.1 := by
    by_cases hze : chessEven z
    · have hzE : z ∈ evenA := by
        change z ∈ A.filter chessEven
        exact Finset.mem_filter.2 ⟨hz, hze⟩
      have hztO : shift z (vec east) ∈ oddA := by
        change shift z (vec east) ∈ A.filter (fun x ↦ ¬ chessEven x)
        exact Finset.mem_filter.2 ⟨hzt, shift_vec_chessOdd east hze⟩
      rcases complete hzE hztO with ⟨d, hde, hdt⟩
      rw [hde] at hdt
      have hd : d = east := by
        apply vec_injective
        apply Prod.ext
        · have h := congrArg Prod.fst hdt
          simp [shift] at h ⊢
          omega
        · have h := congrArg Prod.snd hdt
          simp [shift] at h ⊢
          omega
      have hea : e east = z := hd ▸ hde
      exact congrArg Prod.fst hea.symm
    · have hzO : z ∈ oddA := by
        change z ∈ A.filter (fun x ↦ ¬ chessEven x)
        exact Finset.mem_filter.2 ⟨hz, hze⟩
      have hztE : shift z (vec east) ∈ evenA := by
        change shift z (vec east) ∈ A.filter chessEven
        exact Finset.mem_filter.2 ⟨hzt, (shift_vec_chessEven_iff east z).2 hze⟩
      rcases complete hztE hzO with ⟨d, hde, hdt⟩
      rw [hde] at hdt
      have hd : d = west := by
        apply vec_injective
        apply Prod.ext
        · have h := congrArg Prod.fst hdt
          simp [shift, vec, east, west] at h ⊢
          omega
        · have h := congrArg Prod.snd hdt
          simp [shift, vec, east, west] at h ⊢
          omega
      have heb : e west = shift z (vec east) := hd ▸ hde
      calc
        z.1 = l.1 := by
          have h := congrArg Prod.fst heb
          simp [l, b, shift, vec, east, west] at h ⊢
          omega
        _ = a.1 := hleft

  rcases (not_pairFree_Y_iff A).mp hY with ⟨u, hu, hue, hut⟩
  rcases (not_pairFree_Y'_iff A).mp hY' with ⟨v, hv, hvo, hvt⟩
  have hua : u.1 = a.1 := horizontal_left hu hut
  have hva : v.1 = a.1 := horizontal_left hv hvt
  rw [hua] at hue
  rw [hva] at hvo
  exact Int.not_even_iff_odd.mpr hvo hue

/-- Embed the four chessboard pairings into the first four `Fin 6` indices. -/
def xIndex (d : Dir) : Fin 6 := ⟨d.1, by omega⟩

/-- Index of the horizontal pairing with even left endpoint. -/
def yIndex : Fin 6 := 4

/-- Index of the horizontal pairing with odd left endpoint. -/
def yIndex' : Fin 6 := 5

/-- The six domino pairings as a single `Fin 6`-indexed family. -/
def pairingRelation (i : Fin 6) : Site → Site → Prop :=
  match i.1 with
  | 0 => XPair east
  | 1 => XPair north
  | 2 => XPair west
  | 3 => XPair south
  | 4 => YPair
  | _ => YPair'

@[simp] theorem pairingRelation_xIndex (d : Dir) :
    pairingRelation (xIndex d) = XPair d := by
  fin_cases d <;> rfl

@[simp] theorem pairingRelation_yIndex : pairingRelation yIndex = YPair := rfl

@[simp] theorem pairingRelation_yIndex' : pairingRelation yIndex' = YPair' := rfl

/-- The six displayed indices exhaust `Fin 6`. -/
theorem fin6_eq_xIndex_or_yIndex (i : Fin 6) :
    (∃ d : Dir, i = xIndex d) ∨ i = yIndex ∨ i = yIndex' := by
  fin_cases i
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inl ⟨2, rfl⟩
  · exact Or.inl ⟨3, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The `i`th concrete pairing subevent at level `m`: at some time before
level `m + 1` is reached, four level-`m` sites can be selected with no two in
one domino of the `i`th tiling. -/
def pairingEvent (m : ℕ) (i : Fin 6) : Set (ℕ → Site) :=
  {s | ∃ n : ℕ, ∃ A : Finset Site,
    maxLocalTime s n < m + 1 ∧
    A ⊆ sitesAtLeastLevel s n m ∧
    A.card = 4 ∧ PairFree (pairingRelation i) A}

theorem measurableSet_pairingEvent (m : ℕ) (i : Fin 6) :
    MeasurableSet (pairingEvent m i) := by
  apply measurableSet_setOfPred.mpr
  change Measurable fun s : ℕ → Site ↦ ∃ n : ℕ, ∃ A : Finset Site,
    maxLocalTime s n < m + 1 ∧
    A ⊆ sitesAtLeastLevel s n m ∧
    A.card = 4 ∧ PairFree (pairingRelation i) A
  apply Measurable.exists
  intro n
  let f : (ℕ × Finset Site) → Prop := fun z ↦ ∃ A : Finset Site,
    z.1 < m + 1 ∧ A ⊆ z.2 ∧ A.card = 4 ∧ PairFree (pairingRelation i) A
  exact (measurable_of_countable f).comp
    ((measurable_maxLocalTime_eval n).prodMk
      (measurable_sitesAtLeastLevel_eval n m))

/-- Every concrete pairing event is a subevent of HLOZ's bad level event. -/
theorem pairingEvent_subset_hlozFourSitesReachLevelFirst (m : ℕ) (i : Fin 6) :
    pairingEvent m i ⊆ hlozFourSitesReachLevelFirst m := by
  rintro s ⟨n, A, hbelow, hsub, hcard, _hfree⟩
  refine ⟨n, ?_, hbelow⟩
  calc
    4 = A.card := hcard.symm
    _ ≤ (sitesAtLeastLevel s n m).card := Finset.card_le_card hsub

/-- The six concrete pairing subevents cover HLOZ's bad level event. -/
theorem hlozFourSitesReachLevelFirst_subset_iUnion_pairingEvent (m : ℕ) :
    hlozFourSitesReachLevelFirst m ⊆ ⋃ i : Fin 6, pairingEvent m i := by
  intro s hs
  rcases hs with ⟨n, hfour, hbelow⟩
  obtain ⟨A, hsub, hcard⟩ := Finset.exists_subset_card_eq hfour
  rcases six_pairing_cover A hcard with hX | hY | hY'
  · rcases hX with ⟨d, hd⟩
    apply Set.mem_iUnion_of_mem (xIndex d)
    exact ⟨n, A, hbelow, hsub, hcard, by simpa using hd⟩
  · apply Set.mem_iUnion_of_mem yIndex
    exact ⟨n, A, hbelow, hsub, hcard, by simpa using hY⟩
  · apply Set.mem_iUnion_of_mem yIndex'
    exact ⟨n, A, hbelow, hsub, hcard, by simpa using hY'⟩

/-! ### The exact first-four source pairing event -/

/-- A creation site at the (possibly infinite) direct level threshold is a
measurable function on canonical path space. -/
theorem measurable_levelCreationSite (m k : ℕ) :
    Measurable fun s : ℕ → Site ↦ levelCreationSite s m k := by
  change Measurable (MeasureTheory.stoppedValue HLOZFoundation.coordinateProcess
    (firstKSitesReachLevel m k))
  have hstop := isStoppingTime_firstKSitesReachLevel m k
  exact (MeasureTheory.measurable_stoppedValue
    HLOZFoundation.adapted_coordinateProcess.stronglyAdapted.isStronglyProgressive_of_discrete
    hstop).mono hstop.measurableSpace_le le_rfl

/-- The source finset `{L_m^1,\ldots,L_m^4}` written without an interval
image. -/
theorem levelCreationSitesUpTo_four (s : ℕ → Site) (m : ℕ) :
    levelCreationSitesUpTo s m 4 =
      {levelCreationSite s m 1, levelCreationSite s m 2,
        levelCreationSite s m 3, levelCreationSite s m 4} := by
  ext x
  simp only [levelCreationSitesUpTo, Finset.mem_image, Finset.mem_Icc,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, ⟨hi, hik⟩, rfl⟩
    interval_cases i <;> simp
  · intro hx
    rcases hx with hx | hx | hx | hx
    · exact ⟨1, by omega, hx.symm⟩
    · exact ⟨2, by omega, hx.symm⟩
    · exact ⟨3, by omega, hx.symm⟩
    · exact ⟨4, by omega, hx.symm⟩

/-- The exact pairing subevent in HLOZ Proposition 4.7: `M_m^4` occurs and
the first four level-`m` creation sites `L_m^1,\ldots,L_m^4` are free in the
chosen domino tiling.  This is smaller than `pairingEvent`, which retained an
arbitrary four-site subset as a convenient stronger interface. -/
def firstFourPairingEvent (m : ℕ) (i : Fin 6) : Set (ℕ → Site) :=
  hlozFourSitesReachLevelFirst m ∩
    {s | PairFree (pairingRelation i) (levelCreationSitesUpTo s m 4)}

theorem measurableSet_firstFourPairingEvent (m : ℕ) (i : Fin 6) :
    MeasurableSet (firstFourPairingEvent m i) := by
  apply (measurableSet_hlozFourSitesReachLevelFirst m).inter
  apply measurableSet_setOfPred.mpr
  have hcoords : Measurable fun s : ℕ → Site ↦
      (((levelCreationSite s m 1, levelCreationSite s m 2),
        levelCreationSite s m 3), levelCreationSite s m 4) :=
    (((measurable_levelCreationSite m 1).prodMk
      (measurable_levelCreationSite m 2)).prodMk
      (measurable_levelCreationSite m 3)).prodMk
      (measurable_levelCreationSite m 4)
  have hp : Measurable fun z : ((Site × Site) × Site) × Site ↦
      PairFree (pairingRelation i) {z.1.1.1, z.1.1.2, z.1.2, z.2} :=
    measurable_of_countable _
  convert hp.comp hcoords using 1
  funext s
  rw [levelCreationSitesUpTo_four]
  rfl

theorem hlozFourSitesReachLevelFirst_zero_empty :
    hlozFourSitesReachLevelFirst 0 = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨n, _hfour, hbelow⟩
  have hpos := maxLocalTime_pos s n
  omega

/-- The six exact first-four pairing subevents cover `M_m^4`. -/
theorem hlozFourSitesReachLevelFirst_subset_iUnion_firstFourPairingEvent (m : ℕ) :
    hlozFourSitesReachLevelFirst m ⊆ ⋃ i : Fin 6, firstFourPairingEvent m i := by
  intro s hs
  by_cases hm : m = 0
  · subst m
    rw [hlozFourSitesReachLevelFirst_zero_empty] at hs
    exact hs.elim
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hthreshold : s ∈ hlozThresholdTimeEvent m := by
    rw [hlozThresholdTimeEvent_eq]
    exact hs
  have hfinite : firstKSitesReachLevel m 4 s ≠ ⊤ := ne_top_of_lt hthreshold
  have hsites := sitesAtLeastLevel_at_threshold_eq_creationSites
    s m 4 hmpos (by omega) hfinite
  have hcardThreshold := card_at_firstKSitesReachLevel_eq
    s m 4 (by omega) hfinite
  have hcard : (levelCreationSitesUpTo s m 4).card = 4 := by
    rw [← hsites]
    exact hcardThreshold
  rcases six_pairing_cover (levelCreationSitesUpTo s m 4) hcard with hX | hY | hY'
  · rcases hX with ⟨d, hd⟩
    apply Set.mem_iUnion_of_mem (xIndex d)
    exact ⟨hs, by simpa using hd⟩
  · apply Set.mem_iUnion_of_mem yIndex
    exact ⟨hs, by simpa using hY⟩
  · apply Set.mem_iUnion_of_mem yIndex'
    exact ⟨hs, by simpa using hY'⟩

/-- The older arbitrary-four-subset event remains a valid stronger
interface. -/
theorem hlozPlanarConclusion_of_general_pairing_polynomial_bounds
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hpair : ∀ m i,
      simpleRandomWalkLaw (pairingEvent m i) ≤
        ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p)) :
    HLOZPlanarConclusion := by
  exact Erdos1166.hlozPlanarConclusion_of_six_pairing_cover
    pairingEvent measurableSet_pairingEvent
    hlozFourSitesReachLevelFirst_subset_iUnion_pairingEvent hC hp hpair

/-- Source-facing reduction: polynomial bounds for the six explicit domino
pairing subevents on the first four creation sites imply the planar HLOZ
conclusion. -/
theorem hlozPlanarConclusion_of_concrete_pairing_polynomial_bounds
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hpair : ∀ m i,
      simpleRandomWalkLaw (firstFourPairingEvent m i) ≤
        ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p)) :
    HLOZPlanarConclusion := by
  exact Erdos1166.hlozPlanarConclusion_of_six_pairing_cover
    firstFourPairingEvent measurableSet_firstFourPairingEvent
    hlozFourSitesReachLevelFirst_subset_iUnion_firstFourPairingEvent hC hp hpair

end HLOZPairing
end Erdos1166
