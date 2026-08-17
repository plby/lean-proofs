import ErdosProblems.Erdos220.Fundamental
import ErdosProblems.Erdos220.CompatibleStateEquiv

/-!
# Compatible prime coordinates

This file transports the arbitrary-support prime coordinate to the concrete
subtype of supported zero-sum vectors used by the compatible model.
-/

open scoped BigOperators

namespace Erdos220

noncomputable section

@[instance_reducible] private noncomputable def compatiblePrimeStateFintype
    (p : ℕ) [NeZero p]
    (J : Finset (Fin 6)) (hJ : J.Nonempty) : Fintype (CompatiblePrimeState p J) := by
  let j0 := J.min' hJ
  exact Fintype.ofEquiv (↑(J.erase j0) → ZMod p)
    (CompatiblePrimeState.compatiblePrimeStateEquivErase
      p J j0 (Finset.min'_mem J hJ)).symm

private noncomputable def compatibleSupportPerm (K J : Finset (Fin 6))
    (h : K.card = J.card) : Equiv.Perm (Fin 6) :=
  Classical.choose (Equiv.Perm.exists_map_finset_eq K J h)

private theorem compatibleSupportPerm_map (K J : Finset (Fin 6))
    (h : K.card = J.card) :
    K.map (compatibleSupportPerm K J h).toEmbedding = J :=
  Classical.choose_spec (Equiv.Perm.exists_map_finset_eq K J h)

private theorem permutedProject_zero_outside
    {p : ℕ} [NeZero p] (K J : Finset (Fin 6)) (hcard : K.card = J.card)
    {S : Type} (project : Fin 6 → S → ZMod p)
    (hzero : ∀ s i, i ∉ K → project i s = 0)
    (s : S) (i : Fin 6) (hi : i ∉ J) :
    project ((compatibleSupportPerm K J hcard).symm i) s = 0 := by
  apply hzero
  intro hmem
  apply hi
  rw [← compatibleSupportPerm_map K J hcard]
  exact Finset.mem_map.mpr
    ⟨_, hmem, (compatibleSupportPerm K J hcard).apply_symm_apply i⟩

private theorem sum_permutedProject
    {p : ℕ} [NeZero p] {S : Type} (project : Fin 6 → S → ZMod p)
    (σ : Equiv.Perm (Fin 6)) (s : S) (hsum : ∑ i, project i s = 0) :
    ∑ i, project (σ.symm i) s = 0 := by
  rw [Fintype.sum_equiv σ.symm (fun i ↦ project (σ.symm i) s)
    (fun i ↦ project i s) (fun _ ↦ rfl)]
  exact hsum

private theorem twoProject_zero {p : ℕ} [NeZero p] (s : ZMod p) (i : Fin 6)
    (hi : i ∉ ({0, 1} : Finset (Fin 6))) :
    twoConvolutionProject p i s = 0 := by
  fin_cases i <;> simp_all [twoConvolutionProject]

private theorem threeProject_zero {p : ℕ} [NeZero p]
    (s : ThreeConvolutionState p) (i : Fin 6)
    (hi : i ∉ ({0, 1, 2} : Finset (Fin 6))) :
    threeConvolutionProject p i s = 0 := by
  fin_cases i <;> simp_all [threeConvolutionProject]

private theorem fourProject_zero {p : ℕ} [NeZero p]
    (s : FourConvolutionState p) (i : Fin 6)
    (hi : i ∉ ({0, 1, 2, 3} : Finset (Fin 6))) :
    fourConvolutionProject p i s = 0 := by
  fin_cases i <;> simp_all [fourConvolutionProject]

private theorem fiveProject_zero {p : ℕ} [NeZero p]
    (s : FiveConvolutionState p) (i : Fin 6)
    (hi : i ∉ ({0, 1, 2, 3, 4} : Finset (Fin 6))) :
    fiveConvolutionProject p i s = 0 := by
  fin_cases i <;> simp_all [fiveConvolutionProject]

private theorem sixProject_zero {p : ℕ} [NeZero p]
    (s : SixConvolutionState p) (i : Fin 6)
    (hi : i ∉ ({0, 1, 2, 3, 4, 5} : Finset (Fin 6))) :
    sixConvolutionProject p i s = 0 := by
  fin_cases i <;> simp_all

private theorem twoProject_sum {p : ℕ} [NeZero p] (s : ZMod p) :
    ∑ i, twoConvolutionProject p i s = 0 := by
  simp [Fin.sum_univ_succ, twoConvolutionProject]

private theorem threeProject_sum {p : ℕ} [NeZero p] (s : ThreeConvolutionState p) :
    ∑ i, threeConvolutionProject p i s = 0 := by
  simp [Fin.sum_univ_succ, threeConvolutionProject]
  ring

private theorem fourProject_sum {p : ℕ} [NeZero p] (s : FourConvolutionState p) :
    ∑ i, fourConvolutionProject p i s = 0 := by
  simp [Fin.sum_univ_succ, fourConvolutionProject]
  ring

private theorem fiveProject_sum {p : ℕ} [NeZero p] (s : FiveConvolutionState p) :
    ∑ i, fiveConvolutionProject p i s = 0 := by
  simp [Fin.sum_univ_succ, fiveConvolutionProject]
  ring

private theorem sixProject_sum {p : ℕ} [NeZero p] (s : SixConvolutionState p) :
    ∑ i, sixConvolutionProject p i s = 0 := by
  simp [Fin.sum_univ_succ, sixConvolutionProject]
  ring

private theorem twoProject_injective {p : ℕ} [NeZero p] :
    Function.Injective (fun s : ZMod p ↦ fun i ↦ twoConvolutionProject p i s) := by
  intro s t h
  simpa [twoConvolutionProject] using congrFun h 0

private theorem threeProject_injective {p : ℕ} [NeZero p] :
    Function.Injective
      (fun s : ThreeConvolutionState p ↦ fun i ↦ threeConvolutionProject p i s) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp only [threeConvolutionProject] at h0 h2
  ext <;> simp_all

private theorem fourProject_injective {p : ℕ} [NeZero p] :
    Function.Injective
      (fun s : FourConvolutionState p ↦ fun i ↦ fourConvolutionProject p i s) := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [fourConvolutionProject] at h0 h2 h3
  ext <;> simp_all

private theorem fiveProject_injective {p : ℕ} [NeZero p] :
    Function.Injective
      (fun s : FiveConvolutionState p ↦ fun i ↦ fiveConvolutionProject p i s) := by
  rintro ⟨a, b, c, d⟩ ⟨e, f, g, h⟩ hv
  have h0 := congrFun hv 0
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  have h4 := congrFun hv 4
  simp only [fiveConvolutionProject] at h0 h2 h3 h4
  ext <;> simp_all

private theorem sixProject_injective {p : ℕ} [NeZero p] :
    Function.Injective
      (fun s : SixConvolutionState p ↦ fun i ↦ sixConvolutionProject p i s) := by
  rintro ⟨a, b, c, d, e⟩ ⟨f, g, h, k, l⟩ hv
  have h0 := congrFun hv 0
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  have h4 := congrFun hv 4
  have h5 := congrFun hv 5
  simp only [sixConvolutionProject] at h0 h2 h3 h4 h5
  ext <;> simp_all

private theorem permutedProject_injective
    {p : ℕ} [NeZero p] {S : Type} (project : Fin 6 → S → ZMod p)
    (σ : Equiv.Perm (Fin 6))
    (hinj : Function.Injective (fun s ↦ fun i ↦ project i s)) :
    Function.Injective (fun s ↦ fun i ↦ project (σ.symm i) s) := by
  intro s t h
  apply hinj
  funext i
  simpa using congrFun h (σ i)

private theorem permutedLocalBound
    {p : ℕ} [NeZero p] {S : Type} [Fintype S]
    (project : Fin 6 → S → ZMod p) (σ : Equiv.Perm (Fin 6)) (scale : ℝ)
    (hbound : ∀ f : Fin 6 → ZMod p → ℂ,
      ‖∑ s : S, ∏ i, f i (project i s)‖ ≤
        scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2)) :
    ∀ f : Fin 6 → ZMod p → ℂ,
      ‖∑ s : S, ∏ i, f i (project (σ.symm i) s)‖ ≤
        scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
  intro f
  have h := hbound (fun i ↦ f (σ i))
  calc
    ‖∑ s : S, ∏ i, f i (project (σ.symm i) s)‖ =
        ‖∑ s : S, ∏ i, f (σ i) (project i s)‖ := by
      congr 2
      funext s
      symm
      exact Fintype.prod_equiv σ _ _ (by simp)
    _ ≤ scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f (σ i) x‖ ^ 2) := h
    _ = scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
      congr 1
      exact Fintype.prod_equiv σ _ _ (by simp)

private theorem compatiblePrimeState_card [NeZero p]
    (J : Finset (Fin 6)) [Fintype (CompatiblePrimeState p J)] (hJ : J.Nonempty) :
    Fintype.card (CompatiblePrimeState p J) = p ^ (J.card - 1) := by
  let j0 := J.min' hJ
  rw [Fintype.card_congr (CompatiblePrimeState.compatiblePrimeStateEquivErase
    p J j0 (Finset.min'_mem J hJ))]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_coe]
  rw [Finset.card_erase_of_mem (Finset.min'_mem J hJ)]

private theorem fintypeElems_eq_univ {α : Type} (A : Fintype α) :
    A.elems = Finset.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    exact A.complete x

private noncomputable def compatibleStateEquivOfProject
    {p : ℕ} [NeZero p] {S : Type} [Fintype S] (J : Finset (Fin 6))
    [Fintype (CompatiblePrimeState p J)]
    (project : Fin 6 → S → ZMod p)
    (hzero : ∀ s i, i ∉ J → project i s = 0)
    (hsum : ∀ s, ∑ i, project i s = 0)
    (hinj : Function.Injective (fun s ↦ fun i ↦ project i s))
    (hcard : Fintype.card S = Fintype.card (CompatiblePrimeState p J)) :
    S ≃ CompatiblePrimeState p J := by
  let f : S → CompatiblePrimeState p J := fun s ↦
    ⟨fun i ↦ project i s, hzero s, hsum s⟩
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨fun s t h ↦ hinj (congrArg Subtype.val h), hcard⟩)

private theorem compatibleLocalBoundOfEquiv
    {p : ℕ} [NeZero p] {S : Type} [Fintype S] (J : Finset (Fin 6))
    [Fintype (CompatiblePrimeState p J)]
    (project : Fin 6 → S → ZMod p) (scale : ℝ)
    (hbound : ∀ f : Fin 6 → ZMod p → ℂ,
      ‖∑ s : S, ∏ i, f i (project i s)‖ ≤
        scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2))
    (e : S ≃ CompatiblePrimeState p J)
    (he : ∀ s i, (e s).1 i = project i s)
    (f : Fin 6 → ZMod p → ℂ) :
    ‖∑ a : CompatiblePrimeState p J, ∏ i, f i (a.1 i)‖ ≤
      scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
  calc
    _ = ‖∑ s : S, ∏ i, f i (project i s)‖ := by
      congr 1
      symm
      apply Fintype.sum_equiv e
      intro s
      simp only [he]
    _ ≤ _ := hbound f

private theorem compatiblePrimeCoordinate_localBound (p : ℕ) [NeZero p]
    (J : Finset (Fin 6)) (hJ : 2 ≤ J.card)
    [Fintype (CompatiblePrimeState p J)]
    (f : Fin 6 → ZMod p → ℂ) :
    ‖∑ a : CompatiblePrimeState p J, ∏ i, f i (a.1 i)‖ ≤
      Real.sqrt p ^ (J.card - 2) *
        ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
  classical
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  by_cases h2 : J.card = 2
  · let K : Finset (Fin 6) := {0, 1}
    have hcard : K.card = J.card := by simp [K, h2]
    let σ := compatibleSupportPerm K J hcard
    let project : Fin 6 → ZMod p → ZMod p :=
      fun i s ↦ twoConvolutionProject p (σ.symm i) s
    have hz : ∀ s i, i ∉ J → project i s = 0 := by
      intro s i hi
      exact permutedProject_zero_outside K J hcard (twoConvolutionProject p)
        twoProject_zero s i hi
    have hs : ∀ s, ∑ i, project i s = 0 := by
      intro s
      exact sum_permutedProject (twoConvolutionProject p) σ s (twoProject_sum s)
    have hinj : Function.Injective (fun s ↦ fun i ↦ project i s) :=
      permutedProject_injective (twoConvolutionProject p) σ twoProject_injective
    have hc : Fintype.card (ZMod p) = Fintype.card (CompatiblePrimeState p J) := by
      rw [compatiblePrimeState_card (p := p) J hJne, ZMod.card, h2]
      norm_num
    let e := compatibleStateEquivOfProject J project hz hs hinj hc
    refine compatibleLocalBoundOfEquiv J project (Real.sqrt p ^ (J.card - 2))
      ?_ e ?_ f
    · intro f
      apply permutedLocalBound (twoConvolutionProject p) σ _ _ f
      intro g
      simpa [h2, primeCoordinateTwo] using
        (primeCoordinateTwo p).localBound_with
          (by change Fintype (ZMod p); infer_instance)
          (fun _ ↦ by change Fintype (ZMod p); infer_instance) g
    · intro s i
      rfl
  · by_cases h3 : J.card = 3
    · let K : Finset (Fin 6) := {0, 1, 2}
      have hcard : K.card = J.card := by simp [K, h3]
      let σ := compatibleSupportPerm K J hcard
      let project : Fin 6 → ThreeConvolutionState p → ZMod p :=
        fun i s ↦ threeConvolutionProject p (σ.symm i) s
      have hz : ∀ s i, i ∉ J → project i s = 0 := by
        intro s i hi
        exact permutedProject_zero_outside K J hcard (threeConvolutionProject p)
          threeProject_zero s i hi
      have hs : ∀ s, ∑ i, project i s = 0 := by
        intro s
        exact sum_permutedProject (threeConvolutionProject p) σ s (threeProject_sum s)
      have hinj : Function.Injective (fun s ↦ fun i ↦ project i s) :=
        permutedProject_injective (threeConvolutionProject p) σ threeProject_injective
      have hc : Fintype.card (ThreeConvolutionState p) =
          Fintype.card (CompatiblePrimeState p J) := by
        rw [compatiblePrimeState_card (p := p) J hJne, h3]
        simp [ThreeConvolutionState, ZMod.card]
        ring
      let e := compatibleStateEquivOfProject J project hz hs hinj hc
      refine compatibleLocalBoundOfEquiv J project (Real.sqrt p ^ (J.card - 2))
        ?_ e ?_ f
      · intro f
        apply permutedLocalBound (threeConvolutionProject p) σ _ _ f
        intro g
        simpa [h3, primeCoordinateThree] using
          (primeCoordinateThree p).localBound_with
            (by change Fintype (ThreeConvolutionState p); infer_instance)
            (fun _ ↦ by change Fintype (ZMod p); infer_instance) g
      · intro s i
        rfl
    · by_cases h4 : J.card = 4
      · let K : Finset (Fin 6) := {0, 1, 2, 3}
        have hcard : K.card = J.card := by simp [K, h4]
        let σ := compatibleSupportPerm K J hcard
        let project : Fin 6 → FourConvolutionState p → ZMod p :=
          fun i s ↦ fourConvolutionProject p (σ.symm i) s
        have hz : ∀ s i, i ∉ J → project i s = 0 := by
          intro s i hi
          exact permutedProject_zero_outside K J hcard (fourConvolutionProject p)
            fourProject_zero s i hi
        have hs : ∀ s, ∑ i, project i s = 0 := by
          intro s
          exact sum_permutedProject (fourConvolutionProject p) σ s (fourProject_sum s)
        have hinj : Function.Injective (fun s ↦ fun i ↦ project i s) :=
          permutedProject_injective (fourConvolutionProject p) σ fourProject_injective
        have hc : Fintype.card (FourConvolutionState p) =
            Fintype.card (CompatiblePrimeState p J) := by
          rw [compatiblePrimeState_card (p := p) J hJne, h4]
          simp [FourConvolutionState, ZMod.card]
          ring
        let e := compatibleStateEquivOfProject J project hz hs hinj hc
        refine compatibleLocalBoundOfEquiv J project (Real.sqrt p ^ (J.card - 2))
          ?_ e ?_ f
        · intro f
          apply permutedLocalBound (fourConvolutionProject p) σ _ _ f
          intro g
          simpa [h4, primeCoordinateFour] using
            (primeCoordinateFour p).localBound_with
              (by change Fintype (FourConvolutionState p); infer_instance)
              (fun _ ↦ by change Fintype (ZMod p); infer_instance) g
        · intro s i
          rfl
      · by_cases h5 : J.card = 5
        · let K : Finset (Fin 6) := {0, 1, 2, 3, 4}
          have hcard : K.card = J.card := by simp [K, h5]
          let σ := compatibleSupportPerm K J hcard
          let project : Fin 6 → FiveConvolutionState p → ZMod p :=
            fun i s ↦ fiveConvolutionProject p (σ.symm i) s
          have hz : ∀ s i, i ∉ J → project i s = 0 := by
            intro s i hi
            exact permutedProject_zero_outside K J hcard (fiveConvolutionProject p)
              fiveProject_zero s i hi
          have hs : ∀ s, ∑ i, project i s = 0 := by
            intro s
            exact sum_permutedProject (fiveConvolutionProject p) σ s (fiveProject_sum s)
          have hinj : Function.Injective (fun s ↦ fun i ↦ project i s) :=
            permutedProject_injective (fiveConvolutionProject p) σ fiveProject_injective
          have hc : Fintype.card (FiveConvolutionState p) =
              Fintype.card (CompatiblePrimeState p J) := by
            rw [compatiblePrimeState_card (p := p) J hJne, h5]
            simp [FiveConvolutionState, ZMod.card]
            ring
          let e := compatibleStateEquivOfProject J project hz hs hinj hc
          refine compatibleLocalBoundOfEquiv J project (Real.sqrt p ^ (J.card - 2))
            ?_ e ?_ f
          · intro f
            apply permutedLocalBound (fiveConvolutionProject p) σ _ _ f
            intro g
            simpa [h5, primeCoordinateFive] using
              (primeCoordinateFive p).localBound_with
                (by change Fintype (FiveConvolutionState p); infer_instance)
                (fun _ ↦ by change Fintype (ZMod p); infer_instance) g
          · intro s i
            rfl
        · have h6 : J.card = 6 := by
            have hle : J.card ≤ 6 := by simpa using J.card_le_univ
            omega
          let K : Finset (Fin 6) := {0, 1, 2, 3, 4, 5}
          have hcard : K.card = J.card := by simp [K, h6]
          let σ := compatibleSupportPerm K J hcard
          let project : Fin 6 → SixConvolutionState p → ZMod p :=
            fun i s ↦ sixConvolutionProject p (σ.symm i) s
          have hz : ∀ s i, i ∉ J → project i s = 0 := by
            intro s i hi
            exact permutedProject_zero_outside K J hcard (sixConvolutionProject p)
              sixProject_zero s i hi
          have hs : ∀ s, ∑ i, project i s = 0 := by
            intro s
            exact sum_permutedProject (sixConvolutionProject p) σ s (sixProject_sum s)
          have hinj : Function.Injective (fun s ↦ fun i ↦ project i s) :=
            permutedProject_injective (sixConvolutionProject p) σ sixProject_injective
          have hc : Fintype.card (SixConvolutionState p) =
              Fintype.card (CompatiblePrimeState p J) := by
            rw [compatiblePrimeState_card (p := p) J hJne, h6]
            simp [SixConvolutionState, ZMod.card]
            ring
          let e := compatibleStateEquivOfProject J project hz hs hinj hc
          refine compatibleLocalBoundOfEquiv J project (Real.sqrt p ^ (J.card - 2))
            ?_ e ?_ f
          · intro f
            apply permutedLocalBound (sixConvolutionProject p) σ _ _ f
            intro g
            have hsqrt : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (by positivity)
            simpa [h6, primeCoordinateSix, pow_succ, hsqrt, mul_comm, mul_left_comm,
              mul_assoc] using
              (primeCoordinateSix p).localBound_with
                (by change Fintype (SixConvolutionState p); infer_instance)
                (fun _ ↦ by change Fintype (ZMod p); infer_instance) g
          · intro s i
            rfl

/-- The arbitrary-support prime coordinate with its state type replaced by
the concrete supported zero-sum vector subtype.  Its data fields are a
single record literal; only the proof of `localBound` performs support-card
case analysis. -/
@[reducible] noncomputable def compatiblePrimeCoordinate (p : ℕ) [NeZero p]
    (J : Finset (Fin 6)) (hJ : 2 ≤ J.card) : FundamentalCoordinate where
  State := CompatiblePrimeState p J
  stateFintype := compatiblePrimeStateFintype p J
    (Finset.card_pos.mp (by omega))
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := fun i a ↦ a.1 i
  scale := Real.sqrt p ^ (J.card - 2)
  scale_nonneg := pow_nonneg (Real.sqrt_nonneg _) _
  localBound := by
    intro f
    simp_rw [fintypeElems_eq_univ]
    exact @compatiblePrimeCoordinate_localBound p _ J hJ
      (compatiblePrimeStateFintype p J (Finset.card_pos.mp (by omega))) f

@[simp] theorem compatiblePrimeCoordinate_scale (p : ℕ) [NeZero p]
    (J : Finset (Fin 6)) (hJ : 2 ≤ J.card) :
    (compatiblePrimeCoordinate p J hJ).scale =
      Real.sqrt p ^ (J.card - 2) := by
  rfl

end

end Erdos220
