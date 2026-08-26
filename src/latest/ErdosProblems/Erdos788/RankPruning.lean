import ErdosProblems.Erdos788.ExtractorInterface

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pruning rank-deficient extractor seeds

The raw Trevisan construction gives one linear map for every binary seed but
does not make each map surjective.  Applying the raw extractor to the uniform
source shows that only a small fraction of seeds can be rank deficient.  This
file formalizes that finite argument and renormalizes the retained family.
-/

namespace Erdos788

open scoped BigOperators

/-- The range of a finite linear map, represented as a finset of its
codomain. -/
noncomputable def linearRangeFinset {p m r : ℕ} [Fact p.Prime]
    (F : FFVec p m →ₗ[ZMod p] FFVec p r) : Finset (FFVec p r) :=
  by
    classical
    exact Finset.univ.image (fun z : F.range ↦ z.val)

@[simp]
theorem mem_linearRangeFinset {p m r : ℕ} [Fact p.Prime]
    (F : FFVec p m →ₗ[ZMod p] FFVec p r) (z : FFVec p r) :
    z ∈ linearRangeFinset F ↔ z ∈ F.range := by
  classical
  constructor
  · intro hz
    rw [linearRangeFinset, Finset.mem_image] at hz
    obtain ⟨w, _hw, rfl⟩ := hz
    exact w.property
  · intro hz
    rw [linearRangeFinset, Finset.mem_image]
    exact ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩

theorem card_linearRangeFinset {p m r : ℕ} [Fact p.Prime]
    (F : FFVec p m →ₗ[ZMod p] FFVec p r) :
    (linearRangeFinset F).card =
      p ^ Module.finrank (ZMod p) F.range := by
  classical
  calc
    (linearRangeFinset F).card = Fintype.card F.range := by
      rw [linearRangeFinset, Finset.card_image_of_injective]
      · exact Finset.card_univ
      · exact Subtype.val_injective
    _ = Nat.card F.range := Nat.card_eq_fintype_card.symm
    _ = p ^ Module.finrank (ZMod p) F.range := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := F.range),
        Nat.card_zmod]

/-- A non-surjective map to `ᵓ_p^r` has image of size at most
`p^(r-1)`. -/
theorem card_linearRangeFinset_le_of_not_surjective
    {p m r : ℕ} [Fact p.Prime] (hp : 0 < p)
    (F : FFVec p m →ₗ[ZMod p] FFVec p r)
    (hF : ¬Function.Surjective F) :
    (linearRangeFinset F).card ≤ p ^ (r - 1) := by
  have hrange_ne : F.range ≠ ⊤ := by
    intro hrange
    exact hF (LinearMap.range_eq_top.mp hrange)
  have hrange_lt : F.range < ⊤ := lt_top_iff_ne_top.mpr hrange_ne
  have hfinrank := Submodule.finrank_lt_finrank_of_lt hrange_lt
  have htop : Module.finrank (ZMod p)
      (⊤ : Submodule (ZMod p) (FFVec p r)) = r := by
    rw [finrank_top, Module.finrank_fintype_fun_eq_card]
    simp
  rw [htop] at hfinrank
  rw [card_linearRangeFinset]
  exact Nat.pow_le_pow_right hp (by omega)

/-- The pushforward of the uniform source is supported on the linear range. -/
theorem map_uniform_mass_eq_zero_of_notMem_linearRange
    {p m r : ℕ} [Fact p.Prime]
    (F : FFVec p m →ₗ[ZMod p] FFVec p r) {z : FFVec p r}
    (hz : z ∉ linearRangeFinset F) :
    ((FinDist.uniform (FFVec p m)).map F).mass z = 0 := by
  rw [FinDist.map_mass]
  apply Finset.sum_eq_zero
  intro x hx
  have hFx : F x = z := (Finset.mem_filter.mp hx).2
  have hzrange : z ∈ linearRangeFinset F := by
    rw [mem_linearRangeFinset]
    exact ⟨x, hFx⟩
  exact (hz hzrange).elim

/-- In odd prime characteristic, every rank-deficient fixed-seed map sends
the uniform source to a distribution at total variation at least `2/3` from
uniform. -/
theorem two_thirds_le_tv_map_uniform_of_not_surjective
    {p m r : ℕ} [Fact p.Prime] (hp : 2 < p) (hr : 0 < r)
    (F : FFVec p m →ₗ[ZMod p] FFVec p r)
    (hF : ¬Function.Surjective F) :
    (2 / 3 : ℝ) ≤
      ((FinDist.uniform (FFVec p m)).map F).tv
        (FinDist.uniform (FFVec p r)) := by
  have hp0 : 0 < p := by omega
  let T := linearRangeFinset F
  have hTcard : T.card ≤ p ^ (r - 1) :=
    card_linearRangeFinset_le_of_not_surjective hp0 F hF
  have hpow : p ^ (r - 1) * p = p ^ r := by
    rw [← pow_succ]
    congr 1
    omega
  have hthree : 3 * T.card ≤ p ^ r := by
    calc
      3 * T.card ≤ p * p ^ (r - 1) :=
        Nat.mul_le_mul (by omega) hTcard
      _ = p ^ r := by rw [Nat.mul_comm, hpow]
  have hpowR : (0 : ℝ) < (p ^ r : ℕ) := by
    exact_mod_cast pow_pos hp0 r
  have hthreeR : (3 : ℝ) * T.card ≤ (p ^ r : ℕ) := by
    exact_mod_cast hthree
  have hratio : (T.card : ℝ) / (p ^ r : ℕ) ≤ 1 / 3 := by
    apply (div_le_iff₀ hpowR).2
    nlinarith
  have hsupport : ∀ z, z ∉ T →
      ((FinDist.uniform (FFVec p m)).map F).mass z = 0 := by
    intro z hz
    exact map_uniform_mass_eq_zero_of_notMem_linearRange F hz
  have htv := FinDist.tv_uniform_ge_one_sub_support
    ((FinDist.uniform (FFVec p m)).map F) T hsupport
  rw [fintypeCard_ffVec p r] at htv
  nlinarith

/-- A raw family before rank pruning. -/
structure RawLinearExtractorFamily (p r d s : ℕ) [Fact p.Prime] where
  Seed : Type
  [seedFintype : Fintype Seed]
  [seedDecidableEq : DecidableEq Seed]
  [seedNonempty : Nonempty Seed]
  card_seed_le : Fintype.card Seed ≤ p ^ d
  map : Seed → FFVec p (2 * r) →ₗ[ZMod p] FFVec p r
  extracts : ∀ P : FinDist (FFVec p (2 * r)),
    P.PointBound (p ^ (r + s)) →
      (Fintype.card Seed : ℝ)⁻¹ *
          ∑ y : Seed, (P.map (map y)).tv (FinDist.uniform (FFVec p r)) ≤
        1 / 20

attribute [instance] RawLinearExtractorFamily.seedFintype
  RawLinearExtractorFamily.seedDecidableEq
  RawLinearExtractorFamily.seedNonempty

/-- Seeds whose fixed-seed map has full rank. -/
noncomputable def surjectiveSeeds {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) : Finset E.Seed := by
  classical
  exact Finset.univ.filter fun y ↦ Function.Surjective (E.map y)

/-- Seeds whose fixed-seed map is rank deficient. -/
noncomputable def nonsurjectiveSeeds {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) : Finset E.Seed := by
  classical
  exact Finset.univ.filter fun y ↦ ¬Function.Surjective (E.map y)

@[simp]
theorem mem_surjectiveSeeds {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) (y : E.Seed) :
    y ∈ surjectiveSeeds E ↔ Function.Surjective (E.map y) := by
  classical
  simp [surjectiveSeeds]

@[simp]
theorem mem_nonsurjectiveSeeds {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) (y : E.Seed) :
    y ∈ nonsurjectiveSeeds E ↔ ¬Function.Surjective (E.map y) := by
  classical
  simp [nonsurjectiveSeeds]

theorem card_surjectiveSeeds_add_card_nonsurjectiveSeeds
    {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) :
    (surjectiveSeeds E).card + (nonsurjectiveSeeds E).card =
      Fintype.card E.Seed := by
  classical
  simpa [surjectiveSeeds, nonsurjectiveSeeds] using!
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset E.Seed))
      (fun y ↦ Function.Surjective (E.map y)))

/-- The retained seed type. -/
def SurjectiveSeed {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) :=
  {y : E.Seed // Function.Surjective (E.map y)}

noncomputable instance surjectiveSeedFintype
    {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) : Fintype (SurjectiveSeed E) := by
  classical
  exact Subtype.fintype fun y : E.Seed ↦ Function.Surjective (E.map y)

theorem card_surjectiveSeed {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) :
    Fintype.card (SurjectiveSeed E) = (surjectiveSeeds E).card := by
  classical
  simpa [SurjectiveSeed, surjectiveSeeds] using!
    (Fintype.card_subtype fun y : E.Seed ↦ Function.Surjective (E.map y))

/-- Remove the averaging denominator from the raw extractor guarantee. -/
theorem RawLinearExtractorFamily.total_error_le_card_div_twenty
    {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s)
    (P : FinDist (FFVec p (2 * r)))
    (hP : P.PointBound (p ^ (r + s))) :
    ∑ y : E.Seed, (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) ≤
      (Fintype.card E.Seed : ℝ) / 20 := by
  have hraw := E.extracts P hP
  have hcardpos : (0 : ℝ) < Fintype.card E.Seed := by
    exact_mod_cast Fintype.card_pos
  have hcardne : (Fintype.card E.Seed : ℝ) ≠ 0 := ne_of_gt hcardpos
  calc
    ∑ y : E.Seed, (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) =
        (Fintype.card E.Seed : ℝ) *
          ((Fintype.card E.Seed : ℝ)⁻¹ *
            ∑ y : E.Seed,
              (P.map (E.map y)).tv (FinDist.uniform (FFVec p r))) := by
          rw [← mul_assoc, mul_inv_cancel₀ hcardne, one_mul]
    _ ≤ (Fintype.card E.Seed : ℝ) * (1 / 20 : ℝ) :=
      mul_le_mul_of_nonneg_left hraw hcardpos.le
    _ = (Fintype.card E.Seed : ℝ) / 20 := by ring

/-- The uniform source has enough min-entropy for the raw guarantee whenever
`r+s ≤ 2r`. -/
theorem uniform_source_pointBound_of_add_le_two_mul
    {p r s : ℕ} [Fact p.Prime] (hp : 2 < p) (hrs : r + s ≤ 2 * r) :
    (FinDist.uniform (FFVec p (2 * r))).PointBound (p ^ (r + s)) := by
  have hp0 : 0 < p := by omega
  have hfull : (FinDist.uniform (FFVec p (2 * r))).PointBound (p ^ (2 * r)) := by
    simpa only [fintypeCard_ffVec] using!
      (FinDist.uniform_pointBound (α := FFVec p (2 * r)))
  exact FinDist.pointBound_mono (pow_pos hp0 _) (Nat.pow_le_pow_right hp0 hrs) hfull

/-- At most a `3/40` fraction of raw seeds are rank deficient. -/
theorem forty_mul_card_nonsurjectiveSeeds_le_three_mul_card
    {p r d s : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hrs : r + s ≤ 2 * r)
    (E : RawLinearExtractorFamily p r d s) :
    40 * (nonsurjectiveSeeds E).card ≤ 3 * Fintype.card E.Seed := by
  classical
  let P : FinDist (FFVec p (2 * r)) := FinDist.uniform (FFVec p (2 * r))
  have hpoint : P.PointBound (p ^ (r + s)) := by
    exact uniform_source_pointBound_of_add_le_two_mul hp hrs
  have hbadPoint : ∀ y ∈ nonsurjectiveSeeds E, (2 / 3 : ℝ) ≤
      (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) := by
    intro y hy
    exact two_thirds_le_tv_map_uniform_of_not_surjective hp hr (E.map y)
      ((mem_nonsurjectiveSeeds E y).mp hy)
  have hbadLower : ((nonsurjectiveSeeds E).card : ℝ) * (2 / 3 : ℝ) ≤
      ∑ y ∈ nonsurjectiveSeeds E,
        (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) := by
    calc
      ((nonsurjectiveSeeds E).card : ℝ) * (2 / 3 : ℝ) =
          ∑ y ∈ nonsurjectiveSeeds E, (2 / 3 : ℝ) := by simp
      _ ≤ ∑ y ∈ nonsurjectiveSeeds E,
          (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) :=
        Finset.sum_le_sum hbadPoint
  have hbadLeTotal :
      (∑ y ∈ nonsurjectiveSeeds E,
          (P.map (E.map y)).tv (FinDist.uniform (FFVec p r))) ≤
        ∑ y : E.Seed,
          (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro y _hy _hbad
    exact FinDist.tv_nonneg _ _
  have htotal :
      (∑ y : E.Seed,
          (P.map (E.map y)).tv (FinDist.uniform (FFVec p r))) ≤
        (Fintype.card E.Seed : ℝ) / 20 :=
    E.total_error_le_card_div_twenty P hpoint
  have hbadReal : (40 : ℝ) * (nonsurjectiveSeeds E).card ≤
      3 * Fintype.card E.Seed := by
    nlinarith [hbadLower.trans hbadLeTotal]
  exact_mod_cast hbadReal

/-- Consequently at least a `37/40` fraction of raw seeds are retained. -/
theorem thirty_seven_mul_card_le_forty_mul_card_surjectiveSeeds
    {p r d s : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hrs : r + s ≤ 2 * r)
    (E : RawLinearExtractorFamily p r d s) :
    37 * Fintype.card E.Seed ≤ 40 * (surjectiveSeeds E).card := by
  have hbad := forty_mul_card_nonsurjectiveSeeds_le_three_mul_card hp hr hrs E
  have hpartition := card_surjectiveSeeds_add_card_nonsurjectiveSeeds E
  omega

theorem nonempty_surjectiveSeed
    {p r d s : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hrs : r + s ≤ 2 * r)
    (E : RawLinearExtractorFamily p r d s) :
    Nonempty (SurjectiveSeed E) := by
  have hgood := thirty_seven_mul_card_le_forty_mul_card_surjectiveSeeds hp hr hrs E
  have hall : 0 < Fintype.card E.Seed := Fintype.card_pos
  have hcard : 0 < Fintype.card (SurjectiveSeed E) := by
    rw [card_surjectiveSeed]
    omega
  exact Fintype.card_pos_iff.mp hcard

/-- Prune every rank-deficient seed and renormalize the extractor average.
The retained average is at most `2/37`, hence strictly below `1/3`. -/
theorem prune_rank_deficient_seeds
    {p r d s : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hrs : r + s ≤ 2 * r)
    (E : RawLinearExtractorFamily p r d s) :
    Nonempty (LinearExtractorFamily p r d s) := by
  classical
  letI : Nonempty (SurjectiveSeed E) := nonempty_surjectiveSeed hp hr hrs E
  refine ⟨{
    Seed := SurjectiveSeed E
    seedFintype := inferInstance
    seedDecidableEq := inferInstance
    seedNonempty := inferInstance
    card_seed_le := ?_
    map := fun y ↦ E.map y.val
    surjective := fun y ↦ y.property
    extracts := ?_ }⟩
  · exact (Fintype.card_subtype_le fun y : E.Seed ↦
      Function.Surjective (E.map y)).trans E.card_seed_le
  · intro P hP
    let loss : E.Seed → ℝ := fun y ↦
      (P.map (E.map y)).tv (FinDist.uniform (FFVec p r))
    have htotal : ∑ y : E.Seed, loss y ≤
        (Fintype.card E.Seed : ℝ) / 20 := by
      exact E.total_error_le_card_div_twenty P hP
    have hsumEq : (∑ y : SurjectiveSeed E, loss y.val) =
        ∑ y ∈ (Finset.univ : Finset E.Seed) with
          Function.Surjective (E.map y), loss y := by
      simpa [SurjectiveSeed] using!
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset E.Seed)) loss
          (p := fun y ↦ Function.Surjective (E.map y)))
    have hretainedLeAll : (∑ y : SurjectiveSeed E, loss y.val) ≤
        ∑ y : E.Seed, loss y := by
      rw [hsumEq]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro y _hy _hgood
      exact FinDist.tv_nonneg _ _
    have hretained : (∑ y : SurjectiveSeed E, loss y.val) ≤
        (Fintype.card E.Seed : ℝ) / 20 :=
      hretainedLeAll.trans htotal
    have hgoodNat :=
      thirty_seven_mul_card_le_forty_mul_card_surjectiveSeeds hp hr hrs E
    have hgoodNat' : 37 * Fintype.card E.Seed ≤
        40 * Fintype.card (SurjectiveSeed E) := by
      simpa [card_surjectiveSeed] using! hgoodNat
    have hgoodReal : (37 : ℝ) * Fintype.card E.Seed ≤
        40 * Fintype.card (SurjectiveSeed E) := by
      exact_mod_cast hgoodNat'
    have hcardpos : (0 : ℝ) < Fintype.card (SurjectiveSeed E) := by
      exact_mod_cast Fintype.card_pos
    have hscaled : (Fintype.card (SurjectiveSeed E) : ℝ)⁻¹ *
        (∑ y : SurjectiveSeed E, loss y.val) ≤ 2 / 37 := by
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ hcardpos).2
      have hratio : (Fintype.card E.Seed : ℝ) / 20 ≤
          (2 / 37 : ℝ) * Fintype.card (SurjectiveSeed E) := by
        nlinarith
      exact hretained.trans hratio
    exact hscaled.trans_lt (by norm_num)

end Erdos788
