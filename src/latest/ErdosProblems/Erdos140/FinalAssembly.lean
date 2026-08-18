import ErdosProblems.Erdos140.KelleyMekaCount
import ErdosProblems.Erdos140.BalancedRestrictionAssembly
import ErdosProblems.Erdos140.Bookkeeping

/-!
# Final dense-pair assembly

The terminal Holder step uses two Bohr carriers with different jobs.  The
baseline carrier controls the balanced function and the main term, while the
weight carrier is the doubled middle-fibre carrier on which the Holder norm
is measured.  Keeping those roles separate is essential for the exact
normalizations in the cyclic counting endpoint.
-/

open Finset Fintype Function
open scoped BigOperators NNReal mu

namespace Erdos140.FinalAssembly

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The scaled balanced convolution appearing in the Holder endpoint. -/
def scaledBalanced (K : BohrData G) (A : Finset G) : G → ℝ :=
  (Fintype.card G : ℝ) •
    normalizedConvolution (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier)

/-- Concrete two-carrier balanced restriction.  The comparison theorem is
run with the weight carrier, while localized unbalancing is run with the
baseline carrier. -/
theorem balanced_of_twoBohr_concrete_stopping
    {K W : BohrData G} (hKreg : K.IsRankRegular)
    (hWreg : W.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAK : A ⊆ K.carrier)
    {eta : ℝ≥0} (heta : 0 < eta)
    (hnarrow : 4 * eta ≤
      1 / (400 * (max W.rank 1 : ℕ) : ℝ≥0))
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    (hDsmall : D ⊆ (W.dilate eta).carrier)
    (hEsmall : E ⊆ (W.dilate eta).carrier)
    {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max K.rank 1 : ℕ) : ℝ≥0))
    (hsupport : ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (K.dilate kappa).carrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hwidth :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
        (K.carrier.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
        epsilon / 8 * (K.carrier.card : ℝ)⁻¹)
    {p : ℕ} (hp : 0 < p)
    (hstopping :
      BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          (μ_[ℝ] A ○ᵈ μ A) (BalancedRestriction.stoppingExponent epsilon p) <
        (1 + epsilon / 8) * (K.carrier.card : ℝ)⁻¹) :
    BalancedRestriction.weightedLpNorm (normalizedIndicator W.carrier)
        (normalizedConvolution
          (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier)) p ≤
      epsilon * (K.carrier.card : ℝ)⁻¹ := by
  let a : G → ℝ := μ_[ℝ] A - μ K.carrier
  have hq : 0 < BalancedRestriction.comparisonExponent p :=
    Nat.mul_pos (by norm_num) hp
  have hcomparison :=
    BalancedRestrictionAssembly.concrete_comparison_lp hWreg heta hnarrow
      hD hE hDsmall hEsmall hq
      (BalancedRestriction.comparisonExponent_even p) a
  rw [BalancedRestrictionAssembly.normalizedDifferenceConvolution_eq_dddconv]
    at hcomparison
  apply BalancedRestrictionAssembly.balanced_of_localized_unbalancing
      hKreg hA hAK hD hE hkappa hsupport hepsilon hepsilon_one hwidth hp
      ⟨normalizedIndicator_nonneg W.carrier,
        sum_normalizedIndicator W.carrier_nonempty⟩
  · simpa [a] using hcomparison
  · exact hstopping

/-- The exact endpoint data attached to one dense-pair branch.

The baseline carrier is the first child, and the weight carrier is the
doubled second child.  The approximation field is the remaining
normalization/boundary estimate for the selected fibres. -/
structure TwoBohrEndpointPackage
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {epsilon sizeCost : ℝ} {rankCost p : ℕ}
    (P : DensityStep.NarrowingPackage s epsilon sizeCost rankCost)
    (hdense : DensityStep.HasDensePair s P.childOne P.childTwo epsilon) where
  base : BohrData G
  weight : BohrData G
  base_regular : base.IsRankRegular
  weight_regular : weight.IsRankRegular
  base_carrier : base.carrier = P.childOne.carrier
  weight_carrier :
    weight.carrier = GroupCount.doubledFinset P.childTwo.carrier
  endpoint_nonempty :
    (GroupCount.densePairEndpointSet P hdense).Nonempty
  endpoint_subset :
    GroupCount.densePairEndpointSet P hdense ⊆ base.carrier
  eta : ℝ≥0
  eta_pos : 0 < eta
  eta_narrow : 4 * eta ≤
    1 / (400 * (max weight.rank 1 : ℕ) : ℝ≥0)
  D : Finset G
  E : Finset G
  D_nonempty : D.Nonempty
  E_nonempty : E.Nonempty
  D_small : D ⊆ (weight.dilate eta).carrier
  E_small : E ⊆ (weight.dilate eta).carrier
  kappa : ℝ≥0
  rank_width : kappa ≤ 1 / (100 * (max base.rank 1 : ℕ) : ℝ≥0)
  smoothing_support :
    ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (base.dilate kappa).carrier
  boundary_width :
    2 * (((GroupCount.densePairEndpointSet P hdense).card : ℝ)⁻¹ *
        (200 * ((max base.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
      (base.carrier.card : ℝ)⁻¹ *
        (200 * ((max base.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
      (1 / 8 : ℝ) / 8 * (base.carrier.card : ℝ)⁻¹
  density_power :
    (2 / 3 : ℝ) ^ p ≤ GroupCount.densePairDensity s epsilon
  approximation :
    |(GroupCount.normalizedMixedProgression
          (GroupCount.densePairEndpointSet P hdense)
          (GroupCount.densePairMiddleSet P hdense) -
        (Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) -
        HolderLifting.pairing
          (scaledBalanced base (GroupCount.densePairEndpointSet P hdense))
          (GroupCount.doubledFinset
            (GroupCount.densePairMiddleSet P hdense))| ≤
      ((Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) / 8
  highNorm_increment :
    (1 + (1 / 8 : ℝ) / 8) * (base.carrier.card : ℝ)⁻¹ ≤
        BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          (μ_[ℝ] (GroupCount.densePairEndpointSet P hdense) ○ᵈ
            μ (GroupCount.densePairEndpointSet P hdense))
          (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p) →
      ∃ t : DensityStep.LocatedRestriction original,
        (257 / 256 : ℝ) * GroupCount.densePairDensity s epsilon ≤ t.density ∧
        t.rank ≤ s.rank + rankCost ∧
        Real.exp (-sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ)

/-- Weakening the demanded density gain preserves the rank and card costs. -/
theorem controlledIncrement_of_le
    {q q' sizeCost : ℝ} {rankCost : ℕ}
    {s t : BohrStopping.RegularRestriction G}
    (hqq' : q ≤ q')
    (h : BohrStopping.IsControlledIncrement q' rankCost sizeCost s t) :
    BohrStopping.IsControlledIncrement q rankCost sizeCost s t := by
  refine ⟨?_, h.2.1, h.2.2⟩
  exact (mul_le_mul_of_nonneg_right hqq' s.density_nonneg).trans h.1

/-! ## Rank-regular located states

The quantitative narrowing theorem is rank-regular, whereas the generic
located state remembers only coarse shell regularity.  The final recursion
therefore carries the stronger invariant explicitly. -/

/-- A located restriction together with the rank-regularity needed by the
next quantitative narrowing step. -/
structure RankRegularLocatedRestriction (original : Finset G) where
  located : DensityStep.LocatedRestriction original
  outer_one : located.restriction.outer = 1
  rankRegular : located.restriction.bohr.IsRankRegular

namespace RankRegularLocatedRestriction

def density {original : Finset G} (s : RankRegularLocatedRestriction original) :
    ℝ := s.located.density

def rank {original : Finset G} (s : RankRegularLocatedRestriction original) :
    ℕ := s.located.rank

def card {original : Finset G} (s : RankRegularLocatedRestriction original) :
    ℕ := s.located.card

lemma density_pos {original : Finset G} (s : RankRegularLocatedRestriction original) :
    0 < s.density := s.located.density_pos

lemma density_nonneg {original : Finset G} (s : RankRegularLocatedRestriction original) :
    0 ≤ s.density := s.density_pos.le

end RankRegularLocatedRestriction

/-- Two actual rank-regular children and their quantitative losses.  Unlike
DensityStep.NarrowingPackage, this uses the proved rank-regular Bourgain
alternative directly and does not ask for an unrelated exact plateau. -/
structure RankRegularNarrowingPackage
    {original : Finset G} (s : RankRegularLocatedRestriction original)
    (epsilon sizeCost : ℝ) (rankCost : ℕ) where
  kappa : ℝ≥0
  kappa_small :
    kappa ≤
      1 / (100 * (max s.located.restriction.bohr.rank 1 : ℕ) : ℝ≥0)
  childOne : DensityStep.RegularChild (G := G)
  childTwo : DensityStep.RegularChild (G := G)
  childOne_outer_one : childOne.outer = 1
  childTwo_outer_one : childTwo.outer = 1
  childOne_rankRegular : childOne.bohr.IsRankRegular
  childTwo_rankRegular : childTwo.bohr.IsRankRegular
  smallOne : childOne.carrier ⊆
    (s.located.restriction.bohr.dilate kappa).carrier
  smallTwo : childTwo.carrier ⊆
    (s.located.restriction.bohr.dilate kappa).carrier
  narrowing_small :
    400 * ((max s.located.restriction.bohr.rank 1 : ℕ) : ℝ) * (kappa : ℝ) ≤
      epsilon *
        relativeDensityOn s.located.restriction.set
          s.located.restriction.bohr.carrier / 4
  rankOne : childOne.bohr.rank ≤ s.rank + rankCost
  rankTwo : childTwo.bohr.rank ≤ s.rank + rankCost
  cardOne : Real.exp (-sizeCost) * (s.card : ℝ) ≤ childOne.carrier.card
  cardTwo : Real.exp (-sizeCost) * (s.card : ℝ) ≤ childTwo.carrier.card

/-- Rank-regular narrowing preserves rank-regularity on the increment
branch and retains the honest dense-pair branch on the same two children. -/
theorem densePair_or_rankRegular_increment
    {original : Finset G} (s : RankRegularLocatedRestriction original)
    {epsilon sizeCost : ℝ} {rankCost : ℕ}
    (hepsilon : 0 < epsilon)
    (P : RankRegularNarrowingPackage s epsilon sizeCost rankCost) :
    DensityStep.HasDensePair s.located P.childOne P.childTwo epsilon ∨
      ∃ t : RankRegularLocatedRestriction original,
        BohrStopping.IsControlledIncrement (1 + epsilon / 2) rankCost sizeCost
          s.located.restriction t.located.restriction := by
  have hA := s.located.restriction.nonempty
  have hAK :
      s.located.restriction.set ⊆ s.located.restriction.bohr.carrier := by
    simpa [BohrStopping.RegularRestriction.ambient, s.outer_one] using
      s.located.restriction.subset_carrier
  have hdensityEq :
      relativeDensityOn s.located.restriction.set
          s.located.restriction.bohr.carrier = s.located.density := by
    unfold DensityStep.LocatedRestriction.density BohrStopping.RegularRestriction.density
      relativeDensityOn BohrStopping.RegularRestriction.ambient
    simp [s.outer_one]
  rcases bohr_narrowing_alternative_of_rankRegular
      s.rankRegular P.kappa_small hA hAK
      P.childOne.carrier_nonempty P.childTwo.carrier_nonempty
      P.smallOne P.smallTwo hepsilon P.narrowing_small with
    hdense | hincOne | hincTwo
  · left
    rw [hdensityEq] at hdense
    simpa [DensityStep.HasDensePair, DensityStep.LocatedRestriction.ambient,
      DensityStep.LocatedRestriction.density,
      BohrStopping.RegularRestriction.density,
      BohrStopping.RegularRestriction.ambient, s.outer_one] using hdense
  · right
    obtain ⟨x, hx⟩ := hincOne
    rw [hdensityEq] at hx
    have hpos : 0 < localDensity s.located.restriction.set
        P.childOne.carrier x := by
      have hs : 0 < s.located.density := s.located.density_pos
      have hq : 0 < (1 + epsilon / 2 : ℝ) := by nlinarith
      exact (mul_pos hq hs).trans_le (by simpa using hx)
    let u := DensityStep.narrowLocated s.located P.childOne x hpos
    refine ⟨{ located := u, outer_one := ?_, rankRegular := ?_ }, ?_⟩
    · simpa [u, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
        using P.childOne_outer_one
    · simpa [u, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
        using P.childOne_rankRegular
    · apply DensityStep.narrowLocated_isControlledIncrement
        s.located P.childOne x hpos
      · simpa [DensityStep.LocatedRestriction.density,
          BohrStopping.RegularRestriction.density,
          BohrStopping.RegularRestriction.ambient] using hx
      · exact P.rankOne
      · exact P.cardOne
  · right
    obtain ⟨x, hx⟩ := hincTwo
    rw [hdensityEq] at hx
    have hpos : 0 < localDensity s.located.restriction.set
        P.childTwo.carrier x := by
      have hs : 0 < s.located.density := s.located.density_pos
      have hq : 0 < (1 + epsilon / 2 : ℝ) := by nlinarith
      exact (mul_pos hq hs).trans_le (by simpa using hx)
    let u := DensityStep.narrowLocated s.located P.childTwo x hpos
    refine ⟨{ located := u, outer_one := ?_, rankRegular := ?_ }, ?_⟩
    · simpa [u, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
        using P.childTwo_outer_one
    · simpa [u, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
        using P.childTwo_rankRegular
    · apply DensityStep.narrowLocated_isControlledIncrement
        s.located P.childTwo x hpos
      · simpa [DensityStep.LocatedRestriction.density,
          BohrStopping.RegularRestriction.density,
          BohrStopping.RegularRestriction.ambient] using hx
      · exact P.rankTwo
      · exact P.cardTwo

/-! ## Raw dense-pair Holder endpoint

The old GroupCount constructor takes a NarrowingPackage only to name its two
children.  The rank-regular recursion uses the children directly, so the
same finite-set argument is repeated here without a plateau-shaped wrapper.
-/

def rawDensePairEndpointSet
    {original : Finset G} {s : DensityStep.LocatedRestriction original}
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (h : DensityStep.HasDensePair s childOne childTwo epsilon) : Finset G :=
  DensityStep.narrowingSet s.restriction.set childOne.carrier
    (GroupCount.densePairPoint h)

def rawDensePairMiddleSet
    {original : Finset G} {s : DensityStep.LocatedRestriction original}
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (h : DensityStep.HasDensePair s childOne childTwo epsilon) : Finset G :=
  DensityStep.narrowingSet s.restriction.set childTwo.carrier
    (GroupCount.densePairPoint h)

/-- Generic Holder certificate from two actual children and their common
dense translate. -/
noncomputable def holderCountCertificateOfRawDensePair
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon)
    (_hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    {p : ℕ} (hp : 0 < p) (f : G → ℝ)
    (hpDensity : (2 / 3 : ℝ) ^ p ≤ GroupCount.densePairDensity s epsilon)
    (happrox :
      |(GroupCount.normalizedMixedProgression
            (rawDensePairEndpointSet hdense) (rawDensePairMiddleSet hdense) -
          (Fintype.card G : ℝ) / (#childOne.carrier : ℝ)) -
          HolderLifting.pairing f
            (GroupCount.doubledFinset (rawDensePairMiddleSet hdense))| ≤
        ((Fintype.card G : ℝ) / (#childOne.carrier : ℝ)) / 8)
    (hbalanced :
      BalancedRestriction.weightedLpNorm
          (normalizedIndicator (GroupCount.doubledFinset childTwo.carrier)) f p ≤
        ((Fintype.card G : ℝ) / (#childOne.carrier : ℝ)) / 8) :
    GroupCount.HolderCountCertificate original := by
  let x : G := GroupCount.densePairPoint hdense
  let A' : Finset G := rawDensePairEndpointSet hdense
  let A'' : Finset G := rawDensePairMiddleSet hdense
  let B : Finset G := childOne.carrier
  let B' : Finset G := childTwo.carrier
  let alpha : ℝ := GroupCount.densePairDensity s epsilon
  have hOne : alpha ≤ localDensity s.restriction.set B x := by
    simpa [alpha, x, B, GroupCount.densePairDensity] using
      GroupCount.densePairPoint_density_one hdense
  have hTwo : alpha ≤ localDensity s.restriction.set B' x := by
    simpa [alpha, x, B', GroupCount.densePairDensity] using
      GroupCount.densePairPoint_density_two hdense
  have halpha : 0 < alpha :=
    mul_pos (sub_pos.mpr hepsilon_lt_one) s.density_pos
  have hA' : A'.Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos childOne.carrier_nonempty
    exact halpha.trans_le hOne
  have hA'' : A''.Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos childTwo.carrier_nonempty
    exact halpha.trans_le hTwo
  have hA''B' : A'' ⊆ B' := by
    exact DensityStep.narrowingSet_subset_carrier
      (B := childTwo.bohr) (rho := childTwo.outer)
      (A := s.restriction.set) (C := childTwo.carrier)
      (x := x) (fun _ hz ↦ hz)
  have hA'trans : ∀ z ∈ A', z - (s.shift - x) ∈ original := by
    intro z hz
    have hzSource : x + z ∈ s.restriction.set :=
      (DensityStep.mem_narrowingSet.mp hz).2
    have hs := s.subset_original (x + z) hzSource
    have heq : z - (s.shift - x) = (x + z) - s.shift := by abel
    rwa [heq]
  have hA''trans : ∀ z ∈ A'', z - (s.shift - x) ∈ original := by
    intro z hz
    have hzSource : x + z ∈ s.restriction.set :=
      (DensityStep.mem_narrowingSet.mp hz).2
    have hs := s.subset_original (x + z) hzSource
    have heq : z - (s.shift - x) = (x + z) - s.shift := by abel
    rwa [heq]
  have hDensityOne : alpha * (#B : ℝ) ≤ (#A' : ℝ) := by
    have hBpos : (0 : ℝ) < #B := by exact_mod_cast childOne.carrier_nonempty.card_pos
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      childOne.carrier_nonempty x] at hOne
    exact (le_div_iff₀ hBpos).mp hOne
  have hDensityTwo : alpha * (#B' : ℝ) ≤ (#A'' : ℝ) := by
    have hB'pos : (0 : ℝ) < #B' := by exact_mod_cast childTwo.carrier_nonempty.card_pos
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      childTwo.carrier_nonempty x] at hTwo
    exact (le_div_iff₀ hB'pos).mp hTwo
  have hRelative :
      (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B' := by
    calc
      (2 / 3 : ℝ) ^ p ≤ alpha := hpDensity
      _ ≤ localDensity s.restriction.set B' x := hTwo
      _ = HolderLifting.relativeDensity A'' B' := by
        rw [DensityStep.localDensity_eq_card_narrowingSet_div
          childTwo.carrier_nonempty x]
        rfl
  have hDoubledB' : (GroupCount.doubledFinset B').Nonempty :=
    GroupCount.doubledFinset_nonempty childTwo.carrier_nonempty
  have hMoment :
      HolderLifting.localMoment (GroupCount.doubledFinset B') p f ≤
        (((Fintype.card G : ℝ) / (#B : ℝ)) / 8) ^ p := by
    apply GroupCount.localMoment_le_of_weightedLpNorm_le hDoubledB' hp f (by positivity)
    simpa [B, B'] using hbalanced
  exact
    { A' := A'
      A'' := A''
      B := B
      B' := B'
      translate := s.shift - x
      alpha := alpha
      p := p
      f := f
      A'_nonempty := hA'
      A''_nonempty := hA''
      B_nonempty := childOne.carrier_nonempty
      A''_subset_B' := hA''B'
      A'_sub_translate := hA'trans
      A''_sub_translate := hA''trans
      alpha_nonneg := halpha.le
      A'_density := hDensityOne
      A''_density := hDensityTwo
      p_pos := hp
      doubled_density := hRelative
      approximation := by simpa [A', A'', B] using happrox
      balanced_moment := hMoment }

/-- Two-Bohr analytic output for the raw rank-regular child package.  This
is the target interface for the concrete localized-almost-periodicity
construction. -/
structure RawTwoBohrEndpointPackage
    {original : Finset G} (s : RankRegularLocatedRestriction original)
    {epsilon sizeCost : ℝ} {rankCost p : ℕ}
    (P : RankRegularNarrowingPackage s epsilon sizeCost rankCost)
    (hdense : DensityStep.HasDensePair s.located P.childOne P.childTwo epsilon) where
  base : BohrData G
  weight : BohrData G
  base_regular : base.IsRankRegular
  weight_regular : weight.IsRankRegular
  base_carrier : base.carrier = P.childOne.carrier
  weight_carrier :
    weight.carrier = GroupCount.doubledFinset P.childTwo.carrier
  endpoint_nonempty : (rawDensePairEndpointSet hdense).Nonempty
  endpoint_subset : rawDensePairEndpointSet hdense ⊆ base.carrier
  eta : ℝ≥0
  eta_pos : 0 < eta
  eta_narrow : 4 * eta ≤
    1 / (400 * (max weight.rank 1 : ℕ) : ℝ≥0)
  D : Finset G
  E : Finset G
  D_nonempty : D.Nonempty
  E_nonempty : E.Nonempty
  D_small : D ⊆ (weight.dilate eta).carrier
  E_small : E ⊆ (weight.dilate eta).carrier
  kappa : ℝ≥0
  rank_width : kappa ≤ 1 / (100 * (max base.rank 1 : ℕ) : ℝ≥0)
  smoothing_support :
    ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (base.dilate kappa).carrier
  boundary_width :
    2 * (((rawDensePairEndpointSet hdense).card : ℝ)⁻¹ *
        (200 * ((max base.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
      (base.carrier.card : ℝ)⁻¹ *
        (200 * ((max base.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
      (1 / 8 : ℝ) / 8 * (base.carrier.card : ℝ)⁻¹
  density_power :
    (2 / 3 : ℝ) ^ p ≤ GroupCount.densePairDensity s.located epsilon
  approximation :
    |(GroupCount.normalizedMixedProgression
          (rawDensePairEndpointSet hdense) (rawDensePairMiddleSet hdense) -
        (Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) -
        HolderLifting.pairing
          (scaledBalanced base (rawDensePairEndpointSet hdense))
          (GroupCount.doubledFinset (rawDensePairMiddleSet hdense))| ≤
      ((Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) / 8
  highNorm_increment :
    (1 + (1 / 8 : ℝ) / 8) * (base.carrier.card : ℝ)⁻¹ ≤
        BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          (μ_[ℝ] (rawDensePairEndpointSet hdense) ○ᵈ
            μ (rawDensePairEndpointSet hdense))
          (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p) →
      ∃ t : RankRegularLocatedRestriction original,
        (257 / 256 : ℝ) *
            GroupCount.densePairDensity s.located epsilon ≤ t.density ∧
        t.rank ≤ s.rank + rankCost ∧
        Real.exp (-sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ)

/-- The raw two-Bohr package yields the exact local terminal data after the
balanced stopping inequality has been proved. -/
noncomputable def locatedTerminalDataOfRawTwoBohr
    {original : Finset G} (s : RankRegularLocatedRestriction original)
    {K : ℝ} {d rankCost p : ℕ}
    (P : RankRegularNarrowingPackage s (1 / 512 : ℝ)
      (K * ((d + 1 : ℕ) : ℝ) ^ 11) rankCost)
    (hdense : DensityStep.HasDensePair s.located P.childOne P.childTwo
      (1 / 512 : ℝ))
    (hp : 0 < p)
    (Q : RawTwoBohrEndpointPackage (p := p) s P hdense)
    (hraw :
      BalancedRestriction.weightedLpNorm (normalizedIndicator Q.weight.carrier)
          (normalizedConvolution
            (μ_[ℝ] (rawDensePairEndpointSet hdense) - μ Q.base.carrier)
            (μ (rawDensePairEndpointSet hdense) - μ Q.base.carrier)) p ≤
        (1 / 8 : ℝ) * (Q.base.carrier.card : ℝ)⁻¹) :
    LocatedHolderTerminalData s.located K d := by
  let c := holderCountCertificateOfRawDensePair s.located hdense
    (by norm_num) (by norm_num) hp
    (scaledBalanced Q.base (rawDensePairEndpointSet hdense))
    Q.density_power Q.approximation (by
      let w : G → ℝ≥0 := μ Q.weight.carrier
      have hscale :=
        LocalizedUnbalancing.weightedLpNorm_smul_of_nonneg w
          (normalizedConvolution
            (μ_[ℝ] (rawDensePairEndpointSet hdense) - μ Q.base.carrier)
            (μ (rawDensePairEndpointSet hdense) - μ Q.base.carrier))
          (Fintype.card G : ℝ) (by positivity) hp
      have hscale' :
          BalancedRestriction.weightedLpNorm
              (normalizedIndicator Q.weight.carrier)
              (scaledBalanced Q.base (rawDensePairEndpointSet hdense)) p =
            (Fintype.card G : ℝ) *
              BalancedRestriction.weightedLpNorm
                (normalizedIndicator Q.weight.carrier)
                (normalizedConvolution
                  (μ_[ℝ] (rawDensePairEndpointSet hdense) - μ Q.base.carrier)
                  (μ (rawDensePairEndpointSet hdense) - μ Q.base.carrier)) p := by
        simpa only [w, NNReal.coe_comp_mu,
          LocalizedUnbalancing.mu_eq_normalizedIndicator,
          scaledBalanced] using hscale
      have hscaled :
          BalancedRestriction.weightedLpNorm
              (normalizedIndicator Q.weight.carrier)
              (scaledBalanced Q.base (rawDensePairEndpointSet hdense)) p ≤
            (Fintype.card G : ℝ) *
              ((1 / 8 : ℝ) * (Q.base.carrier.card : ℝ)⁻¹) := by
        rw [hscale']
        exact mul_le_mul_of_nonneg_left hraw (by positivity)
      rw [Q.weight_carrier] at hscaled
      simpa [Q.base_carrier, div_eq_mul_inv, mul_assoc, mul_left_comm,
        mul_comm] using hscaled)
  refine
    { certificate := c
      alpha_lower := ?_
      B_card := ?_
      B'_card := ?_ }
  · change (3 / 4 : ℝ) * s.located.density ≤
      GroupCount.densePairDensity s.located (1 / 512 : ℝ)
    simp only [GroupCount.densePairDensity]
    nlinarith [s.located.density_pos.le]
  · change Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        (s.card : ℝ) ≤ (#P.childOne.carrier : ℝ)
    exact P.cardOne
  · change Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        (s.card : ℝ) ≤ (#P.childTwo.carrier : ℝ)
    exact P.cardTwo

/-- Honest one-step terminal-or-increment result for a rank-regular state.
The dense-pair loss is 1/512, the balanced-restriction loss is 1/8, and the
composed gain is the fixed 1025/1024 used by the global stopping argument. -/
theorem terminalData_or_rankRegular_increment
    {original : Finset G} (s : RankRegularLocatedRestriction original)
    {K : ℝ} {d rankCost p : ℕ}
    (P : RankRegularNarrowingPackage s (1 / 512 : ℝ)
      (K * ((d + 1 : ℕ) : ℝ) ^ 11) rankCost)
    (hp : 0 < p)
    (hendpoint :
      ∀ hdense : DensityStep.HasDensePair s.located P.childOne P.childTwo
          (1 / 512 : ℝ),
        Nonempty (RawTwoBohrEndpointPackage (p := p) s P hdense)) :
    Nonempty (LocatedHolderTerminalData s.located K d) ∨
      ∃ t : RankRegularLocatedRestriction original,
        BohrStopping.IsControlledIncrement (1025 / 1024 : ℝ) rankCost
          (K * ((d + 1 : ℕ) : ℝ) ^ 11)
          s.located.restriction t.located.restriction := by
  rcases densePair_or_rankRegular_increment s
      (by norm_num : (0 : ℝ) < 1 / 512) P with hpair | hincrement
  · obtain ⟨Q⟩ := hendpoint hpair
    by_cases hhigh :
        (1 + (1 / 8 : ℝ) / 8) * (Q.base.carrier.card : ℝ)⁻¹ ≤
          BalancedRestriction.weightedLpNorm
            ((↑) ∘ LocalizedUnbalancing.smoothingWeight Q.D Q.E)
            (μ_[ℝ] (rawDensePairEndpointSet hpair) ○ᵈ
              μ (rawDensePairEndpointSet hpair))
            (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p)
    · right
      obtain ⟨u, hdensity, hurank, hucard⟩ := Q.highNorm_increment hhigh
      refine ⟨u, ?_, hurank, hucard⟩
      calc
        (1025 / 1024 : ℝ) * s.located.density ≤
            (257 / 256 : ℝ) *
              GroupCount.densePairDensity s.located (1 / 512 : ℝ) := by
          simp only [GroupCount.densePairDensity]
          nlinarith [s.located.density_pos.le]
        _ ≤ u.density := hdensity
    · left
      have hstop :
          BalancedRestriction.weightedLpNorm
              ((↑) ∘ LocalizedUnbalancing.smoothingWeight Q.D Q.E)
              (μ_[ℝ] (rawDensePairEndpointSet hpair) ○ᵈ
                μ (rawDensePairEndpointSet hpair))
              (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p) <
            (1 + (1 / 8 : ℝ) / 8) * (Q.base.carrier.card : ℝ)⁻¹ :=
        lt_of_not_ge hhigh
      have hraw := balanced_of_twoBohr_concrete_stopping Q.base_regular
        Q.weight_regular Q.endpoint_nonempty Q.endpoint_subset Q.eta_pos
        Q.eta_narrow Q.D_nonempty Q.E_nonempty Q.D_small Q.E_small
        Q.rank_width Q.smoothing_support (by norm_num) (by norm_num)
        Q.boundary_width hp hstop
      exact ⟨locatedTerminalDataOfRawTwoBohr s P hpair hp Q hraw⟩
  · right
    obtain ⟨u, hu⟩ := hincrement
    refine ⟨u, ?_⟩
    simpa only [show (1 + (1 / 512 : ℝ) / 2) =
        (1025 / 1024 : ℝ) by norm_num] using hu

/-! ## Rank-regular finite stopping

This recursion is the rank-regular replacement for the generic located
stopping theorem.  It keeps the stronger invariant in the state rather than
forgetting it after the first child. -/

inductive RankRegularControlledChain {original : Finset G}
    (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ) :
    ℕ → RankRegularLocatedRestriction original →
      RankRegularLocatedRestriction original → Prop
  | nil (s : RankRegularLocatedRestriction original) :
      RankRegularControlledChain q rankCost sizeCost 0 s s
  | cons {n : ℕ} {s t u : RankRegularLocatedRestriction original}
      (hst : BohrStopping.IsControlledIncrement q rankCost sizeCost
        s.located.restriction t.located.restriction)
      (htu : RankRegularControlledChain q rankCost sizeCost n t u) :
      RankRegularControlledChain q rankCost sizeCost (n + 1) s u

namespace RankRegularControlledChain

theorem forget {original : Finset G} {q sizeCost : ℝ} {rankCost n : ℕ}
    {s t : RankRegularLocatedRestriction original}
    (h : RankRegularControlledChain q rankCost sizeCost n s t) :
    DensityStep.LocatedControlledChain q rankCost sizeCost n s.located t.located := by
  induction h with
  | nil s => exact DensityStep.LocatedControlledChain.nil s.located
  | cons hst _ ih => exact DensityStep.LocatedControlledChain.cons hst ih

end RankRegularControlledChain

/-- Finite stopping while preserving rank-regularity in every state. -/
theorem exists_terminal_rankRegular_chain
    {original : Finset G}
    {Terminal : RankRegularLocatedRestriction original → Prop}
    {q sizeCost : ℝ} {rankCost fuel : ℕ}
    (hq : 0 ≤ q)
    (hstep : ∀ s : RankRegularLocatedRestriction original,
      Terminal s ∨ ∃ t : RankRegularLocatedRestriction original,
        BohrStopping.IsControlledIncrement q rankCost sizeCost
          s.located.restriction t.located.restriction)
    (initial : RankRegularLocatedRestriction original)
    (hgrowth : 1 < q ^ fuel * initial.density) :
    ∃ n ≤ fuel, ∃ t : RankRegularLocatedRestriction original,
      RankRegularControlledChain q rankCost sizeCost n initial t ∧
      Terminal t := by
  induction fuel generalizing initial with
  | zero =>
      have hs := initial.located.density_le_one
      simp only [pow_zero, one_mul] at hgrowth
      exact (not_lt_of_ge hs hgrowth).elim
  | succ fuel ih =>
      rcases hstep initial with hterminal | ⟨t, hst⟩
      · exact ⟨0, by omega, initial,
          RankRegularControlledChain.nil initial, hterminal⟩
      · have hqpow : 0 ≤ q ^ fuel := pow_nonneg hq fuel
        have hgrowth' : 1 < q ^ fuel * t.density := by
          calc
            1 < q ^ (fuel + 1) * initial.density := by simpa using hgrowth
            _ = q ^ fuel * (q * initial.density) := by rw [pow_succ]; ring
            _ ≤ q ^ fuel * t.density :=
              mul_le_mul_of_nonneg_left hst.1 hqpow
        obtain ⟨n, hn, u, hchain, hu⟩ := ih t hgrowth'
        exact ⟨n + 1, by omega, u,
          RankRegularControlledChain.cons hst hchain, hu⟩

/-! ## Cyclic initial rank-regular state

The empty-frequency Bohr datum is rank-regular because every one of its
dilates is the whole group. -/

theorem universalBohrData_rankRegular
    (G : Type*) [AddCommGroup G] [Fintype G] :
    (universalBohrData G).IsRankRegular := by
  intro kappa _hkappa
  simp only [universalBohrData_rank, show max 0 1 = 1 by omega,
    Nat.cast_one]
  rw [universalBohrData_carrier_self]
  simp only [universalBohrData_carrier]
  have hcard : (0 : ℝ) ≤ Fintype.card G := by positivity
  constructor <;> nlinarith [show (0 : ℝ) ≤ kappa by positivity]

/-- The genuine cyclic initial restriction with its rank-regular invariant. -/
noncomputable def cyclicInitialRankRegularLocated (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    RankRegularLocatedRestriction A where
  located := cyclicInitialLocated N A hA
  outer_one := rfl
  rankRegular := universalBohrData_rankRegular (ZMod (intervalModulus N))

@[simp] theorem cyclicInitialRankRegularLocated_density (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRankRegularLocated N A hA).density =
      (#A : ℝ) / (intervalModulus N : ℕ) := by
  exact cyclicInitialLocated_density N A hA

@[simp] theorem cyclicInitialRankRegularLocated_rank (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRankRegularLocated N A hA).rank = 0 := by
  exact cyclicInitialLocated_rank N A hA

@[simp] theorem cyclicInitialRankRegularLocated_card (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRankRegularLocated N A hA).card = intervalModulus N := by
  exact cyclicInitialLocated_card N A hA

/-- Bounded rank-regular stopping with the dyadic and rank invariants exposed
at each used-step index.  This is the form consumed by the concrete supplier,
whose quantitative construction only needs those two bounds. -/
theorem exists_terminal_rankRegular_chain_bounded_aux
    {original : Finset G}
    {Terminal : RankRegularLocatedRestriction original → Prop}
    {q lower sizeCost : ℝ} {rankCost total used remaining : ℕ}
    (hq : 1 ≤ q)
    (hbudget : used + remaining ≤ total)
    (hstep : ∀ n < total, ∀ s : RankRegularLocatedRestriction original,
      lower ≤ s.density →
      s.rank ≤ n * rankCost →
      Terminal s ∨ ∃ t : RankRegularLocatedRestriction original,
        BohrStopping.IsControlledIncrement q rankCost sizeCost
          s.located.restriction t.located.restriction)
    (initial : RankRegularLocatedRestriction original)
    (hscale : lower ≤ initial.density)
    (hrank : initial.rank ≤ used * rankCost)
    (hgrowth : 1 < q ^ remaining * initial.density) :
    ∃ n ≤ remaining, ∃ t : RankRegularLocatedRestriction original,
      RankRegularControlledChain q rankCost sizeCost n initial t ∧
      Terminal t := by
  induction remaining generalizing initial used with
  | zero =>
      have hs := initial.located.density_le_one
      simp only [pow_zero, one_mul] at hgrowth
      exact (not_lt_of_ge hs hgrowth).elim
  | succ remaining ih =>
      have hused : used < total := by omega
      rcases hstep used hused initial hscale hrank with hterminal | ⟨t, hst⟩
      · exact ⟨0, by omega, initial,
          RankRegularControlledChain.nil initial, hterminal⟩
      · have hs_le : initial.density ≤ t.density := by
          calc
            initial.density = 1 * initial.density := by ring
            _ ≤ q * initial.density :=
              mul_le_mul_of_nonneg_right hq initial.density_nonneg
            _ ≤ t.density := hst.1
        have hscale' : lower ≤ t.density := hscale.trans hs_le
        have hrank' : t.rank ≤ (used + 1) * rankCost := by
          calc
            t.rank ≤ initial.rank + rankCost := hst.2.1
            _ ≤ used * rankCost + rankCost :=
              Nat.add_le_add_right hrank rankCost
            _ = (used + 1) * rankCost := by
              rw [Nat.add_mul]
              simp
        have hbudget' : used + 1 + remaining ≤ total := by omega
        have hqpow : 0 ≤ q ^ remaining := pow_nonneg (zero_le_one.trans hq) _
        have hgrowth' : 1 < q ^ remaining * t.density := by
          calc
            1 < q ^ (remaining + 1) * initial.density := by simpa using hgrowth
            _ = q ^ remaining * (q * initial.density) := by
              rw [pow_succ]
              ring
            _ ≤ q ^ remaining * t.density :=
              mul_le_mul_of_nonneg_left hst.1 hqpow
        obtain ⟨n, hn, u, hchain, hu⟩ :=
          ih hbudget' t hscale' hrank' hgrowth'
        exact ⟨n + 1, by omega, u,
          RankRegularControlledChain.cons hst hchain, hu⟩

/-- Dyadic scale for the honest cyclic initial rank-regular state. -/
theorem cyclicInitialRankRegular_onDyadicScale
    {N d : ℕ} (hN : 1 ≤ N)
    {A : Finset (ZMod (intervalModulus N))} (hA : A.Nonempty)
    (hlog : Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
      (d : ℝ) * Real.log 2) :
    BohrStopping.OnDyadicScale d
      (cyclicInitialRankRegularLocated N A hA).density := by
  have hmodNat : 0 < intervalModulus N := by simp [intervalModulus]
  have hmod : (0 : ℝ) < intervalModulus N := by exact_mod_cast hmodNat
  have hcard : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hratio : (0 : ℝ) <
      ((intervalModulus N : ℕ) : ℝ) / (#A : ℝ) := div_pos hmod hcard
  have hpow : (0 : ℝ) < (2 : ℝ) ^ d := pow_pos (by norm_num) _
  have hlog' :
      Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
        Real.log ((2 : ℝ) ^ d) := by
    simpa [Real.log_pow] using hlog
  have hratio_le :
      (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤ (2 : ℝ) ^ d :=
    (Real.log_le_log_iff hratio hpow).mp hlog'
  have hmul : (((intervalModulus N : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ d * (#A : ℝ) := (div_le_iff₀ hcard).mp hratio_le
  rw [BohrStopping.OnDyadicScale]
  simp only [cyclicInitialRankRegularLocated_density]
  apply (div_le_div_iff₀ hpow hmod).2
  simpa [mul_comm] using hmul

/-- Quantitative analytic supply required by the rank-regular recursion.
The used-step index exposes exactly the dyadic density and accumulated rank
bounds available to the concrete construction. -/
def RawConcreteSupply (K : ℝ) : Prop :=
  ∀ (N : ℕ),
    ∀ (A : Finset (ZMod (intervalModulus N))), A.Nonempty →
      ∀ d : ℕ, 1 ≤ d →
        ∃ rankCost p : ℕ, 0 < p ∧
          ∀ n < 1024 * (d + 1),
            ∀ s : RankRegularLocatedRestriction A,
              (1 / (2 : ℝ) ^ d) ≤ s.density →
              s.rank ≤ n * rankCost →
              ∃ P : RankRegularNarrowingPackage s (1 / 512 : ℝ)
                (K * ((d + 1 : ℕ) : ℝ) ^ 11) rankCost,
                ∀ hdense : DensityStep.HasDensePair s.located
                    P.childOne P.childTwo (1 / 512 : ℝ),
                  Nonempty (RawTwoBohrEndpointPackage (p := p) s P hdense)

/-- The concrete rank-regular supply gives the full cyclic Holder
certificate hypothesis without passing through a generic non-regular
maximal-state interface. -/
theorem holderCertificates_of_rawConcreteSupply
    {K : ℝ} (hK : 0 < K) (hsupply : RawConcreteSupply K) :
    KelleyMekaHolderCertificateHypothesis
      (8 + 2050 * (2 : ℝ) ^ 12 * K) := by
  refine ⟨by positivity, ?_⟩
  intro N hN A hA d hd hlog
  obtain ⟨rankCost, p, hp, hlocal⟩ := hsupply N A hA d hd
  let fuel : ℕ := 1024 * (d + 1)
  let initial := cyclicInitialRankRegularLocated N A hA
  let Terminal : RankRegularLocatedRestriction A → Prop :=
    fun s => Nonempty (LocatedHolderTerminalData s.located K d)
  have hstep : ∀ n < fuel, ∀ s : RankRegularLocatedRestriction A,
      (1 / (2 : ℝ) ^ d) ≤ s.density →
      s.rank ≤ n * rankCost →
      Terminal s ∨ ∃ t : RankRegularLocatedRestriction A,
        BohrStopping.IsControlledIncrement (1025 / 1024 : ℝ) rankCost
          (K * ((d + 1 : ℕ) : ℝ) ^ 11)
          s.located.restriction t.located.restriction := by
    intro n hn s hscale hrank
    obtain ⟨P, hendpoint⟩ := hlocal n (by simpa [fuel] using hn) s hscale hrank
    exact terminalData_or_rankRegular_increment s P hp hendpoint
  have hdyadic := cyclicInitialRankRegular_onDyadicScale hN hA hlog
  have hscaleInitial :
      (1 / (2 : ℝ) ^ d) ≤ initial.density := by
    change (1 / (2 : ℝ) ^ d) ≤ (cyclicInitialLocated N A hA).density
    exact hdyadic
  have hgrowth :
      1 < (1025 / 1024 : ℝ) ^ fuel * initial.density := by
    simpa [fuel, initial] using
      fixedIncrement_growth_of_dyadicScale
        (cyclicInitialLocated N A hA) hdyadic
  obtain ⟨n, hn, t, hchain, hterminal⟩ :=
    exists_terminal_rankRegular_chain_bounded_aux
      (Terminal := Terminal) (q := (1025 / 1024 : ℝ))
      (lower := 1 / (2 : ℝ) ^ d)
      (sizeCost := K * ((d + 1 : ℕ) : ℝ) ^ 11)
      (rankCost := rankCost) (total := fuel) (used := 0)
      (remaining := fuel) (by norm_num) (by omega) hstep initial
      hscaleInitial (by simp [initial]) hgrowth
  let data := Classical.choice hterminal
  have hforget := hchain.forget
  have hdensity0 :=
    hforget.density_bound (by norm_num)
  change (1025 / 1024 : ℝ) ^ n *
      (cyclicInitialLocated N A hA).density ≤ t.located.density at hdensity0
  have hdensity :
      (1025 / 1024 : ℝ) ^ n *
          (cyclicInitialLocated N A hA).density ≤ t.located.density := by
    exact hdensity0
  have hcard0 := hforget.card_bound
  change Real.exp (-(n : ℝ) * (K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
      ((cyclicInitialLocated N A hA).card : ℝ) ≤ t.located.card at hcard0
  have hcard :
      Real.exp (-(n : ℝ) * (K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
          ((cyclicInitialLocated N A hA).card : ℝ) ≤ t.located.card := by
    exact hcard0
  exact ⟨CyclicHolderCertificate.of_locatedTerminalData hd hA hK.le hn
    hdyadic hdensity hcard data⟩

/-- Scale a raw two-Bohr balanced bound into the Holder normalization. -/
theorem scaledBalanced_bound_of_raw
    {K W : BohrData G} {A : Finset G} {p : ℕ} (hp : 0 < p)
    {epsilon : ℝ}
    (hraw :
      BalancedRestriction.weightedLpNorm (normalizedIndicator W.carrier)
          (normalizedConvolution
            (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier)) p ≤
        epsilon * (K.carrier.card : ℝ)⁻¹) :
    BalancedRestriction.weightedLpNorm (normalizedIndicator W.carrier)
        (scaledBalanced K A) p ≤
      (Fintype.card G : ℝ) * (epsilon * (K.carrier.card : ℝ)⁻¹) := by
  let w : G → ℝ≥0 := μ W.carrier
  have hscale :=
    LocalizedUnbalancing.weightedLpNorm_smul_of_nonneg w
      (normalizedConvolution
        (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier))
      (Fintype.card G : ℝ) (by positivity) hp
  have hscale' :
      BalancedRestriction.weightedLpNorm (normalizedIndicator W.carrier)
          (scaledBalanced K A) p =
        (Fintype.card G : ℝ) *
          BalancedRestriction.weightedLpNorm (normalizedIndicator W.carrier)
            (normalizedConvolution
              (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier)) p := by
    simpa only [w, NNReal.coe_comp_mu,
      LocalizedUnbalancing.mu_eq_normalizedIndicator,
      scaledBalanced] using hscale
  rw [hscale']
  exact mul_le_mul_of_nonneg_left hraw (by positivity)

/-- Convert the two-carrier endpoint package and a raw balanced bound into
the exact located Holder terminal data. -/
noncomputable def locatedTerminalDataOfTwoBohr
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {K : ℝ} {d rankCost p : ℕ}
    (P : DensityStep.NarrowingPackage s (1 / 512 : ℝ)
      (K * ((d + 1 : ℕ) : ℝ) ^ 11) rankCost)
    (hdense : DensityStep.HasDensePair s P.childOne P.childTwo (1 / 512 : ℝ))
    (hp : 0 < p)
    (Q : TwoBohrEndpointPackage (p := p) s P hdense)
    (hraw :
      BalancedRestriction.weightedLpNorm (normalizedIndicator Q.weight.carrier)
          (normalizedConvolution
            (μ_[ℝ] (GroupCount.densePairEndpointSet P hdense) -
              μ Q.base.carrier)
            (μ (GroupCount.densePairEndpointSet P hdense) -
              μ Q.base.carrier)) p ≤
        (1 / 8 : ℝ) * (Q.base.carrier.card : ℝ)⁻¹) :
    LocatedHolderTerminalData s K d := by
  let c := GroupCount.holderCountCertificateOfDensePair s P hdense
    (by norm_num) (by norm_num) hp
    (scaledBalanced Q.base (GroupCount.densePairEndpointSet P hdense))
    Q.density_power Q.approximation (by
      have hscaled := scaledBalanced_bound_of_raw hp hraw
      rw [Q.weight_carrier] at hscaled
      simpa [Q.base_carrier, div_eq_mul_inv, mul_assoc, mul_left_comm,
        mul_comm] using hscaled)
  refine
    { certificate := c
      alpha_lower := ?_
      B_card := ?_
      B'_card := ?_ }
  · change (3 / 4 : ℝ) * s.density ≤
      GroupCount.densePairDensity s (1 / 512 : ℝ)
    simp only [GroupCount.densePairDensity]
    nlinarith [s.density_pos.le]
  · change Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        (s.card : ℝ) ≤ (#P.childOne.carrier : ℝ)
    exact P.cardOne
  · change Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        (s.card : ℝ) ≤ (#P.childTwo.carrier : ℝ)
    exact P.cardTwo

/-- Exact local interface still required from the analytic construction. -/
def ConcreteTerminalSupply (K : ℝ) : Prop :=
  ∀ (N : ℕ),
    ∀ (A : Finset (ZMod (intervalModulus N))), A.Nonempty →
      ∀ d : ℕ, 1 ≤ d →
        ∃ rankCost p : ℕ, 0 < p ∧
          ∀ t : DensityStep.LocatedRestriction A,
            (1 / (2 : ℝ) ^ d) ≤ t.density →
            t.rank ≤ 1024 * (d + 1) * rankCost →
            ∃ P : DensityStep.NarrowingPackage t (1 / 512 : ℝ)
              (K * ((d + 1 : ℕ) : ℝ) ^ 11) rankCost,
              ∀ hdense : DensityStep.HasDensePair t P.childOne P.childTwo
                  (1 / 512 : ℝ),
                Nonempty (TwoBohrEndpointPackage (p := p) t P hdense)

/-- A concrete local supply implies the exact producer expected by
KelleyMekaCount. -/
theorem terminalProducer_of_concreteSupply
    {K : ℝ} (hK : 0 < K) (hsupply : ConcreteTerminalSupply K) :
    KelleyMekaTerminalProducerHypothesis K := by
  refine ⟨hK, ?_⟩
  intro N A hA d hd
  obtain ⟨rankCost, p, hp, hlocal⟩ := hsupply N A hA d hd
  refine ⟨rankCost, ?_⟩
  intro t hscale hrank hno
  obtain ⟨P, hendpoint⟩ := hlocal t hscale hrank
  rcases DensityStep.densePair_or_controlledIncrement t P.plateau
      P.childOne P.childTwo P.smallOne P.smallTwo
      (by norm_num : (0 : ℝ) < 1 / 512) P.rankOne P.rankTwo P.cardOne P.cardTwo with
    hpair | hincrement
  · obtain ⟨Q⟩ := hendpoint hpair
    have hhigh_not :
        ¬ ((1 + (1 / 8 : ℝ) / 8) * (Q.base.carrier.card : ℝ)⁻¹ ≤
          BalancedRestriction.weightedLpNorm
            ((↑) ∘ LocalizedUnbalancing.smoothingWeight Q.D Q.E)
            (μ_[ℝ] (GroupCount.densePairEndpointSet P hpair) ○ᵈ
              μ (GroupCount.densePairEndpointSet P hpair))
            (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p)) := by
      intro hhigh
      apply hno
      obtain ⟨u, hdensity, hurank, hucard⟩ := Q.highNorm_increment hhigh
      refine ⟨u, ?_, hurank, hucard⟩
      calc
        (1025 / 1024 : ℝ) * t.density ≤
            (257 / 256 : ℝ) *
              GroupCount.densePairDensity t (1 / 512 : ℝ) := by
          simp only [GroupCount.densePairDensity]
          nlinarith [t.density_pos.le]
        _ ≤ u.density := hdensity
    have hstop :
        BalancedRestriction.weightedLpNorm
            ((↑) ∘ LocalizedUnbalancing.smoothingWeight Q.D Q.E)
            (μ_[ℝ] (GroupCount.densePairEndpointSet P hpair) ○ᵈ
              μ (GroupCount.densePairEndpointSet P hpair))
            (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p) <
          (1 + (1 / 8 : ℝ) / 8) * (Q.base.carrier.card : ℝ)⁻¹ :=
      lt_of_not_ge hhigh_not
    have hraw := balanced_of_twoBohr_concrete_stopping Q.base_regular
      Q.weight_regular Q.endpoint_nonempty
      Q.endpoint_subset Q.eta_pos Q.eta_narrow Q.D_nonempty Q.E_nonempty
      Q.D_small Q.E_small Q.rank_width Q.smoothing_support
      (by norm_num) (by norm_num) Q.boundary_width hp hstop
    let data := locatedTerminalDataOfTwoBohr t P hpair hp Q hraw
    exact ⟨data.certificate, data.alpha_lower, data.B_card, data.B'_card⟩
  · exfalso
    apply hno
    obtain ⟨u, hu⟩ := hincrement
    refine ⟨u, ?_⟩
    simpa only [show (1 + (1 / 512 : ℝ) / 2) =
        (1025 / 1024 : ℝ) by norm_num] using hu

#print axioms balanced_of_twoBohr_concrete_stopping
#print axioms controlledIncrement_of_le
#print axioms scaledBalanced_bound_of_raw
#print axioms holderCountCertificateOfRawDensePair
#print axioms terminalData_or_rankRegular_increment
#print axioms exists_terminal_rankRegular_chain_bounded_aux
#print axioms holderCertificates_of_rawConcreteSupply

end

end Erdos140.FinalAssembly
