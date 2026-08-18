import ErdosProblems.Erdos140.BohrBasic
import ErdosProblems.Erdos140.BalancedRestriction
import ErdosProblems.Erdos140.DensityStep
import ErdosProblems.Erdos140.FiniteConvolution
import ErdosProblems.Erdos140.HolderLifting

/-!
# The odd-cyclic progression-counting endpoint

This file performs the normalization-sensitive final counting step in the
Kelley--Meka argument.  If `A'` and `A''` are the translated local endpoint
and middle-term sets, then Holder lifting is applied on the doubled sets

`D = 2 B'` and `C = 2 A''`.

Injectivity of doubling gives `|D| = |B'|`, `|C| = |A''|`, and the exact
probability-normalized convolution identity

`P(A',A'') = |G| * mixedThreeAPCount A' A'' / (|A'|^2 |A''|)`.

The common translation taking `A'` and `A''` back into the original set is
then used to inject the mixed triples into the ordered progressions of that
set.  All constants (`1/2`, `1/8`, and `2/3`) are exposed literally.
-/

open Finset

namespace Erdos140
namespace GroupCount

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The image of a finite set under doubling. -/
def doubledFinset (S : Finset G) : Finset G :=
  S.image fun x ↦ x + x

@[simp] theorem mem_doubledFinset {S : Finset G} {x : G} :
    x ∈ doubledFinset S ↔ ∃ y ∈ S, y + y = x := by
  simp [doubledFinset]

theorem doubledFinset_nonempty {S : Finset G} (hS : S.Nonempty) :
    (doubledFinset S).Nonempty := by
  exact hS.image _

theorem doubledFinset_mono {S T : Finset G} (hST : S ⊆ T) :
    doubledFinset S ⊆ doubledFinset T := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_doubledFinset.mp hx
  exact mem_doubledFinset.mpr ⟨y, hST hy, rfl⟩

/-- Doubling preserves finite-set cardinality whenever it is injective on the
ambient group. -/
theorem card_doubledFinset (S : Finset G)
    (hdouble : Function.Injective (fun x : G ↦ x + x)) :
    #(doubledFinset S) = #S := by
  exact card_image_of_injective _ hdouble

/-- Consequently doubling preserves relative density. -/
theorem relativeDensity_doubledFinset (S T : Finset G)
    (hdouble : Function.Injective (fun x : G ↦ x + x)) :
    HolderLifting.relativeDensity (doubledFinset S) (doubledFinset T) =
      HolderLifting.relativeDensity S T := by
  simp only [HolderLifting.relativeDensity, card_doubledFinset S hdouble,
    card_doubledFinset T hdouble]

/-! ## The doubled Bohr carrier in an odd cyclic group -/

/-- Transporting Bohr data through an additive equivalence maps its carrier
exactly, not merely up to cardinality. -/
theorem image_bohrCarrier_eq_map
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (B : BohrData G) (e : G ≃+ H) :
    B.carrier.image e = (B.map e).carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (BohrData.mem_map_carrier B e y).2 hy
  · intro hx
    refine Finset.mem_image.mpr ⟨e.symm x, ?_, by simp⟩
    have hmap := (BohrData.mem_map_carrier B e (e.symm x)).1
    exact hmap (by simpa using hx)

/-- The transported Bohr datum whose carrier is `2 B`. -/
def doubledBohrData (M : ℕ) (hM : Odd M) (B : BohrData (ZMod M)) :
    BohrData (ZMod M) :=
  B.map (BohrData.zmodDoublingEquiv M hM)

theorem doubledFinset_bohrCarrier_eq_doubledBohrData
    {M : ℕ} [NeZero M] (hM : Odd M) (B : BohrData (ZMod M)) :
    doubledFinset B.carrier = (doubledBohrData M hM B).carrier := by
  rw [doubledFinset, doubledBohrData, ← image_bohrCarrier_eq_map]
  apply Finset.image_congr
  intro x _
  exact BohrData.zmodDoublingEquiv_apply M hM x

@[simp] theorem rank_doubledBohrData
    (M : ℕ) (hM : Odd M) (B : BohrData (ZMod M)) :
    (doubledBohrData M hM B).rank = B.rank := by
  exact BohrData.rank_map B (BohrData.zmodDoublingEquiv M hM)

@[simp] theorem card_doubledBohrData_carrier
    (M : ℕ) [NeZero M] (hM : Odd M) (B : BohrData (ZMod M)) :
    (doubledBohrData M hM B).carrier.card = B.carrier.card := by
  exact BohrData.card_map_zmodDoubling M hM B

/-- The normalized mixed-progression scalar used in Holder lifting.  The
indicators in `FiniteConvolution` have total mass one for counting measure;
the leading ambient cardinality converts the result to the normalized
ambient-measure convention used in the analytic argument. -/
def normalizedMixedProgression (A' A'' : Finset G) : ℝ :=
  (Fintype.card G : ℝ) *
    finiteInner
      (normalizedConvolution (normalizedIndicator A') (normalizedIndicator A'))
      (normalizedIndicator (doubledFinset A''))

/-- Exact normalized-indicator identity, in inverse-cardinality form. -/
theorem normalizedMixedProgression_eq
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    (A' A'' : Finset G) :
    normalizedMixedProgression A' A'' =
      (Fintype.card G : ℝ) * (mixedThreeAPCount A' A'' : ℝ) *
        (#A' : ℝ)⁻¹ ^ 2 * (#A'' : ℝ)⁻¹ := by
  rw [normalizedMixedProgression,
    doubledFinset,
    finiteInner_convolution_mixedDoubleIndicator hdouble]
  ring

/-- Exact normalized-indicator identity with a single explicit denominator. -/
theorem normalizedMixedProgression_eq_div
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A' A'' : Finset G} (hA' : A'.Nonempty) (hA'' : A''.Nonempty) :
    normalizedMixedProgression A' A'' =
      (Fintype.card G : ℝ) * (mixedThreeAPCount A' A'' : ℝ) /
        ((#A' : ℝ) ^ 2 * (#A'' : ℝ)) := by
  rw [normalizedMixedProgression_eq hdouble]
  have hA'card : (#A' : ℝ) ≠ 0 := by exact_mod_cast hA'.card_ne_zero
  have hA''card : (#A'' : ℝ) ≠ 0 := by exact_mod_cast hA''.card_ne_zero
  field_simp

/-- The same scalar is the local average over the doubled middle-term set.
This is the precise bridge to `HolderLifting.pairing_eq_localAverage`. -/
theorem normalizedMixedProgression_eq_localAverage
    {A' A'' : Finset G} (hA'' : A''.Nonempty) :
    normalizedMixedProgression A' A'' =
      HolderLifting.localAverage (doubledFinset A'') (fun x ↦
        (Fintype.card G : ℝ) *
          normalizedConvolution (normalizedIndicator A') (normalizedIndicator A') x) := by
  let D := doubledFinset A''
  let F := normalizedConvolution (normalizedIndicator A') (normalizedIndicator A')
  have hD : D.Nonempty := doubledFinset_nonempty hA''
  have hDcard : (#D : ℝ) ≠ 0 := by exact_mod_cast hD.card_ne_zero
  unfold normalizedMixedProgression HolderLifting.localAverage finiteInner
  change (Fintype.card G : ℝ) *
      ∑ x : G, F x * normalizedIndicator D x =
    (∑ x ∈ D, (Fintype.card G : ℝ) * F x) / (#D : ℝ)
  have hrestrict :
      (∑ x : G, F x * normalizedIndicator D x) =
        (∑ x ∈ D, F x) * (#D : ℝ)⁻¹ := by
    change (∑ x : G, F x * (if x ∈ D then (#D : ℝ)⁻¹ else 0)) = _
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter : univ.filter (fun x : G ↦ x ∈ D) = D := by ext; simp
    rw [hfilter, Finset.sum_mul]
  rw [hrestrict]
  rw [show (∑ x ∈ D, (Fintype.card G : ℝ) * F x) =
      (Fintype.card G : ℝ) * ∑ x ∈ D, F x by
    rw [Finset.mul_sum]]
  field_simp

/-! ## Conversion from the balanced-restriction norm to the Holder moment -/

/-- The counting-probability normalized indicator is a probability weight in
the sense used by `BalancedRestriction`. -/
theorem normalizedIndicator_isProbabilityWeight {S : Finset G} (hS : S.Nonempty) :
    BalancedRestriction.ProbabilityWeight (normalizedIndicator S) := by
  refine ⟨normalizedIndicator_nonneg S, ?_⟩
  exact sum_normalizedIndicator hS

/-- The weighted absolute moment for the uniform weight on `S` is exactly the
local moment used by Holder lifting. -/
theorem weightedAbsMoment_normalizedIndicator_eq_localMoment
    {S : Finset G} (hS : S.Nonempty) (p : ℕ) (f : G → ℝ) :
    weightedAbsMoment (normalizedIndicator S) f p =
      HolderLifting.localMoment S p f := by
  have hScard : (#S : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  unfold weightedAbsMoment HolderLifting.localMoment HolderLifting.localAverage
    normalizedIndicator
  change (∑ x : G, (if x ∈ S then (#S : ℝ)⁻¹ else 0) * |f x| ^ p) =
    (∑ x ∈ S, |f x| ^ p) / (#S : ℝ)
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilter : univ.filter (fun x : G ↦ x ∈ S) = S := by ext; simp
  rw [hfilter]
  rw [← Finset.mul_sum, div_eq_mul_inv]
  ring

/-- A balanced `L^p` bound on the concrete uniform probability measure gives
the power-moment bound expected by `HolderLifting`. -/
theorem localMoment_le_of_weightedLpNorm_le
    {S : Finset G} (hS : S.Nonempty) {p : ℕ} (hp : 0 < p)
    (f : G → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbalanced :
      BalancedRestriction.weightedLpNorm (normalizedIndicator S) f p ≤ C) :
    HolderLifting.localMoment S p f ≤ C ^ p := by
  have hprob := normalizedIndicator_isProbabilityWeight hS
  rw [← weightedAbsMoment_normalizedIndicator_eq_localMoment hS p f,
    ← BalancedRestriction.weightedLpNorm_pow hprob hp]
  exact pow_le_pow_left₀
    (BalancedRestriction.weightedLpNorm_nonneg hprob f p) hbalanced p

/-! ## Concrete terminal data from a located dense pair -/

/-- Generic, fully concrete Holder-count certificate.  The cyclic layer only
has to add its quantitative lower bound for `alpha^3 |B| |B'| / 2`; all set,
translation, doubling, approximation, and balanced-moment data live here. -/
structure HolderCountCertificate (original : Finset G) where
  A' : Finset G
  A'' : Finset G
  B : Finset G
  B' : Finset G
  translate : G
  alpha : ℝ
  p : ℕ
  f : G → ℝ
  A'_nonempty : A'.Nonempty
  A''_nonempty : A''.Nonempty
  B_nonempty : B.Nonempty
  A''_subset_B' : A'' ⊆ B'
  A'_sub_translate : ∀ x ∈ A', x - translate ∈ original
  A''_sub_translate : ∀ x ∈ A'', x - translate ∈ original
  alpha_nonneg : 0 ≤ alpha
  A'_density : alpha * (#B : ℝ) ≤ (#A' : ℝ)
  A''_density : alpha * (#B' : ℝ) ≤ (#A'' : ℝ)
  p_pos : 0 < p
  doubled_density :
    (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B'
  approximation :
    |(normalizedMixedProgression A' A'' -
        (Fintype.card G : ℝ) / (#B : ℝ)) -
        HolderLifting.pairing f (doubledFinset A'')| ≤
      ((Fintype.card G : ℝ) / (#B : ℝ)) / 8
  balanced_moment :
    HolderLifting.localMoment (doubledFinset B') p f ≤
      (((Fintype.card G : ℝ) / (#B : ℝ)) / 8) ^ p

/-- The canonical point selected from a terminal simultaneous dense pair. -/
noncomputable def densePairPoint {original : Finset G}
    {s : DensityStep.LocatedRestriction original}
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (h : DensityStep.HasDensePair s childOne childTwo epsilon) : G :=
  Classical.choose h

theorem densePairPoint_mem {original : Finset G}
    {s : DensityStep.LocatedRestriction original}
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (h : DensityStep.HasDensePair s childOne childTwo epsilon) :
    densePairPoint h ∈ s.ambient :=
  (Classical.choose_spec h).1

theorem densePairPoint_density_one {original : Finset G}
    {s : DensityStep.LocatedRestriction original}
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (h : DensityStep.HasDensePair s childOne childTwo epsilon) :
    (1 - epsilon) * s.density ≤
      localDensity s.restriction.set childOne.carrier (densePairPoint h) :=
  (Classical.choose_spec h).2.1

theorem densePairPoint_density_two {original : Finset G}
    {s : DensityStep.LocatedRestriction original}
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (h : DensityStep.HasDensePair s childOne childTwo epsilon) :
    (1 - epsilon) * s.density ≤
      localDensity s.restriction.set childTwo.carrier (densePairPoint h) :=
  (Classical.choose_spec h).2.2

/-- The endpoint fibre selected from a terminal dense-pair witness. -/
def densePairEndpointSet {original : Finset G}
    {s : DensityStep.LocatedRestriction original}
    {epsilon sizeCost : ℝ} {rankCost : ℕ}
    (P : DensityStep.NarrowingPackage s epsilon sizeCost rankCost)
    (h : DensityStep.HasDensePair s P.childOne P.childTwo epsilon) : Finset G :=
  DensityStep.narrowingSet s.restriction.set P.childOne.carrier (densePairPoint h)

/-- The middle-term fibre selected from the same terminal dense-pair point. -/
def densePairMiddleSet {original : Finset G}
    {s : DensityStep.LocatedRestriction original}
    {epsilon sizeCost : ℝ} {rankCost : ℕ}
    (P : DensityStep.NarrowingPackage s epsilon sizeCost rankCost)
    (h : DensityStep.HasDensePair s P.childOne P.childTwo epsilon) : Finset G :=
  DensityStep.narrowingSet s.restriction.set P.childTwo.carrier (densePairPoint h)

/-- The common relative-density lower bound of the two selected fibres. -/
def densePairDensity {original : Finset G}
    (s : DensityStep.LocatedRestriction original) (epsilon : ℝ) : ℝ :=
  (1 - epsilon) * s.density

/-- **Terminal conversion from an actual located dense pair.**

The finite sets and common translation are constructed from the selected
point of `HasDensePair`.  Their nonemptiness, containment, provenance, and
cardinality-density bounds are proved here.  The only analytic inputs are the
actual Holder approximation and the concrete balanced weighted-`L^p` bound;
the latter is converted to a local moment internally.  In particular this
constructor has no progression-count or certificate-shaped hypothesis. -/
noncomputable def holderCountCertificateOfDensePair
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {epsilon sizeCost : ℝ} {rankCost : ℕ}
    (P : DensityStep.NarrowingPackage s epsilon sizeCost rankCost)
    (hdense : DensityStep.HasDensePair s P.childOne P.childTwo epsilon)
    (_hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    {p : ℕ} (hp : 0 < p) (f : G → ℝ)
    (hpDensity : (2 / 3 : ℝ) ^ p ≤ densePairDensity s epsilon)
    (happrox :
      |(normalizedMixedProgression
            (densePairEndpointSet P hdense) (densePairMiddleSet P hdense) -
          (Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) -
          HolderLifting.pairing f (doubledFinset (densePairMiddleSet P hdense))| ≤
        ((Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) / 8)
    (hbalanced :
      BalancedRestriction.weightedLpNorm
          (normalizedIndicator (doubledFinset P.childTwo.carrier)) f p ≤
        ((Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) / 8) :
    HolderCountCertificate original := by
  let x : G := densePairPoint hdense
  let A' : Finset G := densePairEndpointSet P hdense
  let A'' : Finset G := densePairMiddleSet P hdense
  let B : Finset G := P.childOne.carrier
  let B' : Finset G := P.childTwo.carrier
  let alpha : ℝ := densePairDensity s epsilon
  have hOne : alpha ≤ localDensity s.restriction.set B x := by
    simpa [alpha, x, B, densePairDensity] using densePairPoint_density_one hdense
  have hTwo : alpha ≤ localDensity s.restriction.set B' x := by
    simpa [alpha, x, B', densePairDensity] using densePairPoint_density_two hdense
  have halpha : 0 < alpha := by
    exact mul_pos (sub_pos.mpr hepsilon_lt_one) s.density_pos
  have hA' : A'.Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos P.childOne.carrier_nonempty
    exact halpha.trans_le hOne
  have hA'' : A''.Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos P.childTwo.carrier_nonempty
    exact halpha.trans_le hTwo
  have hA''B' : A'' ⊆ B' := by
    exact DensityStep.narrowingSet_subset_carrier
      (B := P.childTwo.bohr) (rho := P.childTwo.outer)
      (A := s.restriction.set) (C := P.childTwo.carrier)
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
    have hBpos : (0 : ℝ) < #B := by exact_mod_cast P.childOne.carrier_nonempty.card_pos
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      P.childOne.carrier_nonempty x] at hOne
    exact (le_div_iff₀ hBpos).mp hOne
  have hDensityTwo : alpha * (#B' : ℝ) ≤ (#A'' : ℝ) := by
    have hB'pos : (0 : ℝ) < #B' := by exact_mod_cast P.childTwo.carrier_nonempty.card_pos
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      P.childTwo.carrier_nonempty x] at hTwo
    exact (le_div_iff₀ hB'pos).mp hTwo
  have hRelative :
      (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B' := by
    calc
      (2 / 3 : ℝ) ^ p ≤ alpha := hpDensity
      _ ≤ localDensity s.restriction.set B' x := by
        simpa [alpha, x, B', densePairDensity] using
          densePairPoint_density_two hdense
      _ = HolderLifting.relativeDensity A'' B' := by
        rw [DensityStep.localDensity_eq_card_narrowingSet_div
          P.childTwo.carrier_nonempty x]
        rfl
  have hDoubledB' : (doubledFinset B').Nonempty :=
    doubledFinset_nonempty P.childTwo.carrier_nonempty
  have hMoment :
      HolderLifting.localMoment (doubledFinset B') p f ≤
        (((Fintype.card G : ℝ) / (#B : ℝ)) / 8) ^ p := by
    apply localMoment_le_of_weightedLpNorm_le hDoubledB' hp f (by positivity)
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
      B_nonempty := P.childOne.carrier_nonempty
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

/-- A half-main-term Holder conclusion gives an exact mixed-count lower
bound. -/
theorem mixedThreeAPCount_lower_bound_of_half
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A' A'' : Finset G} (hA' : A'.Nonempty) (hA'' : A''.Nonempty)
    {mainTerm : ℝ}
    (hhalf : mainTerm / 2 ≤ normalizedMixedProgression A' A'') :
    mainTerm * (#A' : ℝ) ^ 2 * (#A'' : ℝ) /
        (2 * (Fintype.card G : ℝ)) ≤
      (mixedThreeAPCount A' A'' : ℝ) := by
  have hG : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hdenom : (0 : ℝ) < (#A' : ℝ) ^ 2 * (#A'' : ℝ) := by
    positivity
  rw [normalizedMixedProgression_eq_div hdouble hA' hA''] at hhalf
  have hmul :
      mainTerm / 2 * ((#A' : ℝ) ^ 2 * (#A'' : ℝ)) ≤
        (Fintype.card G : ℝ) * (mixedThreeAPCount A' A'' : ℝ) :=
    (le_div_iff₀ hdenom).mp hhalf
  rw [div_le_iff₀ (mul_pos (by norm_num) hG)]
  nlinarith

/-- The complete finite Holder endpoint.  The local set used by Holder is
literally `2 B'`, its dense subset is literally `2 A''`, and the resulting
mixed triples are translated injectively into progressions in `A`. -/
theorem threeAPCount_lower_bound_of_holder
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A A' A'' B' : Finset G} (hA' : A'.Nonempty) (hA'' : A''.Nonempty)
    (hA''B' : A'' ⊆ B') (t : G)
    (hA'trans : ∀ x ∈ A', x - t ∈ A)
    (hA''trans : ∀ x ∈ A'', x - t ∈ A)
    {p : ℕ} (hp : 0 < p) (f : G → ℝ) {mainTerm : ℝ}
    (hmain : 0 < mainTerm)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B')
    (happrox :
      |(normalizedMixedProgression A' A'' - mainTerm) -
          HolderLifting.pairing f (doubledFinset A'')| ≤ mainTerm / 8)
    (hbalanced :
      HolderLifting.localMoment (doubledFinset B') p f ≤ (mainTerm / 8) ^ p) :
    mainTerm * (#A' : ℝ) ^ 2 * (#A'' : ℝ) /
        (2 * (Fintype.card G : ℝ)) ≤ (threeAPCount A : ℝ) := by
  have hC : (doubledFinset A'').Nonempty := doubledFinset_nonempty hA''
  have hCB : doubledFinset A'' ⊆ doubledFinset B' := doubledFinset_mono hA''B'
  have hdensity' :
      (2 / 3 : ℝ) ^ p ≤
        HolderLifting.relativeDensity (doubledFinset A'') (doubledFinset B') := by
    rwa [relativeDensity_doubledFinset A'' B' hdouble]
  have hhalf :
      mainTerm / 2 ≤ normalizedMixedProgression A' A'' :=
    HolderLifting.half_main_term_of_balanced_eighth hC hCB p hp f
      (normalizedMixedProgression A' A'') mainTerm hmain hdensity' happrox hbalanced
  have hmixed :=
    mixedThreeAPCount_lower_bound_of_half hdouble hA' hA'' hhalf
  have hcountNat : mixedThreeAPCount A' A'' ≤ threeAPCount A :=
    mixedThreeAPCount_le_threeAPCount_of_sub_translate t hA'trans hA''trans
  have hcountReal :
      (mixedThreeAPCount A' A'' : ℝ) ≤ (threeAPCount A : ℝ) := by
    exact_mod_cast hcountNat
  exact hmixed.trans hcountReal

/-- Version of `threeAPCount_lower_bound_of_holder` consuming the concrete
weighted-`L^p` conclusion returned by `BalancedRestriction`, rather than
asking for the corresponding power moment separately. -/
theorem threeAPCount_lower_bound_of_balancedLp
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A A' A'' B' : Finset G} (hA' : A'.Nonempty) (hA'' : A''.Nonempty)
    (hB' : B'.Nonempty) (hA''B' : A'' ⊆ B') (t : G)
    (hA'trans : ∀ x ∈ A', x - t ∈ A)
    (hA''trans : ∀ x ∈ A'', x - t ∈ A)
    {p : ℕ} (hp : 0 < p) (f : G → ℝ) {mainTerm : ℝ}
    (hmain : 0 < mainTerm)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B')
    (happrox :
      |(normalizedMixedProgression A' A'' - mainTerm) -
          HolderLifting.pairing f (doubledFinset A'')| ≤ mainTerm / 8)
    (hbalanced :
      BalancedRestriction.weightedLpNorm
          (normalizedIndicator (doubledFinset B')) f p ≤ mainTerm / 8) :
    mainTerm * (#A' : ℝ) ^ 2 * (#A'' : ℝ) /
        (2 * (Fintype.card G : ℝ)) ≤ (threeAPCount A : ℝ) := by
  have hD : (doubledFinset B').Nonempty := doubledFinset_nonempty hB'
  have hmoment :
      HolderLifting.localMoment (doubledFinset B') p f ≤
        (mainTerm / 8) ^ p :=
    localMoment_le_of_weightedLpNorm_le hD hp f (by positivity) hbalanced
  exact threeAPCount_lower_bound_of_holder hdouble hA' hA'' hA''B' t
    hA'trans hA''trans hp f hmain hdensity happrox hmoment

/-- Cardinality/density form of the finite Holder endpoint.  If `A'` has
relative density at least `alpha` in `B`, and `A''` has relative density at
least `alpha` in `B'`, then the progression count is at least
`alpha^3 |B| |B'| / 2`. -/
theorem threeAPCount_lower_bound_of_holder_density
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A A' A'' B B' : Finset G}
    (hA' : A'.Nonempty) (hA'' : A''.Nonempty) (hB : B.Nonempty)
    (hA''B' : A'' ⊆ B') (t : G)
    (hA'trans : ∀ x ∈ A', x - t ∈ A)
    (hA''trans : ∀ x ∈ A'', x - t ∈ A)
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hA'density : alpha * (#B : ℝ) ≤ (#A' : ℝ))
    (hA''density : alpha * (#B' : ℝ) ≤ (#A'' : ℝ))
    {p : ℕ} (hp : 0 < p) (f : G → ℝ)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B')
    (happrox :
      |(normalizedMixedProgression A' A'' -
          (Fintype.card G : ℝ) / (#B : ℝ)) -
          HolderLifting.pairing f (doubledFinset A'')| ≤
        ((Fintype.card G : ℝ) / (#B : ℝ)) / 8)
    (hbalanced :
      HolderLifting.localMoment (doubledFinset B') p f ≤
        (((Fintype.card G : ℝ) / (#B : ℝ)) / 8) ^ p) :
    alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2 ≤
      (threeAPCount A : ℝ) := by
  have hG : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hBcard : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  have hmain : (0 : ℝ) < (Fintype.card G : ℝ) / (#B : ℝ) :=
    div_pos hG hBcard
  have hlower := threeAPCount_lower_bound_of_holder hdouble hA' hA'' hA''B' t
    hA'trans hA''trans hp f hmain hdensity happrox hbalanced
  have hsquare :
      (alpha * (#B : ℝ)) ^ 2 ≤ (#A' : ℝ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg halpha hBcard.le) hA'density 2
  have hnumer :
      alpha ^ 3 * (#B : ℝ) ^ 2 * (#B' : ℝ) ≤
        (#A' : ℝ) ^ 2 * (#A'' : ℝ) := by
    have hmul := mul_le_mul hsquare hA''density
      (mul_nonneg halpha (Nat.cast_nonneg _)) (sq_nonneg (#A' : ℝ))
    nlinarith only [hmul]
  have hleft :
      alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2 =
        (alpha ^ 3 * (#B : ℝ) ^ 2 * (#B' : ℝ)) /
          (2 * (#B : ℝ)) := by
    field_simp
  have hright :
      ((Fintype.card G : ℝ) / (#B : ℝ)) * (#A' : ℝ) ^ 2 *
          (#A'' : ℝ) / (2 * (Fintype.card G : ℝ)) =
        ((#A' : ℝ) ^ 2 * (#A'' : ℝ)) / (2 * (#B : ℝ)) := by
    field_simp
  rw [hright] at hlower
  rw [hleft]
  exact (div_le_div_of_nonneg_right hnumer (by positivity)).trans hlower

namespace HolderCountCertificate

/-- Every concrete Holder certificate gives its advertised mixed-progression
lower bound in the original set. -/
theorem count_bound {original : Finset G} (c : HolderCountCertificate original)
    (hdouble : Function.Injective (fun x : G ↦ x + x)) :
    c.alpha ^ 3 * (#c.B : ℝ) * (#c.B' : ℝ) / 2 ≤
      (threeAPCount original : ℝ) := by
  exact threeAPCount_lower_bound_of_holder_density hdouble
    c.A'_nonempty c.A''_nonempty c.B_nonempty c.A''_subset_B' c.translate
    c.A'_sub_translate c.A''_sub_translate c.alpha_nonneg c.A'_density
    c.A''_density c.p_pos c.f c.doubled_density c.approximation c.balanced_moment

end HolderCountCertificate

/-- Density form consuming the balanced weighted norm directly. -/
theorem threeAPCount_lower_bound_of_balancedLp_density
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A A' A'' B B' : Finset G}
    (hA' : A'.Nonempty) (hA'' : A''.Nonempty) (hB : B.Nonempty)
    (hB' : B'.Nonempty) (hA''B' : A'' ⊆ B') (t : G)
    (hA'trans : ∀ x ∈ A', x - t ∈ A)
    (hA''trans : ∀ x ∈ A'', x - t ∈ A)
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hA'density : alpha * (#B : ℝ) ≤ (#A' : ℝ))
    (hA''density : alpha * (#B' : ℝ) ≤ (#A'' : ℝ))
    {p : ℕ} (hp : 0 < p) (f : G → ℝ)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B')
    (happrox :
      |(normalizedMixedProgression A' A'' -
          (Fintype.card G : ℝ) / (#B : ℝ)) -
          HolderLifting.pairing f (doubledFinset A'')| ≤
        ((Fintype.card G : ℝ) / (#B : ℝ)) / 8)
    (hbalanced :
      BalancedRestriction.weightedLpNorm
          (normalizedIndicator (doubledFinset B')) f p ≤
        ((Fintype.card G : ℝ) / (#B : ℝ)) / 8) :
    alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2 ≤
      (threeAPCount A : ℝ) := by
  have hG : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hBcard : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  have hmain : (0 : ℝ) < (Fintype.card G : ℝ) / (#B : ℝ) :=
    div_pos hG hBcard
  have hlower := threeAPCount_lower_bound_of_balancedLp hdouble hA' hA'' hB'
    hA''B' t hA'trans hA''trans hp f hmain hdensity happrox hbalanced
  have hsquare :
      (alpha * (#B : ℝ)) ^ 2 ≤ (#A' : ℝ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg halpha hBcard.le) hA'density 2
  have hnumer :
      alpha ^ 3 * (#B : ℝ) ^ 2 * (#B' : ℝ) ≤
        (#A' : ℝ) ^ 2 * (#A'' : ℝ) := by
    have hmul := mul_le_mul hsquare hA''density
      (mul_nonneg halpha (Nat.cast_nonneg _)) (sq_nonneg (#A' : ℝ))
    nlinarith only [hmul]
  have hleft :
      alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2 =
        (alpha ^ 3 * (#B : ℝ) ^ 2 * (#B' : ℝ)) /
          (2 * (#B : ℝ)) := by
    field_simp
  have hright :
      ((Fintype.card G : ℝ) / (#B : ℝ)) * (#A' : ℝ) ^ 2 *
          (#A'' : ℝ) / (2 * (Fintype.card G : ℝ)) =
        ((#A' : ℝ) ^ 2 * (#A'' : ℝ)) / (2 * (#B : ℝ)) := by
    field_simp
  rw [hright] at hlower
  rw [hleft]
  exact (div_le_div_of_nonneg_right hnumer (by positivity)).trans hlower

/-- A form that can be used directly for the exponential cyclic counting
statement once the balanced-restriction output supplies the final Bohr
cardinality product. -/
theorem cyclic_count_bound_of_holder_density
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A A' A'' B B' : Finset G}
    (hA' : A'.Nonempty) (hA'' : A''.Nonempty) (hB : B.Nonempty)
    (hA''B' : A'' ⊆ B') (t : G)
    (hA'trans : ∀ x ∈ A', x - t ∈ A)
    (hA''trans : ∀ x ∈ A'', x - t ∈ A)
    {alpha K : ℝ} {d p : ℕ} (halpha : 0 ≤ alpha)
    (hA'density : alpha * (#B : ℝ) ≤ (#A' : ℝ))
    (hA''density : alpha * (#B' : ℝ) ≤ (#A'' : ℝ))
    (hp : 0 < p) (f : G → ℝ)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B')
    (happrox :
      |(normalizedMixedProgression A' A'' -
          (Fintype.card G : ℝ) / (#B : ℝ)) -
          HolderLifting.pairing f (doubledFinset A'')| ≤
        ((Fintype.card G : ℝ) / (#B : ℝ)) / 8)
    (hbalanced :
      HolderLifting.localMoment (doubledFinset B') p f ≤
        (((Fintype.card G : ℝ) / (#B : ℝ)) / 8) ^ p)
    (hquant : Real.exp (-K * (d : ℝ) ^ 12) * (Fintype.card G : ℝ) ^ 2 ≤
      alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2) :
    Real.exp (-K * (d : ℝ) ^ 12) * (Fintype.card G : ℝ) ^ 2 ≤
      (threeAPCount A : ℝ) := by
  exact hquant.trans <|
    threeAPCount_lower_bound_of_holder_density hdouble hA' hA'' hB hA''B' t
      hA'trans hA''trans halpha hA'density hA''density hp f hdensity happrox hbalanced

/-- Odd cyclic specialization: doubling is supplied by the explicit additive
automorphism from `BohrBasic`. -/
theorem zmod_cyclic_count_bound_of_holder_density
    {M : ℕ} [NeZero M] (hM : Odd M)
    {A A' A'' B B' : Finset (ZMod M)}
    (hA' : A'.Nonempty) (hA'' : A''.Nonempty) (hB : B.Nonempty)
    (hA''B' : A'' ⊆ B') (t : ZMod M)
    (hA'trans : ∀ x ∈ A', x - t ∈ A)
    (hA''trans : ∀ x ∈ A'', x - t ∈ A)
    {alpha K : ℝ} {d p : ℕ} (halpha : 0 ≤ alpha)
    (hA'density : alpha * (#B : ℝ) ≤ (#A' : ℝ))
    (hA''density : alpha * (#B' : ℝ) ≤ (#A'' : ℝ))
    (hp : 0 < p) (f : ZMod M → ℝ)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B')
    (happrox :
      |(normalizedMixedProgression A' A'' -
          (Fintype.card (ZMod M) : ℝ) / (#B : ℝ)) -
          HolderLifting.pairing f (doubledFinset A'')| ≤
        ((Fintype.card (ZMod M) : ℝ) / (#B : ℝ)) / 8)
    (hbalanced :
      HolderLifting.localMoment (doubledFinset B') p f ≤
        (((Fintype.card (ZMod M) : ℝ) / (#B : ℝ)) / 8) ^ p)
    (hquant : Real.exp (-K * (d : ℝ) ^ 12) *
        (Fintype.card (ZMod M) : ℝ) ^ 2 ≤
      alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2) :
    Real.exp (-K * (d : ℝ) ^ 12) *
        (Fintype.card (ZMod M) : ℝ) ^ 2 ≤ (threeAPCount A : ℝ) := by
  apply cyclic_count_bound_of_holder_density
    (BohrData.zmodDoublingEquiv M hM).injective hA' hA'' hB hA''B' t
    hA'trans hA''trans halpha hA'density hA''density hp f hdensity happrox hbalanced
    hquant

#print axioms normalizedMixedProgression_eq
#print axioms normalizedMixedProgression_eq_localAverage
#print axioms localMoment_le_of_weightedLpNorm_le
#print axioms holderCountCertificateOfDensePair
#print axioms HolderCountCertificate.count_bound
#print axioms threeAPCount_lower_bound_of_holder
#print axioms threeAPCount_lower_bound_of_balancedLp_density
#print axioms threeAPCount_lower_bound_of_holder_density
#print axioms zmod_cyclic_count_bound_of_holder_density

end

end GroupCount
end Erdos140
