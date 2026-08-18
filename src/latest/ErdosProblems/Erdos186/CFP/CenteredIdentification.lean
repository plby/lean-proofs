/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Preprocessing

/-!
# Centered minimal-box coordinates

The canonical minimal-box identification is affine: the coordinate of zero
need not be the zero vector.  The random-partition and generator-completion
stages need a coordinate map which really sends the distinguished source
origin to zero.  We center the canonical coordinates and reprove the two
sumset comparisons behind the finite relative-index estimate.  Centering
does not cost a larger coefficient box: an exact `h`-term centered sum is a
fixed translate of the corresponding exact `h`-term affine-coordinate sum.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace Stability

/-- Canonical minimal-box coordinates translated so that source zero maps
to the coordinate origin. -/
def centeredMinimalIdentificationFamily {A : Finset ℤ}
    {relevant : Finset ℕ} (hproper : RelevantBoxesProper A relevant) :
    (d : ℕ) → ℤ → LatticePoint d :=
  fun d z ↦ minimalIdentificationFamily hproper d z -
    minimalIdentificationFamily hproper d 0

@[simp]
theorem centeredMinimalIdentificationFamily_zero {A : Finset ℤ}
    {relevant : Finset ℕ} (hproper : RelevantBoxesProper A relevant)
    (d : ℕ) :
    centeredMinimalIdentificationFamily hproper d 0 = 0 := by
  simp [centeredMinimalIdentificationFamily]

end Stability

namespace Preprocessing

/-- Centering an affine bounding-box identification makes step evaluation
recover the represented integer exactly. -/
theorem stepEvaluation_centeredIdentificationMap
    {A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ A) (z : {z // z ∈ A}) :
    stepEvaluation P.progression
        (P.identificationMap hproper z -
          P.identificationMap hproper ⟨0, hzero⟩) = z.1 := by
  rw [map_sub, stepEvaluation_identificationMap P hproper z,
    stepEvaluation_identificationMap P hproper ⟨0, hzero⟩]
  change (z.1 - P.progression.offset 0) -
    (0 - P.progression.offset 0) = z.1
  omega

/-- Abstract centered-coordinate lower bound.  If an additive evaluation
sends every coordinate generator back to its source integer, coordinate
iterated sums are at least as numerous as ordinary multifold sums. -/
theorem card_multifoldSumset_le_ambientSubsetIteratedSumset_of_evaluation
    {A B : Finset ℤ} {d h : ℕ} (hBA : B ⊆ A)
    (phi : ℤ → LatticePoint d) (eval : LatticePoint d →+ ℤ)
    (heval : ∀ z (hz : z ∈ A), eval (phi z) = z) :
    (GrowthLemmas.multifoldSumset h B).card ≤
      (constantIteratedSumset
        (ambientSubsetGeneratorFinset phi A B hBA) h).card := by
  classical
  let Gamma := Stability.generatedSubgroup phi A
  let X := ambientSubsetGeneratorFinset phi A B hBA
  let S := constantIteratedSumset X h
  let e : Gamma →+ ℤ := eval.comp Gamma.subtype
  let F := GrowthLemmas.multifoldSumset h B
  have hFsub : F ⊆ S.image e := by
    intro z hz
    obtain ⟨f, hf, hsum⟩ := GrowthLemmas.mem_multifoldSumset_iff.mp hz
    let g : Fin h → Gamma := fun i ↦
      ⟨phi (f i), Stability.image_mem_generatedSubgroup (hBA (hf i))⟩
    have hg (i : Fin h) : g i ∈ X := by
      rw [show X = insert 0 (B.attach.image fun b ↦
          ⟨phi b.1, Stability.image_mem_generatedSubgroup (hBA b.2)⟩) by
        rfl]
      apply Finset.mem_insert.mpr
      right
      exact Finset.mem_image.mpr ⟨⟨f i, hf i⟩, by simp, rfl⟩
    have hgsum : (∑ i, g i) ∈ S := by
      apply mem_constantIteratedSumset_iff.mpr
      exact ⟨g, hg, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨∑ i, g i, hgsum, ?_⟩
    dsimp only [e]
    change eval (Gamma.subtype (∑ i, g i)) = z
    have hcoeg : Gamma.subtype (∑ i, g i) =
        ∑ i, Gamma.subtype (g i) := by
      simpa using map_sum Gamma.subtype g (Finset.univ : Finset (Fin h))
    rw [hcoeg, map_sum]
    change (∑ i, eval (phi (f i))) = z
    simp_rw [heval (f _) (hBA (hf _))]
    exact hsum
  calc
    F.card ≤ (S.image e).card := Finset.card_le_card hFsub
    _ ≤ S.card := Finset.card_image_le

/-- Source-specific specialization for the centered canonical minimal-box
coordinates. -/
theorem card_multifoldSumset_le_centeredMinimalIdentificationIteratedSumset
    {A B : Finset ℤ} {d h : ℕ} {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper A relevant)
    (hd : d ∈ relevant) (hzero : 0 ∈ A) (hBA : B ⊆ A) :
    (GrowthLemmas.multifoldSumset h B).card ≤
      (constantIteratedSumset
        (ambientSubsetGeneratorFinset
          (Stability.centeredMinimalIdentificationFamily hproper d)
          A B hBA) h).card := by
  apply card_multifoldSumset_le_ambientSubsetIteratedSumset_of_evaluation
    hBA (Stability.centeredMinimalIdentificationFamily hproper d)
    (stepEvaluation
      (BoundingBox.dBoundingBox A d (hproper.positive hd)).progression)
  intro z hz
  rw [Stability.centeredMinimalIdentificationFamily,
    Stability.minimalIdentificationFamily_apply hproper hd hz,
    Stability.minimalIdentificationFamily_apply hproper hd hzero]
  exact stepEvaluation_centeredIdentificationMap
    (BoundingBox.dBoundingBox A d (hproper.positive hd))
    (hproper.proper hd) hzero ⟨z, hz⟩

/-- Exact upper coefficient-box bound for centered affine coordinates.
Although an individual centered coordinate may have negative entries, an
exact `k`-term sum becomes an ordinary nonnegative-coordinate sum after the
single translation by `k * raw(0)`. -/
theorem card_centeredCoordinateGeneratorIteratedSumset_le_dilate_volume
    {A : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP A d) (hproper : P.progression.Proper)
    (raw centered : ℤ → LatticePoint d) (hzero : 0 ∈ A)
    (hraw : ∀ z (hz : z ∈ A), raw z =
      P.identificationMap hproper ⟨z, hz⟩)
    (hcentered : ∀ z (hz : z ∈ A), centered z = raw z - raw 0)
    (k : ℕ) :
    (constantIteratedSumset (coordinateGeneratorFinset centered A) k).card ≤
      (P.progression.dilate k).volume := by
  classical
  let Gamma := Stability.generatedSubgroup centered A
  let X := coordinateGeneratorFinset centered A
  let S := constantIteratedSumset X k
  let shift : Gamma → LatticePoint d := fun x ↦ x.1 + k • raw 0
  have hshiftInjective : Function.Injective shift := by
    intro x y hxy
    apply Subtype.ext
    exact add_right_cancel hxy
  have hrawBox : A.image raw ⊆ coordinateBox P.progression 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [hraw a ha]
    exact identificationMap_mem_coordinateBox P hproper ⟨a, ha⟩
  have hshiftSubset : S.image shift ⊆ coordinateBox P.progression k := by
    intro y hy
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨f, hf, hsum⟩ := mem_constantIteratedSumset_iff.mp hxS
    have hterm : ∀ i : Fin k, ∃ a ∈ A, (f i).1 = centered a := by
      intro i
      have hfi := hf i
      rw [show X = insert 0 (A.attach.image fun a ↦
          ⟨centered a.1, Stability.image_mem_generatedSubgroup a.2⟩) by
        rfl] at hfi
      rcases Finset.mem_insert.mp hfi with hfi | hfi
      · refine ⟨0, hzero, ?_⟩
        rw [hfi, hcentered 0 hzero]
        simp
      · obtain ⟨a, _ha, hai⟩ := Finset.mem_image.mp hfi
        exact ⟨a.1, a.2, (congrArg Subtype.val hai).symm⟩
    choose a ha hfa using hterm
    let g : Fin k → LatticePoint d := fun i ↦ raw (a i)
    have hg (i : Fin k) : g i ∈ A.image raw :=
      Finset.mem_image.mpr ⟨a i, ha i, rfl⟩
    have hgsum : (∑ i, g i) ∈
        constantIteratedSumset (A.image raw) k :=
      mem_constantIteratedSumset_iff.mpr ⟨g, hg, rfl⟩
    have hsumBox : (∑ i, g i) ∈ coordinateBox P.progression k :=
      constantIteratedSumset_subset_coordinateBox P.progression
        (A.image raw) hrawBox k hgsum
    have hxsum : (x.1 : LatticePoint d) = ∑ i, centered (a i) := by
      rw [← hsum]
      change Gamma.subtype (∑ i, f i) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      exact hfa i
    have hshiftEq : shift x = ∑ i, g i := by
      funext j
      simp only [shift, hxsum, g, Finset.sum_apply, Pi.add_apply,
        Pi.smul_apply, nsmul_eq_mul, hcentered (a _) (ha _), Pi.sub_apply]
      simp
    rw [hshiftEq]
    exact hsumBox
  calc
    (constantIteratedSumset (coordinateGeneratorFinset centered A) k).card =
        S.card := rfl
    _ = (S.image shift).card :=
      (Finset.card_image_of_injective S hshiftInjective).symm
    _ ≤ (coordinateBox P.progression k).card :=
      Finset.card_le_card hshiftSubset
    _ = (P.progression.dilate k).volume := card_coordinateBox _ _

/-- Canonical centered-coordinate specialization of the exact upper bound. -/
theorem card_centeredMinimalIdentificationIteratedSumset_le_dilate_volume
    {A : Finset ℤ} {d k : ℕ} {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper A relevant)
    (hd : d ∈ relevant) (hzero : 0 ∈ A) :
    (constantIteratedSumset
        (coordinateGeneratorFinset
          (Stability.centeredMinimalIdentificationFamily hproper d) A) k).card ≤
      ((BoundingBox.dBoundingBox A d
        (hproper.positive hd)).progression.dilate k).volume := by
  let P := BoundingBox.dBoundingBox A d (hproper.positive hd)
  let raw := Stability.minimalIdentificationFamily hproper d
  apply card_centeredCoordinateGeneratorIteratedSumset_le_dilate_volume
    P (hproper.proper hd) raw
      (Stability.centeredMinimalIdentificationFamily hproper d) hzero
  · intro z hz
    exact Stability.minimalIdentificationFamily_apply hproper hd hz
  · intro z hz
    rfl

/-- Rank-flexible relative-index estimate for the centered canonical
coordinates.  This is the source-specific replacement for trying to
transfer the raw affine-coordinate index bound by a generic translation,
which would be false for arbitrary maps. -/
theorem HApproximation.centeredMinimalIdentification_relIndex_general_ne_zero_and_le
    {A B : Finset ℤ} {x D n h d e scaleNum scaleDen : ℕ}
    {relevant : Finset ℕ}
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hBA : B ⊆ A) (hloss : A.card ≤ B.card + x)
    (WA : HDimension.HApproximation A h d scaleNum scaleDen)
    (WB : HDimension.HApproximation B h e scaleNum scaleDen)
    (hdmem : d ∈ relevant)
    (hproper : Stability.RelevantBoxesProper A relevant)
    (he : 0 < e) (hdD : d ≤ D) (heD : e ≤ D)
    (hhn : h ≤ n) (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hnumericB :
      (2 * scaleDen) ^ e * (h + 1) ^ (e - 1) <
        (scaleNum * h) ^ e)
    (hlarge : 4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D ≤ h) :
    let phi := Stability.centeredMinimalIdentificationFamily hproper d
    (Stability.generatedSubgroup phi B).relIndex
          (Stability.generatedSubgroup phi A) ≠ 0 ∧
      (Stability.generatedSubgroup phi B).relIndex
          (Stability.generatedSubgroup phi A) ≤
        4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D := by
  classical
  let phi := Stability.centeredMinimalIdentificationFamily hproper d
  let X := coordinateGeneratorFinset phi A
  let XB := ambientSubsetGeneratorFinset phi A B hBA
  let S := constantIteratedSumset XB h
  have hSsub : S ⊆ constantIteratedSumset X h :=
    constantIteratedSumset_mono_set
      (ambientSubsetGeneratorFinset_subset phi hBA) h
  have hSH : ∀ s ∈ S,
      (s.1 : LatticePoint d) ∈ Stability.generatedSubgroup phi B := by
    intro s hs
    exact ambientSubsetIteratedSumset_mem_generatedSubgroup phi hBA hs
  have hpack := quotientGeneratorIteratedSumset_card_mul_le_twice
    (Stability.generatedSubgroup_mono hBA) X S h hSsub hSH
  have hsumLower : (GrowthLemmas.multifoldSumset h B).card ≤ S.card := by
    exact card_multifoldSumset_le_centeredMinimalIdentificationIteratedSumset
      hproper hdmem WA.zero_mem hBA
  have hambientUpper : (constantIteratedSumset X (2 * h)).card ≤
      ((BoundingBox.dBoundingBox A d
        (hproper.positive hdmem)).progression.dilate (2 * h)).volume := by
    exact card_centeredMinimalIdentificationIteratedSumset_le_dilate_volume
      hproper hdmem WA.zero_mem
  have hvolume :
      ((BoundingBox.dBoundingBox A d
        (hproper.positive hdmem)).progression.dilate (2 * h)).volume ≤
      (4 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e) *
        (GrowthLemmas.multifoldSumset h B).card := by
    exact HApproximation.two_mul_dilate_volume_le_general_indexBound_mul_card
      hstable hBA hloss WA WB (hproper.positive hdmem) he heD hhn hA hnumericB
  let Kde := 4 * (6 * scaleDen) ^ d * (4 * scaleDen) ^ e
  let KD := 4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D
  have hKde : Kde ≤ KD := by
    dsimp only [Kde, KD]
    have h6pos : 1 ≤ 6 * scaleDen := by
      have := WA.scaleDen_pos
      omega
    have h4pos : 1 ≤ 4 * scaleDen := by
      have := WA.scaleDen_pos
      omega
    have hp6 : (6 * scaleDen) ^ d ≤ (6 * scaleDen) ^ D :=
      pow_le_pow_right' h6pos hdD
    have hp4 : (4 * scaleDen) ^ e ≤ (4 * scaleDen) ^ D :=
      pow_le_pow_right' h4pos heD
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hp6) hp4
  have hmul :
      (quotientGeneratorIteratedSumset
        (Stability.generatedSubgroup phi B)
        (Stability.generatedSubgroup phi A) X h).card * S.card ≤
        KD * S.card := by
    calc
      _ ≤ (constantIteratedSumset X (2 * h)).card := hpack
      _ ≤ ((BoundingBox.dBoundingBox A d
          (hproper.positive hdmem)).progression.dilate (2 * h)).volume :=
        hambientUpper
      _ ≤ Kde * (GrowthLemmas.multifoldSumset h B).card := hvolume
      _ ≤ Kde * S.card := by gcongr
      _ ≤ KD * S.card := Nat.mul_le_mul_right S.card hKde
  have hSpos : 0 < S.card := by
    have hzeroB : 0 ∈ GrowthLemmas.multifoldSumset h B :=
      GrowthLemmas.zero_mem_multifoldSumset WB.zero_mem h
    have hpositive : 0 < (GrowthLemmas.multifoldSumset h B).card :=
      Finset.card_pos.mpr ⟨0, hzeroB⟩
    omega
  have hcard :
      (quotientGeneratorIteratedSumset
        (Stability.generatedSubgroup phi B)
        (Stability.generatedSubgroup phi A)
        (coordinateGeneratorFinset phi A) h).card ≤ KD := by
    dsimp only [X] at hmul
    exact Nat.le_of_mul_le_mul_right hmul hSpos
  apply generatedSubgroup_relIndex_ne_zero_and_le_of_quotient_sumset
    phi hBA (by simpa only [KD] using hlarge)
  simpa only [KD] using hcard

/-- The quotient-packing bound, packaged for the pruning iterator with the
centered canonical coordinates.  This is the centered analogue of
`accessibleSpanIndexBound_of_hApproximations`; it has exactly the same
source-facing approximation hypotheses and the same index bound. -/
theorem accessibleSpanIndexBound_of_centeredHApproximations
    {A : Finset ℤ} {x D n scaleNum scaleDen deletionCap : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper A relevant)
    (hAt : {d // d ∈ relevant} → ℕ)
    (hambient : ∀ d : {d // d ∈ relevant},
      HDimension.HApproximation A (hAt d) d.1 scaleNum scaleDen)
    (hrank_le : ∀ d : {d // d ∈ relevant}, d.1 ≤ D)
    (hh_le : ∀ d : {d // d ∈ relevant}, hAt d ≤ n)
    (hlarge : ∀ d : {d // d ∈ relevant},
      4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D ≤ hAt d)
    (haccessible : ∀ {B : Finset ℤ}, B ⊆ A →
      A.card ≤ B.card + deletionCap → 0 ∈ B →
      ∀ d : {d // d ∈ relevant},
        ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
          ∃ W : HDimension.HApproximation B (hAt d) e scaleNum scaleDen,
            (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
              (scaleNum * hAt d) ^ e)
    (hcap : deletionCap ≤ x) :
    AccessibleSpanIndexBound A relevant
      (Stability.centeredMinimalIdentificationFamily hproper) deletionCap
      (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) := by
  classical
  let K := 4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D
  have bound {B : Finset ℤ} (hBA : B ⊆ A)
      (hloss : A.card ≤ B.card + deletionCap) (hzero : 0 ∈ B)
      (d : {d // d ∈ relevant}) :
      (Stability.generatedSubgroup
            (Stability.centeredMinimalIdentificationFamily hproper d.1) B).relIndex
          (Stability.generatedSubgroup
            (Stability.centeredMinimalIdentificationFamily hproper d.1) A) ≠ 0 ∧
        (Stability.generatedSubgroup
            (Stability.centeredMinimalIdentificationFamily hproper d.1) B).relIndex
          (Stability.generatedSubgroup
            (Stability.centeredMinimalIdentificationFamily hproper d.1) A) ≤ K := by
    obtain ⟨e, he, heD, W, hnumeric⟩ :=
      haccessible hBA hloss hzero d
    have hlossx : A.card ≤ B.card + x :=
      hloss.trans (Nat.add_le_add_left hcap B.card)
    have hresult :=
      HApproximation.centeredMinimalIdentification_relIndex_general_ne_zero_and_le
        hstable hBA hlossx (hambient d) W d.property hproper he
        (hrank_le d) heD (hh_le d) hA hnumeric (hlarge d)
    simpa only [K] using hresult
  refine ⟨?_, ?_⟩
  · intro B hBA hloss hzero d
    exact (bound hBA hloss hzero d).1
  · intro B hBA hloss hzero d
    simpa only [K] using (bound hBA hloss hzero d).2

/-- Centered-coordinate form of CFP Lemma 2.32.  The same approximation
family now produces a core whose subgroup span is robust for a map sending
the distinguished source origin to the lattice origin. -/
theorem span_pruning_lemma232_of_centeredHApproximations
    {A : Finset ℤ} {x D n scaleNum scaleDen robustBudget : ℕ}
    (hzero : 0 ∈ A)
    (hstable : Stability.WeaklyStableMinimalFor A x D n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper A relevant)
    (hAt : {d // d ∈ relevant} → ℕ)
    (hambient : ∀ d : {d // d ∈ relevant},
      HDimension.HApproximation A (hAt d) d.1 scaleNum scaleDen)
    (hrank_le : ∀ d : {d // d ∈ relevant}, d.1 ≤ D)
    (hh_le : ∀ d : {d // d ∈ relevant}, hAt d ≤ n)
    (hlarge : ∀ d : {d // d ∈ relevant},
      4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D ≤ hAt d)
    (haccessible : ∀ {B : Finset ℤ}, B ⊆ A →
      A.card ≤ B.card +
        robustBudget *
          (D * Nat.log 2
            (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) + 1) →
      0 ∈ B → ∀ d : {d // d ∈ relevant},
        ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
          ∃ W : HDimension.HApproximation B (hAt d) e scaleNum scaleDen,
            (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
              (scaleNum * hAt d) ^ e)
    (hcap : robustBudget *
      (D * Nat.log 2
        (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D) + 1) ≤ x) :
    ∃ B : Finset ℤ, B ⊆ A ∧ 0 ∈ B ∧
      A.card ≤ B.card +
        robustBudget *
          (D * Nat.log 2
            (4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D)) ∧
      Stability.SpanRobust 0 B robustBudget relevant
        (Stability.centeredMinimalIdentificationFamily hproper) := by
  let K := 4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D
  have hrelcard : relevant.card ≤ D :=
    relevant_card_le_rankBound hproper.positive hrank_le
  have hheight : relevant.card * Nat.log 2 K ≤ D * Nat.log 2 K :=
    Nat.mul_le_mul_right _ hrelcard
  have haccessible' : ∀ {B : Finset ℤ}, B ⊆ A →
      A.card ≤ B.card +
        robustBudget * (relevant.card * Nat.log 2 K + 1) →
      0 ∈ B → ∀ d : {d // d ∈ relevant},
        ∃ e : ℕ, 0 < e ∧ e ≤ D ∧
          ∃ W : HDimension.HApproximation B (hAt d) e scaleNum scaleDen,
            (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
              (scaleNum * hAt d) ^ e := by
    intro B hBA hcard hzeroB d
    apply haccessible hBA ?_ hzeroB d
    have hcapMono : robustBudget *
        (relevant.card * Nat.log 2 K + 1) ≤
          robustBudget * (D * Nat.log 2 K + 1) := by gcongr
    exact hcard.trans (Nat.add_le_add_left hcapMono B.card)
  have hindex : AccessibleSpanIndexBound A relevant
      (Stability.centeredMinimalIdentificationFamily hproper)
      (robustBudget * (relevant.card * Nat.log 2 K + 1)) K := by
    apply accessibleSpanIndexBound_of_centeredHApproximations
      hstable hA hproper hAt hambient hrank_le hh_le hlarge haccessible'
    have hcapMono : robustBudget *
        (relevant.card * Nat.log 2 K + 1) ≤
          robustBudget * (D * Nat.log 2 K + 1) := by gcongr
    exact hcapMono.trans (by simpa only [K] using hcap)
  obtain ⟨B, hBA, hzeroB, hcard, hrobust⟩ :=
    span_pruning_of_accessibleIndexBound hzero hindex
  refine ⟨B, hBA, hzeroB, ?_, hrobust⟩
  exact hcard.trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left robustBudget hheight) _)

/-- Centered-coordinate form of CFP Lemma 2.38.  It preserves the public
HApproximation boundary while returning the `StronglyStableFor` data needed
by random partition and generator completion with a coordinate map whose
value at zero is definitionally zero. -/
theorem preprocessing_lemma238_centered {A : Finset ℤ}
    {stableBudget maxRank n C0 scaleNum scaleDen : ℕ}
    (hzero : 0 ∈ A) (hC0 : 0 < C0)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (happrox : ∀ {W : Finset ℤ}, W ⊆ A → 0 ∈ W →
      Stability.WeaklyStableMinimalFor W (2 * stableBudget) maxRank n →
      ∃ (relevant : Finset ℕ)
        (hproper : Stability.RelevantBoxesProper W relevant)
        (hAt : {d // d ∈ relevant} → ℕ),
        (∀ d : {d // d ∈ relevant},
          Nonempty
            (HDimension.HApproximation W (hAt d) d.1 scaleNum scaleDen)) ∧
        (∀ d : {d // d ∈ relevant}, d.1 ≤ maxRank) ∧
        (∀ d : {d // d ∈ relevant}, hAt d ≤ n) ∧
        (∀ d : {d // d ∈ relevant},
          4 * (6 * scaleDen) ^ maxRank * (4 * scaleDen) ^ maxRank ≤ hAt d) ∧
        (∀ {B : Finset ℤ}, B ⊆ W →
          W.card ≤ B.card +
            (stableBudget / C0) *
              (maxRank * Nat.log 2
                (4 * (6 * scaleDen) ^ maxRank *
                  (4 * scaleDen) ^ maxRank) + 1) →
          0 ∈ B → ∀ d : {d // d ∈ relevant},
            ∃ e : ℕ, 0 < e ∧ e ≤ maxRank ∧
              ∃ V : HDimension.HApproximation B (hAt d) e
                  scaleNum scaleDen,
                (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
                  (scaleNum * hAt d) ^ e) ∧
        (stableBudget / C0) *
          (maxRank * Nat.log 2
            (4 * (6 * scaleDen) ^ maxRank *
              (4 * scaleDen) ^ maxRank)) ≤ stableBudget) :
    ∃ W B : Finset ℤ, ∃ relevant : Finset ℕ,
      ∃ hproper : Stability.RelevantBoxesProper W relevant,
        B ⊆ W ∧ W ⊆ A ∧ 0 ∈ B ∧
        A.card ≤ B.card +
          (2 * stableBudget) * boxPotential A maxRank + stableBudget ∧
        Stability.StronglyStableFor B (Stability.minimalBoxFamily W)
          stableBudget maxRank (n ^ 2) relevant
          (Stability.centeredMinimalIdentificationFamily hproper) C0 := by
  classical
  obtain ⟨W, hWA, hzeroW, hweakW, hlossW⟩ :=
    exists_weaklyStable_core hzero
  obtain ⟨relevant, hproper, hAt, hambient, hrank_le, hh_le,
      hlarge, haccessible, hspanLoss⟩ := happrox hWA hzeroW hweakW
  let hambient' : ∀ d : {d // d ∈ relevant},
      HDimension.HApproximation W (hAt d) d.1 scaleNum scaleDen :=
    fun d ↦ Classical.choice (hambient d)
  let K := 4 * (6 * scaleDen) ^ maxRank * (4 * scaleDen) ^ maxRank
  let height := maxRank * Nat.log 2 K
  let robustBudget := stableBudget / C0
  have hrobust_le : robustBudget ≤ stableBudget := by
    exact Nat.div_le_self _ _
  have hcap : robustBudget * (height + 1) ≤ 2 * stableBudget := by
    have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa only [robustBudget, height, K] using hspanLoss
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have haccessible' : ∀ {B : Finset ℤ}, B ⊆ W →
      W.card ≤ B.card + robustBudget * (height + 1) → 0 ∈ B →
      ∀ d : {d // d ∈ relevant},
        ∃ e : ℕ, 0 < e ∧ e ≤ maxRank ∧
          ∃ V : HDimension.HApproximation B (hAt d) e scaleNum scaleDen,
            (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
              (scaleNum * hAt d) ^ e := by
    intro B hBW hcard hzeroB d
    apply haccessible hBW (B := B) ?_ hzeroB d
    simpa only [robustBudget, height, K] using hcard
  obtain ⟨B, hBW, hzeroB, hlossB, hspanB⟩ :=
    span_pruning_lemma232_of_centeredHApproximations
      hzeroW hweakW (fun z hz ↦ hA z (hWA hz)) hproper hAt
      hambient' hrank_le hh_le hlarge haccessible' hcap
  have hweakB : Stability.WeaklyStableFor B (Stability.minimalBoxFamily W)
      stableBudget maxRank (n ^ 2) := by
    apply Stability.WeaklyStableFor.delete hweakW hBW hzeroB hlossB
    have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa only [robustBudget, height, K] using hspanLoss
    exact (Nat.add_le_add_right hspanLoss' stableBudget).trans_eq (by omega)
  refine ⟨W, B, relevant, hproper, hBW, hWA, hzeroB, ?_,
    ⟨hweakB, hC0, ?_⟩⟩
  · have hspanLoss' : robustBudget * height ≤ stableBudget := by
      simpa only [robustBudget, height, K] using hspanLoss
    have hlossB' : W.card ≤ B.card + stableBudget :=
      hlossB.trans (Nat.add_le_add_left hspanLoss' B.card)
    omega
  · intro d hd B' hB'B hcard hzeroB'
    exact hspanB hd hB'B (by simpa only [robustBudget] using hcard) hzeroB'

end Preprocessing

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.Preprocessing.card_multifoldSumset_le_centeredMinimalIdentificationIteratedSumset
#print axioms
  Erdos186.CFP.Preprocessing.card_centeredMinimalIdentificationIteratedSumset_le_dilate_volume
#print axioms
  Erdos186.CFP.Preprocessing.HApproximation.centeredMinimalIdentification_relIndex_general_ne_zero_and_le
#print axioms
  Erdos186.CFP.Preprocessing.accessibleSpanIndexBound_of_centeredHApproximations
#print axioms
  Erdos186.CFP.Preprocessing.span_pruning_lemma232_of_centeredHApproximations
#print axioms
  Erdos186.CFP.Preprocessing.preprocessing_lemma238_centered
