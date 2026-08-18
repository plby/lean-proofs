/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Construction
import ErdosProblems.Erdos186.CFP.Bilu.Section9ContainerIntegration

/-!
# The Proposition 7.5 to Lemma 4.5 replacement seed

Bilu does not use the section-volume inequality in isolation.  He translates
the large affine slice into `C₀`, retaining a finite subset of
`B₀ ∩ Γ₀`; projection to the first coordinates is injective on that subset.
This file packages precisely that finite replacement data.
-/

namespace Erdos186.CFP.Bilu.Section9Replacement

open Set Module Submodule
open scoped Pointwise RealInnerProductSpace
open Proposition75Data Proposition75Construction Proposition74Construction
open Section7AffineSlice Section7FreimanMap Section7PlaneSeed
open SubspaceLattice
open DistortingMeasure BadlyApproximable PolarSeparation Section8Synthesis

noncomputable section

/-- The source-faithful finite certificate passed from Sections 7--8 to
Lemma 4.5.  `embed` is the translated Freiman map
`x ↦ Φ(x)-Φ(x₀)` bundled into `C₀`. -/
structure Lemma45SectionSeed {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) (K : Finset (Mahler.IntegralPoint m))
    (coverConstant : ℕ) where
  sourceSlice : Finset (Mahler.IntegralPoint m)
  sourceSlice_nonempty : sourceSlice.Nonempty
  sourceSlice_subset : sourceSlice ⊆ K
  base : Mahler.IntegralPoint m
  base_mem : base ∈ sourceSlice
  offset : Fin r → ℝ
  embed : {x // x ∈ sourceSlice} ↪ D.C0
  embed_apply : ∀ x,
    (embed x : Ambient m r) = freimanDifference a offset x base
  embed_body : ∀ x, (embed x : D.C0) ∈ D.B0
  embed_lattice : ∀ x, (embed x : D.C0) ∈ D.latticePoints
  head_injective : Function.Injective
    (fun x ↦ head ((embed x : D.C0) : Ambient m r))
  large : K.card ≤ coverConstant * sourceSlice.card

namespace Lemma45SectionSeed

variable {m r : ℕ} {B : Set (EuclideanSpace ℝ (Fin m))}
  {a : Fin r → EuclideanSpace ℝ (Fin m)}
  {D : GeometricData B a} {K : Finset (Mahler.IntegralPoint m)}
  {coverConstant : ℕ}

/-- The literal translated set `K₀' ⊆ C₀` from Bilu Lemma 4.5. -/
def sectionSlice (S : Lemma45SectionSeed D K coverConstant) : Finset D.C0 :=
  S.sourceSlice.attach.map S.embed

@[simp] theorem card_sectionSlice
    (S : Lemma45SectionSeed D K coverConstant) :
    S.sectionSlice.card = S.sourceSlice.card := by
  rw [sectionSlice, Finset.card_map, Finset.card_attach]

theorem sectionSlice_nonempty
    (S : Lemma45SectionSeed D K coverConstant) :
    S.sectionSlice.Nonempty := by
  rw [← Finset.card_pos, S.card_sectionSlice]
  exact S.sourceSlice_nonempty.card_pos

/-- `K₀'` lies in the literal section body `B₀`. -/
theorem sectionSlice_subset_B0
    (S : Lemma45SectionSeed D K coverConstant) :
    (S.sectionSlice : Set D.C0) ⊆ D.B0 := by
  intro z hz
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_map.mp hz
  exact S.embed_body x

/-- `K₀'` consists of points of the literal section lattice `Γ₀`. -/
theorem sectionSlice_subset_lattice
    (S : Lemma45SectionSeed D K coverConstant) :
    (S.sectionSlice : Set D.C0) ⊆ D.latticePoints := by
  intro z hz
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_map.mp hz
  exact S.embed_lattice x

/-- Projection `π : C₀ → E_m` is injective on `K₀'`, exactly because the
Freiman map retains its first coordinate. -/
theorem head_injOn_sectionSlice
    (S : Lemma45SectionSeed D K coverConstant) :
    Set.InjOn (fun z : D.C0 ↦ head (z : Ambient m r)) S.sectionSlice := by
  rintro z hz w hw hhead
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_map.mp hz
  obtain ⟨y, _hy, rfl⟩ := Finset.mem_map.mp hw
  exact congrArg S.embed (S.head_injective hhead)

theorem large_sectionSlice
    (S : Lemma45SectionSeed D K coverConstant) :
    K.card ≤ coverConstant * S.sectionSlice.card := by
  calc
    K.card ≤ coverConstant * S.sourceSlice.card := S.large
    _ = coverConstant * S.sectionSlice.card := by rw [S.card_sectionSlice]

end Lemma45SectionSeed

/-- Construct the Lemma 4.5 finite replacement seed from the translated
affine slice retained by `Proposition75Construction`. -/
def lemma45SectionSeedOfAffineSlice {m r proportionConstant : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {K : Finset (Mahler.IntegralPoint m)}
    {alpha : Fin r → Fin 2}
    (W : SourceAffineSlice a 0 proportionConstant
      (residueCell a 0 alpha K))
    (hcell : (residueCell a 0 alpha K).Nonempty)
    (D : GeometricData B a)
    (hKB : ∀ x ∈ K, integralReal x ∈ B)
    (hlarge : K.card ≤
      (2 ^ r * proportionConstant) * W.sourceSlice.card)
    (x0 : Mahler.IntegralPoint m) (hx0 : x0 ∈ W.sourceSlice)
    (hdiff : ∀ x ∈ W.sourceSlice, freimanDifference a 0 x x0 ∈ D.C0) :
    Lemma45SectionSeed D K (2 ^ r * proportionConstant) where
  sourceSlice := W.sourceSlice
  sourceSlice_nonempty := W.sourceSlice_nonempty hcell
  sourceSlice_subset := fun x hx ↦
    ((mem_residueCell a 0 alpha K x).mp (W.sourceSlice_subset hx)).1
  base := x0
  base_mem := hx0
  offset := 0
  embed :=
    { toFun := fun x ↦ ⟨freimanDifference a 0 x x0, hdiff x x.property⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        have hxy' := congrArg (fun z : D.C0 ↦ (z : Ambient m r)) hxy
        change freimanRealMap a 0 x - freimanRealMap a 0 x0 =
          freimanRealMap a 0 y - freimanRealMap a 0 x0 at hxy'
        exact freimanRealMap_injective a 0 (sub_left_inj.mp hxy') }
  embed_apply := fun _ ↦ rfl
  embed_body := by
    intro x
    exact freimanDifference_mem_distortionBody_of_mem hbalanced hconvex
      a 0 x x0
      (hKB x (((mem_residueCell a 0 alpha K x).mp
        (W.sourceSlice_subset x.property)).1))
      (hKB x0 (((mem_residueCell a 0 alpha K x0).mp
        (W.sourceSlice_subset hx0)).1))
  embed_lattice := by
    intro x
    exact freimanDifference_mem_ambientProductIntegralPoints a 0 x x0
  head_injective := by
    intro x y hxy
    apply Subtype.ext
    change integralReal (x : Mahler.IntegralPoint m) - integralReal x0 =
      integralReal (y : Mahler.IntegralPoint m) - integralReal x0 at hxy
    have hreal : integralReal (x : Mahler.IntegralPoint m) =
        integralReal (y : Mahler.IntegralPoint m) := sub_left_inj.mp hxy
    ext i
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin m) ↦ z i) hreal
    change (((x : Mahler.IntegralPoint m) i : ℤ) : ℝ) =
      (((y : Mahler.IntegralPoint m) i : ℤ) : ℝ) at hi
    exact_mod_cast hi
  large := hlarge

/-- Source-correct Sections 5--8 synthesis directly into the finite
Lemma 4.5 replacement certificate.  This theorem is the terminal handoff:
it uses the genuine `2^(r-delta)` affine-slice theorem and retains both
the Proposition 8.3 system and the translated set `K₀'`. -/
theorem exists_lemma45SectionSeed_of_proposition83_rpow {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r) {delta : ℝ} (hdelta : 0 < delta)
    (K : Finset (Mahler.IntegralPoint m)) (hK : K.Nonempty)
    (sigma epsilon : ℝ) (hsigma : 1 ≤ sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hrank : sigma * (2 : ℝ) ^ r ≤
      Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - delta))
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (hKB : ∀ x ∈ K, integralReal x ∈ B)
    (p : Seminorm ℝ (Fin m → ℝ))
    (hindependent : Mahler.AdmitsIndependent p m 1)
    (hunit : ∀ x : Mahler.IntegralPoint m,
      p (Mahler.integralEmbed x) ≤ 1 → integralReal x ∈ (2 : ℝ) • B)
    (hpolarMeasurable :
      MeasurableSet (euclideanPolar (WithLp.ofLp '' B)))
    (hpolarVolume :
      MeasureTheory.volume (euclideanPolar (WithLp.ofLp '' B)) ≤
        ENNReal.ofReal ((4 : ℝ) ^ m / (epsilon * K.card)))
    (hepsilon : proposition83Threshold m r sigma < epsilon) :
    ∃ proportionConstant : ℕ,
      ∃ a : Fin r → EuclideanSpace ℝ (Fin m),
        ∃ D : GeometricData B a,
          (∀ i, WithLp.ofLp (a i) ∈
            cubeDistortingSet (1 / (2 * Real.sqrt sigma)) K) ∧
          IsBadlyApproximable
            (euclideanPolar (WithLp.ofLp '' B))
            (epsilon ^ proposition83Exponent m r)
            (epsilon ^ proposition83Exponent m r)
            (fun i ↦ WithLp.ofLp (a i)) ∧
          Nonempty (Lemma45SectionSeed D K
            (2 ^ r * proportionConstant)) := by
  obtain ⟨proportionConstant, a, D, alpha, W, haCube, haBad,
      hlarge, x0, hx0, hdiff⟩ :=
    exists_geometricData_of_proposition83_rpow hm hr hdelta K hK
      sigma epsilon hsigma hsum hrank B hbalanced hconvex hKB p
      hindependent hunit hpolarMeasurable hpolarVolume hepsilon
  have hW : W.sourceSlice.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hzero
    have hzero' : W.sourceSlice.card = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hzero', mul_zero] at hlarge
    exact (not_le_of_gt hK.card_pos) hlarge
  have hcell : (residueCell a 0 alpha K).Nonempty :=
    hW.mono W.sourceSlice_subset
  let S : Lemma45SectionSeed D K (2 ^ r * proportionConstant) :=
    lemma45SectionSeedOfAffineSlice hbalanced hconvex W hcell D hKB
      hlarge x0 hx0 hdiff
  exact ⟨proportionConstant, a, D, haCube, haBad, ⟨S⟩⟩

end

end Erdos186.CFP.Bilu.Section9Replacement

#print axioms Erdos186.CFP.Bilu.Section9Replacement.lemma45SectionSeedOfAffineSlice
#print axioms Erdos186.CFP.Bilu.Section9Replacement.exists_lemma45SectionSeed_of_proposition83_rpow
#print axioms Erdos186.CFP.Bilu.Section9Replacement.Lemma45SectionSeed.head_injOn_sectionSlice
