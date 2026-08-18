/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MahlerOuterContainer
import ErdosProblems.Erdos186.CFP.BiluFreiman
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Bilu Section 9 container integration

The output of Proposition 7.5 is used in Lemma 4.5 to cover a large subset
`K₀`.  Section 9.1 repairs this partial cover by choosing a maximal family
of disjoint translates of `K₀`.  The centers are few, and adjoining one box
coordinate for every center converts the partial geometric container into a
container of the whole set.

This file isolates that finite combinatorial step and the terminal transport
of the Section 3 Mahler box.  In particular, the covering result below is
constructive finite induction; it does not assume a maximal-family lemma.
-/

namespace Erdos186.CFP.Bilu.Section9ContainerIntegration

open scoped Pointwise BigOperators

section Covering

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The translate `a + S`, written as an image so its cardinality simp lemma
does not depend on the pointwise-finset API. -/
def translate (a : G) (S : Finset G) : Finset G :=
  S.image fun s ↦ a + s

@[simp]
theorem mem_translate {a x : G} {S : Finset G} :
    x ∈ translate a S ↔ ∃ s ∈ S, a + s = x := by
  constructor
  · rintro hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact Finset.mem_image.mpr ⟨s, hs, rfl⟩

@[simp]
theorem card_translate (a : G) (S : Finset G) :
    (translate a S).card = S.card := by
  exact Finset.card_image_of_injective S (add_right_injective a)

/-- A finite family of centers whose `S`-translates are pairwise disjoint. -/
def IsTranslatePacking (S centers : Finset G) : Prop :=
  ∀ a ∈ centers, ∀ b ∈ centers, a ≠ b →
    Disjoint (translate a S) (translate b S)

/-- The finite certificate produced by the maximal-disjoint-translates
argument in Bilu Section 9.1. -/
structure CoveringCertificate (K S : Finset G) where
  centers : Finset G
  centers_subset : centers ⊆ K
  packing : IsTranslatePacking S centers
  cover : K ⊆ centers + (S - S)

/-- Intersecting two translates puts the difference of their centers in
`S-S`; equivalently, the first center belongs to the second center plus
`S-S`. -/
theorem mem_add_sub_of_not_disjoint_translate {a b : G} {S : Finset G}
    (h : ¬ Disjoint (translate a S) (translate b S)) :
    a ∈ ({b} : Finset G) + (S - S) := by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨x, hxa, hxb⟩ := h
  obtain ⟨s, hs, has⟩ := mem_translate.mp hxa
  obtain ⟨t, ht, hbt⟩ := mem_translate.mp hxb
  rw [Finset.mem_add]
  refine ⟨b, Finset.mem_singleton_self b, t - s, ?_, ?_⟩
  · exact Finset.mem_sub.mpr ⟨t, ht, s, hs, rfl⟩
  · rw [← has] at hbt
    calc
      b + (t - s) = (b + t) - s := by abel
      _ = (a + s) - s := congrArg (fun z ↦ z - s) hbt
      _ = a := by abel

/-- Ruzsa's greedy covering lemma in the exact Section 9.1 form.  The
chosen centers lie in `K`, their `S`-translates are disjoint, and every
element of `K` is a center plus an element of `S-S`. -/
theorem exists_coveringCertificate (K S : Finset G) (hS : S.Nonempty) :
    Nonempty (CoveringCertificate K S) := by
  induction K using Finset.induction_on with
  | empty =>
      refine ⟨⟨∅, Finset.Subset.rfl, ?_, ?_⟩⟩
      · intro a ha
        simp at ha
      · simp
  | @insert a K ha ih =>
      obtain ⟨C⟩ := ih
      by_cases hdisj : ∀ b ∈ C.centers,
          Disjoint (translate a S) (translate b S)
      · refine ⟨⟨insert a C.centers, ?_, ?_, ?_⟩⟩
        · exact Finset.insert_subset_insert a C.centers_subset
        · intro x hx y hy hxy
          rw [Finset.mem_insert] at hx hy
          rcases hx with rfl | hx
          · rcases hy with rfl | hy
            · exact (hxy rfl).elim
            · exact hdisj y hy
          · rcases hy with rfl | hy
            · exact (hdisj x hx).symm
            · exact C.packing x hx y hy hxy
        · intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · rw [Finset.mem_add]
            refine ⟨x, Finset.mem_insert_self x C.centers, 0, ?_, add_zero x⟩
            obtain ⟨s, hs⟩ := hS
            exact Finset.mem_sub.mpr ⟨s, hs, s, hs, sub_self s⟩
          · obtain ⟨c, hc, u, hu, hcu⟩ := Finset.mem_add.mp (C.cover hx)
            exact Finset.mem_add.mpr
              ⟨c, Finset.mem_insert_of_mem hc, u, hu, hcu⟩
      · push Not at hdisj
        obtain ⟨b, hbC, hab⟩ := hdisj
        refine ⟨⟨C.centers, C.centers_subset.trans (Finset.subset_insert a K),
          C.packing, ?_⟩⟩
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · have haCover := mem_add_sub_of_not_disjoint_translate hab
          exact Finset.add_subset_add_right
            (Finset.singleton_subset_iff.mpr hbC) haCover
        · exact C.cover hx

namespace CoveringCertificate

variable {K S : Finset G} (C : CoveringCertificate K S)

/-- Pairwise disjoint translates make addition injective on the product of
the chosen centers with `S`. -/
theorem injOn_add_product :
    Set.InjOn (fun p : G × G ↦ p.1 + p.2)
      (C.centers ×ˢ S : Set (G × G)) := by
  rintro ⟨a, s⟩ has ⟨b, t⟩ hbt hab
  simp only [Set.mem_prod] at has hbt
  by_cases heq : a = b
  · subst b
    have hst : s = t := add_left_cancel hab
    subst t
    rfl
  · have hdisj := C.packing a has.1 b hbt.1 heq
    have hmemA : a + s ∈ translate a S :=
      mem_translate.mpr ⟨s, has.2, rfl⟩
    have hmemB : a + s ∈ translate b S :=
      mem_translate.mpr ⟨t, hbt.2, hab.symm⟩
    exact (Finset.disjoint_left.mp hdisj hmemA hmemB).elim

/-- Exact cardinality of the union of the packed translates. -/
theorem card_centers_add :
    (C.centers + S).card = C.centers.card * S.card := by
  exact Finset.card_add_iff.mpr C.injOn_add_product

/-- The disjoint translates all lie in `K+S`, giving the cardinal product
inequality used in equation (9.3). -/
theorem card_centers_mul_card_le :
    C.centers.card * S.card ≤ (K + S).card := by
  rw [← C.card_centers_add]
  exact Finset.card_le_card
    (Finset.add_subset_add C.centers_subset Finset.Subset.rfl)

/-- Source arithmetic for equation (9.3).  If `S=K₀` is a subset of `K`,
`|K|≤c|K₀|`, and `|K+K|≤σ|K|`, then the number of new box
directions is at most `σc`. -/
theorem centers_card_le_of_small_doubling
    (hS : S.Nonempty) (hSK : S ⊆ K) {sigma c : ℕ}
    (hlarge : K.card ≤ c * S.card)
    (hdouble : (K + K).card ≤ sigma * K.card) :
    C.centers.card ≤ sigma * c := by
  have hKS : K + S ⊆ K + K :=
    Finset.add_subset_add Finset.Subset.rfl hSK
  have hmul : C.centers.card * S.card ≤ (sigma * c) * S.card := by
    calc
      C.centers.card * S.card ≤ (K + S).card := C.card_centers_mul_card_le
      _ ≤ (K + K).card := Finset.card_le_card hKS
      _ ≤ sigma * K.card := hdouble
      _ ≤ sigma * (c * S.card) := Nat.mul_le_mul_left sigma hlarge
      _ = (sigma * c) * S.card := by simp [mul_assoc]
  exact Nat.le_of_mul_le_mul_right hmul (Finset.card_pos.mpr hS)

end CoveringCertificate

/-- Complete combinatorial output of Bilu Section 9.1, including the
equation-(9.3) bound on the number of newly adjoined box directions. -/
theorem exists_coveringCertificate_with_card_bound
    (K S : Finset G) (hS : S.Nonempty) (hSK : S ⊆ K)
    (sigma c : ℕ) (hlarge : K.card ≤ c * S.card)
    (hdouble : (K + K).card ≤ sigma * K.card) :
    ∃ C : CoveringCertificate K S, C.centers.card ≤ sigma * c := by
  obtain ⟨C⟩ := exists_coveringCertificate K S hS
  exact ⟨C, C.centers_card_le_of_small_doubling hS hSK hlarge hdouble⟩

end Covering

/-! ## Transporting the Section 3 outer progression -/

open Module
open Mahler MahlerBox MahlerOuterContainer MinkowskiSecond
open CFP.BiluFreiman

section GAPTransport

/-- Map every displayed point of a GAP through an additive homomorphism.
Widths and their order are unchanged. -/
def mapGAP {source target rank : ℕ}
    (f : LatticePoint source →+ LatticePoint target)
    (P : GAP source rank) : GAP target rank where
  offset := f P.offset
  steps := fun i ↦ f (P.steps i)
  widths := P.widths
  width_pos := P.width_pos

@[simp]
theorem mapGAP_widths {source target rank : ℕ}
    (f : LatticePoint source →+ LatticePoint target)
    (P : GAP source rank) :
    (mapGAP f P).widths = P.widths := rfl

@[simp]
theorem mapGAP_volume {source target rank : ℕ}
    (f : LatticePoint source →+ LatticePoint target)
    (P : GAP source rank) :
    (mapGAP f P).volume = P.volume := rfl

/-- Mapping commutes with the displayed coordinate map. -/
theorem mapGAP_coordPoint {source target rank : ℕ}
    (f : LatticePoint source →+ LatticePoint target)
    (P : GAP source rank) (c : P.Coord) :
    (mapGAP f P).coordPoint c = f (P.coordPoint c) := by
  funext j
  change f P.offset j + ∑ i, (c i : ℤ) * f (P.steps i) j =
    f (fun q ↦ P.offset q + ∑ i, (c i : ℤ) * P.steps i q) j
  have hinput :
      (fun q ↦ P.offset q + ∑ i, (c i : ℤ) * P.steps i q) =
        P.offset + ∑ i, (c i : ℤ) • P.steps i := by
    funext q
    simp [Finset.sum_apply]
  rw [hinput, map_add, map_sum]
  apply congrArg₂ (fun x y : ℤ ↦ x + y) rfl
  rw [Finset.sum_apply]
  change (∑ i, (c i : ℤ) * f (P.steps i) j) =
    ∑ i, f ((c i : ℤ) • P.steps i) j
  apply Finset.sum_congr rfl
  intro i _hi
  exact congrFun (map_zsmul f (c i : ℤ) (P.steps i)) j |>.symm

/-- The carrier of a mapped GAP is the image of the source carrier. -/
theorem mapGAP_carrier {source target rank : ℕ}
    (f : LatticePoint source →+ LatticePoint target)
    (P : GAP source rank) :
    (mapGAP f P).carrier = P.carrier.image f := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := GAP.mem_carrier_iff.mp hx
    exact Finset.mem_image.mpr
      ⟨P.coordPoint c, P.coordPoint_mem_carrier c,
        (mapGAP_coordPoint f P c).symm⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, rfl⟩ := GAP.mem_carrier_iff.mp hy
    exact GAP.mem_carrier_iff.mpr ⟨c, mapGAP_coordPoint f P c⟩

/-- Mapping commutes with coefficient dilation. -/
theorem mapGAP_dilate {source target rank : ℕ}
    (f : LatticePoint source →+ LatticePoint target)
    (P : GAP source rank) (k : ℕ) :
    (mapGAP f P).dilate k = mapGAP f (P.dilate k) := by
  rw [GAP.mk.injEq]
  refine ⟨?_, rfl, rfl⟩
  funext j
  change (k : ℤ) * f P.offset j =
    f (fun q ↦ (k : ℤ) * P.offset q) j
  have hoff : (fun q ↦ (k : ℤ) * P.offset q) = (k : ℤ) • P.offset := by
    funext q
    rfl
  rw [hoff, map_zsmul]
  rfl

/-- Properness descends through a map which is injective on the relevant
source carrier. -/
theorem mapGAP_proper_of_injOn {source target rank : ℕ}
    (f : LatticePoint source →+ LatticePoint target)
    (P : GAP source rank) (hP : P.Proper)
    (hinj : Set.InjOn f P.carrier) :
    (mapGAP f P).Proper := by
  intro c e hce
  apply hP
  apply hinj (P.coordPoint_mem_carrier c) (P.coordPoint_mem_carrier e)
  calc
    f (P.coordPoint c) = (mapGAP f P).coordPoint c :=
      (mapGAP_coordPoint f P c).symm
    _ = (mapGAP f P).coordPoint e := hce
    _ = f (P.coordPoint e) := mapGAP_coordPoint f P e

/-- A homomorphism from the source lattice to ordinary integers, bundled
as a homomorphism to the one-dimensional lattice used by
`SortedFsContainer`. -/
def integerPointHom {n : ℕ}
    (phi : IntegralPoint n →+ ℤ) : LatticePoint n →+ LatticePoint 1 where
  toFun z := CFP.BiluFreiman.integerPoint (phi z)
  map_zero' := by
    funext i
    simp [CFP.BiluFreiman.integerPoint]
  map_add' x y := by
    funext i
    simp [CFP.BiluFreiman.integerPoint]

@[simp]
theorem integerPointHom_apply {n : ℕ}
    (phi : IntegralPoint n →+ ℤ) (z : IntegralPoint n) :
    integerPointHom phi z = CFP.BiluFreiman.integerPoint (phi z) := rfl

/-- The unconditional Section 3 data, together with its chosen integral
homomorphism to the original one-dimensional ambient group. -/
structure MappedOuterContainer {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (phi : IntegralPoint n →+ ℤ) where
  rank_pos : 0 < n
  basis : Basis (Fin n) ℤ (IntegralPoint n)
  isMahlerBasis : IsMahlerBasis p basis
  basis_det : |(integralBasisMatrix basis).det| = 1
  source_dilates_proper :
    ∀ k : ℕ, ((centeredBasisGAP basis (outerRadius p)).dilate k).Proper
  widths_sorted :
    ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) →
      (centeredBasisGAP basis (outerRadius p)).widths j ≤
        (centeredBasisGAP basis (outerRadius p)).widths i
  width_real_le :
    ∀ i : Fin n,
      ((centeredBasisGAP basis (outerRadius p)).widths i : ℝ) ≤
        5 * outerConstant n * (successiveMinimum p i)⁻¹
  unitBall_integral_subset :
    ∀ z : IntegralPoint n, p (integralEmbed z) ≤ 1 →
      z ∈ (centeredBasisGAP basis (outerRadius p)).carrier
  volume_mul_simplex_le :
    ((centeredBasisGAP basis (outerRadius p)).volume : ENNReal) *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      ENNReal.ofReal ((5 * outerConstant n) ^ n) *
        MeasureTheory.volume {y | p y ≤ 1}
  body_volume_le :
    MeasureTheory.volume.real {y | p y ≤ 1} ≤
      (8 : ℝ) ^ n * (n : ℝ) ^ n *
        (∏ i : Fin n, mahlerFactor i) *
          ((centeredBasisGAP basis (outerRadius p)).volume : ℝ)

namespace MappedOuterContainer

variable {n : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
    {phi : IntegralPoint n →+ ℤ}

/-- The source Mahler box selected by Section 3. -/
noncomputable def source (D : MappedOuterContainer p phi) : GAP n n :=
  centeredBasisGAP D.basis (outerRadius p)

/-- The same displayed box transported to the original integer group. -/
noncomputable def progression (D : MappedOuterContainer p phi) : GAP 1 n :=
  mapGAP (integerPointHom phi) D.source

@[simp]
theorem progression_widths (D : MappedOuterContainer p phi) :
    D.progression.widths = D.source.widths := rfl

@[simp]
theorem progression_volume (D : MappedOuterContainer p phi) :
    D.progression.volume = D.source.volume := rfl

/-- The exact admissibility condition on the enlarged body turns the
transported progression into an `F_s` progression. -/
theorem isFsProgression (D : MappedOuterContainer p phi) (s : ℕ)
    (hinj : Set.InjOn (integerPointHom phi) (D.source.dilate s).carrier) :
    IsFsProgression D.progression s := by
  rw [IsFsProgression]
  change (mapGAP (integerPointHom phi) D.source).dilate s |>.Proper
  rw [mapGAP_dilate]
  exact mapGAP_proper_of_injOn _ _ (D.source_dilates_proper s) hinj

/-- A lattice lift in the unit ball maps into the transported progression. -/
theorem mem_integerCarrier_of_unitBall (D : MappedOuterContainer p phi)
    {a : ℤ} {z : IntegralPoint n} (hz : p (integralEmbed z) ≤ 1)
    (hza : phi z = a) :
    a ∈ integerCarrier D.progression := by
  rw [mem_integerCarrier_iff, progression, mapGAP_carrier]
  exact Finset.mem_image.mpr
    ⟨z, D.unitBall_integral_subset z hz, by simp [hza]⟩

end MappedOuterContainer

/-- Direct consumption of the green Section 3 outer-container theorem. -/
theorem exists_mappedOuterContainer {n : ℕ} (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (hfull : AdmitsIndependent p n 1) (phi : IntegralPoint n →+ ℤ) :
    Nonempty (MappedOuterContainer p phi) := by
  obtain ⟨b, hb, hdet, _hproper, _hhomo, hdilates, hsorted, hwidth,
      hcontains, hupper, hlower⟩ :=
    exists_proper_outerGAP_containing_unitBall_with_two_sided_volume
      hn p hp hfull
  exact ⟨⟨hn, b, hb, hdet, hdilates, hsorted, hwidth, hcontains,
    hupper, hlower⟩⟩

/-- Final field-by-field integration into the source-facing sorted Bilu
container.  Its hypotheses are exactly the outputs supplied by the other
source sections: enlarged-body injectivity (Sections 4/9), lattice lifts of
`A`, the linear-volume and rank estimates (Section 4), and the bounded
successive-minimum tail (Section 5.5). -/
noncomputable def MappedOuterContainer.toSortedFsContainer
    {n s d volumeConstant tailBound rankBound : ℕ}
    {A : Finset ℤ} {p : Seminorm ℝ (Fin n → ℝ)}
    {phi : IntegralPoint n →+ ℤ}
    (D : MappedOuterContainer p phi)
    (hinj : Set.InjOn (integerPointHom phi)
      (D.source.dilate (2 * s)).carrier)
    (hlifts : ∀ a ∈ A, ∃ z : IntegralPoint n,
      p (integralEmbed z) ≤ 1 ∧ phi z = a)
    (hvolume : D.source.volume ≤ volumeConstant * A.card)
    (hrank : n ≤ rankBound)
    (htail : ∀ i : Fin n, d ≤ (i : ℕ) →
      D.source.widths i ≤ tailBound)
    (hvolumeConstant : 0 < volumeConstant) (htailBound : 0 < tailBound) :
    SortedFsContainer s d volumeConstant tailBound rankBound A where
  rank := n
  rank_pos := D.rank_pos
  progression := D.progression
  fsProgression := D.isFsProgression (2 * s) hinj
  A_subset := by
    intro a ha
    obtain ⟨z, hz, hza⟩ := hlifts a ha
    exact D.mem_integerCarrier_of_unitBall hz hza
  volume_le := by simpa only [MappedOuterContainer.progression_volume] using hvolume
  rank_le := hrank
  widths_sorted := by
    intro i j hij
    exact D.widths_sorted i j hij
  tail_width_le := htail
  volumeConstant_pos := hvolumeConstant
  tailBound_pos := htailBound

end GAPTransport

end Erdos186.CFP.Bilu.Section9ContainerIntegration

#print axioms Erdos186.CFP.Bilu.Section9ContainerIntegration.exists_coveringCertificate
#print axioms
  Erdos186.CFP.Bilu.Section9ContainerIntegration.exists_coveringCertificate_with_card_bound
#print axioms Erdos186.CFP.Bilu.Section9ContainerIntegration.exists_mappedOuterContainer
#print axioms
  Erdos186.CFP.Bilu.Section9ContainerIntegration.MappedOuterContainer.toSortedFsContainer
