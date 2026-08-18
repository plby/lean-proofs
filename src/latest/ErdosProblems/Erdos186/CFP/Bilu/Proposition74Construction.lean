/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Data
import ErdosProblems.Erdos186.CFP.Bilu.MahlerTheorem

/-!
# Constructing Bilu's Proposition 7.4 subspace

This file supplies the first construction upstream of the geometric estimate in
`Proposition75Case2`.  Bilu constructs `C₀` as the span of two finite families
of integral points of the distortion body: the difference set in the selected
affine plane and an auxiliary full-rank family whose first coordinates span
`E_m`.  The proof of Proposition 7.4 uses only the three properties recorded
below: the points lie in the body and ambient lattice, there are too few of
them to span `E_m ⊕ E_r`, and their first coordinates span `E_m`.

The resulting `GeometricData` is therefore not assumed.  Its subspace is the
literal real span of the supplied source points, and all three fields are
proved from those finite hypotheses.
-/

namespace Erdos186.CFP.Bilu.Proposition74Construction

open MeasureTheory Set Module Submodule
open scoped Pointwise RealInnerProductSpace
open Proposition75Data
open SubspaceLattice

noncomputable section

/-- The literal subspace used in Proposition 7.4: the real span of the
integral source points selected in Section 7. -/
def seedSubspace {m r : ℕ} (seed : Finset (Ambient m r)) :
    Submodule ℝ (Ambient m r) :=
  Submodule.span ℝ (seed : Set (Ambient m r))

/-- The distortion ambient really has the source dimension `m + r`. -/
theorem finrank_ambient (m r : ℕ) :
    Module.finrank ℝ (Ambient m r) = m + r := by
  rw [(WithLp.linearEquiv 2 ℝ
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin r))).finrank_eq]
  simp [Module.finrank_prod]

/-- The integral tail obtained by rounding the distortion coordinates
downwards.  Bilu only needs the rounding error to be at most one. -/
def distortionTailIntegral {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (x : Mahler.IntegralPoint m) : Fin r → ℤ :=
  fun i ↦ ⌊⟪integralReal x, a i⟫⌋

/-- Lift an integral point of `E_m` to the distortion lattice by adjoining
the rounded inner products with the distortion vectors. -/
def distortionLift {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (x : Mahler.IntegralPoint m) : Ambient m r :=
  WithLp.toLp 2
    (integralReal x, integralReal (distortionTailIntegral a x))

@[simp]
theorem head_distortionLift {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (x : Mahler.IntegralPoint m) :
    head (distortionLift a x) = integralReal x := rfl

@[simp]
theorem tail_distortionLift {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (x : Mahler.IntegralPoint m) :
    tail (distortionLift a x) =
      integralReal (distortionTailIntegral a x) := rfl

/-- The rounded lift is an ambient integral point. -/
theorem distortionLift_mem_ambientProductIntegralPoints {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (x : Mahler.IntegralPoint m) :
    distortionLift a x ∈ ambientProductIntegralPoints m r := by
  apply Submodule.mem_map.mpr
  refine ⟨(integralReal x, integralReal (distortionTailIntegral a x)), ?_, rfl⟩
  constructor
  · exact ⟨x, rfl⟩
  · exact ⟨distortionTailIntegral a x, rfl⟩

/-- If the first coordinate belongs to `2B`, its rounded lift belongs to
the distortion body (7.7). -/
theorem distortionLift_mem_distortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (x : Mahler.IntegralPoint m)
    (hx : integralReal x ∈ (2 : ℝ) • B) :
    distortionLift a x ∈ distortionBody B a := by
  refine ⟨hx, ?_⟩
  intro i
  change |⟪integralReal x, a i⟫ -
    ((⌊⟪integralReal x, a i⟫⌋ : ℤ) : ℝ)| ≤ 1
  apply abs_le.mpr
  constructor
  · have hfloor := Int.floor_le ⟪integralReal x, a i⟫
    linarith
  · have hlt := (Int.lt_floor_add_one ⟪integralReal x, a i⟫).le
    linarith

/-- The lifted finite family attached to `m` independent integral points. -/
def fullRankLiftSeed {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (v : Fin m → Mahler.IntegralPoint m) : Finset (Ambient m r) :=
  Finset.univ.image fun i ↦ distortionLift a (v i)

/-- A finite source family whose first coordinates span `E_m` forces every
normal to its span with zero tail to vanish.  This is Bilu Proposition 7.4(3).
-/
theorem normal_tail_ne_zero_of_head_span {m r : ℕ}
    (seed : Finset (Ambient m r))
    (hhead : Submodule.span ℝ (head '' (seed : Set (Ambient m r))) = ⊤) :
    ∀ z : Ambient m r,
      z ∈ Submodule.orthogonal (seedSubspace seed) →
        z ≠ 0 → tail z ≠ 0 := by
  intro z hz hz0 htail
  have hseed : ∀ w ∈ seed, ⟪z, w⟫ = 0 := by
    intro w hw
    exact (seedSubspace seed).inner_left_of_mem_orthogonal
      (Submodule.subset_span hw) hz
  have hheadSelf : ⟪head z, head z⟫ = 0 := by
    have hzmem : head z ∈
        Submodule.span ℝ (head '' (seed : Set (Ambient m r))) := by
      rw [hhead]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun x _ ↦ ⟪head z, x⟫ = 0)
      ?_ (by simp) (fun x y _ _ hx hy ↦ by
        rw [inner_add_right, hx, hy, add_zero])
      (fun c x _ hx ↦ by rw [inner_smul_right, hx, mul_zero]) hzmem
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hx
    have hw0 := hseed w hw
    change ⟪head z, head w⟫ + ⟪tail z, tail w⟫ = 0 at hw0
    have htailInner : ⟪tail z, tail w⟫ = 0 := by
      rw [htail, inner_zero_left]
    linarith
  have hhead0 : head z = 0 := inner_self_eq_zero.mp hheadSelf
  apply hz0
  apply WithLp.ofLp_injective
  apply Prod.ext
  · exact hhead0
  · exact htail

/-- The source points span the constructed section intrinsically.  If all of
them lie in the distortion body and in the ambient integral lattice, the
lattice points of the section inside the body span the whole section.  This
is Proposition 7.4(2), including the precise subtype formulation consumed by
`GeometricData`.
-/
theorem span_section_lattice_eq_top {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (seed : Finset (Ambient m r))
    (hbody : ∀ z ∈ seed, z ∈ distortionBody B a)
    (hlattice : ∀ z ∈ seed, z ∈ ambientProductIntegralPoints m r) :
    Submodule.span ℝ
      ({z : seedSubspace seed |
          (z : Ambient m r) ∈ distortionBody B a} ∩
        ((ambientProductIntegralPoints m r).comap
          ((seedSubspace seed).subtype.restrictScalars ℤ) :
            Set (seedSubspace seed))) = ⊤ := by
  apply top_unique
  rintro ⟨x, hx⟩ -
  refine Submodule.span_induction
    (p := fun x hx ↦
      (⟨x, hx⟩ : seedSubspace seed) ∈
        Submodule.span ℝ
          ({z : seedSubspace seed |
              (z : Ambient m r) ∈ distortionBody B a} ∩
            ((ambientProductIntegralPoints m r).comap
              ((seedSubspace seed).subtype.restrictScalars ℤ) :
                Set (seedSubspace seed))))
    ?_ ?_ ?_ ?_ hx
  · intro z hz
    apply Submodule.subset_span
    constructor
    · exact hbody z hz
    · exact hlattice z hz
  · convert Submodule.zero_mem
      (Submodule.span ℝ
        ({z : seedSubspace seed |
            (z : Ambient m r) ∈ distortionBody B a} ∩
          ((ambientProductIntegralPoints m r).comap
            ((seedSubspace seed).subtype.restrictScalars ℤ) :
              Set (seedSubspace seed))))
    apply Subtype.ext
    rfl
  · intro x y hxspan hyspan ihx ihy
    convert Submodule.add_mem _ ihx ihy
    apply Subtype.ext
    rfl
  · intro c x hxspan ihx
    convert Submodule.smul_mem _ c ihx
    apply Subtype.ext
    rfl

/-- Finite construction of all `GeometricData` required downstream by
Proposition 7.5.  The cardinality inequality is the source dimension count
`dim C₁ + m < m + r`; the other hypotheses are the literal conclusions of
the two finite selections in Proposition 7.4.
-/
def geometricDataOfSeed {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (seed : Finset (Ambient m r))
    (hbody : ∀ z ∈ seed, z ∈ distortionBody B a)
    (hlattice : ∀ z ∈ seed, z ∈ ambientProductIntegralPoints m r)
    (hcard : seed.card < Module.finrank ℝ (Ambient m r))
    (hhead : Submodule.span ℝ
      (head '' (seed : Set (Ambient m r))) = ⊤) :
    GeometricData B a where
  C0 := seedSubspace seed
  proper := by
    exact (span_lt_top_of_card_lt_finrank
      (R := ℝ) (M := Ambient m r) (s := (seed : Set (Ambient m r)))
      (by simpa using hcard)).ne
  spans := span_section_lattice_eq_top seed hbody hlattice
  normal_tail_ne_zero := normal_tail_ne_zero_of_head_span seed hhead

/-- Source-facing form of the construction.  `planeSeed` consists of a
basis extracted from the differences in the selected affine plane, while
`fullRankSeed` is the lifted full-rank family obtained from lattice points of
`B`.  Their union is exactly the family spanning Bilu's
`C₀ = C₁ + C(M')`.

The numerical hypothesis is stated as in the paper, against `m + r`, rather
than against an abstract `finrank`.
-/
def geometricDataOfPlaneAndFullRankSeed {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (planeSeed fullRankSeed : Finset (Ambient m r))
    (hplane_body : ∀ z ∈ planeSeed, z ∈ distortionBody B a)
    (hfull_body : ∀ z ∈ fullRankSeed, z ∈ distortionBody B a)
    (hplane_lattice : ∀ z ∈ planeSeed,
      z ∈ ambientProductIntegralPoints m r)
    (hfull_lattice : ∀ z ∈ fullRankSeed,
      z ∈ ambientProductIntegralPoints m r)
    (hcard : planeSeed.card + fullRankSeed.card < m + r)
    (hhead : Submodule.span ℝ
      (head '' (fullRankSeed : Set (Ambient m r))) = ⊤) :
    GeometricData B a := by
  let seed := planeSeed ∪ fullRankSeed
  apply geometricDataOfSeed B a seed
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hplane_body z hz
    · exact hfull_body z hz
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hplane_lattice z hz
    · exact hfull_lattice z hz
  · rw [finrank_ambient]
    exact (Finset.card_union_le planeSeed fullRankSeed).trans_lt hcard
  · apply top_unique
    rw [← hhead]
    apply Submodule.span_mono
    apply Set.image_mono
    intro z hz
    exact Finset.mem_union_right planeSeed hz

/-- Proposition 7.4 in the form closest to Bilu's proof.  Starting from a
small family spanning the selected plane direction and `m` independent
integral points of `2B`, this theorem performs the coordinate rounding,
constructs the auxiliary lattice family `M'`, and returns the exact
`GeometricData` used by Proposition 7.5.

The hypothesis `planeSeed.card + m < m + r` is the paper's dimension count.
No geometric-data field is assumed.
-/
def geometricDataOfPlaneAndIndependentIntegralFamily {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (planeSeed : Finset (Ambient m r))
    (v : Fin m → Mahler.IntegralPoint m)
    (hv_independent : LinearIndependent ℝ (fun i ↦ integralReal (v i)))
    (hv_body : ∀ i, integralReal (v i) ∈ (2 : ℝ) • B)
    (hplane_body : ∀ z ∈ planeSeed, z ∈ distortionBody B a)
    (hplane_lattice : ∀ z ∈ planeSeed,
      z ∈ ambientProductIntegralPoints m r)
    (hcard : planeSeed.card + m < m + r) :
    GeometricData B a := by
  let fullSeed := fullRankLiftSeed a v
  apply geometricDataOfPlaneAndFullRankSeed B a planeSeed fullSeed
  · exact hplane_body
  · intro z hz
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hz
    exact distortionLift_mem_distortionBody a (v i) (hv_body i)
  · exact hplane_lattice
  · intro z hz
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hz
    exact distortionLift_mem_ambientProductIntegralPoints a (v i)
  · have hfullCard : fullSeed.card ≤ m := by
      dsimp only [fullSeed, fullRankLiftSeed]
      exact (Finset.card_image_le.trans_eq (Fintype.card_fin m))
    exact (Nat.add_le_add_left hfullCard planeSeed.card).trans_lt hcard
  · have hvSpan : Submodule.span ℝ
        (Set.range fun i ↦ integralReal (v i)) = ⊤ := by
      apply hv_independent.span_eq_top_of_card_eq_finrank'
      simp
    apply top_unique
    rw [← hvSpan]
    apply Submodule.span_mono
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨distortionLift a (v i), ?_, head_distortionLift a (v i)⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Passing from ordinary coordinate functions to `EuclideanSpace` preserves
linear independence.  This is the bridge from the successive-minimum API to
the Section 7 product geometry. -/
theorem linearIndependent_integralReal_of_integralEmbed {m k : ℕ}
    (v : Fin k → Mahler.IntegralPoint m)
    (hv : LinearIndependent ℝ (fun i ↦ Mahler.integralEmbed (v i))) :
    LinearIndependent ℝ (fun i ↦ integralReal (v i)) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg i
  apply hv g
  have h := congrArg WithLp.ofLp hg
  change (∑ j, g j • (fun q ↦ ((v j q : ℤ) : ℝ))) = 0
  simpa [integralReal] using h

/-- Thick-body specialization.  An `m`-point independent family in the
unit ball of a seminorm is exactly the successive-minimum input available in
Bilu's Section 3.  Once that unit ball is known to lie in `2B`, this theorem
constructs Proposition 7.4's `GeometricData` with no further choice or
geometric assumption.
-/
def geometricDataOfPlaneAndAdmitsIndependent {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (p : Seminorm ℝ (Fin m → ℝ))
    (planeSeed : Finset (Ambient m r))
    (hindependent : Mahler.AdmitsIndependent p m 1)
    (hunit : ∀ x : Mahler.IntegralPoint m,
      p (Mahler.integralEmbed x) ≤ 1 → integralReal x ∈ (2 : ℝ) • B)
    (hplane_body : ∀ z ∈ planeSeed, z ∈ distortionBody B a)
    (hplane_lattice : ∀ z ∈ planeSeed,
      z ∈ ambientProductIntegralPoints m r)
    (hcard : planeSeed.card + m < m + r) :
    GeometricData B a := by
  classical
  let v := hindependent.choose
  have hv_independent : LinearIndependent ℝ
      (fun i ↦ integralReal (v i)) :=
    linearIndependent_integralReal_of_integralEmbed v hindependent.choose_spec.1
  apply geometricDataOfPlaneAndIndependentIntegralFamily
    B a planeSeed v hv_independent
  · intro i
    exact hunit (v i) (hindependent.choose_spec.2 i)
  · exact hplane_body
  · exact hplane_lattice
  · exact hcard

end

end Erdos186.CFP.Bilu.Proposition74Construction

#print axioms Erdos186.CFP.Bilu.Proposition74Construction.normal_tail_ne_zero_of_head_span
#print axioms Erdos186.CFP.Bilu.Proposition74Construction.span_section_lattice_eq_top
#print axioms Erdos186.CFP.Bilu.Proposition74Construction.geometricDataOfSeed
#print axioms Erdos186.CFP.Bilu.Proposition74Construction.geometricDataOfPlaneAndFullRankSeed
#print axioms
  Erdos186.CFP.Bilu.Proposition74Construction.geometricDataOfPlaneAndIndependentIntegralFamily
#print axioms Erdos186.CFP.Bilu.Proposition74Construction.geometricDataOfPlaneAndAdmitsIndependent
