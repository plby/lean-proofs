/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Case2
import ErdosProblems.Erdos186.CFP.Bilu.PolarSeparation
import ErdosProblems.Erdos186.CFP.Bilu.ProjectionCovolume
import ErdosProblems.Erdos186.CFP.Bilu.SaturatedFlag
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Constructing the geometric witness in Proposition 7.5, Case 2

This file joins the badly-approximable output of Proposition 8.3 to the
source product geometry of Proposition 7.4.  In particular, it constructs
the graph vector used in (8.7), proves the entire normal segment belongs to
the distortion body, and transports both the separating vector and the
integral normal to the single-coordinate ambient space.
-/

namespace Erdos186.CFP.Bilu.Proposition75Case2Construction

open MeasureTheory Set Module Submodule
open scoped BigOperators Pointwise RealInnerProductSpace
open BadlyApproximable BombieriVaaler PolarSeparation Proposition75Data
open Proposition75Case2 Case2Coordinates ProjectionVolumeCoarse
open SubspaceLattice

noncomputable section

/-- The point on the graph of the linear forms defining the distortion
body.  Its distortion errors are all identically zero. -/
def graphPoint {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) : Ambient m r :=
  WithLp.toLp 2 (b, WithLp.toLp 2 fun i ↦ ⟪b, a i⟫)

@[simp] theorem head_graphPoint {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) :
    head (graphPoint a b) = b := rfl

@[simp] theorem tail_graphPoint_apply {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (i : Fin r) :
    tail (graphPoint a b) i = ⟪b, a i⟫ := rfl

/-- A pair of integral coordinate vectors as a point of the source Hilbert
product. -/
def productIntegralPoint {m r : ℕ}
    (x : Fin m → ℤ) (y : Fin r → ℤ) : Ambient m r :=
  WithLp.toLp 2 (SubspaceLattice.integralReal x,
    SubspaceLattice.integralReal y)

@[simp] theorem head_productIntegralPoint {m r : ℕ}
    (x : Fin m → ℤ) (y : Fin r → ℤ) :
    head (productIntegralPoint x y) = SubspaceLattice.integralReal x := rfl

@[simp] theorem tail_productIntegralPoint {m r : ℕ}
    (x : Fin m → ℤ) (y : Fin r → ℤ) :
    tail (productIntegralPoint x y) = SubspaceLattice.integralReal y := rfl

theorem mem_ambientProductIntegralPoints_iff {m r : ℕ}
    {z : Ambient m r} :
    z ∈ ambientProductIntegralPoints m r ↔
      ∃ x : Fin m → ℤ, ∃ y : Fin r → ℤ,
        productIntegralPoint x y = z := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hpHead, hpTail⟩ := hp
    obtain ⟨x, hx⟩ := hpHead
    obtain ⟨y, hy⟩ := hpTail
    refine ⟨x, y, ?_⟩
    apply (WithLp.linearEquiv 2 ℤ
      (EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin r))).injective
    change (SubspaceLattice.integralReal x,
      SubspaceLattice.integralReal y) = p
    change SubspaceLattice.integralReal x = p.1 at hx
    change SubspaceLattice.integralReal y = p.2 at hy
    exact Prod.ext hx hy
  · rintro ⟨x, y, rfl⟩
    refine ⟨(SubspaceLattice.integralReal x,
      SubspaceLattice.integralReal y), ?_, rfl⟩
    exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩

/-- Concatenate the two integral coordinate blocks in the same order as
`ambientEquiv`. -/
def joinIntegralCoordinates {m r : ℕ}
    (x : Fin m → ℤ) (y : Fin r → ℤ) : Fin (m + r) → ℤ :=
  fun j ↦ Sum.elim x y (finSumFinEquiv.symm j)

/-- First block of a concatenated integral coordinate vector. -/
def integralHeadCoordinates {m r : ℕ}
    (z : Fin (m + r) → ℤ) : Fin m → ℤ :=
  fun i ↦ z (Fin.castAdd r i)

/-- Second block of a concatenated integral coordinate vector. -/
def integralTailCoordinates {m r : ℕ}
    (z : Fin (m + r) → ℤ) : Fin r → ℤ :=
  fun i ↦ z (Fin.natAdd m i)

@[simp] theorem joinIntegralCoordinates_split {m r : ℕ}
    (z : Fin (m + r) → ℤ) :
    joinIntegralCoordinates (integralHeadCoordinates z)
      (integralTailCoordinates z) = z := by
  funext j
  conv_rhs => rw [← finSumFinEquiv.apply_symm_apply j]
  generalize hs : finSumFinEquiv.symm j = s
  cases s <;> simp [hs, joinIntegralCoordinates, integralHeadCoordinates,
    integralTailCoordinates]

/-- The source product integral point becomes the standard concatenated
integral point under the ambient coordinate isometry. -/
theorem ambientEquiv_productIntegralPoint {m r : ℕ}
    (x : Fin m → ℤ) (y : Fin r → ℤ) :
    ambientEquiv m r (productIntegralPoint x y) =
      integralReal (joinIntegralCoordinates x y) := by
  ext j
  conv_rhs => rw [← finSumFinEquiv.apply_symm_apply j]
  generalize hs : finSumFinEquiv.symm j = s
  cases s <;> simp [hs, ambientEquiv,
    VolumeSections.euclideanFinAddEquivProdL2,
    productIntegralPoint, joinIntegralCoordinates]

/-- The literal source lattice in `C₀` and the literal standard lattice in
its concatenated-coordinate copy are the same lattice under the ambient
isometry. -/
def coordinateLatticeEquiv {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    D.latticePoints ≃ₗ[ℤ] integralPoints (coordinateC0 D) := by
  let f : D.latticePoints →ₗ[ℤ]
      integralPoints (coordinateC0 D) :=
    { toFun := fun z ↦ ⟨coordinateC0Equiv D z, by
        rw [mem_integralPoints_iff]
        obtain ⟨x, y, hxy⟩ :=
          mem_ambientProductIntegralPoints_iff.mp z.property
        refine ⟨joinIntegralCoordinates x y, ?_⟩
        change integralReal (joinIntegralCoordinates x y) =
          ambientEquiv m r (z : D.C0)
        rw [← ambientEquiv_productIntegralPoint, hxy]
        rfl⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        apply Subtype.ext
        simp }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (coordinateC0Equiv D).injective
    exact congrArg (fun z : integralPoints (coordinateC0 D) ↦
      (z : coordinateC0 D)) hxy
  · intro y
    let z0 : D.C0 := (coordinateC0Equiv D).symm (y : coordinateC0 D)
    have hcoord : ambientEquiv m r (z0 : Ambient m r) =
        ((y : coordinateC0 D) : EuclideanSpace ℝ (Fin (m + r))) := by
      exact congrArg Subtype.val
        ((coordinateC0Equiv D).apply_symm_apply (y : coordinateC0 D))
    obtain ⟨ell, hell⟩ := y.property
    change integralReal ell =
      ((y : coordinateC0 D) : EuclideanSpace ℝ (Fin (m + r))) at hell
    let x : Fin m → ℤ := integralHeadCoordinates ell
    let yy : Fin r → ℤ := integralTailCoordinates ell
    have hzIntegral : (z0 : Ambient m r) ∈
        ambientProductIntegralPoints m r := by
      rw [mem_ambientProductIntegralPoints_iff]
      refine ⟨x, yy, ?_⟩
      apply (ambientEquiv m r).injective
      rw [ambientEquiv_productIntegralPoint]
      simp only [x, yy, joinIntegralCoordinates_split]
      exact hell.trans hcoord.symm
    let z : D.latticePoints := ⟨z0, hzIntegral⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact (coordinateC0Equiv D).apply_symm_apply
      (y : coordinateC0 D)

@[simp] theorem coordinateLatticeEquiv_coe {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) (z : D.latticePoints) :
    ((coordinateLatticeEquiv D z : integralPoints (coordinateC0 D)) :
      coordinateC0 D) = coordinateC0Equiv D (z : D.C0) := by
  rfl

/-- The coordinate integral lattice pulls back exactly to the source
product integral lattice on `C₀`. -/
theorem coordinateIntegralPoints_comap {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    ZLattice.comap ℝ (integralPoints (coordinateC0 D))
      (coordinateC0Equiv D).toLinearMap = D.latticePoints := by
  ext x
  constructor
  · intro hx
    let y : integralPoints (coordinateC0 D) :=
      ⟨coordinateC0Equiv D x, hx⟩
    let z : D.latticePoints := (coordinateLatticeEquiv D).symm y
    have heq : coordinateC0Equiv D (z : D.C0) =
        coordinateC0Equiv D x := by
      change ((coordinateLatticeEquiv D z :
        integralPoints (coordinateC0 D)) : coordinateC0 D) =
          (y : coordinateC0 D)
      exact congrArg (fun w : integralPoints (coordinateC0 D) ↦
        (w : coordinateC0 D))
        ((coordinateLatticeEquiv D).apply_symm_apply y)
    have hz : (z : D.C0) = x := (coordinateC0Equiv D).injective heq
    change x ∈ D.latticePoints
    rw [← hz]
    exact z.property
  · intro hx
    change coordinateC0Equiv D x ∈ integralPoints (coordinateC0 D)
    exact (coordinateLatticeEquiv D ⟨x, hx⟩).property

/-- A real-linearly independent family of integral rows has a nonsingular
coordinate minor.  This supplies the pivot columns which are bookkeeping in
`SubspaceLattice.Presentation`, rather than additional source data. -/
theorem exists_nonsingular_coordinateMinor {s n : ℕ}
    (A : Matrix (Fin s) (Fin n) ℤ)
    (hA : LinearIndependent ℝ (realRow A)) :
    ∃ g : Fin s → Fin n, Function.Injective g ∧
      (coordinateMinor A g).det ≠ 0 := by
  let AR : Matrix (Fin s) (Fin n) ℝ := A.map (Int.castRingHom ℝ)
  have hARrows : LinearIndependent ℝ AR.row := by
    rw [Fintype.linearIndependent_iff] at hA ⊢
    intro c hc i
    apply hA c
    ext j
    have hj := congrArg (fun v : Fin n → ℝ ↦ v j) hc
    simpa [AR, realRow] using hj
  have hRank : AR.rank = s := by
    simpa using hARrows.rank_matrix
  have hSpanRank : finrank ℝ (Submodule.span ℝ (Set.range AR.col)) = s := by
    rw [← AR.rank_eq_finrank_span_cols, hRank]
  obtain ⟨f, hfRange, _hfSpan, hfLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range AR.col)
  let e : Fin s ≃ Fin (finrank ℝ
      (Submodule.span ℝ (Set.range AR.col))) := finCongr hSpanRank.symm
  let c : Fin s → (Fin s → ℝ) := f ∘ e
  have hcLI : LinearIndependent ℝ c := hfLI.comp e e.injective
  choose g hg using fun i ↦ hfRange (e i)
  have hgcol (i : Fin s) : AR.col (g i) = c i := by
    simpa only [c, Function.comp_apply] using hg i
  have hgInjective : Function.Injective g := by
    intro i j hij
    apply hcLI.injective
    rw [← hgcol i, ← hgcol j, hij]
  let M : Matrix (Fin s) (Fin s) ℝ :=
    (coordinateMinor A g).map (Int.castRingHom ℝ)
  have hMcols : LinearIndependent ℝ M.col := by
    have hMc : M.col = c := by
      funext i j
      simpa only [M, AR, Matrix.col_apply, Matrix.map_apply,
        coordinateMinor_apply] using congrFun (hgcol i) j
    rw [hMc]
    exact hcLI
  have hMdet : M.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det M).mp
      (Matrix.linearIndependent_cols_iff_isUnit.mp hMcols)).ne_zero
  refine ⟨g, hgInjective, ?_⟩
  intro hzero
  apply hMdet
  rw [show M.det = (((coordinateMinor A g).det : ℤ) : ℝ) by
    exact ((Int.castRingHom ℝ).map_det (coordinateMinor A g)).symm,
    hzero]
  simp

/-- Integer coordinate vectors whose real realizations lie in `L`.  This is
the coordinate model of `SubspaceLattice.integralPoints L`. -/
def integralCoordinateLattice {n : ℕ}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Submodule ℤ (Fin n → ℤ) :=
  (L.restrictScalars ℤ).comap (integralRealLinear (n := n))

@[simp] theorem mem_integralCoordinateLattice {n : ℕ}
    {L : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    {x : Fin n → ℤ} :
    x ∈ integralCoordinateLattice L ↔ integralReal x ∈ L := by
  rfl

/-- The coordinate lattice maps linearly and bijectively to the literal
integral-point lattice in the subtype. -/
def integralCoordinateEquiv {n : ℕ}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    integralCoordinateLattice L ≃ₗ[ℤ] integralPoints L := by
  let f : integralCoordinateLattice L →ₗ[ℤ] integralPoints L :=
    { toFun := fun x ↦
        ⟨⟨integralReal x, x.property⟩, ⟨x, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        ext j
        simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        apply Subtype.ext
        ext j
        simp }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext j
    have hj := congrArg (fun z : integralPoints L ↦
      ((z : L) : EuclideanSpace ℝ (Fin n)) j) hxy
    change ((x.val j : ℤ) : ℝ) = ((y.val j : ℤ) : ℝ) at hj
    exact_mod_cast hj
  · intro y
    obtain ⟨x, hx⟩ := y.property
    change integralReal x = (y : L) at hx
    have hxmem : integralReal x ∈ L := by
      rw [hx]
      exact y.val.property
    let xL : integralCoordinateLattice L := ⟨x, hxmem⟩
    refine ⟨xL, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx

@[simp] theorem integralCoordinateEquiv_coe {n : ℕ}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : integralCoordinateLattice L) :
    (((integralCoordinateEquiv L x : integralPoints L) : L) :
        EuclideanSpace ℝ (Fin n)) = integralReal x := by
  rfl

/-- A proper rational subspace whose literal integral points span it admits
an automatically saturated `Presentation`.  The rows are a PID basis of the
full coordinate lattice; the pivot minor and unused coordinate are derived
from independence and properness. -/
theorem exists_saturatedPresentation {n : ℕ}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤) :
    ∃ s : ℕ, ∃ P : Presentation (r := s) L, P.IsSaturated := by
  obtain ⟨s, b⟩ := Submodule.basisOfPid
    (Pi.basisFun ℤ (Fin n)) (integralCoordinateLattice L)
  let eZ := integralCoordinateEquiv L
  let bI : Basis (Fin s) ℤ (integralPoints L) := b.map eZ
  let A : Matrix (Fin s) (Fin n) ℤ :=
    fun i j ↦ ((b i : integralCoordinateLattice L) : Fin n → ℤ) j
  have hbZ : LinearIndependent ℤ
      (fun i ↦ ((b i : integralCoordinateLattice L) : Fin n → ℤ)) := by
    exact b.linearIndependent.map' (integralCoordinateLattice L).subtype
      (by simp)
  have hbRfun : LinearIndependent ℝ
      (fun i j ↦ ((((b i : integralCoordinateLattice L) :
        Fin n → ℤ) j : ℤ) : ℝ)) := by
    change LinearIndependent ℝ (fun i ↦
      algebraMap ℤ ℝ ∘
        ((b i : integralCoordinateLattice L) : Fin n → ℤ))
    rw [linearIndependent_algebraMap_comp_iff]
    exact hbZ
  have hA : LinearIndependent ℝ (realRow A) := by
    apply hbRfun.map'
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap
    simp
  let S : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    Submodule.span ℝ (Set.range (realRow A))
  have hintegral_mem (z : integralPoints L) :
      ((z : L) : EuclideanSpace ℝ (Fin n)) ∈ S := by
    have hz : z ∈ Submodule.span ℤ (Set.range bI) := by
      rw [bI.span_eq]
      exact Submodule.mem_top
    exact Submodule.span_induction (R := ℤ) (s := Set.range bI)
      (p := fun z _ ↦ ((z : L) : EuclideanSpace ℝ (Fin n)) ∈ S)
      (fun (z : integralPoints L) hz ↦ by
        obtain ⟨i, rfl⟩ := hz
        apply Submodule.subset_span
        refine ⟨i, ?_⟩
        ext j
        simp [bI, eZ, A, realRow])
      (by simp)
      (fun _ _ _ _ hx hy ↦ by simpa using S.add_mem hx hy)
      (fun c x _ hz ↦ by
        have hreal := S.smul_mem (c : ℝ) hz
        have heq : (((c • x : integralPoints L) : L) :
            EuclideanSpace ℝ (Fin n)) =
            (c : ℝ) • ((x : L) : EuclideanSpace ℝ (Fin n)) := by
          ext j
          simp
        rw [heq]
        exact hreal)
      hz
  have hSpanEq : S = L := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change integralReal
        ((b i : integralCoordinateLattice L) : Fin n → ℤ) ∈ L
      exact (b i).property
    · intro y hy
      let yL : L := ⟨y, hy⟩
      have hyspan : yL ∈ Submodule.span ℝ
          ((integralPoints L : Submodule ℤ L) : Set L) := by
        rw [hspan]
        exact Submodule.mem_top
      exact Submodule.span_induction (R := ℝ)
        (s := ((integralPoints L : Submodule ℤ L) : Set L))
        (p := fun z _ ↦ (z : EuclideanSpace ℝ (Fin n)) ∈ S)
        (fun (z : L) hz ↦ hintegral_mem ⟨z, hz⟩)
        (by simp)
        (fun _ _ _ _ hx hy ↦ S.add_mem hx hy)
        (fun c _ _ hz ↦ S.smul_mem c hz)
        hyspan
  have hsRank : s = finrank ℝ L := by
    have hcard := linearIndependent_iff_card_eq_finrank_span.mp hA
    simp only [Fintype.card_fin, Set.finrank] at hcard
    change s = finrank ℝ S at hcard
    rwa [hSpanEq] at hcard
  obtain ⟨g, hg, hminor⟩ := exists_nonsingular_coordinateMinor A hA
  have hslt : s < n := by
    rw [hsRank]
    simpa using L.finrank_lt hproper
  have hnotSurj : ¬ Function.Surjective g := by
    intro hsurj
    have := Fintype.card_le_of_surjective g hsurj
    simp only [Fintype.card_fin] at this
    omega
  simp only [Function.Surjective, Classical.not_forall, not_exists] at hnotSurj
  obtain ⟨extra, hextra⟩ := hnotSurj
  have hextraRange : extra ∉ Set.range g := by
    rintro ⟨i, hi⟩
    exact hextra i hi
  let P : Presentation (r := s) L :=
    { A := A
      minorColumns := g
      minorColumns_injective := hg
      extraColumn := extra
      extraColumn_not_mem := hextraRange
      minor_det_ne_zero := hminor
      span_eq := hSpanEq }
  refine ⟨s, P, ?_⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (P.rowBasis i : L) ∈ integralPoints L
    rw [mem_integralPoints_iff]
    refine ⟨((b i : integralCoordinateLattice L) : Fin n → ℤ), ?_⟩
    rw [P.rowBasis_coe]
    ext j
    simp [P, A, realRow]
  · intro z hz
    let zI : integralPoints L := ⟨z, hz⟩
    have hzspan : zI ∈ Submodule.span ℤ (Set.range bI) := by
      rw [bI.span_eq]
      exact Submodule.mem_top
    exact Submodule.span_induction (R := ℤ) (s := Set.range bI)
      (p := fun z _ ↦ (z : L) ∈ P.rowLattice)
      (fun (z : integralPoints L) hz ↦ by
        obtain ⟨i, rfl⟩ := hz
        apply Submodule.subset_span
        refine ⟨i, ?_⟩
        apply Subtype.ext
        rw [P.rowBasis_coe]
        ext j
        simp [bI, eZ, P, A, realRow])
      (by simp)
      (fun _ _ _ _ hx hy ↦ P.rowLattice.add_mem hx hy)
      (fun c _ _ hz ↦ P.rowLattice.smul_mem c hz)
      hzspan

/-- Proposition 7.4 already says that the section lattice spans `C₀`.
After the coordinate isometry, the full literal integral-point lattice spans
the coordinate copy as well. -/
theorem span_coordinateIntegralPoints_eq_top {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    Submodule.span ℝ
      ((integralPoints (coordinateC0 D) :
        Submodule ℤ (coordinateC0 D)) : Set (coordinateC0 D)) = ⊤ := by
  have hsource : Submodule.span ℝ
      ((D.latticePoints : Submodule ℤ D.C0) : Set D.C0) = ⊤ := by
    apply top_unique
    rw [← D.spans]
    apply Submodule.span_mono
    exact Set.inter_subset_right
  let T : Submodule ℝ (coordinateC0 D) := Submodule.span ℝ
    ((integralPoints (coordinateC0 D) :
      Submodule ℤ (coordinateC0 D)) : Set (coordinateC0 D))
  apply top_unique
  intro y _hy
  let x : D.C0 := (coordinateC0Equiv D).symm y
  have hxspan : x ∈ Submodule.span ℝ
      ((D.latticePoints : Submodule ℤ D.C0) : Set D.C0) := by
    rw [hsource]
    exact Submodule.mem_top
  have hout : coordinateC0Equiv D x ∈ T := by
    exact Submodule.span_induction (R := ℝ)
      (s := ((D.latticePoints : Submodule ℤ D.C0) : Set D.C0))
      (p := fun z _ ↦ coordinateC0Equiv D z ∈ T)
      (fun (z : D.C0) hz ↦ by
        apply Submodule.subset_span
        change coordinateC0Equiv D z ∈ integralPoints (coordinateC0 D)
        exact (coordinateLatticeEquiv D ⟨z, hz⟩).property)
      (by simp)
      (fun _ _ _ _ hz hw ↦ by simpa using T.add_mem hz hw)
      (fun c _ _ hz ↦ by simpa using T.smul_mem c hz)
      hxspan
  simpa only [x, (coordinateC0Equiv D).apply_symm_apply] using hout

/-- The Proposition 7.4 subspace therefore carries a saturated presentation
without an extra rationality or presentation hypothesis. -/
theorem exists_saturatedPresentation_coordinateC0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    ∃ s : ℕ, ∃ P : Presentation (r := s) (coordinateC0 D),
      P.IsSaturated := by
  have hproper : coordinateC0 D ≠ ⊤ := by
    intro htop
    apply D.proper
    apply Submodule.eq_top_of_finrank_eq
    calc
      finrank ℝ D.C0 = finrank ℝ (coordinateC0 D) :=
        (finrank_coordinateC0 D).symm
      _ = finrank ℝ (EuclideanSpace ℝ (Fin (m + r))) := by
        rw [htop]
        simp
      _ = m + r := by simp
      _ = finrank ℝ (Ambient m r) := by
        symm
        rw [(WithLp.linearEquiv 2 ℝ
          (EuclideanSpace ℝ (Fin m) ×
            EuclideanSpace ℝ (Fin r))).finrank_eq]
        simp [Module.finrank_prod]
  exact exists_saturatedPresentation (coordinateC0 D) hproper
    (span_coordinateIntegralPoints_eq_top D)

/-- Pull a saturated coordinate row basis back to a row basis of the source
subspace.  It spans the literal source lattice and has the same Gram
matrix. -/
theorem exists_sourceLatticeBasis_of_saturatedPresentation {m r s : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a)
    (P : Presentation (r := s) (coordinateC0 D))
    (hSat : P.IsSaturated) :
    ∃ bS : Basis (Fin s) ℝ D.C0,
      Submodule.span ℤ (Set.range bS) = D.latticePoints ∧
        Matrix.gram ℝ bS = Matrix.gram ℝ P.rowBasis := by
  let bS : Basis (Fin s) ℝ D.C0 := P.rowBasis.map
    (coordinateC0Equiv D).symm.toLinearEquiv
  have hsourceBasis : Submodule.span ℤ (Set.range bS) = D.latticePoints := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      rw [← coordinateIntegralPoints_comap D]
      change coordinateC0Equiv D (bS i) ∈
        integralPoints (coordinateC0 D)
      have hi : P.rowBasis i ∈ P.rowLattice :=
        Submodule.subset_span ⟨i, rfl⟩
      rw [hSat] at hi
      simpa [bS] using hi
    · intro z hz
      have hzcoord : coordinateC0Equiv D z ∈
          P.rowLattice := by
        rw [hSat]
        change z ∈ ZLattice.comap ℝ
          (integralPoints (coordinateC0 D))
            (coordinateC0Equiv D).toLinearMap
        rw [coordinateIntegralPoints_comap D]
        exact hz
      have hout : (coordinateC0Equiv D).symm
          (coordinateC0Equiv D z) ∈
          Submodule.span ℤ (Set.range bS) := by
        exact Submodule.span_induction (R := ℤ)
          (s := Set.range P.rowBasis)
          (p := fun w _ ↦ (coordinateC0Equiv D).symm w ∈
            Submodule.span ℤ (Set.range bS))
          (fun _ hw ↦ by
            obtain ⟨i, rfl⟩ := hw
            apply Submodule.subset_span
            exact ⟨i, by simp [bS]⟩)
          (by simp)
          (fun _ _ _ _ hw hv ↦ by
            simpa using (Submodule.span ℤ
              (Set.range bS)).add_mem hw hv)
          (fun c w _ hw ↦ by
            have hsmul := (Submodule.span ℤ
              (Set.range bS)).smul_mem c hw
            simpa using hsmul)
          hzcoord
      simpa using hout
  have hgram : Matrix.gram ℝ bS = Matrix.gram ℝ P.rowBasis := by
    ext i j
    let xi : D.C0 := (coordinateC0Equiv D).symm (P.rowBasis i)
    let xj : D.C0 := (coordinateC0Equiv D).symm (P.rowBasis j)
    have hinner := (ambientEquiv m r).inner_map_map
      (xi : Ambient m r) (xj : Ambient m r)
    have hi : ambientEquiv m r (xi : Ambient m r) =
        (P.rowBasis i : EuclideanSpace ℝ (Fin (m + r))) := by
      exact congrArg Subtype.val
        ((coordinateC0Equiv D).apply_symm_apply (P.rowBasis i))
    have hj : ambientEquiv m r (xj : Ambient m r) =
        (P.rowBasis j : EuclideanSpace ℝ (Fin (m + r))) := by
      exact congrArg Subtype.val
        ((coordinateC0Equiv D).apply_symm_apply (P.rowBasis j))
    rw [hi, hj, P.rowBasis_coe i, P.rowBasis_coe j] at hinner
    simpa [bS, xi, xj, Matrix.gram_apply, P.rowBasis_coe] using hinner.symm
  exact ⟨bS, hsourceBasis, hgram⟩

/-- Covolume equality for any saturated coordinate presentation. -/
theorem coordinateIntegralPoints_covolume_eq_latticePoints_of_presentation
    {m r s : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a)
    (P : Presentation (r := s) (coordinateC0 D))
    (hSat : P.IsSaturated) :
    ZLattice.covolume (integralPoints (coordinateC0 D))
        μHE[finrank ℝ D.C0] =
      ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0] := by
  let hdiscRow : DiscreteTopology P.rowLattice := by
    change DiscreteTopology
      (Submodule.span ℤ (Set.range P.rowBasis))
    infer_instance
  let hZRow : IsZLattice ℝ P.rowLattice := by
    change IsZLattice ℝ
      (Submodule.span ℤ (Set.range P.rowBasis))
    infer_instance
  let : DiscreteTopology (integralPoints (coordinateC0 D)) :=
    hSat ▸ hdiscRow
  let : IsZLattice ℝ (integralPoints (coordinateC0 D)) :=
    ⟨span_coordinateIntegralPoints_eq_top D⟩
  let : Measure.IsAddHaarMeasure
      (μHE[finrank ℝ D.C0] : Measure (coordinateC0 D)) := by
    rw [← finrank_coordinateC0 D]
    infer_instance
  have hmeasure : MeasurePreserving (coordinateC0Equiv D)
      μHE[finrank ℝ D.C0] μHE[finrank ℝ D.C0] :=
    (coordinateC0Equiv D).toIsometryEquiv
      |>.measurePreserving_euclideanHausdorffMeasure (finrank ℝ D.C0)
  have hc := ZLattice.covolume_comap
    (e := (coordinateC0Equiv D).toContinuousLinearEquiv)
    (integralPoints (coordinateC0 D)) μHE[finrank ℝ D.C0]
      μHE[finrank ℝ D.C0] hmeasure
  have hmap : (coordinateC0Equiv D).toContinuousLinearEquiv.toLinearMap =
      (coordinateC0Equiv D).toLinearMap := rfl
  rw [hmap] at hc
  rw [coordinateIntegralPoints_comap D] at hc
  exact hc.symm

/-- Covolume is unchanged by the source-to-coordinate lattice isometry. -/
theorem coordinateIntegralPoints_covolume_eq_latticePoints {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    ZLattice.covolume (integralPoints (coordinateC0 D))
        μHE[finrank ℝ D.C0] =
      ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0] := by
  obtain ⟨s, P, hSat⟩ := exists_saturatedPresentation_coordinateC0 D
  exact coordinateIntegralPoints_covolume_eq_latticePoints_of_presentation
    D P hSat

/-- The default Euclidean volume on the coordinate subspace gives the same
covolume as the intrinsic Hausdorff measure on the source subspace. -/
theorem coordinateIntegralPoints_volume_covolume_eq_latticePoints
    {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    ZLattice.covolume (integralPoints (coordinateC0 D)) =
      ZLattice.covolume D.latticePoints
        μHE[finrank ℝ D.C0] := by
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    (V := coordinateC0 D), finrank_coordinateC0 D]
  exact coordinateIntegralPoints_covolume_eq_latticePoints D

/-- Pull a coordinate normal back through the ambient isometry. -/
theorem productIntegralPoint_mem_orthogonal_of_coordinate {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) (x : Fin m → ℤ) (y : Fin r → ℤ)
    (hxy : integralReal (joinIntegralCoordinates x y) ∈
      Submodule.orthogonal (coordinateC0 D)) :
    productIntegralPoint x y ∈ Submodule.orthogonal D.C0 := by
  have hmapped : ambientEquiv m r (productIntegralPoint x y) ∈
      Submodule.orthogonal (coordinateC0 D) := by
    rwa [ambientEquiv_productIntegralPoint]
  change ambientEquiv m r (productIntegralPoint x y) ∈
    Submodule.orthogonal
      (D.C0.map (ambientEquiv m r).toLinearMap) at hmapped
  rw [← D.C0.map_orthogonal_equiv (ambientEquiv m r)] at hmapped
  obtain ⟨z, hz, heq⟩ := Submodule.mem_map.mp hmapped
  have : z = productIntegralPoint x y :=
    (ambientEquiv m r).injective heq
  rwa [← this]

/-- Choose orthonormal coordinates on a hyperplane so that the image of an
injective `d`-dimensional map is the first coordinate `d`-plane.  This is
the adapted-coordinate choice implicit in Bilu's passage to (8.9). -/
theorem exists_isometry_adapted_to_range {n d k : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hW : finrank ℝ W = d + k)
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    [FiniteDimensional ℝ L]
    (hL : finrank ℝ L = d) (f : L →ₗ[ℝ] W)
    (hf : Function.Injective f) :
    ∃ q : Base (d + k) ≃ₗᵢ[ℝ] W,
      ∀ z : L,
        q.symm (f z) ∈ LinearMap.range
          (VolumeSections.canonicalCoordinateFlagF d k 0
            (Nat.zero_le k)).toLinearMap := by
  let j := VolumeSections.canonicalCoordinateFlagF d k 0 (Nat.zero_le k)
  let S : Submodule ℝ (Base (d + k)) := LinearMap.range j.toLinearMap
  let H : Submodule ℝ W := LinearMap.range f
  have hS : finrank ℝ S = d := by
    dsimp only [S]
    rw [LinearMap.finrank_range_of_inj j.injective]
    simp
  have hH : finrank ℝ H = d := by
    dsimp only [H]
    rw [LinearMap.finrank_range_of_inj hf, hL]
  let eS : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] S :=
    VolumeSections.euclideanEquivSubmoduleOfFinrankEq S hS
  let eH : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] H :=
    VolumeSections.euclideanEquivSubmoduleOfFinrankEq H hH
  let eSH : S ≃ₗᵢ[ℝ] H := eS.symm.trans eH
  let q0 : Base (d + k) ≃ₗᵢ[ℝ] W :=
    VolumeSections.euclideanEquivSubmoduleOfFinrankEq W hW
  let g : S →ₗᵢ[ℝ] Base (d + k) :=
    q0.symm.toLinearIsometry.comp
      (H.subtypeₗᵢ.comp eSH.toLinearIsometry)
  let A : Base (d + k) →ₗᵢ[ℝ] Base (d + k) := g.extend
  let Ae : Base (d + k) ≃ₗᵢ[ℝ] Base (d + k) :=
    A.toLinearIsometryEquiv rfl
  let q : Base (d + k) ≃ₗᵢ[ℝ] W := Ae.trans q0
  refine ⟨q, ?_⟩
  intro z
  let hzH : H := ⟨f z, LinearMap.mem_range_self f z⟩
  let sz : S := eSH.symm hzH
  have hgsz : g sz = q0.symm (f z) := by
    change q0.symm ((eSH sz : H) : W) = q0.symm (f z)
    congr 1
    exact congrArg Subtype.val (eSH.apply_symm_apply hzH)
  have hqsz : q (sz : Base (d + k)) = f z := by
    change q0 (A (sz : Base (d + k))) = f z
    rw [show A (sz : Base (d + k)) = g sz by
      exact LinearIsometry.extend_apply g sz]
    rw [hgsz]
    exact q0.apply_symm_apply (f z)
  have hsymm : q.symm (f z) = (sz : Base (d + k)) := by
    apply q.injective
    simpa using hqsz.symm
  rw [hsymm]
  exact sz.property

/-- The hyperplane perpendicular to a nonzero separator. -/
def separatorHyperplane {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  (ℝ ∙ u)ᗮ

theorem separator_mem_hyperplane_orthogonal {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n)} :
    u ∈ (separatorHyperplane u)ᗮ := by
  exact (ℝ ∙ u).le_orthogonal_orthogonal
    (Submodule.mem_span_singleton_self u)

theorem separatorHyperplane_codim_one {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n)} (hu0 : u ≠ 0) :
    finrank ℝ (separatorHyperplane u) + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
  have hsum := (ℝ ∙ u).finrank_add_finrank_orthogonal
  have hspan : finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu0
  change finrank ℝ (ℝ ∙ u)ᗮ + 1 =
    finrank ℝ (EuclideanSpace ℝ (Fin n))
  omega

/-- A nonzero pairing with a normal to `L` makes projection from `L` to
the separator hyperplane injective. -/
theorem projectionRestrict_injective_separatorHyperplane {n : ℕ}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {u l : EuclideanSpace ℝ (Fin n)} (hu0 : u ≠ 0)
    (hl0 : l ≠ 0) (hl : l ∈ Lᗮ) (hinner : ⟪u, l⟫ ≠ 0) :
    Function.Injective (projectionRestrict (separatorHyperplane u) L) := by
  let f := projectionRestrict (separatorHyperplane u) L
  have hlower := normDet_projectionRestrict_lower_bound
    (separatorHyperplane u) L u l
      (separatorHyperplane_codim_one hu0)
      separator_mem_hyperplane_orthogonal hu0 hl hl0
  have hleft : 0 < |⟪u, l⟫| / (‖u‖ * ‖l‖) := by
    exact div_pos (abs_pos.mpr hinner)
      (mul_pos (norm_pos_iff.mpr hu0) (norm_pos_iff.mpr hl0))
  have hdet : f.normDet ≠ 0 :=
    ne_of_gt (hleft.trans_le hlower)
  exact (f.normDet_ne_zero_tfae.out 0 4).mp hdet

theorem coe_mem_coordinateDistortionBody_of_mem_coordinateB0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) {z : coordinateC0 D}
    (hz : z ∈ coordinateB0 D) :
    (z : EuclideanSpace ℝ (Fin (m + r))) ∈
      coordinateDistortionBody B a := by
  obtain ⟨w, hw, rfl⟩ := hz
  change (w : Ambient m r) ∈ distortionBody B a at hw
  change ambientEquiv m r (w : Ambient m r) ∈
    coordinateDistortionBody B a
  simpa [coordinateDistortionBody] using hw

/-- Assemble every field of `Case2Witness` from a separating pair.  The
adapted coordinates and the two projection-measurability fields are derived
here; they are not additional source choices. -/
theorem exists_case2Witness_of_separator {m r d k : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a)
    (hmeasurable : MeasurableSet B) (hconvex : Convex ℝ B)
    (hrank : finrank ℝ D.C0 = d)
    (hdim : d + k + 1 = m + r)
    {u l : EuclideanSpace ℝ (Fin (m + r))}
    (hu0 : u ≠ 0) (hl0 : l ≠ 0)
    (hl : l ∈ Submodule.orthogonal (coordinateC0 D))
    {C rho : ℝ} (hC : 0 < C) (hsep : C < |⟪u, l⟫|)
    (hrho : 0 < rho)
    (hinball : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin (m + r))) rho ⊆
        coordinateDistortionBody B a)
    (hcompact : IsCompact (coordinateDistortionBody B a))
    (hsegment : ∀ t ∈ Icc
      (-(‖u‖ / (1 / 2 : ℝ))) (‖u‖ / (1 / 2 : ℝ)),
        t • unitNormal u ∈ coordinateDistortionBody B a) :
    ∃ X : Case2Witness D d k,
      X.u = u ∧ X.l = l ∧ X.C = C ∧ X.rho = rho ∧
        X.gaugeValue = (1 / 2 : ℝ) := by
  let W := separatorHyperplane u
  have huW : u ∈ Wᗮ := separator_mem_hyperplane_orthogonal
  have hWcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin (m + r))) :=
    separatorHyperplane_codim_one hu0
  have hambientRank : finrank ℝ (EuclideanSpace ℝ (Fin (m + r))) =
      m + r := by simp
  have hWrank : finrank ℝ W = d + k := by omega
  let f := projectionRestrict W (coordinateC0 D)
  have hf : Function.Injective f :=
    projectionRestrict_injective_separatorHyperplane
      (coordinateC0 D) hu0 hl0 hl (by
        intro hzero
        rw [hzero, abs_zero] at hsep
        linarith)
  have hLrank : finrank ℝ (coordinateC0 D) = d := by
    rw [finrank_coordinateC0 D, hrank]
  obtain ⟨q, hq⟩ := exists_isometry_adapted_to_range W hWrank hLrank f hf
  let e := normalCoordinateMeasurableEquiv W u q hWcodim huW hu0
  let eLin := normalCoordinateLinearEquiv W u q hWcodim huW hu0
  let Omega : Set (Base (d + k) × ℝ) :=
    e ⁻¹' coordinateDistortionBody B a
  have hOmegaEq : Omega = eLin ⁻¹' coordinateDistortionBody B a := by
    ext z
    change e z ∈ coordinateDistortionBody B a ↔
      eLin z ∈ coordinateDistortionBody B a
    rw [normalCoordinateLinearEquiv_apply]
  have hOmegaCompact : IsCompact Omega := by
    rw [hOmegaEq]
    exact eLin.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr
      hcompact
  have hbaseCompact : IsCompact (baseProjection Omega) :=
    hOmegaCompact.image continuous_fst
  have hhalfCompact : IsCompact (halfBaseProjection Omega) := by
    simpa only [halfBaseProjection] using hbaseCompact.smul (2 : ℝ)⁻¹
  refine ⟨{
    measurable_B := hmeasurable
    convex_B := hconvex
    rank_C0 := hrank
    W := W
    u := u
    u_ne_zero := hu0
    u_mem_orthogonal := huW
    W_codim_one := hWcodim
    q := q
    l := l
    l_ne_zero := hl0
    l_mem_orthogonal := hl
    rho := rho
    gaugeValue := 1 / 2
    C := C
    rho_pos := hrho
    gauge_pos := by norm_num
    gauge_half := by norm_num
    C_pos := hC
    polar_separation := hsep
    ambient_inball := hinball
    normal_segment := hsegment
    base_measurable := hbaseCompact.measurableSet
    half_base_measurable := hhalfCompact.measurableSet
    section_image := ?_ }, rfl, rfl, rfl, rfl, rfl⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨z, hzB0, rfl⟩ := hp
  obtain ⟨v, hv⟩ := hq z
  have hbase : q.symm (f z) ∈ baseProjection Omega := by
    have hproj : (f z : W) ∈
        (fun x : Base (d + k) ↦ q x) '' baseProjection Omega := by
      rw [image_baseProjection_preimage_normalCoordinate
        W u q hWcodim huW hu0 (coordinateDistortionBody B a)]
      refine ⟨(z : coordinateC0 D), ?_, rfl⟩
      exact coe_mem_coordinateDistortionBody_of_mem_coordinateB0 D hzB0
    obtain ⟨x, hxOmega, hx⟩ := hproj
    have hxeq : x = q.symm (f z) := by
      apply q.injective
      simpa using hx
    rwa [← hxeq]
  refine ⟨v, ?_, hv⟩
  change (VolumeSections.canonicalCoordinateFlagF d k 0
    (Nat.zero_le k)).toLinearMap v ∈ baseProjection Omega
  rwa [hv]

/-- The product inner product is exactly the arithmetic pairing used in
Definition 6.7.  We use `-x` in the bad-approximation call, so that the
source integral normal itself has first coordinate `x`. -/
theorem inner_graphPoint_productIntegralPoint {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m))
    (x : Fin m → ℤ) (y : Fin r → ℤ) :
    ⟪graphPoint a b, productIntegralPoint x y⟫ =
      euclideanPairing (WithLp.ofLp b)
        (integerCombination (fun i ↦ WithLp.ofLp (a i)) y -
          integerPoint (-x)) := by
  rw [WithLp.prod_inner_apply]
  simp only [graphPoint, productIntegralPoint, WithLp.ofLp_toLp,
    PiLp.inner_apply, SubspaceLattice.integralReal_apply,
    RCLike.inner_apply, conj_trivial, euclideanPairing,
    integerCombination, integerPoint, Pi.sub_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Pi.neg_apply, Int.cast_neg, sub_neg_eq_add]
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [add_comm]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  · apply Finset.sum_congr rfl
    intro i _hi
    ring

/-- Balancedness of `B` puts every graph multiple with coefficient in
`[-2,2]` into the distortion body `Omega`. -/
theorem smul_graphPoint_mem_distortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {b : EuclideanSpace ℝ (Fin m)} (hb : b ∈ B)
    {s : ℝ} (hs : |s| ≤ 2) :
    s • graphPoint a b ∈ distortionBody B a := by
  change s • b ∈ (2 : ℝ) • B ∧
    ∀ i, |⟪s • b, a i⟫ - (s • (fun i ↦ ⟪b, a i⟫)) i| ≤ 1
  constructor
  · refine ⟨(s / 2) • b, hbalanced.smul_mem ?_ hb, ?_⟩
    · simpa [Real.norm_eq_abs] using
        (div_le_one (by norm_num : (0 : ℝ) < 2)).2 hs
    · module
  · intro i
    simp [inner_smul_left]

/-- Isometric transport carries source normals to normals of the coordinate
copy of `C₀`. -/
theorem ambientEquiv_mem_coordinateC0_orthogonal {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) {z : Ambient m r}
    (hz : z ∈ Submodule.orthogonal D.C0) :
    ambientEquiv m r z ∈ Submodule.orthogonal (coordinateC0 D) := by
  change ambientEquiv m r z ∈
    Submodule.orthogonal (D.C0.map (ambientEquiv m r).toLinearMap)
  rw [← D.C0.map_orthogonal_equiv (ambientEquiv m r)]
  exact Submodule.mem_map.mpr ⟨z, hz, rfl⟩

/-- Isometric transport of a source distortion-body point. -/
theorem ambientEquiv_mem_coordinateDistortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {z : Ambient m r} (hz : z ∈ distortionBody B a) :
    ambientEquiv m r z ∈ coordinateDistortionBody B a := by
  simpa [coordinateDistortionBody] using hz

/-- The direct geometric output of bad approximation for an integral normal
to the Proposition 7.4 subspace.  This is equation (8.7), together with the
normal segment used in equation (8.8). -/
theorem exists_coordinate_separator {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) {X C : ℝ}
    (ha : IsBadlyApproximable
      (euclideanPolar (WithLp.ofLp '' B)) X C
      (fun i ↦ WithLp.ofLp (a i)))
    (hC : 0 < C) (x : Fin m → ℤ) (y : Fin r → ℤ)
    (hl : productIntegralPoint x y ∈ Submodule.orthogonal D.C0)
    (hl0source : productIntegralPoint x y ≠ 0)
    (hx : CoordBound X x) (hy : CoordBound X y) :
    ∃ u : EuclideanSpace ℝ (Fin (m + r)),
      u ≠ 0 ∧
      ambientEquiv m r (productIntegralPoint x y) ≠ 0 ∧
      ambientEquiv m r (productIntegralPoint x y) ∈
        Submodule.orthogonal (coordinateC0 D) ∧
      C < |⟪u, ambientEquiv m r (productIntegralPoint x y)⟫| ∧
      ∀ t ∈ Icc (-(‖u‖ / (1 / 2 : ℝ))) (‖u‖ / (1 / 2 : ℝ)),
        t • unitNormal u ∈ coordinateDistortionBody B a := by
  have hy0 : ∃ i, y i ≠ 0 := by
    have htail := D.normal_tail_ne_zero
      (productIntegralPoint x y) hl hl0source
    by_contra hnone
    push Not at hnone
    apply htail
    exact SubspaceLattice.integralReal_eq_zero_iff y |>.2 (by
      funext i
      exact hnone i)
  obtain ⟨bRaw, ⟨b, hbB, hb⟩, hsep⟩ :=
    exists_inner_gt_of_badlyApproximable ha hC (-x) y (by
      intro i
      simpa using hx i) hy0 hy
  subst bRaw
  let u := ambientEquiv m r (graphPoint a b)
  let l := ambientEquiv m r (productIntegralPoint x y)
  have hinner : ⟪u, l⟫ =
      euclideanPairing (WithLp.ofLp b)
        (integerCombination (fun i ↦ WithLp.ofLp (a i)) y -
          integerPoint (-x)) := by
    dsimp only [u, l]
    rw [(ambientEquiv m r).inner_map_map]
    exact inner_graphPoint_productIntegralPoint a b x y
  have hu0 : u ≠ 0 := by
    intro hu
    have : |⟪u, l⟫| = 0 := by simp [hu]
    rw [hinner] at this
    linarith
  have hl0 : l ≠ 0 := by
    intro hlzero
    have : |⟪u, l⟫| = 0 := by simp [hlzero]
    rw [hinner] at this
    linarith
  refine ⟨u, hu0, ?_,
    ambientEquiv_mem_coordinateC0_orthogonal D hl, ?_, ?_⟩
  · simpa only [l] using hl0
  · rwa [hinner]
  · intro t ht
    have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    let s : ℝ := t / ‖u‖
    have hs : |s| ≤ 2 := by
      have ht' : |t| ≤ 2 * ‖u‖ := by
        rw [abs_le]
        constructor <;> norm_num at ht ⊢ <;> linarith
      dsimp only [s]
      rw [abs_div, abs_of_pos hunorm]
      exact (div_le_iff₀ hunorm).2 ht'
    have hsource : s • graphPoint a b ∈ distortionBody B a :=
      smul_graphPoint_mem_distortionBody hbalanced hbB hs
    have heq : t • unitNormal u = ambientEquiv m r (s • graphPoint a b) := by
      dsimp only [unitNormal, s, u]
      rw [map_smul]
      simp only [norm_map]
      module
    rw [heq]
    exact ambientEquiv_mem_coordinateDistortionBody hsource

/-- A saturated integral presentation supplies the bounded normal required
by the preceding separator construction.  Thus the only numerical input is
the strict comparison between the lattice covolume and the Prop8.3 box
parameter `X`. -/
theorem exists_coordinate_separator_of_presentation {m r s : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a)
    (P : Presentation (r := s) (coordinateC0 D))
    (hSat : P.IsSaturated) {X C : ℝ}
    (ha : IsBadlyApproximable
      (euclideanPolar (WithLp.ofLp '' B)) X C
      (fun i ↦ WithLp.ofLp (a i)))
    (hC : 0 < C)
    (hcovol : ZLattice.covolume
      (integralPoints (coordinateC0 D)) < X) :
    ∃ ell : Fin (m + r) → ℤ,
      ∃ u : EuclideanSpace ℝ (Fin (m + r)),
        ell ≠ 0 ∧
        (∀ j, ((|ell j| : ℤ) : ℝ) ≤
          ZLattice.covolume (integralPoints (coordinateC0 D))) ∧
        u ≠ 0 ∧ integralReal ell ≠ 0 ∧
        integralReal ell ∈ Submodule.orthogonal (coordinateC0 D) ∧
        C < |⟪u, integralReal ell⟫| ∧
        ∀ t ∈ Icc (-(‖u‖ / (1 / 2 : ℝ))) (‖u‖ / (1 / 2 : ℝ)),
          t • unitNormal u ∈ coordinateDistortionBody B a := by
  obtain ⟨ell, hell0, hellNormal, hellBound⟩ :=
    P.exists_integral_normal_abs_le_integralPoints_covolume hSat
  let x : Fin m → ℤ := integralHeadCoordinates ell
  let y : Fin r → ℤ := integralTailCoordinates ell
  have hellMem : integralReal ell ∈
      Submodule.orthogonal (coordinateC0 D) :=
    ((coordinateC0 D).mem_orthogonal (integralReal ell)).2 hellNormal
  have hsource : productIntegralPoint x y ∈
      Submodule.orthogonal D.C0 := by
    apply productIntegralPoint_mem_orthogonal_of_coordinate D
    simpa only [x, y, joinIntegralCoordinates_split] using hellMem
  have hsource0 : productIntegralPoint x y ≠ 0 := by
    intro hzero
    have hmapped := congrArg (ambientEquiv m r) hzero
    rw [ambientEquiv_productIntegralPoint,
      show joinIntegralCoordinates x y = ell by
        simp only [x, y, joinIntegralCoordinates_split]] at hmapped
    have hmapped' : integralReal ell = 0 := by simpa using hmapped
    exact hell0 (integralReal_eq_zero_iff ell |>.1 hmapped')
  have hx : CoordBound X x := by
    intro i
    simpa only [x, integralHeadCoordinates, Int.cast_abs] using
      (hellBound (Fin.castAdd r i)).trans_lt hcovol
  have hy : CoordBound X y := by
    intro i
    simpa only [y, integralTailCoordinates, Int.cast_abs] using
      (hellBound (Fin.natAdd m i)).trans_lt hcovol
  obtain ⟨u, hu0, hl0, hlNormal, hsep, hsegment⟩ :=
    exists_coordinate_separator hbalanced D ha hC x y hsource hsource0 hx hy
  have hcoord : ambientEquiv m r (productIntegralPoint x y) =
      integralReal ell := by
    rw [ambientEquiv_productIntegralPoint]
    simp only [x, y, joinIntegralCoordinates_split]
  refine ⟨ell, u, hell0, hellBound, hu0, ?_, ?_, ?_, hsegment⟩
  · rwa [hcoord] at hl0
  · rwa [hcoord] at hlNormal
  · rwa [hcoord] at hsep

/-- Complete Proposition 7.4/8.3-to-`Case2Witness` bridge.  The selected
normal remains visible in the conclusion, including the Euclidean norm
bound needed by `proposition75Conclusion_of_raw_case2`. -/
theorem exists_case2Witness_of_presentation {m r d k s : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B)
    (hmeasurable : MeasurableSet B) (hconvex : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a)
    (hrank : finrank ℝ D.C0 = d)
    (hdim : d + k + 1 = m + r)
    (P : Presentation (r := s) (coordinateC0 D))
    (hSat : P.IsSaturated) {X C rho : ℝ}
    (ha : IsBadlyApproximable
      (euclideanPolar (WithLp.ofLp '' B)) X C
      (fun i ↦ WithLp.ofLp (a i)))
    (hC : 0 < C)
    (hcovol : ZLattice.covolume
      (integralPoints (coordinateC0 D)) < X)
    (hrho : 0 < rho)
    (hinball : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin (m + r))) rho ⊆
        coordinateDistortionBody B a)
    (hcompact : IsCompact (coordinateDistortionBody B a)) :
    ∃ ell : Fin (m + r) → ℤ,
      ∃ Xw : Case2Witness D d k,
        ell ≠ 0 ∧
        (∀ j, ((|ell j| : ℤ) : ℝ) ≤
          ZLattice.covolume (integralPoints (coordinateC0 D))) ∧
        ‖Xw.l‖ ≤ Real.sqrt (m + r) *
          ZLattice.covolume (integralPoints (coordinateC0 D)) ∧
        Xw.l = integralReal ell ∧ Xw.C = C ∧ Xw.rho = rho ∧
          Xw.gaugeValue = (1 / 2 : ℝ) := by
  obtain ⟨ell, u, hell0, hellBound, hu0, hl0, hl, hsep, hsegment⟩ :=
    exists_coordinate_separator_of_presentation
      hbalanced D P hSat ha hC hcovol
  obtain ⟨Xw, hXu, hXl, hXC, hXrho, hXgauge⟩ :=
    exists_case2Witness_of_separator D hmeasurable hconvex hrank hdim
      hu0 hl0 hl hC hsep hrho hinball hcompact hsegment
  have hnorm : ‖integralReal ell‖ ≤ Real.sqrt (m + r) *
      ZLattice.covolume (integralPoints (coordinateC0 D)) :=
    by simpa only [Nat.cast_add] using
      (ProjectionCovolume.norm_integralReal_le_sqrt_mul
        (D := ZLattice.covolume (integralPoints (coordinateC0 D)))
        ell (by exact ENNReal.toReal_nonneg) hellBound)
  refine ⟨ell, Xw, hell0, hellBound, ?_, hXl, hXC, hXrho, hXgauge⟩
  rwa [hXl]

/-- Presentation-free Proposition 7.4/8.3-to-`Case2Witness` bridge.  The
saturated integral presentation is reconstructed from `GeometricData`, and
all normal bounds are stated using the original section lattice. -/
theorem exists_case2Witness {m r d k : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B)
    (hmeasurable : MeasurableSet B) (hconvex : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a)
    (hrank : finrank ℝ D.C0 = d)
    (hdim : d + k + 1 = m + r)
    {X C rho : ℝ}
    (ha : IsBadlyApproximable
      (euclideanPolar (WithLp.ofLp '' B)) X C
      (fun i ↦ WithLp.ofLp (a i)))
    (hC : 0 < C)
    (hcovol : ZLattice.covolume D.latticePoints
      μHE[finrank ℝ D.C0] < X)
    (hrho : 0 < rho)
    (hinball : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin (m + r))) rho ⊆
        coordinateDistortionBody B a)
    (hcompact : IsCompact (coordinateDistortionBody B a)) :
    ∃ ell : Fin (m + r) → ℤ,
      ∃ Xw : Case2Witness D d k,
        ell ≠ 0 ∧
        (∀ j, ((|ell j| : ℤ) : ℝ) ≤
          ZLattice.covolume D.latticePoints
            μHE[finrank ℝ D.C0]) ∧
        ‖Xw.l‖ ≤ Real.sqrt (m + r) *
          ZLattice.covolume D.latticePoints
            μHE[finrank ℝ D.C0] ∧
        Xw.l = integralReal ell ∧ Xw.C = C ∧ Xw.rho = rho ∧
          Xw.gaugeValue = (1 / 2 : ℝ) := by
  obtain ⟨s, P, hSat⟩ := exists_saturatedPresentation_coordinateC0 D
  have hcovol' : ZLattice.covolume
      (integralPoints (coordinateC0 D)) < X := by
    rwa [coordinateIntegralPoints_volume_covolume_eq_latticePoints D]
  obtain ⟨ell, Xw, hell0, hellBound, hnorm, hl, hXC, hXrho,
      hXgauge⟩ :=
    exists_case2Witness_of_presentation hbalanced hmeasurable hconvex D
      hrank hdim P hSat ha hC hcovol' hrho hinball hcompact
  refine ⟨ell, Xw, hell0, ?_, ?_, hl, hXC, hXrho, hXgauge⟩
  · simpa only [coordinateIntegralPoints_volume_covolume_eq_latticePoints D]
      using hellBound
  · simpa only [coordinateIntegralPoints_volume_covolume_eq_latticePoints D]
      using hnorm

end

end Erdos186.CFP.Bilu.Proposition75Case2Construction

#print axioms Erdos186.CFP.Bilu.Proposition75Case2Construction.exists_coordinate_separator
#print axioms Erdos186.CFP.Bilu.Proposition75Case2Construction.exists_coordinate_separator_of_presentation
#print axioms Erdos186.CFP.Bilu.Proposition75Case2Construction.exists_case2Witness_of_separator
#print axioms Erdos186.CFP.Bilu.Proposition75Case2Construction.exists_case2Witness_of_presentation
#print axioms Erdos186.CFP.Bilu.Proposition75Case2Construction.exists_case2Witness
