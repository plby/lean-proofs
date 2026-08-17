/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Definitions

/-!
# The finite oriented ham-sandwich step in dimension three

This file records the finite, oriented form used in the Pohoata--Zakharov
selection argument.  Affine functionals are oriented so that the first two
colours are retained on the positive side and the last two on the negative
side.

The strictification lemmas are stated separately.  This is useful because a
closed discrete ham-sandwich cut can contain points of the finite sets, while
the later convex-hull argument needs strict separation.
-/

namespace Erdos651

open Set
open scoped InnerProductSpace

noncomputable section

/-- The positive, respectively negative, strict sides of an oriented affine
hyperplane. -/
def strictPositiveSide (φ : Point 3 →ᵃ[ℝ] ℝ) : Set (Point 3) := {x | 0 < φ x}

def strictNegativeSide (φ : Point 3 →ᵃ[ℝ] ℝ) : Set (Point 3) := {x | φ x < 0}

/-- An affine functional strictly separates two finite point sets, with the
orientation from `N` towards `P`. -/
def StrictlySeparates (φ : Point 3 →ᵃ[ℝ] ℝ)
    (P N : Finset (Point 3)) : Prop :=
  (∀ x ∈ P, 0 < φ x) ∧ ∀ x ∈ N, φ x < 0

/-- A finite set lies in the closed positive side of an affine functional. -/
def InClosedPositiveSide (φ : Point 3 →ᵃ[ℝ] ℝ)
    (X : Finset (Point 3)) : Prop :=
  ∀ x ∈ X, 0 ≤ φ x

/-- A finite set lies in the closed negative side of an affine functional. -/
def InClosedNegativeSide (φ : Point 3 →ᵃ[ℝ] ℝ)
    (X : Finset (Point 3)) : Prop :=
  ∀ x ∈ X, φ x ≤ 0

/-- The integer form of "`Y` contains at least half of `X`".  It avoids
rounding conventions and is exactly what is needed in the iterative loss
estimate. -/
def IsHalfOf (Y X : Finset (Point 3)) : Prop :=
  Y ⊆ X ∧ X.card ≤ 2 * Y.card

/-- Data furnished by a strict oriented four-colour ham-sandwich cut. -/
structure OrientedHalfSelection
    (X₁ X₂ X₃ X₄ : Finset (Point 3)) where
  φ : Point 3 →ᵃ[ℝ] ℝ
  Y₁ : Finset (Point 3)
  Y₂ : Finset (Point 3)
  Y₃ : Finset (Point 3)
  Y₄ : Finset (Point 3)
  half₁ : IsHalfOf Y₁ X₁
  half₂ : IsHalfOf Y₂ X₂
  half₃ : IsHalfOf Y₃ X₃
  half₄ : IsHalfOf Y₄ X₄
  positive₁ : ∀ x ∈ Y₁, 0 < φ x
  positive₂ : ∀ x ∈ Y₂, 0 < φ x
  negative₃ : ∀ x ∈ Y₃, φ x < 0
  negative₄ : ∀ x ∈ Y₄, φ x < 0

/-- Closed-side data before perturbing the ham-sandwich hyperplane away
from its finitely many boundary points. -/
structure ClosedOrientedHalfSelection
    (X₁ X₂ X₃ X₄ : Finset (Point 3)) where
  φ : Point 3 →ᵃ[ℝ] ℝ
  Y₁ : Finset (Point 3)
  Y₂ : Finset (Point 3)
  Y₃ : Finset (Point 3)
  Y₄ : Finset (Point 3)
  half₁ : IsHalfOf Y₁ X₁
  half₂ : IsHalfOf Y₂ X₂
  half₃ : IsHalfOf Y₃ X₃
  half₄ : IsHalfOf Y₄ X₄
  positive₁ : InClosedPositiveSide φ Y₁
  positive₂ : InClosedPositiveSide φ Y₂
  negative₃ : InClosedNegativeSide φ Y₃
  negative₄ : InClosedNegativeSide φ Y₄
  nonconstant : φ.linear ≠ 0

/-- A closed hyperplane bisects a finite set if both of its closed sides
contain at least half of that set. -/
def ClosedBisects (φ : Point 3 →ᵃ[ℝ] ℝ) (X : Finset (Point 3)) : Prop :=
  X.card ≤ 2 * (X.filter fun x ↦ 0 ≤ φ x).card ∧
    X.card ≤ 2 * (X.filter fun x ↦ φ x ≤ 0).card

/-- The exact missing topological/combinatorial input: the finite discrete
ham-sandwich theorem for three point sets in `ℝ³`. -/
def ThreeSetDiscreteHamSandwich : Prop :=
  ∀ X₁ X₂ X₃ : Finset (Point 3),
    ∃ φ : Point 3 →ᵃ[ℝ] ℝ, φ.linear ≠ 0 ∧
      ClosedBisects φ X₁ ∧ ClosedBisects φ X₂ ∧ ClosedBisects φ X₃

/-! We prove the topological input in the only dimension needed here.  The
proof is the elementary covering-space proof of Borsuk--Ulam for
`S² → ℝ²`: a zero-free odd map would give an odd circle-valued map;
lifting its restriction to a hemisphere through `Circle.exp` contradicts
the two possible orientations of the equator. -/

private abbrev SphereTwo := Metric.sphere (0 : Point 3) 1
private abbrev DiskTwo := Metric.closedBall (0 : Point 2) 1

private def sphereTwoNeg (x : SphereTwo) : SphereTwo :=
  ⟨-x.1, by simpa [Metric.mem_sphere] using x.2⟩

@[simp] private lemma sphereTwoNeg_val (x : SphereTwo) :
    (sphereTwoNeg x : Point 3) = -x := rfl

private def pointTwoComplex : Point 2 ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

private def pointTwoCircle (x : Point 2) (hx : x ≠ 0) : Circle :=
  ⟨pointTwoComplex x / (‖x‖ : ℂ), by
    change pointTwoComplex x / (‖x‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    rw [norm_div, LinearIsometryEquiv.norm_map]
    simp [norm_ne_zero_iff.mpr hx]⟩

private lemma pointTwoCircle_neg (x : Point 2) (hx : x ≠ 0) :
    pointTwoCircle (-x) (neg_ne_zero.mpr hx) = -pointTwoCircle x hx := by
  apply Circle.ext
  change pointTwoComplex (-x) / (‖-x‖ : ℂ) =
    -(pointTwoComplex x / (‖x‖ : ℂ))
  rw [map_neg, norm_neg]
  exact neg_div _ _

private def upperHemisphere (z : DiskTwo) : SphereTwo :=
  ⟨WithLp.toLp 2 ![(z.1 0), (z.1 1), Real.sqrt (1 - ‖z.1‖ ^ 2)], by
    rw [Metric.mem_sphere, dist_zero_right]
    apply sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1) |>.mp
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [Fin.sum_univ_three]
    simp
    have hzsq : (z.1 0) ^ 2 + (z.1 1) ^ 2 = ‖z.1‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp
    rw [hzsq]
    rw [Real.sq_sqrt]
    · ring
    · have hz := z.2
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      apply sub_nonneg.mpr
      simpa using ((sq_le_sq₀ (norm_nonneg z.1)
        (by norm_num : (0 : ℝ) ≤ 1)).mpr hz)⟩

private lemma continuous_upperHemisphere : Continuous upperHemisphere := by
  apply Continuous.subtype_mk
  fun_prop

private def circleDisk (q : Circle) : DiskTwo :=
  ⟨pointTwoComplex.symm (q : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right,
      LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩

private lemma continuous_circleDisk : Continuous circleDisk := by
  apply Continuous.subtype_mk
  exact pointTwoComplex.symm.continuous.comp continuous_subtype_val

private lemma circleDisk_neg (q : Circle) :
    circleDisk (-q) = -circleDisk q := by
  apply Subtype.ext
  change pointTwoComplex.symm (-(q : ℂ)) = -pointTwoComplex.symm (q : ℂ)
  exact map_neg _ _

private lemma upperHemisphere_circleDisk_neg (q : Circle) :
    upperHemisphere (circleDisk (-q)) =
      sphereTwoNeg (upperHemisphere (circleDisk q)) := by
  apply Subtype.ext
  rw [circleDisk_neg]
  ext i
  fin_cases i <;>
    simp [upperHemisphere, circleDisk, pointTwoComplex,
      Circle.norm_coe]

/-- The two-dimensional Borsuk--Ulam theorem, in the concrete form used by
the finite median argument below. -/
private theorem borsukUlamSphereTwo
    (f : SphereTwo → Point 2) (hf : Continuous f)
    (hodd : ∀ x, f (sphereTwoNeg x) = -f x) :
    ∃ x, f x = 0 := by
  by_contra hzero
  push_neg at hzero
  let g : SphereTwo → Circle := fun x ↦ pointTwoCircle (f x) (hzero x)
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    change Continuous fun x ↦ pointTwoComplex (f x) / (‖f x‖ : ℂ)
    apply Continuous.div₀
    · exact pointTwoComplex.continuous.comp hf
    · exact Complex.continuous_ofReal.comp hf.norm
    · intro x
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hzero x))
  have hgodd (x : SphereTwo) : g (sphereTwoNeg x) = -g x := by
    apply Circle.ext
    change pointTwoComplex (f (sphereTwoNeg x)) /
        (‖f (sphereTwoNeg x)‖ : ℂ) =
      -(pointTwoComplex (f x) / (‖f x‖ : ℂ))
    rw [hodd, map_neg, norm_neg]
    exact neg_div _ _

  let G : C(DiskTwo, Circle) :=
    ⟨fun z ↦ g (upperHemisphere z), hg.comp continuous_upperHemisphere⟩
  let z₀ : DiskTwo := ⟨0, by simp⟩
  letI : ContractibleSpace DiskTwo :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : LocallyPathConnectedSpace DiskTwo :=
    (convex_closedBall (0 : Point 2) 1).locallyPathConnectedSpace
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (G z₀)
  obtain ⟨L, hL, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts G z₀ e₀ he₀

  let D : Circle → ℝ := fun q ↦ L (circleDisk (-q)) - L (circleDisk q)
  have hDcont : Continuous D := by
    dsimp [D]
    exact (L.continuous.comp (continuous_circleDisk.comp continuous_neg)).sub
      (L.continuous.comp continuous_circleDisk)
  have hDexp (q : Circle) : Circle.exp (D q) = -1 := by
    rw [show D q = L (circleDisk (-q)) - L (circleDisk q) by rfl,
      Circle.exp_sub]
    have hLpoint (z : DiskTwo) : Circle.exp (L z) = G z := by
      exact congr_fun hL.2 z
    rw [hLpoint, hLpoint]
    change g (upperHemisphere (circleDisk (-q))) /
      g (upperHemisphere (circleDisk q)) = -1
    rw [upperHemisphere_circleDisk_neg, hgodd]
    rw [neg_div]
    have hself : g (upperHemisphere (circleDisk q)) /
        g (upperHemisphere (circleDisk q)) = 1 := div_self' _
    rw [hself]
  have hDneg (q : Circle) : D (-q) = -D q := by
    simp only [D, neg_neg]
    ring

  let I := Set.Icc (0 : ℝ) 1
  let q : I → Circle := fun t ↦ Circle.exp (Real.pi * t.1)
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  let d : C(I, ℝ) := ⟨fun t ↦ D (q t), hDcont.comp hqcont⟩
  let K : C(I, Circle) := ContinuousMap.const I (-1)
  let t₀ : I := ⟨0, by dsimp [I]; simp⟩
  let t₁ : I := ⟨1, by dsimp [I]; simp⟩
  letI : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  letI : LocallyPathConnectedSpace I :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  have hd_lifts : Circle.exp ∘ d = K := by
    funext t
    exact hDexp (q t)
  obtain ⟨J, hJ, hJunique⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts K t₀ (d t₀)
      (congr_fun hd_lifts t₀)
  have hd_eq_J : d = J := hJunique d ⟨rfl, hd_lifts⟩
  let c : C(I, ℝ) := ContinuousMap.const I (d t₀)
  have hc_lifts : Circle.exp ∘ c = K := by
    funext t
    change Circle.exp (d t₀) = -1
    exact hDexp (q t₀)
  have hc_eq_J : c = J := hJunique c ⟨rfl, hc_lifts⟩
  have hdc : d = c := hd_eq_J.trans hc_eq_J.symm
  have hq₀ : q t₀ = 1 := by
    apply Circle.ext
    simp [q, t₀]
  have hq₁ : q t₁ = -1 := by
    apply Circle.ext
    simp [q, t₁, Circle.coe_exp, Complex.exp_pi_mul_I]
  have hdend : D (-1) = D 1 := by
    have := DFunLike.congr_fun hdc t₁
    simpa [d, c, hq₀, hq₁] using this
  have hD1 : D 1 = 0 := by
    have hneg : D (-1) = -D 1 := by simpa using hDneg (1 : Circle)
    rw [hdend] at hneg
    linarith
  have hone : (1 : Circle) = -1 := by
    calc
      1 = Circle.exp 0 := Circle.exp_zero.symm
      _ = Circle.exp (D 1) := congr_arg Circle.exp hD1.symm
      _ = -1 := hDexp 1
  exact Circle.neg_ne_self 1 hone.symm

private lemma majoritySize_le_card {X : Finset (Point 3)} (hX : X.Nonempty) :
    X.card / 2 + 1 ≤ X.card := by
  have := Finset.card_pos.mpr hX
  omega

private lemma majorityFamily_nonempty {X : Finset (Point 3)} (hX : X.Nonempty) :
    (X.powersetCard (X.card / 2 + 1)).Nonempty :=
  Finset.powersetCard_nonempty.mpr (majoritySize_le_card hX)

private lemma majorityMember_nonempty {X A : Finset (Point 3)}
    (hA : A ∈ X.powersetCard (X.card / 2 + 1)) : A.Nonempty := by
  rw [Finset.mem_powersetCard] at hA
  apply Finset.card_pos.mp
  omega

private lemma neg_finset_sup' {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    -(s.sup' hs f) = s.inf' hs (fun i ↦ -f i) := by
  apply le_antisymm
  · apply Finset.le_inf' hs
    intro i hi
    exact neg_le_neg (Finset.le_sup' f hi)
  · obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup' hs f
    have h := Finset.inf'_le (fun i ↦ -f i) hi
    rw [hsup]
    exact h

private lemma neg_finset_inf' {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    -(s.inf' hs f) = s.sup' hs (fun i ↦ -f i) := by
  apply le_antisymm
  · obtain ⟨i, hi, hinf⟩ := Finset.exists_mem_eq_inf' hs f
    have h := Finset.le_sup' (fun i ↦ -f i) hi
    rw [hinf]
    exact h
  · apply Finset.sup'_le hs
    intro i hi
    exact neg_le_neg (Finset.inf'_le f hi)

private def lowerMedian (X : Finset (Point 3)) (hX : X.Nonempty)
    (u : SphereTwo) : ℝ :=
  let F := X.powersetCard (X.card / 2 + 1)
  F.attach.sup' (majorityFamily_nonempty hX).attach fun A ↦
    A.1.inf' (majorityMember_nonempty A.2) fun x ↦ ⟪u.1, (x : Point 3)⟫_ℝ

private def upperMedian (X : Finset (Point 3)) (hX : X.Nonempty)
    (u : SphereTwo) : ℝ :=
  let F := X.powersetCard (X.card / 2 + 1)
  F.attach.inf' (majorityFamily_nonempty hX).attach fun A ↦
    A.1.sup' (majorityMember_nonempty A.2) fun x ↦ ⟪u.1, (x : Point 3)⟫_ℝ

private def finiteMedian (X : Finset (Point 3)) (u : SphereTwo) : ℝ :=
  if hX : X.Nonempty then (lowerMedian X hX u + upperMedian X hX u) / 2 else 0

private lemma continuous_lowerMedian (X : Finset (Point 3)) (hX : X.Nonempty) :
    Continuous (lowerMedian X hX) := by
  unfold lowerMedian
  apply Continuous.finset_sup'_apply (majorityFamily_nonempty hX).attach
  intro A hA
  apply Continuous.finset_inf'_apply (majorityMember_nonempty A.2)
  intro x hx
  fun_prop

private lemma continuous_upperMedian (X : Finset (Point 3)) (hX : X.Nonempty) :
    Continuous (upperMedian X hX) := by
  unfold upperMedian
  apply Continuous.finset_inf'_apply (majorityFamily_nonempty hX).attach
  intro A hA
  apply Continuous.finset_sup'_apply (majorityMember_nonempty A.2)
  intro x hx
  fun_prop

private lemma continuous_finiteMedian (X : Finset (Point 3)) :
    Continuous (finiteMedian X) := by
  change Continuous fun u ↦ finiteMedian X u
  by_cases hX : X.Nonempty
  · simpa only [finiteMedian, dif_pos hX, Pi.add_apply] using
      (continuous_lowerMedian X hX).add (continuous_upperMedian X hX) |>.div_const 2
  · simpa only [finiteMedian, dif_neg hX] using
      (continuous_const : Continuous fun _ : SphereTwo ↦ (0 : ℝ))

@[simp] private lemma sphereTwoNeg_neg (u : SphereTwo) :
    sphereTwoNeg (sphereTwoNeg u) = u := by
  apply Subtype.ext
  simp [sphereTwoNeg]

private lemma lowerMedian_neg (X : Finset (Point 3)) (hX : X.Nonempty)
    (u : SphereTwo) :
    lowerMedian X hX (sphereTwoNeg u) = -upperMedian X hX u := by
  dsimp only [lowerMedian, upperMedian]
  rw [neg_finset_inf']
  congr 1
  funext A
  rw [neg_finset_sup']
  congr 1
  funext x
  simp [sphereTwoNeg]

private lemma upperMedian_neg (X : Finset (Point 3)) (hX : X.Nonempty)
    (u : SphereTwo) :
    upperMedian X hX (sphereTwoNeg u) = -lowerMedian X hX u := by
  have h := lowerMedian_neg X hX (sphereTwoNeg u)
  simp only [sphereTwoNeg_neg] at h
  linarith

private lemma finiteMedian_neg (X : Finset (Point 3)) (u : SphereTwo) :
    finiteMedian X (sphereTwoNeg u) = -finiteMedian X u := by
  by_cases hX : X.Nonempty
  · simp only [finiteMedian, dif_pos hX, lowerMedian_neg, upperMedian_neg]
    ring
  · simp [finiteMedian, hX]

private lemma majorityMembers_inter_nonempty {X A B : Finset (Point 3)}
    (hA : A ∈ X.powersetCard (X.card / 2 + 1))
    (hB : B ∈ X.powersetCard (X.card / 2 + 1)) :
    (A ∩ B).Nonempty := by
  rw [Finset.mem_powersetCard] at hA hB
  apply Finset.inter_nonempty_of_card_lt_card_add_card hA.1 hB.1
  rw [hA.2, hB.2]
  omega

private lemma lowerMedian_le_upperMedian (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    lowerMedian X hX u ≤ upperMedian X hX u := by
  unfold lowerMedian upperMedian
  apply Finset.sup'_le (majorityFamily_nonempty hX).attach
  intro A hA
  apply Finset.le_inf' (majorityFamily_nonempty hX).attach
  intro B hB
  obtain ⟨x, hx⟩ := majorityMembers_inter_nonempty A.2 B.2
  rw [Finset.mem_inter] at hx
  exact (Finset.inf'_le (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) hx.1).trans
    (Finset.le_sup' (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) hx.2)

private lemma lowerMedian_le_finiteMedian (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    lowerMedian X hX u ≤ finiteMedian X u := by
  rw [finiteMedian, dif_pos hX]
  have := lowerMedian_le_upperMedian X hX u
  linarith

private lemma finiteMedian_le_upperMedian (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    finiteMedian X u ≤ upperMedian X hX u := by
  rw [finiteMedian, dif_pos hX]
  have := lowerMedian_le_upperMedian X hX u
  linarith

private lemma card_filter_lowerMedian_lt_le (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    (X.filter fun x ↦ lowerMedian X hX u < ⟪u.1, x⟫_ℝ).card ≤ X.card / 2 := by
  by_contra hcard
  have hq : X.card / 2 + 1 ≤
      (X.filter fun x ↦ lowerMedian X hX u < ⟪u.1, x⟫_ℝ).card := by omega
  obtain ⟨A, hAfilter, hAcard⟩ := Finset.exists_subset_card_eq hq
  have hAX : A ⊆ X := hAfilter.trans (Finset.filter_subset _ _)
  have hAmem : A ∈ X.powersetCard (X.card / 2 + 1) := by
    rw [Finset.mem_powersetCard]
    exact ⟨hAX, hAcard⟩
  have hlt : lowerMedian X hX u <
      A.inf' (majorityMember_nonempty hAmem) (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) := by
    rw [Finset.lt_inf'_iff]
    intro x hx
    exact (Finset.mem_filter.mp (hAfilter hx)).2
  have hle : A.inf' (majorityMember_nonempty hAmem)
      (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) ≤ lowerMedian X hX u := by
    unfold lowerMedian
    exact Finset.le_sup'
      (fun B : {B // B ∈ X.powersetCard (X.card / 2 + 1)} ↦
        B.1.inf' (majorityMember_nonempty B.2)
          (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ))
      (show (⟨A, hAmem⟩ :
      {A // A ∈ X.powersetCard (X.card / 2 + 1)}) ∈
        (X.powersetCard (X.card / 2 + 1)).attach by simp)
  exact (not_lt_of_ge hle) hlt

private lemma card_filter_lt_upperMedian_le (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    (X.filter fun x ↦ ⟪u.1, x⟫_ℝ < upperMedian X hX u).card ≤ X.card / 2 := by
  by_contra hcard
  have hq : X.card / 2 + 1 ≤
      (X.filter fun x ↦ ⟪u.1, x⟫_ℝ < upperMedian X hX u).card := by omega
  obtain ⟨A, hAfilter, hAcard⟩ := Finset.exists_subset_card_eq hq
  have hAX : A ⊆ X := hAfilter.trans (Finset.filter_subset _ _)
  have hAmem : A ∈ X.powersetCard (X.card / 2 + 1) := by
    rw [Finset.mem_powersetCard]
    exact ⟨hAX, hAcard⟩
  have hlt : A.sup' (majorityMember_nonempty hAmem)
      (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) < upperMedian X hX u := by
    rw [Finset.sup'_lt_iff]
    intro x hx
    exact (Finset.mem_filter.mp (hAfilter hx)).2
  have hle : upperMedian X hX u ≤
      A.sup' (majorityMember_nonempty hAmem) (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ) := by
    unfold upperMedian
    exact Finset.inf'_le
      (fun B : {B // B ∈ X.powersetCard (X.card / 2 + 1)} ↦
        B.1.sup' (majorityMember_nonempty B.2)
          (fun x : Point 3 ↦ ⟪u.1, x⟫_ℝ))
      (show (⟨A, hAmem⟩ :
      {A // A ∈ X.powersetCard (X.card / 2 + 1)}) ∈
        (X.powersetCard (X.card / 2 + 1)).attach by simp)
  exact (not_lt_of_ge hle) hlt

private lemma card_filter_finiteMedian_lt_le (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    (X.filter fun x ↦ finiteMedian X u < ⟪u.1, x⟫_ℝ).card ≤ X.card / 2 := by
  refine (Finset.card_le_card ?_).trans (card_filter_lowerMedian_lt_le X hX u)
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, (lowerMedian_le_finiteMedian X hX u).trans_lt hx.2⟩

private lemma card_filter_lt_finiteMedian_le (X : Finset (Point 3))
    (hX : X.Nonempty) (u : SphereTwo) :
    (X.filter fun x ↦ ⟪u.1, x⟫_ℝ < finiteMedian X u).card ≤ X.card / 2 := by
  refine (Finset.card_le_card ?_).trans (card_filter_lt_upperMedian_le X hX u)
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans_le (finiteMedian_le_upperMedian X hX u)⟩

private def medianAffine (u : SphereTwo) (t : ℝ) : Point 3 →ᵃ[ℝ] ℝ :=
  (innerSL ℝ u.1).toLinearMap.toAffineMap - AffineMap.const ℝ (Point 3) t

@[simp] private lemma medianAffine_apply (u : SphereTwo) (t : ℝ) (x : Point 3) :
    medianAffine u t x = ⟪u.1, x⟫_ℝ - t := by
  simp [medianAffine]

private lemma medianAffine_linear_ne_zero (u : SphereTwo) :
    (medianAffine u t).linear ≠ 0 := by
  intro hzero
  have h := LinearMap.congr_fun hzero u.1
  have hunorm : ‖u.1‖ = 1 := by
    simpa [Metric.mem_sphere] using u.2
  simp [medianAffine, real_inner_self_eq_norm_sq, hunorm] at h

private lemma medianAffine_closedBisects (X : Finset (Point 3)) (u : SphereTwo) :
    ClosedBisects (medianAffine u (finiteMedian X u)) X := by
  classical
  by_cases hX : X.Nonempty
  · have hlt := card_filter_lt_finiteMedian_le X hX u
    have hgt := card_filter_finiteMedian_lt_le X hX u
    have hpospart := Finset.card_filter_add_card_filter_not
      (s := X) (fun x ↦ 0 ≤ medianAffine u (finiteMedian X u) x)
    have hnegpart := Finset.card_filter_add_card_filter_not
      (s := X) (fun x ↦ medianAffine u (finiteMedian X u) x ≤ 0)
    have hnotpos :
        (X.filter fun x ↦ ¬0 ≤ medianAffine u (finiteMedian X u) x).card ≤
          X.card / 2 := by
      simpa only [medianAffine_apply, not_le, sub_neg] using hlt
    have hnotneg :
        (X.filter fun x ↦ ¬medianAffine u (finiteMedian X u) x ≤ 0).card ≤
          X.card / 2 := by
      simpa only [medianAffine_apply, not_le, sub_pos] using hgt
    constructor <;> omega
  · have : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    subst X
    simp [ClosedBisects]

/-- The finite discrete ham-sandwich theorem for three finite point sets in
dimension three.  The proof uses continuous canonical medians of the three
families of one-dimensional projections and `borsukUlamSphereTwo`. -/
theorem threeSetDiscreteHamSandwich : ThreeSetDiscreteHamSandwich := by
  intro X₁ X₂ X₃
  let F : SphereTwo → Point 2 := fun u ↦
    WithLp.toLp 2 ![finiteMedian X₂ u - finiteMedian X₁ u,
      finiteMedian X₃ u - finiteMedian X₁ u]
  have hFcont : Continuous F := by
    have h₁c : Continuous (finiteMedian X₁) := continuous_finiteMedian X₁
    have h₂c : Continuous (finiteMedian X₂) := continuous_finiteMedian X₂
    have h₃c : Continuous (finiteMedian X₃) := continuous_finiteMedian X₃
    dsimp [F]
    fun_prop
  have hFodd (u : SphereTwo) : F (sphereTwoNeg u) = -F u := by
    ext i
    fin_cases i <;> simp [F, finiteMedian_neg] <;> ring
  obtain ⟨u, hu⟩ := borsukUlamSphereTwo F hFcont hFodd
  have h₂₁ : finiteMedian X₂ u = finiteMedian X₁ u := by
    have h := congr_arg (fun v : Point 2 ↦ v 0) hu
    have hz : finiteMedian X₂ u - finiteMedian X₁ u = 0 := by
      simpa [F] using h
    exact sub_eq_zero.mp hz
  have h₃₁ : finiteMedian X₃ u = finiteMedian X₁ u := by
    have h := congr_arg (fun v : Point 2 ↦ v 1) hu
    have hz : finiteMedian X₃ u - finiteMedian X₁ u = 0 := by
      simpa [F] using h
    exact sub_eq_zero.mp hz
  refine ⟨medianAffine u (finiteMedian X₁ u), medianAffine_linear_ne_zero u,
    medianAffine_closedBisects X₁ u, ?_, ?_⟩
  · simpa [h₂₁] using medianAffine_closedBisects X₂ u
  · simpa [h₃₁] using medianAffine_closedBisects X₃ u

/-- At least one of the two closed sides of any oriented affine hyperplane
contains half of a finite set. -/
lemma half_in_one_closed_side (φ : Point 3 →ᵃ[ℝ] ℝ) (X : Finset (Point 3)) :
    X.card ≤ 2 * (X.filter fun x ↦ 0 ≤ φ x).card ∨
      X.card ≤ 2 * (X.filter fun x ↦ φ x ≤ 0).card := by
  classical
  let P := X.filter fun x ↦ 0 ≤ φ x
  let N := X.filter fun x ↦ φ x ≤ 0
  have hsub : X ⊆ P ∪ N := by
    intro x hx
    rcases le_total 0 (φ x) with h | h
    · exact Finset.mem_union_left N (by simp [P, hx, h])
    · exact Finset.mem_union_right P (by simp [N, hx, h])
  have hcard : X.card ≤ P.card + N.card := by
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_union_le P N).trans_eq (by omega))
  change X.card ≤ 2 * P.card ∨ X.card ≤ 2 * N.card
  by_cases hP : X.card ≤ 2 * P.card
  · exact Or.inl hP
  · right
    omega

/-- Bisecting three colours and orienting the cut according to the fourth
gives the required `2`-versus-`2` closed-side selection. -/
theorem exists_closedOrientedHalfSelection_of_bisectsThree
    (X₁ X₂ X₃ X₄ : Finset (Point 3)) (φ : Point 3 →ᵃ[ℝ] ℝ)
    (h₁ : ClosedBisects φ X₁) (h₂ : ClosedBisects φ X₂)
    (h₃ : ClosedBisects φ X₃) (hφ : φ.linear ≠ 0) :
    ∃ S : ClosedOrientedHalfSelection X₁ X₂ X₃ X₄, True := by
  classical
  rcases half_in_one_closed_side φ X₄ with h₄ | h₄
  · refine ⟨
      { φ := -φ
        Y₁ := X₁.filter fun x ↦ φ x ≤ 0
        Y₂ := X₂.filter fun x ↦ φ x ≤ 0
        Y₃ := X₃.filter fun x ↦ 0 ≤ φ x
        Y₄ := X₄.filter fun x ↦ 0 ≤ φ x
        half₁ := ⟨Finset.filter_subset _ _, h₁.2⟩
        half₂ := ⟨Finset.filter_subset _ _, h₂.2⟩
        half₃ := ⟨Finset.filter_subset _ _, h₃.1⟩
        half₄ := ⟨Finset.filter_subset _ _, h₄⟩
        positive₁ := by simp [InClosedPositiveSide]
        positive₂ := by simp [InClosedPositiveSide]
        negative₃ := by simp [InClosedNegativeSide]
        negative₄ := by simp [InClosedNegativeSide]
        nonconstant := by simpa using hφ }, trivial⟩
  · refine ⟨
      { φ := φ
        Y₁ := X₁.filter fun x ↦ 0 ≤ φ x
        Y₂ := X₂.filter fun x ↦ 0 ≤ φ x
        Y₃ := X₃.filter fun x ↦ φ x ≤ 0
        Y₄ := X₄.filter fun x ↦ φ x ≤ 0
        half₁ := ⟨Finset.filter_subset _ _, h₁.1⟩
        half₂ := ⟨Finset.filter_subset _ _, h₂.1⟩
        half₃ := ⟨Finset.filter_subset _ _, h₃.2⟩
        half₄ := ⟨Finset.filter_subset _ _, h₄⟩
        positive₁ := by simp [InClosedPositiveSide]
        positive₂ := by simp [InClosedPositiveSide]
        negative₃ := by simp [InClosedNegativeSide]
        negative₄ := by simp [InClosedNegativeSide]
        nonconstant := hφ }, trivial⟩

noncomputable def closedOrientedHalfSelection_of_bisectsThree
    (X₁ X₂ X₃ X₄ : Finset (Point 3)) (φ : Point 3 →ᵃ[ℝ] ℝ)
    (h₁ : ClosedBisects φ X₁) (h₂ : ClosedBisects φ X₂)
    (h₃ : ClosedBisects φ X₃) (hφ : φ.linear ≠ 0) :
    ClosedOrientedHalfSelection X₁ X₂ X₃ X₄ :=
  (exists_closedOrientedHalfSelection_of_bisectsThree X₁ X₂ X₃ X₄ φ h₁ h₂ h₃ hφ).choose

/-- In a point set of cardinality at least four, the project's exact-card
general-position predicate also gives affine independence of every subset of
cardinality at most four.  The lower bound is necessary because
`InGeneralPosition` is intentionally phrased using exact four-subsets. -/
lemma affineIndependent_of_subset_of_card_le_four
    {U A : Finset (Point 3)} (hU : 4 ≤ U.card)
    (hgp : InGeneralPosition 3 U) (hAU : A ⊆ U) (hA : A.card ≤ 4) :
    AffineIndependent ℝ (fun x : A ↦ (x : Point 3)) := by
  classical
  obtain ⟨S, hAS, hSU, hScard⟩ :=
    Finset.exists_subsuperset_card_eq hAU hA hU
  have hSind : AffineIndependent ℝ (fun x : S ↦ (x : Point 3)) := by
    apply hgp S hSU
    omega
  let e : A ↪ S :=
    ⟨fun x ↦ ⟨x, hAS x.2⟩, fun x y h ↦ Subtype.ext
      (show (x : Point 3) = (y : Point 3) from
        congr_arg (fun z : S ↦ (z : Point 3)) h)⟩
  convert hSind.comp_embedding e using 1
  funext x
  rfl

/-- A nonconstant affine hyperplane contains at most three points of a
general-position set in `ℝ³`. -/
lemma card_filter_affineMap_eq_zero_le_three
    {U : Finset (Point 3)} {φ : Point 3 →ᵃ[ℝ] ℝ}
    (hgp : InGeneralPosition 3 U) (hφ : φ.linear ≠ 0) :
    (U.filter fun x ↦ φ x = 0).card ≤ 3 := by
  classical
  let B := U.filter fun x ↦ φ x = 0
  by_contra hB
  have hfour : 4 ≤ B.card := by
    dsimp [B]
    omega
  obtain ⟨S, hSB, hScard⟩ := Finset.exists_subset_card_eq hfour
  have hSind : AffineIndependent ℝ (fun x : S ↦ (x : Point 3)) := by
    apply hgp S (hSB.trans (Finset.filter_subset _ _))
    omega
  have hSspan : affineSpan ℝ (Set.range fun x : S ↦ (x : Point 3)) = ⊤ := by
    apply hSind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    simpa using hScard
  let b : AffineBasis S ℝ (Point 3) :=
    ⟨(fun x : S ↦ (x : Point 3)), hSind, hSspan⟩
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  let i : S := ⟨hSne.choose, hSne.choose_spec⟩
  have hzero (x : S) : φ (b x) = 0 := by
    exact (Finset.mem_filter.mp (hSB x.2)).2
  have hlin : φ.linear = 0 := by
    apply (b.basisOf i).ext
    intro j
    rw [b.basisOf_apply, φ.linearMap_vsub]
    simp [hzero]
  exact hφ hlin

lemma convex_strictPositiveSide (φ : Point 3 →ᵃ[ℝ] ℝ) :
    Convex ℝ (strictPositiveSide φ) := by
  exact (convex_Ioi (0 : ℝ)).affine_preimage φ

lemma convex_strictNegativeSide (φ : Point 3 →ᵃ[ℝ] ℝ) :
    Convex ℝ (strictNegativeSide φ) := by
  exact (convex_Iio (0 : ℝ)).affine_preimage φ

/-- Strict affine separation propagates from a finite set to its convex
hull. -/
lemma convexHull_subset_strictPositiveSide {φ : Point 3 →ᵃ[ℝ] ℝ}
    {P : Finset (Point 3)} (hP : ∀ x ∈ P, 0 < φ x) :
    convexHull ℝ (↑P : Set (Point 3)) ⊆ strictPositiveSide φ := by
  apply convexHull_min
  · intro x hx
    exact hP x (by simpa using hx)
  · exact convex_strictPositiveSide φ

lemma convexHull_subset_strictNegativeSide {φ : Point 3 →ᵃ[ℝ] ℝ}
    {N : Finset (Point 3)} (hN : ∀ x ∈ N, φ x < 0) :
    convexHull ℝ (↑N : Set (Point 3)) ⊆ strictNegativeSide φ := by
  apply convexHull_min
  · intro x hx
    exact hN x (by simpa using hx)
  · exact convex_strictNegativeSide φ

/-- The convex-hull wrapper used by the two-separation iteration. -/
theorem convexHulls_disjoint_of_strictlySeparates
    {φ : Point 3 →ᵃ[ℝ] ℝ} {P N : Finset (Point 3)}
    (h : StrictlySeparates φ P N) :
    Disjoint (convexHull ℝ (↑P : Set (Point 3)))
      (convexHull ℝ (↑N : Set (Point 3))) := by
  rw [Set.disjoint_left]
  intro x hxP hxN
  have hp : 0 < φ x := convexHull_subset_strictPositiveSide h.1 hxP
  have hn : φ x < 0 := convexHull_subset_strictNegativeSide h.2 hxN
  exact (not_lt_of_ge hp.le) hn

/-- All prescribed values on an affinely independent family extend to an
affine functional. -/
lemma AffineIndependent.exists_affineMap_apply_eq
    {ι : Type*} {p : ι → Point 3} (hp : AffineIndependent ℝ p)
    (w : ι → ℝ) :
    ∃ g : Point 3 →ᵃ[ℝ] ℝ, ∀ i, g (p i) = w i := by
  classical
  let s : Set (Point 3) := Set.range p
  let e : ι ≃ s := Equiv.ofInjective p hp.injective
  have hs : AffineIndependent ℝ (fun x : s ↦ (x : Point 3)) := by
    convert hp.comp_embedding e.symm.toEmbedding using 1
    funext x
    exact (congr_arg Subtype.val (e.apply_symm_apply x)).symm
  obtain ⟨t, hst, htind, htspan⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t ℝ (Point 3) :=
    ⟨(fun x : t ↦ (x : Point 3)), htind, by
      have hrange : Set.range (fun x : t ↦ (x : Point 3)) = t := by
        ext x
        simp
      rw [hrange]
      exact htspan⟩
  letI : Finite t := b.finite
  letI : Fintype t := Fintype.ofFinite t
  let value : t → ℝ := fun x ↦ if h : (x : Point 3) ∈ s then w (e.symm ⟨x, h⟩) else 0
  let g : Point 3 →ᵃ[ℝ] ℝ := ∑ j : t, value j • b.coord j
  refine ⟨g, ?_⟩
  intro i
  let j : t := ⟨p i, hst ⟨i, rfl⟩⟩
  have hj : b j = p i := rfl
  have hvalue : value j = w i := by
    simp [value, j, s, e]
  rw [← hj]
  dsimp [g]
  have happly (S : Finset t) :
      (∑ k ∈ S, value k • b.coord k) (b j) =
        ∑ k ∈ S, value k * b.coord k (b j) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih => simp [hk, ih]
  rw [happly Finset.univ]
  rw [Finset.sum_eq_single j]
  · simpa using hvalue
  · intro k _ hkj
    rw [b.coord_apply_ne hkj]
    simp
  · simp

/-- A positive perturbation which is already strict at parameter `t` stays
strict when the parameter is decreased, provided the unperturbed value is
nonnegative and zeros point in the positive perturbation direction. -/
private lemma perturb_pos_of_le
    {a b t u : ℝ} (ha : 0 ≤ a) (hz : a = 0 → 0 < b)
    (ht : 0 < t) (hu : 0 < u) (hut : u ≤ t) (h : 0 < a + t * b) :
    0 < a + u * b := by
  by_cases hb : 0 ≤ b
  · by_cases ha0 : a = 0
    · subst a
      simpa using mul_pos hu (hz rfl)
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne ha (Ne.symm ha0))
        (mul_nonneg hu.le hb)
  · have hb' : b < 0 := lt_of_not_ge hb
    have hm : t * b ≤ u * b := mul_le_mul_of_nonpos_right hut hb'.le
    linarith

/-- Simultaneously make finitely many weak positive inequalities strict by a
sufficiently small positive perturbation. -/
private lemma exists_small_strict_perturb
    {α : Type*} (S : Finset α) (a b : α → ℝ)
    (ha : ∀ x ∈ S, 0 ≤ a x)
    (hz : ∀ x ∈ S, a x = 0 → 0 < b x) :
    ∃ t : ℝ, 0 < t ∧ ∀ x ∈ S, 0 < a x + t * b x := by
  classical
  induction S using Finset.induction_on
  case empty => exact ⟨1, by norm_num, by simp⟩
  case insert y S hy ih =>
      have haS : ∀ z ∈ S, 0 ≤ a z := fun z hzmem ↦ ha z (Finset.mem_insert_of_mem hzmem)
      have hzS : ∀ z ∈ S, a z = 0 → 0 < b z :=
        fun z hzmem ↦ hz z (Finset.mem_insert_of_mem hzmem)
      obtain ⟨t, ht, hSt⟩ := ih haS hzS
      by_cases hb : 0 ≤ b y
      · refine ⟨t, ht, ?_⟩
        intro z hzmem
        rw [Finset.mem_insert] at hzmem
        rcases hzmem with hzy | hzmem
        · subst z
          by_cases hay0 : a y = 0
          · rw [hay0, zero_add]
            exact mul_pos ht (hz y (by simp) hay0)
          · exact add_pos_of_pos_of_nonneg
              (lt_of_le_of_ne (ha y (by simp)) (Ne.symm hay0)) (mul_nonneg ht.le hb)
        · exact hSt z hzmem
      · have hby : b y < 0 := lt_of_not_ge hb
        have hay : 0 < a y := by
          refine lt_of_le_of_ne (ha y (by simp)) ?_
          intro hzero
          have := hz y (by simp) hzero.symm
          linarith
        let d : ℝ := a y / (2 * (-b y))
        have hd : 0 < d := div_pos hay (mul_pos (by norm_num) (neg_pos.mpr hby))
        let u := min t d
        have hu : 0 < u := lt_min ht hd
        have hut : u ≤ t := min_le_left _ _
        have hud : u ≤ d := min_le_right _ _
        have hdcalc : d * b y = -(a y) / 2 := by
          dsimp [d]
          field_simp [hby.ne]
        have huy : 0 < a y + u * b y := by
          have hmul : d * b y ≤ u * b y :=
            mul_le_mul_of_nonpos_right hud hby.le
          rw [hdcalc] at hmul
          linarith
        refine ⟨u, hu, ?_⟩
        intro z hzmem
        rw [Finset.mem_insert] at hzmem
        rcases hzmem with hzy | hzmem
        · subst z
          exact huy
        · exact perturb_pos_of_le (haS z hzmem) (hzS z hzmem) ht hu hut (hSt z hzmem)

/-- Perturb an oriented affine hyperplane away from two finite sets.  The
boundary points may be prescribed independently as long as their union is
affinely independent. -/
theorem exists_strict_separator_of_weak_of_boundary_affineIndependent
    {φ : Point 3 →ᵃ[ℝ] ℝ} {P N : Finset (Point 3)}
    (hP : InClosedPositiveSide φ P) (hN : InClosedNegativeSide φ N)
    (hdisj : Disjoint P N)
    (hind : AffineIndependent ℝ
      (fun x : ↥((P.filter fun p ↦ φ p = 0) ∪
        (N.filter fun p ↦ φ p = 0)) ↦ (x : Point 3))) :
    ∃ ψ : Point 3 →ᵃ[ℝ] ℝ, StrictlySeparates ψ P N := by
  classical
  let Bp := P.filter fun p ↦ φ p = 0
  let Bn := N.filter fun p ↦ φ p = 0
  let B := Bp ∪ Bn
  let w : B → ℝ := fun x ↦ if (x : Point 3) ∈ Bp then 1 else -1
  obtain ⟨g, hg⟩ := AffineIndependent.exists_affineMap_apply_eq hind w
  have hgP : ∀ x ∈ P, φ x = 0 → 0 < g x := by
    intro x hx hx0
    have hxbp : x ∈ Bp := by simp [Bp, hx, hx0]
    have hxb : x ∈ B := Finset.mem_union_left Bn hxbp
    have := hg (⟨x, hxb⟩ : B)
    simp [w, hxbp] at this
    linarith
  have hgN : ∀ x ∈ N, φ x = 0 → g x < 0 := by
    intro x hx hx0
    have hxbn : x ∈ Bn := by simp [Bn, hx, hx0]
    have hxnot : x ∉ Bp := by
      intro hxbp
      exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hxbp).1 hx
    have hxb : x ∈ B := Finset.mem_union_right Bp hxbn
    have := hg (⟨x, hxb⟩ : B)
    simp [w, hxnot] at this
    linarith
  let S : Finset (Point 3 ⊕ Point 3) := P.disjSum N
  let a : Point 3 ⊕ Point 3 → ℝ := fun z ↦ Sum.elim φ (fun x ↦ -φ x) z
  let b : Point 3 ⊕ Point 3 → ℝ := fun z ↦ Sum.elim g (fun x ↦ -g x) z
  have ha : ∀ z ∈ S, 0 ≤ a z := by
    intro z hz
    rcases z with x | x
    · exact hP x (by simpa [S] using hz)
    · exact neg_nonneg.mpr (hN x (by simpa [S] using hz))
  have hz : ∀ z ∈ S, a z = 0 → 0 < b z := by
    intro z hzS hz0
    rcases z with x | x
    · exact hgP x (by simpa [S] using hzS) (by simpa [a] using hz0)
    · have hx0 : φ x = 0 := by simpa [a] using hz0
      exact neg_pos.mpr (hgN x (by simpa [S] using hzS) hx0)
  obtain ⟨t, ht, htS⟩ := exists_small_strict_perturb S a b ha hz
  let ψ : Point 3 →ᵃ[ℝ] ℝ := φ + t • g
  refine ⟨ψ, ?_, ?_⟩
  · intro x hx
    have := htS (Sum.inl x) (by simp [S, hx])
    simpa [ψ, a, b] using this
  · intro x hx
    have := htS (Sum.inr x) (by simp [S, hx])
    dsimp [a, b] at this
    change φ x + t * g x < 0
    linarith

/-- General position makes the closed oriented selection strict after an
arbitrarily small affine perturbation.  The explicit `4 ≤ U.card` hypothesis
is needed because `InGeneralPosition 3` only speaks about exact four-point
subsets and is vacuous on smaller ambient finsets. -/
theorem ClosedOrientedHalfSelection.exists_strictification
    {X₁ X₂ X₃ X₄ : Finset (Point 3)}
    (S : ClosedOrientedHalfSelection X₁ X₂ X₃ X₄)
    (hdisj : Disjoint (S.Y₁ ∪ S.Y₂) (S.Y₃ ∪ S.Y₄))
    (hcard : 4 ≤ (((X₁ ∪ X₂) ∪ X₃) ∪ X₄).card)
    (hgp : InGeneralPosition 3 (((X₁ ∪ X₂) ∪ X₃) ∪ X₄)) :
    Nonempty (OrientedHalfSelection X₁ X₂ X₃ X₄) := by
  classical
  let U := ((X₁ ∪ X₂) ∪ X₃) ∪ X₄
  let P := S.Y₁ ∪ S.Y₂
  let N := S.Y₃ ∪ S.Y₄
  let B := (P.filter fun p ↦ S.φ p = 0) ∪ (N.filter fun p ↦ S.φ p = 0)
  have hPU : P ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hx₁ := S.half₁.1 hx
      simp [U, hx₁]
    · have hx₂ := S.half₂.1 hx
      simp [U, hx₂]
  have hNU : N ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hx₃ := S.half₃.1 hx
      simp [U, hx₃]
    · have hx₄ := S.half₄.1 hx
      simp [U, hx₄]
  have hBU : B ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hPU (Finset.mem_filter.mp hx).1
    · exact hNU (Finset.mem_filter.mp hx).1
  have hBzero : B ⊆ U.filter fun x ↦ S.φ x = 0 := by
    intro x hx
    simp only [Finset.mem_filter]
    refine ⟨hBU hx, ?_⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hx).2
  have hBcard : B.card ≤ 4 := by
    have hz := card_filter_affineMap_eq_zero_le_three
      (U := U) (φ := S.φ) (show InGeneralPosition 3 U by simpa [U] using hgp) S.nonconstant
    have := Finset.card_le_card hBzero
    omega
  have hBind : AffineIndependent ℝ (fun x : B ↦ (x : Point 3)) := by
    apply affineIndependent_of_subset_of_card_le_four
      (U := U) (A := B) (by simpa [U] using hcard) (by simpa [U] using hgp) hBU hBcard
  obtain ⟨ψ, hψ⟩ :=
    exists_strict_separator_of_weak_of_boundary_affineIndependent
      (φ := S.φ) (P := P) (N := N) (by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact S.positive₁ x hx
        · exact S.positive₂ x hx) (by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact S.negative₃ x hx
        · exact S.negative₄ x hx) hdisj hBind
  refine ⟨
    { φ := ψ
      Y₁ := S.Y₁
      Y₂ := S.Y₂
      Y₃ := S.Y₃
      Y₄ := S.Y₄
      half₁ := S.half₁
      half₂ := S.half₂
      half₃ := S.half₃
      half₄ := S.half₄
      positive₁ := fun x hx ↦ hψ.1 x (Finset.mem_union_left _ hx)
      positive₂ := fun x hx ↦ hψ.1 x (Finset.mem_union_right _ hx)
      negative₃ := fun x hx ↦ hψ.2 x (Finset.mem_union_left _ hx)
      negative₄ := fun x hx ↦ hψ.2 x (Finset.mem_union_right _ hx) }⟩

/-- Ambient-set version of strictification.  It is the form needed during
iteration: the four current colour classes may have become small, but their
boundary points are still controlled by the original general-position set. -/
theorem ClosedOrientedHalfSelection.exists_strictification_in_ambient
    {U X₁ X₂ X₃ X₄ : Finset (Point 3)}
    (S : ClosedOrientedHalfSelection X₁ X₂ X₃ X₄)
    (hX₁ : X₁ ⊆ U) (hX₂ : X₂ ⊆ U) (hX₃ : X₃ ⊆ U) (hX₄ : X₄ ⊆ U)
    (hdisj : Disjoint (S.Y₁ ∪ S.Y₂) (S.Y₃ ∪ S.Y₄))
    (hcard : 4 ≤ U.card) (hgp : InGeneralPosition 3 U) :
    Nonempty (OrientedHalfSelection X₁ X₂ X₃ X₄) := by
  classical
  let P := S.Y₁ ∪ S.Y₂
  let N := S.Y₃ ∪ S.Y₄
  let B := (P.filter fun p ↦ S.φ p = 0) ∪ (N.filter fun p ↦ S.φ p = 0)
  have hPU : P ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hX₁ (S.half₁.1 hx)
    · exact hX₂ (S.half₂.1 hx)
  have hNU : N ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hX₃ (S.half₃.1 hx)
    · exact hX₄ (S.half₄.1 hx)
  have hBU : B ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hPU (Finset.mem_filter.mp hx).1
    · exact hNU (Finset.mem_filter.mp hx).1
  have hBzero : B ⊆ U.filter fun x ↦ S.φ x = 0 := by
    intro x hx
    simp only [Finset.mem_filter]
    refine ⟨hBU hx, ?_⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hx).2
  have hBcard : B.card ≤ 4 := by
    have hz := card_filter_affineMap_eq_zero_le_three hgp S.nonconstant
    have := Finset.card_le_card hBzero
    omega
  have hBind : AffineIndependent ℝ (fun x : B ↦ (x : Point 3)) := by
    exact affineIndependent_of_subset_of_card_le_four hcard hgp hBU hBcard
  obtain ⟨ψ, hψ⟩ :=
    exists_strict_separator_of_weak_of_boundary_affineIndependent
      (φ := S.φ) (P := P) (N := N) (by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact S.positive₁ x hx
        · exact S.positive₂ x hx) (by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact S.negative₃ x hx
        · exact S.negative₄ x hx) hdisj hBind
  refine ⟨
    { φ := ψ
      Y₁ := S.Y₁
      Y₂ := S.Y₂
      Y₃ := S.Y₃
      Y₄ := S.Y₄
      half₁ := S.half₁
      half₂ := S.half₂
      half₃ := S.half₃
      half₄ := S.half₄
      positive₁ := fun x hx ↦ hψ.1 x (Finset.mem_union_left _ hx)
      positive₂ := fun x hx ↦ hψ.1 x (Finset.mem_union_right _ hx)
      negative₃ := fun x hx ↦ hψ.2 x (Finset.mem_union_left _ hx)
      negative₄ := fun x hx ↦ hψ.2 x (Finset.mem_union_right _ hx) }⟩

/-- Complete source-exact reduction of the four-colour strict statement to
the standard three-set discrete ham-sandwich theorem. -/
theorem exists_orientedHalfSelection_of_threeSetDiscreteHamSandwich
    (hham : ThreeSetDiscreteHamSandwich)
    (X₁ X₂ X₃ X₄ : Finset (Point 3))
    (hdisj : Disjoint (X₁ ∪ X₂) (X₃ ∪ X₄))
    (hcard : 4 ≤ (((X₁ ∪ X₂) ∪ X₃) ∪ X₄).card)
    (hgp : InGeneralPosition 3 (((X₁ ∪ X₂) ∪ X₃) ∪ X₄)) :
    Nonempty (OrientedHalfSelection X₁ X₂ X₃ X₄) := by
  obtain ⟨φ, hφ, h₁, h₂, h₃⟩ := hham X₁ X₂ X₃
  let S := closedOrientedHalfSelection_of_bisectsThree X₁ X₂ X₃ X₄ φ h₁ h₂ h₃ hφ
  have hselDisj : Disjoint (S.Y₁ ∪ S.Y₂) (S.Y₃ ∪ S.Y₄) := by
    apply hdisj.mono
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (S.half₁.1 hx)
      · exact Finset.mem_union_right _ (S.half₂.1 hx)
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (S.half₃.1 hx)
      · exact Finset.mem_union_right _ (S.half₄.1 hx)
  exact S.exists_strictification hselDisj hcard hgp

/-- Iteration-friendly ambient wrapper for the unconditional theorem. -/
theorem exists_orientedHalfSelection_of_subset_ambient
    (U X₁ X₂ X₃ X₄ : Finset (Point 3))
    (hX₁ : X₁ ⊆ U) (hX₂ : X₂ ⊆ U) (hX₃ : X₃ ⊆ U) (hX₄ : X₄ ⊆ U)
    (hdisj : Disjoint (X₁ ∪ X₂) (X₃ ∪ X₄))
    (hcard : 4 ≤ U.card) (hgp : InGeneralPosition 3 U) :
    Nonempty (OrientedHalfSelection X₁ X₂ X₃ X₄) := by
  obtain ⟨φ, hφ, h₁, h₂, h₃⟩ := threeSetDiscreteHamSandwich X₁ X₂ X₃
  let S := closedOrientedHalfSelection_of_bisectsThree X₁ X₂ X₃ X₄ φ h₁ h₂ h₃ hφ
  have hselDisj : Disjoint (S.Y₁ ∪ S.Y₂) (S.Y₃ ∪ S.Y₄) := by
    apply hdisj.mono
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (S.half₁.1 hx)
      · exact Finset.mem_union_right _ (S.half₂.1 hx)
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (S.half₃.1 hx)
      · exact Finset.mem_union_right _ (S.half₄.1 hx)
  exact S.exists_strictification_in_ambient hX₁ hX₂ hX₃ hX₄ hselDisj hcard hgp

/-- A strict separator directly gives a half-selection by filtering its two
open sides. -/
noncomputable def orientedHalfSelection_of_strict_counts
    (X₁ X₂ X₃ X₄ : Finset (Point 3)) (φ : Point 3 →ᵃ[ℝ] ℝ)
    (h₁ : X₁.card ≤ 2 * (X₁.filter fun x ↦ 0 < φ x).card)
    (h₂ : X₂.card ≤ 2 * (X₂.filter fun x ↦ 0 < φ x).card)
    (h₃ : X₃.card ≤ 2 * (X₃.filter fun x ↦ φ x < 0).card)
    (h₄ : X₄.card ≤ 2 * (X₄.filter fun x ↦ φ x < 0).card) :
    OrientedHalfSelection X₁ X₂ X₃ X₄ where
  φ := φ
  Y₁ := X₁.filter fun x ↦ 0 < φ x
  Y₂ := X₂.filter fun x ↦ 0 < φ x
  Y₃ := X₃.filter fun x ↦ φ x < 0
  Y₄ := X₄.filter fun x ↦ φ x < 0
  half₁ := ⟨Finset.filter_subset _ _, h₁⟩
  half₂ := ⟨Finset.filter_subset _ _, h₂⟩
  half₃ := ⟨Finset.filter_subset _ _, h₃⟩
  half₄ := ⟨Finset.filter_subset _ _, h₄⟩
  positive₁ := by simp
  positive₂ := by simp
  negative₃ := by simp
  negative₄ := by simp

/-- The selected positive and negative unions have disjoint convex hulls. -/
theorem OrientedHalfSelection.convexHulls_disjoint
    {X₁ X₂ X₃ X₄ : Finset (Point 3)}
    (S : OrientedHalfSelection X₁ X₂ X₃ X₄) :
    Disjoint
      (convexHull ℝ (↑(S.Y₁ ∪ S.Y₂) : Set (Point 3)))
      (convexHull ℝ (↑(S.Y₃ ∪ S.Y₄) : Set (Point 3))) := by
  apply convexHulls_disjoint_of_strictlySeparates (φ := S.φ)
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact S.positive₁ x hx
    · exact S.positive₂ x hx
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact S.negative₃ x hx
    · exact S.negative₄ x hx

/-- The unconditional finite oriented four-colour ham-sandwich statement
used in the Pohoata--Zakharov iteration.  The lower bound on the ambient
cardinality is necessary for the project's exact-four-point formulation of
general position to control boundary points. -/
theorem exists_orientedHalfSelection
    (X₁ X₂ X₃ X₄ : Finset (Point 3))
    (hdisj : Disjoint (X₁ ∪ X₂) (X₃ ∪ X₄))
    (hcard : 4 ≤ (((X₁ ∪ X₂) ∪ X₃) ∪ X₄).card)
    (hgp : InGeneralPosition 3 (((X₁ ∪ X₂) ∪ X₃) ∪ X₄)) :
    Nonempty (OrientedHalfSelection X₁ X₂ X₃ X₄) :=
  exists_orientedHalfSelection_of_threeSetDiscreteHamSandwich
    threeSetDiscreteHamSandwich X₁ X₂ X₃ X₄ hdisj hcard hgp

/-- Existence wrapper which packages the half-cardinality conclusions and
the disjointness of the two selected convex hulls in one statement. -/
theorem exists_orientedHalfSelection_with_disjoint_convexHulls
    (X₁ X₂ X₃ X₄ : Finset (Point 3))
    (hdisj : Disjoint (X₁ ∪ X₂) (X₃ ∪ X₄))
    (hcard : 4 ≤ (((X₁ ∪ X₂) ∪ X₃) ∪ X₄).card)
    (hgp : InGeneralPosition 3 (((X₁ ∪ X₂) ∪ X₃) ∪ X₄)) :
    ∃ S : OrientedHalfSelection X₁ X₂ X₃ X₄,
      Disjoint
        (convexHull ℝ (↑(S.Y₁ ∪ S.Y₂) : Set (Point 3)))
        (convexHull ℝ (↑(S.Y₃ ∪ S.Y₄) : Set (Point 3))) := by
  let ⟨S⟩ := exists_orientedHalfSelection X₁ X₂ X₃ X₄ hdisj hcard hgp
  exact ⟨S, S.convexHulls_disjoint⟩

end

end Erdos651

#print axioms Erdos651.threeSetDiscreteHamSandwich
#print axioms Erdos651.exists_orientedHalfSelection
#print axioms Erdos651.exists_orientedHalfSelection_with_disjoint_convexHulls
