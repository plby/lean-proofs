/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.CupsCaps
import ErdosProblems.Erdos651.AboveBelow

/-!
# The planar positive-fraction configuration

This file records the exact robust-transversal output used in the
Pohoata--Zakharov argument.  A configuration consists of `k` disjoint cells
inside the original planar set; every cell contains the stated
`2^(-40*k)` fraction, and every transversal is in convex position.
-/

namespace Erdos651

open Set
open scoped BigOperators

noncomputable section

/-- The integral form of the density `|X_i| >= 2^(-40*k) |X|`.
It avoids any rounding convention: over the naturals this is exactly
`|X| <= 2^(40*k) * |X_i|`. -/
def HasPositiveFractionDensity (k : ℕ) (X A : Finset (Point 2)) : Prop :=
  X.card ≤ 2 ^ (40 * k) * A.card

def planarClusterUnion {k : ℕ} (cell : Fin k → Finset (Point 2))
    (I : Finset (Fin k)) : Finset (Point 2) :=
  I.biUnion cell

/-- Source-correct strong convex position: the hull of each whole cell is
disjoint from the hull of the union of all other whole cells. -/
def StrongConvexPositionPlanarCells {k : ℕ}
    (cell : Fin k → Finset (Point 2)) : Prop :=
  ∀ i,
    Disjoint
      (convexHull ℝ ((cell i : Finset (Point 2)) : Set (Point 2)))
      (convexHull ℝ
        ((planarClusterUnion cell (Finset.univ.erase i) :
          Finset (Point 2)) : Set (Point 2)))

/-- A robust convex `k`-clustering of a planar point set. -/
structure PositiveFractionConfiguration (k : ℕ) (X : Finset (Point 2)) where
  cell : Fin k → Finset (Point 2)
  cell_subset : ∀ i, cell i ⊆ X
  cell_disjoint : ∀ ⦃i j⦄, i ≠ j → Disjoint (cell i) (cell j)
  cell_dense : ∀ i, HasPositiveFractionDensity k X (cell i)
  transversal_convex : ∀ p : Fin k → Point 2,
    (∀ i, p i ∈ cell i) → InConvexPosition (Finset.univ.image p)

/-- The source-correct strengthened output retained for the three-dimensional
Pohoata--Zakharov assembly. -/
structure StrongPositiveFractionConfiguration (k : ℕ)
    (X : Finset (Point 2)) extends PositiveFractionConfiguration k X where
  strong_convex : StrongConvexPositionPlanarCells cell

lemma inConvexPosition_of_affineEquiv_image {X : Finset (Point 2)}
    (e : Point 2 ≃ᵃ[ℝ] Point 2) (h : InConvexPosition (X.image e)) :
    InConvexPosition X := by
  intro x hxX hxHull
  apply h (e x) (Finset.mem_image_of_mem e hxX)
  rw [← Finset.image_erase e.injective X x, Finset.coe_image,
    show (⇑e : Point 2 → Point 2) = e.toAffineMap from rfl]
  have hxImage : e.toAffineMap x ∈
      e.toAffineMap '' convexHull ℝ (↑(X.erase x) : Set (Point 2)) :=
    ⟨x, hxHull, rfl⟩
  rwa [e.toAffineMap.image_convexHull] at hxImage

/-- Positive-fraction configurations are invariant under affine changes of
coordinates. -/
def PositiveFractionConfiguration.comapAffineEquiv {k : ℕ}
    {X : Finset (Point 2)} (e : Point 2 ≃ᵃ[ℝ] Point 2)
    (C : PositiveFractionConfiguration k (X.image e)) :
    PositiveFractionConfiguration k X where
  cell i := (C.cell i).image e.symm
  cell_subset := by
    intro i z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hwX := C.cell_subset i hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hwX
    simpa only [e.symm_apply_apply] using hx
  cell_disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro z hzi hzj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzi
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hzj
    have hab' : a = b := e.symm.injective hab.symm
    exact Finset.disjoint_left.mp (C.cell_disjoint hij) ha (hab' ▸ hb)
  cell_dense := by
    intro i
    have heX : (X.image e).card = X.card :=
      Finset.card_image_iff.mpr e.injective.injOn
    have hecell : ((C.cell i).image e.symm).card = (C.cell i).card :=
      Finset.card_image_iff.mpr e.symm.injective.injOn
    simpa [HasPositiveFractionDensity, heX, hecell] using C.cell_dense i
  transversal_convex := by
    intro p hp
    let q : Fin k → Point 2 := fun i ↦ e (p i)
    have hq : ∀ i, q i ∈ C.cell i := by
      intro i
      have hpi := hp i
      obtain ⟨w, hw, hwp⟩ := Finset.mem_image.mp hpi
      simpa only [q, ← hwp, e.apply_symm_apply] using hw
    have hconv := C.transversal_convex q hq
    have himage : (Finset.univ.image p).image e = Finset.univ.image q := by
      ext z
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨p i, ⟨i, rfl⟩, rfl⟩
    apply inConvexPosition_of_affineEquiv_image e
    rwa [himage]

/-- An affinely independent finite family is in convex position. -/
lemma affineIndependent_inConvexPosition {d : ℕ} {Y : Finset (Point d)}
    (hY : AffineIndependent ℝ (fun y : ↥Y ↦ (y : Point d))) :
    InConvexPosition Y := by
  intro x hxY hx
  let i : ↥Y := ⟨x, hxY⟩
  have hnot := hY.notMem_affineSpan_sdiff i (Set.univ : Set ↥Y)
  apply hnot
  have hxspan : x ∈ affineSpan ℝ (↑(Y.erase x) : Set (Point d)) :=
    (convexHull_subset_affineSpan (𝕜 := ℝ)
      (↑(Y.erase x) : Set (Point d))) hx
  have himage :
      ((fun y : ↥Y ↦ (y : Point d)) '' (Set.univ \ {i})) =
        (↑(Y.erase x) : Set (Point d)) := by
    ext z
    simp only [Set.mem_image, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff,
      Finset.mem_coe, Finset.mem_erase]
    constructor
    · rintro ⟨y, ⟨_, hy⟩, rfl⟩
      exact ⟨fun h => hy (Subtype.ext h), y.property⟩
    · rintro ⟨hzx, hzY⟩
      refine ⟨⟨z, hzY⟩, ⟨trivial, ?_⟩, rfl⟩
      intro heq
      exact hzx (congrArg Subtype.val heq)
  rwa [himage]

/-- A convenient certificate for convex position: every point has a convex
strict half-space containing all the other points but not that point.  The
functions need not be linear; convexity of their positive sets is precisely
the property used by `convexHull_min`. -/
lemma inConvexPosition_of_strict_separators {d : ℕ}
    {Y : Finset (Point d)} (f : Point d → Point d → ℝ)
    (hconv : ∀ x ∈ Y, Convex ℝ {z | 0 < f x z})
    (hneg : ∀ x ∈ Y, f x x < 0)
    (hpos : ∀ x ∈ Y, ∀ z ∈ Y, z ≠ x → 0 < f x z) :
    InConvexPosition Y := by
  intro x hxY hxHull
  have hsubset : (↑(Y.erase x) : Set (Point d)) ⊆ {z | 0 < f x z} := by
    intro z hz
    have hz' := Finset.mem_erase.mp hz
    exact hpos x hxY z hz'.2 hz'.1
  have hxpos : x ∈ {z | 0 < f x z} :=
    convexHull_min hsubset (hconv x hxY) hxHull
  exact (not_lt_of_ge (le_of_lt (hneg x hxY))) hxpos

/-- Pairwise-disjoint cells separated by strict convex half-spaces give the
robust-transversal conclusion.  This is the final geometric step of the
Pór--Valtr support-region argument. -/
lemma transversal_convex_of_cell_separators {k : ℕ}
    (cell : Fin k → Finset (Point 2))
    (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (cell i) (cell j))
    (f : Fin k → Point 2 → ℝ)
    (hconv : ∀ i, Convex ℝ {z | 0 < f i z})
    (hneg : ∀ i, ∀ z ∈ cell i, f i z < 0)
    (hpos : ∀ i j, i ≠ j → ∀ z ∈ cell j, 0 < f i z)
    (p : Fin k → Point 2) (hp : ∀ i, p i ∈ cell i) :
    InConvexPosition (Finset.univ.image p) := by
  have hp_inj : Function.Injective p := by
    intro i j hij
    by_contra hne
    exact (Finset.disjoint_left.mp (hdisj hne)) (hp i) (by simpa [hij] using hp j)
  intro z hzY hzHull
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzY
  have hsubset :
      (↑((Finset.univ.image p).erase (p i)) : Set (Point 2)) ⊆
        {z | 0 < f i z} := by
    intro w hw
    have hw' := Finset.mem_erase.mp hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw'.2
    have hij : i ≠ j := fun h => hw'.1 (congrArg p h).symm
    exact hpos i j hij (p j) (hp j)
  have hipos : p i ∈ {z | 0 < f i z} :=
    convexHull_min hsubset (hconv i) hzHull
  exact (not_lt_of_ge (le_of_lt (hneg i (p i) (hp i)))) hipos

/-! ## Oriented support wedges -/

/-- The determinant of two vectors in the coordinate plane. -/
def det2 (u v : Point 2) : ℝ := u 0 * v 1 - u 1 * v 0

/-- Signed oriented distance, up to a positive scale, from the directed line
`ab`.  Pór--Valtr support wedges are intersections of strict sign conditions
for these functions. -/
def supportValue (σ : ℝ) (a b z : Point 2) : ℝ :=
  σ * det2 (b - a) (z - a)

/-- The open Pór--Valtr support cell at edge `i` of an oriented supporting
polygon. Its own edge sees the point on the negative side and every other
supporting edge sees it on the positive side. -/
def SupportCell {m : ℕ} (σ : ℝ)
    (edgeStart edgeEnd : Fin m → Point 2) (i : Fin m) :
    Set (Point 2) :=
  {z | supportValue σ (edgeStart i) (edgeEnd i) z < 0 ∧
    ∀ j : Fin m, j ≠ i →
      0 < supportValue σ (edgeStart j) (edgeEnd j) z}

/-- A generic linear coordinate used to put a finite planar set in
left-to-right order. -/
def genericCoordinate (t : ℝ) (p : Point 2) : ℝ := p 0 + t * p 1

/-- The shear realizing `genericCoordinate` as the first coordinate. -/
def genericShearLinearEquiv (t : ℝ) : Point 2 ≃ₗ[ℝ] Point 2 where
  toFun p := WithLp.toLp 2 ![p 0 + t * p 1, p 1]
  invFun p := WithLp.toLp 2 ![p 0 - t * p 1, p 1]
  left_inv p := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> ring
  right_inv p := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> ring
  map_add' p q := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> ring
  map_smul' c p := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> ring

def genericShear (t : ℝ) : Point 2 ≃ᵃ[ℝ] Point 2 :=
  (genericShearLinearEquiv t).toAffineEquiv

@[simp] lemma planeX_genericShear (t : ℝ) (p : Point 2) :
    planeX (genericShear t p) = genericCoordinate t p := by
  simp [genericShear, genericShearLinearEquiv, planeX, genericCoordinate]

@[simp] lemma planeY_genericShear (t : ℝ) (p : Point 2) :
    planeY (genericShear t p) = p 1 := by
  simp [genericShear, genericShearLinearEquiv, planeY]

/-! The two orientations used below are represented by a bit.  Keeping the
bit in the finite support-frame type is what gives exactly the factor `2` in
the incidence count. -/
def pvSigma (upper : Bool) : ℝ := if upper then 1 else -1

@[simp] lemma pvSigma_true : pvSigma true = 1 := rfl
@[simp] lemma pvSigma_false : pvSigma false = -1 := rfl

/-- Coordinate form of collinearity in the plane.  This is deliberately
stated for `Point 2`, so the strictness supplied by general position can be
fed directly into the support-value inequalities. -/
lemma collinear_iff_det2_eq_zero (a b c : Point 2) :
    Collinear ℝ ({a, b, c} : Set (Point 2)) ↔ det2 (b - a) (c - a) = 0 := by
  rw [collinear_iff_of_mem
    (show a ∈ ({a, b, c} : Set (Point 2)) by simp)]
  constructor
  · rintro ⟨v, hv⟩
    rcases hv b (by simp) with ⟨r₂, hr₂⟩
    rcases hv c (by simp) with ⟨r₃, hr₃⟩
    have hx₂ : b 0 - a 0 = r₂ * v 0 := by
      have h := congrArg (fun p : Point 2 => p 0) hr₂
      simp at h
      linarith
    have hy₂ : b 1 - a 1 = r₂ * v 1 := by
      have h := congrArg (fun p : Point 2 => p 1) hr₂
      simp at h
      linarith
    have hx₃ : c 0 - a 0 = r₃ * v 0 := by
      have h := congrArg (fun p : Point 2 => p 0) hr₃
      simp at h
      linarith
    have hy₃ : c 1 - a 1 = r₃ * v 1 := by
      have h := congrArg (fun p : Point 2 => p 1) hr₃
      simp at h
      linarith
    simp only [det2, PiLp.sub_apply]
    rw [hx₂, hy₂, hx₃, hy₃]
    ring
  · intro hdet
    by_cases hx : b 0 - a 0 = 0
    · by_cases hy : b 1 - a 1 = 0
      · refine ⟨c - a, ?_⟩
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with hpa | hpb | hpc
        · subst p
          refine ⟨0, by simp⟩
        · subst p
          refine ⟨0, ?_⟩
          apply PiLp.ext
          intro i
          fin_cases i
          · simpa using sub_eq_zero.mp hx
          · simpa using sub_eq_zero.mp hy
        · subst p
          refine ⟨1, by simp⟩
      · have hx₃ : c 0 - a 0 = 0 := by
          have hprod : (b 1 - a 1) * (c 0 - a 0) = 0 := by
            have hneg : -((b 1 - a 1) * (c 0 - a 0)) = 0 := by
              simpa [det2, hx] using hdet
            exact neg_eq_zero.mp hneg
          exact (mul_eq_zero.mp hprod).resolve_left hy
        refine ⟨b - a, ?_⟩
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with hpa | hpb | hpc
        · subst p
          refine ⟨0, by simp⟩
        · subst p
          refine ⟨1, by simp⟩
        · subst p
          refine ⟨(c 1 - a 1) / (b 1 - a 1), ?_⟩
          apply PiLp.ext
          intro i
          fin_cases i
          · simp [AffineMap.lineMap_apply, vsub_eq_sub, hx, hx₃]
            linarith
          · simp [AffineMap.lineMap_apply, vsub_eq_sub]
            field_simp [hy]
            linarith
    · refine ⟨b - a, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hpa | hpb | hpc
      · subst p
        refine ⟨0, by simp⟩
      · subst p
        refine ⟨1, by simp⟩
      · subst p
        refine ⟨(c 0 - a 0) / (b 0 - a 0), ?_⟩
        have hy₃ : c 1 - a 1 =
            ((c 0 - a 0) / (b 0 - a 0)) * (b 1 - a 1) := by
          simp only [det2, PiLp.sub_apply] at hdet
          field_simp [hx]
          nlinarith
        apply PiLp.ext
        intro i
        fin_cases i
        · simp [AffineMap.lineMap_apply, vsub_eq_sub]
          field_simp [hx]
          linarith
        · simp [AffineMap.lineMap_apply, vsub_eq_sub]
          linarith [hy₃]

/-- General position gives the strict determinant alternative for every
three distinct members. -/
lemma det2_ne_zero_of_generalPosition {X : Finset (Point 2)}
    (hgp : InGeneralPosition 2 X) {a b c : Point 2}
    (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    det2 (b - a) (c - a) ≠ 0 := by
  let p : Fin 3 → Point 2 := ![a, b, c]
  have hp_inj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p]
  let S : Finset (Point 2) := Finset.univ.image p
  have hSX : S ⊆ X := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i <;> simpa [p]
  have hScard : S.card = 2 + 1 := by
    dsimp [S]
    rw [Finset.card_image_iff.mpr hp_inj.injOn]
    simp
  have hAI := hgp S hSX hScard
  let e : Fin 3 ↪ S :=
    ⟨fun i => ⟨p i, Finset.mem_image_of_mem p (Finset.mem_univ i)⟩,
      fun i j hij => hp_inj (Subtype.ext_iff.mp hij)⟩
  have hcomp := hAI.comp_embedding e
  have hpAI : AffineIndependent ℝ p := by
    have heq : (fun i : Fin 3 ↦ ((e i : S) : Point 2)) = p := by
      rfl
    rw [← heq]
    exact hcomp
  have hncol : ¬ Collinear ℝ ({a, b, c} : Set (Point 2)) := by
    exact affineIndependent_iff_not_collinear_set.mp (by simpa [p] using hpAI)
  exact fun hzero => hncol ((collinear_iff_det2_eq_zero a b c).2 hzero)

/-- The orientation colouring of four points in increasing first-coordinate
order is transitive. -/
lemma supportValue_transitive (upper : Bool) {a b c d : Point 2}
    (hab : planeX a < planeX b) (hbc : planeX b < planeX c)
    (hcd : planeX c < planeX d)
    (habc : 0 < supportValue (pvSigma upper) a b c)
    (hbcd : 0 < supportValue (pvSigma upper) b c d) :
    0 < supportValue (pvSigma upper) a b d ∧
      0 < supportValue (pvSigma upper) a c d := by
  have hA : 0 < planeX b - planeX a := sub_pos.mpr hab
  have hB : 0 < planeX c - planeX b := sub_pos.mpr hbc
  have hC : 0 < planeX d - planeX c := sub_pos.mpr hcd
  have hid₁ :
      (planeX c - planeX b) * supportValue (pvSigma upper) a b d =
        ((planeX c - planeX b) + (planeX d - planeX c)) *
            supportValue (pvSigma upper) a b c +
          (planeX b - planeX a) * supportValue (pvSigma upper) b c d := by
    simp only [supportValue, det2, planeX, PiLp.sub_apply]
    ring
  have hid₂ :
      (planeX c - planeX b) * supportValue (pvSigma upper) a c d =
        (planeX d - planeX c) * supportValue (pvSigma upper) a b c +
          ((planeX b - planeX a) + (planeX c - planeX b)) *
            supportValue (pvSigma upper) b c d := by
    simp only [supportValue, det2, planeX, PiLp.sub_apply]
    ring
  constructor
  · apply pos_of_mul_pos_right _ hB.le
    rw [hid₁]
    exact add_pos (mul_pos (add_pos hB hC) habc) (mul_pos hA hbcd)
  · apply pos_of_mul_pos_right _ hB.le
    rw [hid₂]
    exact add_pos (mul_pos hC habc) (mul_pos (add_pos hA hB) hbcd)

lemma supportValue_genericShear (t σ : ℝ) (a b c : Point 2) :
    supportValue σ (genericShear t a) (genericShear t b) (genericShear t c) =
      supportValue σ a b c := by
  unfold supportValue
  apply congrArg (fun r : ℝ ↦ σ * r)
  simp [det2, genericShear, genericShearLinearEquiv]
  ring

lemma supportValue_transitive_generic (t : ℝ) (upper : Bool)
    {a b c d : Point 2}
    (hab : genericCoordinate t a < genericCoordinate t b)
    (hbc : genericCoordinate t b < genericCoordinate t c)
    (hcd : genericCoordinate t c < genericCoordinate t d)
    (habc : 0 < supportValue (pvSigma upper) a b c)
    (hbcd : 0 < supportValue (pvSigma upper) b c d) :
    0 < supportValue (pvSigma upper) a b d ∧
      0 < supportValue (pvSigma upper) a c d := by
  have h := supportValue_transitive upper
    (a := genericShear t a) (b := genericShear t b)
    (c := genericShear t c) (d := genericShear t d)
    (by simpa using hab) (by simpa using hbc) (by simpa using hcd)
    (by simpa only [supportValue_genericShear] using habc)
    (by simpa only [supportValue_genericShear] using hbcd)
  simpa only [supportValue_genericShear] using h

/-- For the transitive orientation colouring, a monochromatic tight path is
already monochromatic on all triples. -/
lemma adjacent_supportValue_all (t : ℝ) (upper : Bool) (q : ℕ → Point 2)
    (n : ℕ)
    (hx : ∀ i j, i < j → j < n →
      genericCoordinate t (q i) < genericCoordinate t (q j))
    (hadj : ∀ i, i + 2 < n →
      0 < supportValue (pvSigma upper) (q i) (q (i + 1)) (q (i + 2))) :
    ∀ i j l, i < j → j < l → l < n →
      0 < supportValue (pvSigma upper) (q i) (q j) (q l) := by
  intro i j l hij hjl hln
  induction l using Nat.strong_induction_on generalizing i j with
  | h l ih =>
      have hl2 : 2 ≤ l := by omega
      have hlast : ∀ a, a < l - 1 →
          0 < supportValue (pvSigma upper) (q a) (q (l - 1)) (q l) := by
        intro a halast
        by_cases ha : a + 1 = l - 1
        · have hal : a + 2 = l := by omega
          simpa [ha, hal] using hadj a (by omega)
        · have ha' : a < l - 2 := by omega
          have hm : l - 2 < l - 1 := by omega
          have hml : l - 1 < l := by omega
          have hold : 0 < supportValue (pvSigma upper)
              (q a) (q (l - 2)) (q (l - 1)) :=
            ih (l - 1) (by omega) a (l - 2) ha' hm (by omega)
          have hadj' : 0 < supportValue (pvSigma upper)
              (q (l - 2)) (q (l - 1)) (q l) := by
            have heq1 : l - 2 + 1 = l - 1 := by omega
            have heq2 : l - 2 + 2 = l := by omega
            simpa [heq1, heq2] using hadj (l - 2) (by omega)
          exact (supportValue_transitive_generic t upper
            (hx a (l - 2) ha' (by omega))
            (hx (l - 2) (l - 1) hm (by omega))
            (hx (l - 1) l hml hln) hold hadj').2
      by_cases hj : j = l - 1
      · subst j
        exact hlast i (by omega)
      · have hj' : j < l - 1 := by omega
        have hold : 0 < supportValue (pvSigma upper)
            (q i) (q j) (q (l - 1)) :=
          ih (l - 1) (by omega) i j hij hj' (by omega)
        exact (supportValue_transitive_generic t upper
          (hx i j hij (by omega))
          (hx j (l - 1) hj' (by omega))
          (hx (l - 1) l (by omega) hln) hold (hlast j hj')).1

lemma supportValue_swap_right (σ : ℝ) (a b c : Point 2) :
    supportValue σ a c b = -supportValue σ a b c := by
  unfold supportValue
  have h : det2 (c - a) (b - a) = -det2 (b - a) (c - a) := by
    simp only [det2, PiLp.sub_apply]
    ring
  rw [h]
  ring

lemma supportValue_swap_left (σ : ℝ) (a b c : Point 2) :
    supportValue σ b a c = -supportValue σ a b c := by
  unfold supportValue
  have h : det2 (a - b) (c - b) = -det2 (b - a) (c - a) := by
    simp only [det2, PiLp.sub_apply]
    ring
  rw [h]
  ring

lemma supportValue_rotate (σ : ℝ) (a b c : Point 2) :
    supportValue σ b c a = supportValue σ a b c := by
  unfold supportValue
  apply congrArg (fun r : ℝ ↦ σ * r)
  simp only [det2, PiLp.sub_apply]
  ring

lemma supportValue_rotate' (σ : ℝ) (a b c : Point 2) :
    supportValue σ c a b = supportValue σ a b c := by
  unfold supportValue
  apply congrArg (fun r : ℝ ↦ σ * r)
  simp only [det2, PiLp.sub_apply]
  ring

/-- A good `4*k`-set, with its canonical left-to-right cup/cap witness. -/
def PVGood (t : ℝ) (k : ℕ) (Q : Finset (Point 2)) : Prop :=
  ∃ upper : Bool, ∃ q : Fin (4 * k) → Point 2,
    Function.Injective q ∧ Finset.univ.image q = Q ∧
    StrictMono (genericCoordinate t ∘ q) ∧
    ∀ i j l : Fin (4 * k), i < j → j < l →
      0 < supportValue (pvSigma upper) (q i) (q j) (q l)

/-- The finite type over which support frames are averaged.  The bit is a
duplicate incidence label; the orientation itself is recovered from the
ordered anchor tuple.  Thus there are exactly `2 * |X|^(2*k)` possible
frames while each good cup/cap is incident to two of them. -/
abbrev PVFrame (k : ℕ) (X : Finset (Point 2)) :=
  Bool × (Fin (2 * k) → ↥X)

def cyclicSucc {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ hn⟩

def pvFrameSigma {k : ℕ} {X : Finset (Point 2)}
    (hk : 2 ≤ k) (F : PVFrame k X) : ℝ :=
  if 0 < det2
      ((F.2 ⟨1, by omega⟩ : Point 2) - (F.2 ⟨0, by omega⟩ : Point 2))
      ((F.2 ⟨2, by omega⟩ : Point 2) - (F.2 ⟨0, by omega⟩ : Point 2))
    then 1 else -1

def pvFrameStart {k : ℕ} {X : Finset (Point 2)}
    (F : PVFrame k X) (i : Fin (2 * k)) : Point 2 := F.2 i

def pvFrameEnd {k : ℕ} {X : Finset (Point 2)}
    (hk : 0 < k) (F : PVFrame k X) (i : Fin (2 * k)) : Point 2 :=
  F.2 (cyclicSucc (by omega : 0 < 2 * k) i)

def pvFrameCell {k : ℕ} {X : Finset (Point 2)}
    (hk : 2 ≤ k) (F : PVFrame k X) (i : Fin (2 * k)) :
    Finset (Point 2) := by
  classical
  exact X.filter fun z => z ∈ SupportCell (pvFrameSigma hk F)
    (pvFrameStart F) (pvFrameEnd (by omega : 0 < k) F) i

/-- The data witnessing that a good cup/cap is incident to a support frame.
Keeping the actual ordered `4*k`-chain makes both the fiber injection and the
later interlaced-chord certificate lossless. -/
structure PVSupportData (t : ℝ) {k : ℕ} {X : Finset (Point 2)} (hk : 2 ≤ k)
    (Q : Finset (Point 2)) (F : PVFrame k X) where
  upper : Bool
  q : Fin (4 * k) → Point 2
  q_injective : Function.Injective q
  q_image : Finset.univ.image q = Q
  q_strictMono : StrictMono (genericCoordinate t ∘ q)
  q_orient : ∀ i j l : Fin (4 * k), i < j → j < l →
    0 < supportValue (pvSigma upper) (q i) (q j) (q l)
  frame_sigma : pvFrameSigma hk F = pvSigma upper
  anchor_even : ∀ i : Fin (2 * k),
    (F.2 i : Point 2) = q ⟨2 * i, by omega⟩
  odd_mem_cell : ∀ i : Fin (2 * k),
    q ⟨2 * i + 1, by omega⟩ ∈ pvFrameCell hk F i

def PVSupports (t : ℝ) {k : ℕ} {X : Finset (Point 2)} (hk : 2 ≤ k)
    (Q : Finset (Point 2)) (F : PVFrame k X) : Prop :=
  Nonempty (PVSupportData t hk Q F)

/-- The even vertices of an oriented `4*k`-chain support all the odd
vertices in the corresponding `2*k` open cells. -/
lemma alternating_support_cells {t : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (upper : Bool) (q : Fin (4 * k) → Point 2)
    (hx : StrictMono (genericCoordinate t ∘ q))
    (horient : ∀ i j l : Fin (4 * k), i < j → j < l →
      0 < supportValue (pvSigma upper) (q i) (q j) (q l)) :
    let a : Fin (2 * k) → Point 2 := fun i => q ⟨2 * i, by omega⟩
    let v : Fin (2 * k) → Point 2 := fun i => q ⟨2 * i + 1, by omega⟩
    ∀ i, v i ∈ SupportCell (pvSigma upper) a
      (fun j => a (cyclicSucc (by omega : 0 < 2 * k) j)) i := by
  dsimp only
  intro i
  let evenIdx : Fin (2 * k) → Fin (4 * k) := fun r ↦
    ⟨2 * (r : ℕ), by have := r.isLt; omega⟩
  let oddIdx : Fin (2 * k) → Fin (4 * k) := fun r ↦
    ⟨2 * (r : ℕ) + 1, by have := r.isLt; omega⟩
  let nextIdx : Fin (2 * k) → Fin (4 * k) := fun r ↦
    evenIdx (cyclicSucc (by omega : 0 < 2 * k) r)
  change supportValue (pvSigma upper) (q (evenIdx i)) (q (nextIdx i))
      (q (oddIdx i)) < 0 ∧
    ∀ j, j ≠ i →
      0 < supportValue (pvSigma upper) (q (evenIdx j)) (q (nextIdx j))
        (q (oddIdx i))
  constructor
  · by_cases hi : (i : ℕ) + 1 < 2 * k
    · let ip : Fin (2 * k) := ⟨(i : ℕ) + 1, hi⟩
      have hsucc : cyclicSucc (by omega : 0 < 2 * k) i = ip := by
        apply Fin.ext
        simp [cyclicSucc, ip, Nat.mod_eq_of_lt hi]
      have hnext : nextIdx i = evenIdx ip := by
        dsimp [nextIdx]
        rw [hsucc]
      have h := horient (evenIdx i) (oddIdx i) (evenIdx ip)
        (Fin.mk_lt_mk.mpr (by simp [evenIdx, oddIdx]))
        (Fin.mk_lt_mk.mpr (by simp [evenIdx, oddIdx, ip]; omega))
      rw [hnext, supportValue_swap_right]
      exact neg_lt_zero.mpr h
    · have hlast : (i : ℕ) = 2 * k - 1 := by omega
      let iz : Fin (2 * k) := ⟨0, by omega⟩
      have hsucc : cyclicSucc (by omega : 0 < 2 * k) i = iz := by
        apply Fin.ext
        have heq : 2 * k - 1 + 1 = 2 * k := by omega
        simp [cyclicSucc, iz, hlast, heq]
      have hnext : nextIdx i = evenIdx iz := by
        dsimp [nextIdx]
        rw [hsucc]
      have h := horient (evenIdx iz) (evenIdx i) (oddIdx i)
        (Fin.mk_lt_mk.mpr (by simp [evenIdx, iz]; omega))
        (Fin.mk_lt_mk.mpr (by simp [evenIdx, oddIdx]))
      rw [hnext, supportValue_swap_left]
      exact neg_lt_zero.mpr h
  · intro j hji
    by_cases hj : (j : ℕ) + 1 < 2 * k
    · let jp : Fin (2 * k) := ⟨(j : ℕ) + 1, hj⟩
      have hsucc : cyclicSucc (by omega : 0 < 2 * k) j = jp := by
        apply Fin.ext
        simp [cyclicSucc, jp, Nat.mod_eq_of_lt hj]
      have hnext : nextIdx j = evenIdx jp := by
        dsimp [nextIdx]
        rw [hsucc]
      rw [hnext]
      rcases lt_or_gt_of_ne hji with hij | hij
      · exact horient (evenIdx j) (evenIdx jp) (oddIdx i)
          (Fin.mk_lt_mk.mpr (by simp [evenIdx, jp]))
          (Fin.mk_lt_mk.mpr (by simp [evenIdx, oddIdx, jp]; omega))
      · have h := horient (oddIdx i) (evenIdx j) (evenIdx jp)
          (Fin.mk_lt_mk.mpr (by
            change 2 * (i : ℕ) + 1 < 2 * (j : ℕ)
            omega))
          (Fin.mk_lt_mk.mpr (by simp [evenIdx, jp]))
        rw [supportValue_rotate]
        exact h
    · have hjlast : (j : ℕ) = 2 * k - 1 := by omega
      let iz : Fin (2 * k) := ⟨0, by omega⟩
      have hsucc : cyclicSucc (by omega : 0 < 2 * k) j = iz := by
        apply Fin.ext
        have heq : 2 * k - 1 + 1 = 2 * k := by omega
        simp [cyclicSucc, iz, hjlast, heq]
      have hnext : nextIdx j = evenIdx iz := by
        dsimp [nextIdx]
        rw [hsucc]
      rw [hnext]
      have hi : (i : ℕ) < 2 * k - 1 := by omega
      have h := horient (evenIdx iz) (oddIdx i) (evenIdx j)
        (Fin.mk_lt_mk.mpr (by simp [evenIdx, oddIdx, iz]))
        (Fin.mk_lt_mk.mpr (by
          change 2 * (i : ℕ) + 1 < 2 * (j : ℕ)
          omega))
      rw [supportValue_rotate']
      exact h

lemma pvFrameSigma_alternating {t : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (upper : Bool) (q : Fin (4 * k) → Point 2)
    (horient : ∀ i j l : Fin (4 * k), i < j → j < l →
      0 < supportValue (pvSigma upper) (q i) (q j) (q l))
    {X : Finset (Point 2)}
    (hqX : ∀ i, q i ∈ X) (tag : Bool) :
    pvFrameSigma hk
      (tag, fun i : Fin (2 * k) =>
        (⟨q ⟨2 * i, by omega⟩, hqX _⟩ : ↥X)) = pvSigma upper := by
  let i₀ : Fin (4 * k) := ⟨0, by omega⟩
  let i₁ : Fin (4 * k) := ⟨2, by omega⟩
  let i₂ : Fin (4 * k) := ⟨4, by omega⟩
  have h := horient i₀ i₁ i₂
    (by simp [i₀, i₁]) (by simp [i₁, i₂])
  cases upper
  · have hdet : det2 (q ⟨2, by omega⟩ - q ⟨0, by omega⟩)
        (q ⟨4, by omega⟩ - q ⟨0, by omega⟩) < 0 := by
      simpa [supportValue, pvSigma] using h
    have hnpos : ¬ 0 < det2 (q ⟨2, by omega⟩ - q ⟨0, by omega⟩)
        (q ⟨4, by omega⟩ - q ⟨0, by omega⟩) := by
      exact not_lt.mpr (le_of_lt hdet)
    simp [pvFrameSigma, pvSigma, hnpos]
  · have hpos : 0 < det2 (q ⟨2, by omega⟩ - q ⟨0, by omega⟩)
        (q ⟨4, by omega⟩ - q ⟨0, by omega⟩) := by
      simpa [supportValue, pvSigma] using h
    simp [pvFrameSigma, pvSigma, hpos]

lemma image_even_union_image_odd {k : ℕ} (hk : 1 ≤ k)
    (q : Fin (4 * k) → Point 2) :
    (Finset.univ.image fun i : Fin (2 * k) => q ⟨2 * i, by omega⟩) ∪
        (Finset.univ.image fun i : Fin (2 * k) => q ⟨2 * i + 1, by omega⟩) =
      Finset.univ.image q := by
  ext z
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨⟨2 * i, by omega⟩, rfl⟩
    · exact ⟨⟨2 * i + 1, by omega⟩, rfl⟩
  · rintro ⟨r, rfl⟩
    rcases Nat.mod_two_eq_zero_or_one (r : ℕ) with heven | hodd
    · left
      let i : Fin (2 * k) := ⟨(r : ℕ) / 2, by omega⟩
      refine ⟨i, ?_⟩
      congr 1
      apply Fin.ext
      dsimp [i]
      omega
    · right
      let i : Fin (2 * k) := ⟨(r : ℕ) / 2, by omega⟩
      refine ⟨i, ?_⟩
      congr 1
      apply Fin.ext
      dsimp [i]
      omega

/-- Every good cup/cap is incident to both duplicate labels of its even
support frame. -/
lemma pvGood_supports_two_frames {t : ℝ} {k : ℕ} (hk : 2 ≤ k)
    {X Q : Finset (Point 2)} (hQX : Q ⊆ X) (hgood : PVGood t k Q) :
    ∃ A : Fin (2 * k) → ↥X,
      PVSupports t hk Q (false, A) ∧ PVSupports t hk Q (true, A) := by
  classical
  obtain ⟨upper, q, hqinj, hqQ, hx, horient⟩ := hgood
  have hqX : ∀ i, q i ∈ X := by
    intro i
    apply hQX
    rw [← hqQ]
    exact Finset.mem_image_of_mem q (Finset.mem_univ i)
  let A : Fin (2 * k) → ↥X := fun i => ⟨q ⟨2 * i, by omega⟩, hqX _⟩
  let v : Fin (2 * k) → Point 2 := fun i => q ⟨2 * i + 1, by omega⟩
  have hcells (tag : Bool) : ∀ i, v i ∈ pvFrameCell hk (tag, A) i := by
    intro i
    rw [pvFrameCell, Finset.mem_filter]
    constructor
    · exact hqX _
    · rw [pvFrameSigma_alternating (t := t) hk upper q horient hqX tag]
      change q ⟨2 * (i : ℕ) + 1, by omega⟩ ∈
        SupportCell (pvSigma upper)
          (fun j : Fin (2 * k) => q ⟨2 * (j : ℕ), by omega⟩)
          (fun j : Fin (2 * k) =>
            q ⟨2 * ((cyclicSucc (by omega : 0 < 2 * k) j) : ℕ), by
              have hj := (cyclicSucc (by omega : 0 < 2 * k) j).isLt
              omega⟩) i
      exact alternating_support_cells (show 1 ≤ k by omega) upper q hx horient i
  refine ⟨A, ?_, ?_⟩
  all_goals
    refine ⟨{
      upper := upper
      q := q
      q_injective := hqinj
      q_image := hqQ
      q_strictMono := hx
      q_orient := horient
      frame_sigma := pvFrameSigma_alternating (t := t) hk upper q horient hqX _
      anchor_even := by intro i; rfl
      odd_mem_cell := hcells _ }⟩

lemma ordered_pairwise_lt {I : List ℕ} (hI : Ordered I) : I.Pairwise (· < ·) := by
  induction I with
  | nil => simp
  | cons x tail ih =>
      cases tail with
      | nil => simp
      | cons y tail =>
          exact List.Pairwise.cons_cons_of_trans hI.1 (ih hI.2)

lemma tightPath_get_consecutive {χ : ℕ → ℕ → ℕ → Bool} {c : Bool}
    {I : List ℕ} (hI : TightPath χ c I) (i : ℕ) (hi : i + 2 < I.length) :
    χ I[i] I[i + 1] I[i + 2] = c := by
  induction i generalizing I with
  | zero =>
      cases I with
      | nil => simp at hi
      | cons x tail =>
          cases tail with
          | nil => simp at hi
          | cons y tail =>
              cases tail with
              | nil => simp at hi
              | cons z tail => simpa [TightPath] using hI.1
  | succ i ih =>
      cases I with
      | nil => simp at hi
      | cons x tail =>
          cases tail with
          | nil => simp at hi
          | cons y tail =>
              cases tail with
              | nil => simp at hi
              | cons z tail =>
                  have hi' : i + 2 < (y :: z :: tail).length := by
                    simp only [List.length_cons] at hi ⊢
                    omega
                  have hh := ih hI.2 hi'
                  simpa using hh

/-- The local cups--caps witness inside every `2^(8*k)`-set. -/
lemma exists_pvGood_subset {t : ℝ} {k : ℕ} (hk : 2 ≤ k)
    {X Z : Finset (Point 2)}
    (ht : Set.InjOn (genericCoordinate t) X)
    (hgp : InGeneralPosition 2 X) (hZX : Z ⊆ X)
    (hZcard : Z.card = 2 ^ (8 * k)) :
    ∃ Q ∈ X.powersetCard (4 * k), PVGood t k Q ∧ Q ⊆ Z := by
  classical
  have htZ : Set.InjOn (genericCoordinate t) Z := ht.mono hZX
  letI : LinearOrder ↥Z := LinearOrder.lift'
    (fun z : ↥Z => genericCoordinate t z) (by
      intro a b hab
      exact Subtype.ext (htZ a.property b.property hab))
  let e : Fin (2 ^ (8 * k)) ≃o ↥Z :=
    Fintype.orderIsoFinOfCardEq ↥Z (by simpa using hZcard)
  let p : ℕ → Point 2 := fun i =>
    if hi : i < 2 ^ (8 * k) then (e ⟨i, hi⟩ : Point 2) else 0
  have hp_mem : ∀ i ∈ Finset.range (2 ^ (8 * k)), p i ∈ Z := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [p, hi', e]
  have hp_strict : ∀ i j, i ∈ Finset.range (2 ^ (8 * k)) →
      j ∈ Finset.range (2 ^ (8 * k)) → i < j →
      genericCoordinate t (p i) < genericCoordinate t (p j) := by
    intro i j hi hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have he := e.strictMono (show (⟨i, hi'⟩ : Fin _) < ⟨j, hj'⟩ by exact hij)
    change genericCoordinate t (e ⟨i, hi'⟩ : Point 2) <
      genericCoordinate t (e ⟨j, hj'⟩ : Point 2) at he
    simpa [p, hi', hj'] using he
  let χ : ℕ → ℕ → ℕ → Bool := fun i j l =>
    decide (0 < supportValue 1 (p i) (p j) (p l))
  have hchoose : Nat.choose (4 * k + 4 * k - 4) (4 * k - 2) <
      (Finset.range (2 ^ (8 * k))).card := by
    have hle : Nat.choose (4 * k + 4 * k - 4) (4 * k - 2) ≤
        2 ^ (4 * k + 4 * k - 4) := Nat.choose_le_two_pow _ _
    simp only [Finset.card_range]
    exact hle.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  rcases ordered_cups_caps χ (Finset.range (2 ^ (8 * k)))
      (4 * k) (4 * k) (by omega) (by omega) hchoose with hred | hblue
  all_goals
    obtain ⟨I, hordered, hIrange, hIlen, hpath⟩ := ‹HasTightPath χ _ _ _›
    let idx : Fin (4 * k) → Fin I.length := fun i =>
      ⟨i, by simpa [hIlen] using i.isLt⟩
    let q : Fin (4 * k) → Point 2 := fun i => p (I.get (idx i))
    have hIpair := ordered_pairwise_lt hordered
    have hqx : StrictMono (genericCoordinate t ∘ q) := by
      intro i j hij
      apply hp_strict
      · exact hIrange _ (List.get_mem _ _)
      · exact hIrange _ (List.get_mem _ _)
      · exact hIpair.rel_get_of_lt (show idx i < idx j by simpa [idx] using hij)
    have hqinj : Function.Injective q := by
      intro i j hij
      apply hqx.injective
      exact congrArg (genericCoordinate t) hij
    let qNat : ℕ → Point 2 := fun r =>
      if hr : r < I.length then p (I.get ⟨r, hr⟩) else 0
    have qNat_eq (r : ℕ) (hr : r < 4 * k) :
        qNat r = q ⟨r, hr⟩ := by
      have hrI : r < I.length := by simpa [hIlen] using hr
      simp [qNat, q, idx, hrI]
    let Q := Finset.univ.image q
    have hQcard : Q.card = 4 * k := by
      dsimp [Q]
      rw [Finset.card_image_iff.mpr hqinj.injOn]
      simp
    have hQZ : Q ⊆ Z := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact hp_mem _ (hIrange _ (List.get_mem _ _))
    have hQX : Q ⊆ X := hQZ.trans hZX
    refine ⟨Q, Finset.mem_powersetCard.mpr ⟨hQX, hQcard⟩, ?_, hQZ⟩
  · refine ⟨true, q, hqinj, rfl, hqx, ?_⟩
    intro i j l hij hjl
    have hall := adjacent_supportValue_all t true
      qNat (4 * k)
      (by
        intro a b hab hbn
        rw [qNat_eq a (by omega), qNat_eq b hbn]
        exact hqx (show (⟨a, by omega⟩ : Fin (4 * k)) < ⟨b, hbn⟩ by exact hab))
      (by
        intro a ha
        have htight := tightPath_get_consecutive hpath a (by simpa [hIlen] using ha)
        rw [qNat_eq a (by omega), qNat_eq (a + 1) (by omega),
          qNat_eq (a + 2) ha]
        simpa [χ, q, idx] using of_decide_eq_true htight)
      i j l hij hjl l.isLt
    simpa only [qNat_eq i i.isLt, qNat_eq j j.isLt, qNat_eq l l.isLt] using hall
  · refine ⟨false, q, hqinj, rfl, hqx, ?_⟩
    have hadjneg : ∀ a, a + 2 < 4 * k →
        0 < supportValue (pvSigma false)
          (qNat a) (qNat (a + 1)) (qNat (a + 2)) := by
      intro a ha
      have htight := tightPath_get_consecutive hpath a (by simpa [hIlen] using ha)
      have haI : a < I.length := by omega
      have ha1I : a + 1 < I.length := by omega
      have ha2I : a + 2 < I.length := by omega
      have hnpos : ¬ 0 < supportValue 1
          (qNat a) (qNat (a + 1)) (qNat (a + 2)) := by
        simpa [χ, qNat, haI, ha1I, ha2I] using of_decide_eq_false htight
      let ia : Fin (4 * k) := ⟨a, by omega⟩
      let ib : Fin (4 * k) := ⟨a + 1, by omega⟩
      let ic : Fin (4 * k) := ⟨a + 2, ha⟩
      have hne : det2
          (q ib - q ia) (q ic - q ia) ≠ 0 := by
        apply det2_ne_zero_of_generalPosition hgp
        · exact hZX (hp_mem _ (hIrange _ (List.get_mem _ _)))
        · exact hZX (hp_mem _ (hIrange _ (List.get_mem _ _)))
        · exact hZX (hp_mem _ (hIrange _ (List.get_mem _ _)))
        · intro heq
          exact (ne_of_lt (hqx (by simp [ia, ib])))
            (congrArg (genericCoordinate t) heq)
        · intro heq
          exact (ne_of_lt (hqx (by simp [ia, ic])))
            (congrArg (genericCoordinate t) heq)
        · intro heq
          exact (ne_of_lt (hqx (by simp [ib, ic])))
            (congrArg (genericCoordinate t) heq)
      have hne' : det2
          (qNat (a + 1) - qNat a) (qNat (a + 2) - qNat a) ≠ 0 := by
        simpa only [qNat_eq a (by omega), qNat_eq (a + 1) (by omega),
          qNat_eq (a + 2) ha, ia, ib, ic] using hne
      simp only [supportValue, pvSigma_false, neg_mul, one_mul]
      simp only [supportValue, one_mul] at hnpos
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hnpos) hne')
    intro i j l hij hjl
    have hall := adjacent_supportValue_all t false
      qNat (4 * k)
      (by
        intro a b hab hbn
        rw [qNat_eq a (by omega), qNat_eq b hbn]
        exact hqx (show (⟨a, by omega⟩ : Fin (4 * k)) < ⟨b, hbn⟩ by exact hab))
      hadjneg i j l hij hjl l.isLt
    simpa only [qNat_eq i i.isLt, qNat_eq j j.isLt, qNat_eq l l.isLt] using hall
/-- Every finite planar set admits a linear coordinate taking distinct
values on distinct points.  This is the formal version of the harmless
generic rotation at the start of the cups--caps argument. -/
lemma exists_genericCoordinate_injOn (X : Finset (Point 2)) :
    ∃ t : ℝ, Set.InjOn (genericCoordinate t) X := by
  classical
  let pairs : Finset (Point 2 × Point 2) :=
    (X.product X).filter (fun pq ↦ pq.1 ≠ pq.2 ∧ pq.1 1 ≠ pq.2 1)
  let bad : Finset ℝ := pairs.image
    (fun pq ↦ -(pq.1 0 - pq.2 0) / (pq.1 1 - pq.2 1))
  let B : ℝ := ∑ u ∈ bad, |u|
  let t : ℝ := B + 1
  have ht : t ∉ bad := by
    intro htbad
    have habs : |t| ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum
        (s := bad) (f := fun u : ℝ ↦ |u|) (fun _ _ ↦ abs_nonneg _) htbad
    have ht_le : t ≤ B := (le_abs_self t).trans habs
    dsimp [t] at ht_le
    linarith
  refine ⟨t, ?_⟩
  intro p hp q hq heq
  by_cases hy : p 1 = q 1
  · have hx : p 0 = q 0 := by
      dsimp [genericCoordinate] at heq
      rw [hy] at heq
      linarith
    apply PiLp.ext
    intro i
    fin_cases i
    · exact hx
    · exact hy
  · have hpq : p ≠ q := by
      intro h
      exact hy (congrArg (fun z : Point 2 ↦ z 1) h)
    have hpairs : (p, q) ∈ pairs := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq, hy⟩
    have htbad : t ∈ bad := by
      rw [Finset.mem_image]
      exact ⟨(p, q), hpairs, by
        dsimp [genericCoordinate] at heq
        field_simp
        nlinarith⟩
    exact (ht htbad).elim

/-- The positive side of an oriented line is convex. -/
lemma supportValue_positive_convex (σ : ℝ) (a b : Point 2) :
    Convex ℝ {z | 0 < supportValue σ a b z} := by
  let L : Point 2 →ₗ[ℝ] ℝ :=
    { toFun := fun z => σ * det2 (b - a) z
      map_add' := by
        intro x y
        simp [det2]
        ring
      map_smul' := by
        intro c x
        simp [det2]
        ring }
  have hL (z : Point 2) : supportValue σ a b z = L z - L a := by
    simp [supportValue, L, det2]
    ring
  have hlinear : IsLinearMap ℝ (L : Point 2 → ℝ) :=
    LinearMap.isLinearMap_of_compatibleSMul ℝ L
  simpa only [hL, sub_pos] using convex_halfSpace_gt hlinear (L a)

lemma supportValue_negative_convex (σ : ℝ) (a b : Point 2) :
    Convex ℝ {z | supportValue σ a b z < 0} := by
  have h := supportValue_positive_convex (-σ) a b
  simpa [supportValue] using h

lemma supportCell_disjoint {m : ℕ} (σ : ℝ)
    (edgeStart edgeEnd : Fin m → Point 2)
    {i j : Fin m} (hij : i ≠ j) :
    Disjoint (SupportCell σ edgeStart edgeEnd i)
      (SupportCell σ edgeStart edgeEnd j) := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  exact (not_lt_of_ge (le_of_lt (hzj.2 i hij))) hzi.1

lemma supportValue_lineMap (σ : ℝ) (a b x y : Point 2) (t : ℝ) :
    supportValue σ a b (AffineMap.lineMap x y t) =
      (1 - t) * supportValue σ a b x + t * supportValue σ a b y := by
  simp [supportValue, det2, AffineMap.lineMap_apply, vsub_eq_sub]
  ring

lemma supportCell_convex {m : ℕ} (σ : ℝ)
    (edgeStart edgeEnd : Fin m → Point 2) (i : Fin m) :
    Convex ℝ (SupportCell σ edgeStart edgeEnd i) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  constructor
  · exact (convex_iff_add_mem.mp
      (supportValue_negative_convex σ (edgeStart i) (edgeEnd i)))
        hx.1 hy.1 ha hb hab
  · intro j hji
    exact (convex_iff_add_mem.mp
      (supportValue_positive_convex σ (edgeStart j) (edgeEnd j)))
        (hx.2 j hji) (hy.2 j hji) ha hb hab

/-- Three distinct support cells contain no collinear transversal, including
points in the convex open cells rather than only points of the finite set. -/
lemma det2_ne_zero_of_mem_supportCells {m : ℕ} {σ : ℝ}
    {edgeStart edgeEnd : Fin m → Point 2} {i j l : Fin m}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {a b c : Point 2}
    (ha : a ∈ SupportCell σ edgeStart edgeEnd i)
    (hb : b ∈ SupportCell σ edgeStart edgeEnd j)
    (hc : c ∈ SupportCell σ edgeStart edgeEnd l) :
    det2 (b - a) (c - a) ≠ 0 := by
  have hab : a ≠ b := by
    intro h
    subst b
    linarith [ha.1, hb.2 i hij]
  have hac : a ≠ c := by
    intro h
    subst c
    linarith [ha.1, hc.2 i hil]
  intro hdet
  have contradiction_of_line (r : ℝ)
      (hline : c = AffineMap.lineMap a b r) : False := by
    by_cases hr0 : r ≤ 0
    · have hid := supportValue_lineMap σ (edgeStart i) (edgeEnd i) a b r
      rw [← hline] at hid
      have hfirst : (1 - r) * supportValue σ (edgeStart i) (edgeEnd i) a < 0 :=
        mul_neg_of_pos_of_neg (by linarith) ha.1
      have hsecond : r * supportValue σ (edgeStart i) (edgeEnd i) b ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hr0 (hb.2 i hij).le
      linarith [hc.2 i hil]
    · by_cases hr1 : 1 ≤ r
      · have hid := supportValue_lineMap σ (edgeStart j) (edgeEnd j) a b r
        rw [← hline] at hid
        have hfirst : (1 - r) * supportValue σ (edgeStart j) (edgeEnd j) a ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (ha.2 j hij.symm).le
        have hsecond : r * supportValue σ (edgeStart j) (edgeEnd j) b < 0 :=
          mul_neg_of_pos_of_neg (by linarith) hb.1
        linarith [hc.2 j hjl]
      · have hid := supportValue_lineMap σ (edgeStart l) (edgeEnd l) a b r
        rw [← hline] at hid
        have hfirst : 0 < (1 - r) * supportValue σ (edgeStart l) (edgeEnd l) a :=
          mul_pos (by linarith) (ha.2 l hil.symm)
        have hsecond : 0 < r * supportValue σ (edgeStart l) (edgeEnd l) b :=
          mul_pos (by linarith) (hb.2 l hjl.symm)
        linarith [hc.1]
  by_cases hx : b 0 - a 0 = 0
  · have hy : b 1 - a 1 ≠ 0 := by
      intro hy
      apply hab
      apply PiLp.ext
      intro r
      fin_cases r <;> simp_all <;> linarith
    let r := (c 1 - a 1) / (b 1 - a 1)
    apply contradiction_of_line r
    apply PiLp.ext
    intro q
    fin_cases q
    · have hx' : c 0 - a 0 = 0 := by
        simp only [det2, PiLp.sub_apply, hx, zero_mul, zero_sub] at hdet
        have hp : (b 1 - a 1) * (c 0 - a 0) = 0 := neg_eq_zero.mp hdet
        exact (mul_eq_zero.mp hp).resolve_left hy
      simp [r, AffineMap.lineMap_apply, vsub_eq_sub, hx]
      linarith [hx']
    · simp [r, AffineMap.lineMap_apply, vsub_eq_sub]
      field_simp [hy]
      ring
  · let r := (c 0 - a 0) / (b 0 - a 0)
    apply contradiction_of_line r
    have hy : c 1 - a 1 = r * (b 1 - a 1) := by
      dsimp [r]
      simp only [det2, PiLp.sub_apply] at hdet
      field_simp [hx]
      nlinarith
    apply PiLp.ext
    intro q
    fin_cases q
    · simp [r, AffineMap.lineMap_apply, vsub_eq_sub]
      field_simp [hx]
      ring
    · simp [AffineMap.lineMap_apply, vsub_eq_sub]
      linarith [hy]

/-- Moving the third point inside one convex support cell cannot change the
orientation of a transversal triple. -/
lemma supportValue_transport_third {m : ℕ} {σ : ℝ} (hσ : σ ≠ 0)
    {edgeStart edgeEnd : Fin m → Point 2} {i j l : Fin m}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {a b c c' : Point 2}
    (ha : a ∈ SupportCell σ edgeStart edgeEnd i)
    (hb : b ∈ SupportCell σ edgeStart edgeEnd j)
    (hc : c ∈ SupportCell σ edgeStart edgeEnd l)
    (hc' : c' ∈ SupportCell σ edgeStart edgeEnd l)
    (hpos : 0 < supportValue σ a b c) :
    0 < supportValue σ a b c' := by
  have hdet' := det2_ne_zero_of_mem_supportCells hij hil hjl ha hb hc'
  have hsv' : supportValue σ a b c' ≠ 0 := by
    simpa only [supportValue] using mul_ne_zero hσ hdet'
  by_contra hnpos
  have hneg : supportValue σ a b c' < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnpos) hsv'
  let s := supportValue σ a b c /
    (supportValue σ a b c - supportValue σ a b c')
  have hden : 0 < supportValue σ a b c - supportValue σ a b c' := by linarith
  have hs0 : 0 < s := div_pos hpos hden
  have hs1 : s < 1 := by
    rw [div_lt_one hden]
    linarith
  let z := AffineMap.lineMap c c' s
  have hzcell : z ∈ SupportCell σ edgeStart edgeEnd l :=
    (supportCell_convex σ edgeStart edgeEnd l).lineMap_mem hc hc' ⟨hs0.le, hs1.le⟩
  have hzero : supportValue σ a b z = 0 := by
    rw [show supportValue σ a b z =
      (1 - s) * supportValue σ a b c + s * supportValue σ a b c' by
        exact supportValue_lineMap σ a b c c' s]
    dsimp [s]
    field_simp [ne_of_gt hden]
    ring
  have hdetz := det2_ne_zero_of_mem_supportCells hij hil hjl ha hb hzcell
  exact hdetz ((mul_eq_zero.mp hzero).resolve_left hσ)

/-- Strong output together with the increasing cyclic support-edge labels
used to form its cells. -/
structure OrderedStrongPositiveFractionConfiguration (k : ℕ)
    (X : Finset (Point 2))
    extends StrongPositiveFractionConfiguration k X where
  supportSize : ℕ
  supportSize_pos : 0 < supportSize
  supportIndex : Fin k → Fin supportSize
  supportIndex_strictMono : StrictMono supportIndex
  supportSigma : ℝ
  supportSigma_ne_zero : supportSigma ≠ 0
  supportStart : Fin supportSize → Point 2
  supportEnd : Fin supportSize → Point 2
  cell_support_sign : ∀ i, ∀ z ∈ cell i,
    z ∈ SupportCell supportSigma supportStart supportEnd (supportIndex i)
  representative : Fin k → Point 2
  representative_mem : ∀ i, representative i ∈ cell i
  representative_orient : ∀ i j l : Fin k, i < j → j < l →
    0 < supportValue supportSigma
      (representative i) (representative j) (representative l)

/-- Every transversal has the cyclic orientation fixed by the retained
cup/cap representative, even after the cells are shrunk. -/
theorem OrderedStrongPositiveFractionConfiguration.transversal_orient
    {k : ℕ} {X : Finset (Point 2)}
    (C : OrderedStrongPositiveFractionConfiguration k X)
    (p : Fin k → Point 2) (hp : ∀ i, p i ∈ C.cell i) :
    ∀ i j l : Fin k, i < j → j < l →
      0 < supportValue C.supportSigma (p i) (p j) (p l) := by
  intro i j l hij hjl
  have hidx_ij : C.supportIndex i ≠ C.supportIndex j :=
    ne_of_lt (C.supportIndex_strictMono hij)
  have hidx_il : C.supportIndex i ≠ C.supportIndex l :=
    ne_of_lt (C.supportIndex_strictMono (hij.trans hjl))
  have hidx_jl : C.supportIndex j ≠ C.supportIndex l :=
    ne_of_lt (C.supportIndex_strictMono hjl)
  have hri := C.cell_support_sign i (C.representative i) (C.representative_mem i)
  have hrj := C.cell_support_sign j (C.representative j) (C.representative_mem j)
  have hrl := C.cell_support_sign l (C.representative l) (C.representative_mem l)
  have hpi := C.cell_support_sign i (p i) (hp i)
  have hpj := C.cell_support_sign j (p j) (hp j)
  have hpl := C.cell_support_sign l (p l) (hp l)
  have h₁ : 0 < supportValue C.supportSigma
      (C.representative i) (C.representative j) (p l) :=
    supportValue_transport_third C.supportSigma_ne_zero
      hidx_ij hidx_il hidx_jl hri hrj hrl hpl
      (C.representative_orient i j l hij hjl)
  have h₂rot : 0 < supportValue C.supportSigma
      (p l) (C.representative i) (p j) := by
    apply supportValue_transport_third C.supportSigma_ne_zero
      hidx_il.symm hidx_jl.symm hidx_ij hpl hri hrj hpj
    rw [supportValue_rotate']
    exact h₁
  have h₂ : 0 < supportValue C.supportSigma
      (C.representative i) (p j) (p l) := by
    rw [supportValue_rotate]
    exact h₂rot
  have h₃rot : 0 < supportValue C.supportSigma (p j) (p l) (p i) := by
    apply supportValue_transport_third C.supportSigma_ne_zero
      hidx_jl hidx_ij.symm hidx_il.symm hpj hpl hri hpi
    rw [supportValue_rotate]
    exact h₂
  rw [supportValue_rotate] at h₃rot
  exact h₃rot

/-- Four points with one strict orientation on all increasing triples have
crossing interlaced open segments. -/
lemma interlaced_planar_segments_cross {σ : ℝ} {a b c d : Point 2}
    (habc : 0 < supportValue σ a b c)
    (habd : 0 < supportValue σ a b d)
    (hacd : 0 < supportValue σ a c d)
    (hbcd : 0 < supportValue σ b c d) :
    ∃ t u : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∈ Set.Ioo (0 : ℝ) 1 ∧
      AffineMap.lineMap a c t = AffineMap.lineMap b d u := by
  let A := supportValue σ a b d
  let C := supportValue σ a b c
  let S := supportValue σ a b c + supportValue σ a c d
  have hA : 0 < A := habd
  have hC : 0 < C := habc
  have hS : 0 < S := by dsimp [S]; linarith
  have hSA : S - A = supportValue σ b c d := by
    dsimp [S, A]
    simp [supportValue, det2]
    ring
  have hSC : S - C = supportValue σ a c d := by
    dsimp [S, C]
    ring
  refine ⟨A / S, C / S, ⟨div_pos hA hS, ?_⟩,
    ⟨div_pos hC hS, ?_⟩, ?_⟩
  · rw [div_lt_one hS]
    linarith
  · rw [div_lt_one hS]
    linarith
  · apply PiLp.ext
    intro i
    fin_cases i <;>
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, PiLp.add_apply,
        PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    all_goals
      dsimp [A, C, S]
      field_simp [ne_of_gt hS]
      simp [supportValue, det2]
      ring

/-- The ordered planar representatives in a positive-fraction package give
the exact projected-chain predicate after any lift whose four-tuples are
affinely independent. -/
theorem OrderedStrongPositiveFractionConfiguration.isProjectedConvexChain
    {k : ℕ} {X : Finset (Point 2)}
    (C : OrderedStrongPositiveFractionConfiguration k X)
    (x : Fin k → Point 3)
    (hproj : ∀ i, verticalProjection (x i) ∈ C.cell i)
    (hAI : ∀ i₀ i₁ i₂ i₃ : Fin k,
      i₀ < i₁ → i₁ < i₂ → i₂ < i₃ →
      AffineIndependent ℝ ![x i₀, x i₁, x i₂, x i₃]) :
    IsProjectedConvexChain x Finset.univ := by
  intro i₀ _ i₁ _ i₂ _ i₃ _ h01 h12 h23
  refine ⟨hAI i₀ i₁ i₂ i₃ h01 h12 h23, ?_⟩
  let p : Fin k → Point 2 := fun i => verticalProjection (x i)
  obtain ⟨t, u, ht, hu, hcross⟩ := interlaced_planar_segments_cross
    (C.transversal_orient p hproj i₀ i₁ i₂ h01 h12)
    (C.transversal_orient p hproj i₀ i₁ i₃ h01 (h12.trans h23))
    (C.transversal_orient p hproj i₀ i₂ i₃ (h01.trans h12) h23)
    (C.transversal_orient p hproj i₁ i₂ i₃ h12 h23)
  refine ⟨t, u, ht, hu, ?_⟩
  have hline (p q : Point 3) (r : ℝ) :
      verticalProjection (segmentPoint p q r) =
        AffineMap.lineMap (verticalProjection p) (verticalProjection q) r := by
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [verticalProjection, segmentPoint, AffineMap.lineMap_apply,
        vsub_eq_sub]
  rw [hline, hline]
  simpa only [p] using hcross

/-- The support signs separate the convex hull of each entire cell from the
hull of all other entire cells.  This is the source's strong family-convexity
property, stronger than merely checking transversals. -/
lemma strongConvexPositionPlanarCells_of_supportSigns {k : ℕ}
    (cell : Fin k → Finset (Point 2))
    (σ : ℝ) (edgeStart edgeEnd : Fin k → Point 2)
    (hsign : ∀ i, ∀ z ∈ cell i,
      z ∈ SupportCell σ edgeStart edgeEnd i) :
    StrongConvexPositionPlanarCells cell := by
  intro i
  rw [Set.disjoint_left]
  intro z hzi hzothers
  let f : Point 2 → ℝ := supportValue σ (edgeStart i) (edgeEnd i)
  have hown : (↑(cell i) : Set (Point 2)) ⊆ {w | f w < 0} := by
    intro w hw
    exact (hsign i w hw).1
  have hzneg : f z < 0 :=
    convexHull_min hown (by
      simpa [f] using supportValue_negative_convex σ (edgeStart i) (edgeEnd i)) hzi
  have hother :
      (↑(planarClusterUnion cell (Finset.univ.erase i)) : Set (Point 2)) ⊆
        {w | 0 < f w} := by
    intro w hw
    simp only [planarClusterUnion, Finset.mem_coe, Finset.mem_biUnion] at hw
    obtain ⟨j, hj, hwj⟩ := hw
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact (hsign j w hwj).2 i hji.symm
  have hzpos : 0 < f z :=
    convexHull_min hother (by
      simpa [f] using supportValue_positive_convex σ (edgeStart i) (edgeEnd i)) hzothers
  linarith

/-- The finite output of the support-region counting argument.  Unlike the
usual picture of the regions, this records only their affine sign pattern,
which is exactly what is needed for robust convexity. -/
structure PositiveFractionSupportFrame (k : ℕ) (X : Finset (Point 2)) where
  sigma : ℝ
  edgeStart : Fin k → Point 2
  edgeEnd : Fin k → Point 2
  cell : Fin k → Finset (Point 2)
  cell_subset : ∀ i, cell i ⊆ X
  cell_dense : ∀ i, HasPositiveFractionDensity k X (cell i)
  cell_sign : ∀ i, ∀ z ∈ cell i,
    z ∈ SupportCell sigma edgeStart edgeEnd i

/-- Strict support-region sign certificates produce a positive-fraction
configuration.  Thus all geometry after the Pór--Valtr incidence count is
contained in this short lemma. -/
def PositiveFractionSupportFrame.toConfiguration {k : ℕ}
    {X : Finset (Point 2)} (F : PositiveFractionSupportFrame k X) :
    PositiveFractionConfiguration k X where
  cell := F.cell
  cell_subset := F.cell_subset
  cell_disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro z hzi hzj
    have hzi' := F.cell_sign i z hzi
    have hzj' := F.cell_sign j z hzj
    exact Set.disjoint_left.mp
      (supportCell_disjoint F.sigma F.edgeStart F.edgeEnd hij) hzi' hzj'
  cell_dense := F.cell_dense
  transversal_convex := by
    intro p hp
    apply transversal_convex_of_cell_separators F.cell
      (fun {i j} hij => by
        rw [Finset.disjoint_left]
        intro z hzi hzj
        exact Set.disjoint_left.mp
          (supportCell_disjoint F.sigma F.edgeStart F.edgeEnd hij)
          (F.cell_sign _ _ hzi) (F.cell_sign _ _ hzj))
      (fun i z => supportValue F.sigma (F.edgeStart i) (F.edgeEnd i) z)
      (fun i => supportValue_positive_convex _ _ _)
      (fun i z hz => (F.cell_sign i z hz).1)
      (fun i j hij z hz => (F.cell_sign j z hz).2 i hij)
      p hp

def PositiveFractionSupportFrame.toStrongConfiguration {k : ℕ}
    {X : Finset (Point 2)} (F : PositiveFractionSupportFrame k X) :
    StrongPositiveFractionConfiguration k X where
  toPositiveFractionConfiguration := F.toConfiguration
  strong_convex := strongConvexPositionPlanarCells_of_supportSigns
    F.cell F.sigma F.edgeStart F.edgeEnd F.cell_sign

/-! ## Finite incidence counting -/

/-- Double-counting local witnesses inside all `m`-subsets gives the usual
supersaturation inequality. -/
theorem supersaturation_double_count
    {α : Type*} [DecidableEq α]
    (X : Finset α) (m s : ℕ) (good : Finset α → Prop)
    [DecidablePred good]
    (hsm : s ≤ m) (hmX : m ≤ X.card)
    (hlocal : ∀ Z ∈ X.powersetCard m,
      ∃ Q ∈ X.powersetCard s, good Q ∧ Q ⊆ Z) :
    X.card.choose s ≤ m.choose s * ((X.powersetCard s).filter good).card := by
  classical
  let Ms := X.powersetCard m
  let Gs := (X.powersetCard s).filter good
  let inc : ℕ := ∑ Z ∈ Ms, ∑ Q ∈ Gs, if Q ⊆ Z then 1 else 0
  have hlower : Ms.card ≤ inc := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro Z hZ
    obtain ⟨Q, hQ, hgood, hQZ⟩ := hlocal Z (by simpa [Ms] using hZ)
    have hQGs : Q ∈ Gs := by simp [Gs, hQ, hgood]
    have hone := Finset.single_le_sum
      (s := Gs) (f := fun Q ↦ if Q ⊆ Z then 1 else 0)
      (fun _ _ ↦ Nat.zero_le _) hQGs
    simpa [hQZ] using hone
  have hswap : inc = ∑ Q ∈ Gs, ((Ms.filter (Q ⊆ ·)).card) := by
    dsimp [inc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro Q _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hext (Q : Finset α) (hQ : Q ∈ Gs) :
      (Ms.filter (Q ⊆ ·)).card = (X.card - s).choose (m - s) := by
    have hQpow : Q ∈ X.powersetCard s := (Finset.mem_filter.mp hQ).1
    have hQX : Q ⊆ X := (Finset.mem_powersetCard.mp hQpow).1
    have hQcard : Q.card = s := (Finset.mem_powersetCard.mp hQpow).2
    simpa [Ms, hQcard] using
      Finset.card_filter_powersetCard_subset Q X m hQX
        (hQcard.trans_le hsm)
  have hinc : inc = Gs.card * (X.card - s).choose (m - s) := by
    rw [hswap]
    calc
      (∑ Q ∈ Gs, (Ms.filter (Q ⊆ ·)).card) =
          ∑ Q ∈ Gs, (X.card - s).choose (m - s) := by
            apply Finset.sum_congr rfl
            intro Q hQ
            exact hext Q hQ
      _ = Gs.card * (X.card - s).choose (m - s) := by simp
  have hraw : X.card.choose m ≤
      Gs.card * (X.card - s).choose (m - s) := by
    simpa [Ms, Finset.card_powersetCard, hinc] using hlower
  have hmul := Nat.mul_le_mul_right (m.choose s) hraw
  have hchoose : X.card.choose m * m.choose s =
      X.card.choose s * (X.card - s).choose (m - s) := Nat.choose_mul hsm
  have hextpos : 0 < (X.card - s).choose (m - s) := by
    apply Nat.choose_pos
    exact Nat.sub_le_sub_right hmX s
  have hcancel : X.card.choose s * (X.card - s).choose (m - s) ≤
      (m.choose s * Gs.card) * (X.card - s).choose (m - s) := by
    calc
      X.card.choose s * (X.card - s).choose (m - s) =
          X.card.choose m * m.choose s := hchoose.symm
      _ ≤ (Gs.card * (X.card - s).choose (m - s)) * m.choose s := hmul
      _ = (m.choose s * Gs.card) * (X.card - s).choose (m - s) := by ac_rfl
  simpa [Gs] using Nat.le_of_mul_le_mul_right hcancel hextpos

/-- Averaging a two-sided incidence relation over at most `2*N^q` frames. -/
theorem frame_incidence_averaging
    {Good Frame : Type*} [DecidableEq Good] [DecidableEq Frame]
    (G : Finset Good) (F : Finset Frame) (supports : Good → Frame → Prop)
    [DecidableRel supports]
    (ambient arity : ℕ) (hG : G.Nonempty)
    (htwo : ∀ g ∈ G, 2 ≤ (F.filter (supports g)).card)
    (hframes : F.card ≤ 2 * ambient ^ arity) :
    ∃ f ∈ F,
      G.card ≤ ambient ^ arity * (G.filter (fun g ↦ supports g f)).card := by
  classical
  let inc : ℕ := ∑ g ∈ G, ∑ f ∈ F, if supports g f then 1 else 0
  have hlower : 2 * G.card ≤ inc := by
    calc
      2 * G.card = ∑ g ∈ G, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ g ∈ G, (F.filter (supports g)).card := by
        apply Finset.sum_le_sum
        intro g hg
        exact htwo g hg
      _ = inc := by
        dsimp [inc]
        apply Finset.sum_congr rfl
        intro g _
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hF : F.Nonempty := by
    obtain ⟨g, hg⟩ := hG
    have hp : 0 < (F.filter (supports g)).card :=
      lt_of_lt_of_le (by norm_num) (htwo g hg)
    obtain ⟨f, hf⟩ := Finset.card_pos.mp hp
    exact ⟨f, (Finset.mem_filter.mp hf).1⟩
  obtain ⟨f, hfF, hfmax⟩ := F.exists_max_image
    (fun f ↦ (G.filter (fun g ↦ supports g f)).card) hF
  have hswap : inc = ∑ f ∈ F, (G.filter (fun g ↦ supports g f)).card := by
    dsimp [inc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f' _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hupper : inc ≤ F.card * (G.filter (fun g ↦ supports g f)).card := by
    rw [hswap]
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul F
      (fun f' ↦ (G.filter (fun g ↦ supports g f')).card)
      ((G.filter (fun g ↦ supports g f)).card) hfmax
  refine ⟨f, hfF, ?_⟩
  apply Nat.le_of_mul_le_mul_left (c := 2) _ (by norm_num)
  calc
    2 * G.card ≤ inc := hlower
    _ ≤ F.card * (G.filter (fun g ↦ supports g f)).card := hupper
    _ ≤ (2 * ambient ^ arity) * (G.filter (fun g ↦ supports g f)).card :=
      Nat.mul_le_mul_right _ hframes
    _ = 2 * (ambient ^ arity * (G.filter (fun g ↦ supports g f)).card) := by ac_rfl

/-- The eight bits per requested point between the Pór--Valtr bound
`2^(-32*k)` and the stated bound `2^(-40*k)` absorb the integral rounding
loss of one point. -/
lemma positiveFraction_density_of_rounding
    (k N t : ℕ) (hk : 1 ≤ k) (hN : 2 ^ (40 * k) ≤ N)
    (ht : N < 2 ^ (32 * k) * (t + 1)) :
    N ≤ 2 ^ (40 * k) * t := by
  have hpow32_le : 2 ^ (32 * k) ≤ 2 ^ (40 * k) := by
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have htpos : 0 < t := by
    by_contra h
    have htzero : t = 0 := Nat.eq_zero_of_not_pos h
    subst t
    simp only [Nat.zero_add, Nat.mul_one] at ht
    omega
  have hfactor : 2 ≤ 2 ^ (8 * k) := by
    have hexp : 1 ≤ 8 * k := by omega
    exact (show 2 ^ 1 ≤ 2 ^ (8 * k) from Nat.pow_le_pow_right (by norm_num) hexp)
  have hround : t + 1 ≤ 2 ^ (8 * k) * t := by
    calc
      t + 1 ≤ 2 * t := by omega
      _ ≤ 2 ^ (8 * k) * t := Nat.mul_le_mul_right t hfactor
  calc
    N ≤ 2 ^ (32 * k) * (t + 1) := Nat.le_of_lt ht
    _ ≤ 2 ^ (32 * k) * (2 ^ (8 * k) * t) :=
      Nat.mul_le_mul_left _ hround
    _ = 2 ^ (40 * k) * t := by
      rw [← Nat.mul_assoc]
      rw [← Nat.pow_add]
      congr 2
      omega

/-- Integral fourth-power form of the numerical Pór--Valtr estimate. -/
theorem density_of_pv_power_bound_le
    (k N alpha : ℕ) (hk : 0 < k) (h8 : 8 * k ≤ N)
    (hpow : ((N - 4 * k) ^ 4) ^ k ≤
      (2 ^ (32 * k) * alpha * N ^ 3) ^ k) :
    N ≤ 2 ^ (40 * k) * alpha := by
  have hbase : (N - 4 * k) ^ 4 ≤ 2 ^ (32 * k) * alpha * N ^ 3 := by
    apply Nat.le_of_not_lt
    intro hrev
    have hp := (Nat.pow_lt_pow_iff_left hk.ne').mpr hrev
    omega
  have hhalf : N ≤ 2 * (N - 4 * k) := by omega
  have hfour : N ^ 4 ≤ 16 * (N - 4 * k) ^ 4 := by
    calc
      N ^ 4 ≤ (2 * (N - 4 * k)) ^ 4 := Nat.pow_le_pow_left hhalf _
      _ = 16 * (N - 4 * k) ^ 4 := by ring
  have hwide : N ^ 4 ≤ (16 * 2 ^ (32 * k) * alpha) * N ^ 3 := by
    calc
      N ^ 4 ≤ 16 * (N - 4 * k) ^ 4 := hfour
      _ ≤ 16 * (2 ^ (32 * k) * alpha * N ^ 3) := Nat.mul_le_mul_left _ hbase
      _ = (16 * 2 ^ (32 * k) * alpha) * N ^ 3 := by ring
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity : 0 < 8 * k) h8
  have hcubic : 0 < N ^ 3 := pow_pos hNpos _
  have hsmall : N ≤ 16 * 2 ^ (32 * k) * alpha := by
    apply Nat.le_of_mul_le_mul_right (c := N ^ 3) _ hcubic
    simpa only [show N * N ^ 3 = N ^ 4 by ring] using hwide
  have hscale : 16 * 2 ^ (32 * k) ≤ 2 ^ (40 * k) := by
    calc
      16 * 2 ^ (32 * k) = 2 ^ (32 * k + 4) := by ring
      _ ≤ 2 ^ (40 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact hsmall.trans (Nat.mul_le_mul_right alpha hscale)

lemma eight_mul_le_two_pow_40_mul (k : ℕ) : 8 * k ≤ 2 ^ (40 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hp : 1 ≤ 2 ^ (40 * k) := Nat.one_le_two_pow
      rw [Nat.mul_succ, Nat.mul_succ, Nat.pow_add]
      norm_num at ⊢
      nlinarith

/-- Splitting `2*k` natural numbers into their upper and lower halves gives
the order-statistic estimate used in the Pór--Valtr product argument. -/
theorem exists_half_order_statistic (k N : ℕ) (hk : 0 < k)
    (t : Fin (2 * k) → ℕ) (htN : ∀ i, t i ≤ N) :
    ∃ alpha : ℕ, ∃ I : Finset (Fin (2 * k)),
      I.card = k ∧ (∀ i ∈ I, alpha ≤ t i) ∧
      (∏ i, t i) ≤ alpha ^ k * N ^ k := by
  classical
  let sigma : Equiv.Perm (Fin (2 * k)) := Tuple.sort t
  let L : Finset (Fin (2 * k)) :=
    Finset.univ.filter (fun j ↦ (j : ℕ) < k)
  let H : Finset (Fin (2 * k)) :=
    Finset.univ.filter (fun j ↦ k ≤ (j : ℕ))
  let alpha := t (sigma ⟨k, by omega⟩)
  let I := H.image sigma
  have hLcard : L.card = k := by
    simpa [L, min_eq_right (by omega : k ≤ 2 * k)] using
      (Fin.card_filter_val_lt (n := 2 * k) (m := k))
  have hHcard : H.card = k := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * k))))
      (p := fun j ↦ (j : ℕ) < k)
    have hnot : (Finset.univ.filter fun j : Fin (2 * k) ↦ ¬ (j : ℕ) < k) = H := by
      ext j
      simp [H]
    rw [hnot, hLcard] at hsum
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    omega
  have hdisj : Disjoint L H := by
    simp [L, H, Finset.disjoint_left]
  have hcover : L ∪ H = Finset.univ := by
    ext j
    simp [L, H]
    omega
  have hmono : Monotone (t ∘ sigma) := Tuple.monotone_sort t
  have hlow : ∀ j ∈ L, t (sigma j) ≤ alpha := by
    intro j hj
    apply hmono
    have hjlt : (j : ℕ) < k := by simpa [L] using hj
    exact Fin.mk_le_mk.mpr (by omega)
  have hlarge : ∀ j ∈ H, alpha ≤ t (sigma j) := by
    intro j hj
    apply hmono
    have hjge : k ≤ (j : ℕ) := by simpa [H] using hj
    exact Fin.mk_le_mk.mpr hjge
  have hLprod : (∏ j ∈ L, t (sigma j)) ≤ alpha ^ k := by
    calc
      (∏ j ∈ L, t (sigma j)) ≤ ∏ _j ∈ L, alpha := by
        apply Finset.prod_le_prod
        · exact fun _ _ ↦ Nat.zero_le _
        · exact hlow
      _ = alpha ^ k := by simp [hLcard]
  have hHprod : (∏ j ∈ H, t (sigma j)) ≤ N ^ k := by
    calc
      (∏ j ∈ H, t (sigma j)) ≤ ∏ _j ∈ H, N := by
        apply Finset.prod_le_prod
        · exact fun _ _ ↦ Nat.zero_le _
        · intro j _
          exact htN (sigma j)
      _ = N ^ k := by simp [hHcard]
  have hperm : (∏ i, t i) = ∏ j, t (sigma j) := by
    exact Finset.prod_equiv sigma.symm (fun _ ↦ by simp) (fun _ _ ↦ by simp)
  refine ⟨alpha, I, ?_, ?_, ?_⟩
  · rw [show I.card = H.card from Finset.card_image_of_injective H sigma.injective]
    exact hHcard
  · intro i hi
    simp only [I, Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact hlarge j hj
  · rw [hperm, ← hcover, Finset.prod_union hdisj]
    exact Nat.mul_le_mul hLprod hHprod

/-- The complete cardinality endgame of the Pór--Valtr proof.  The
geometric incidence argument supplies `hsuper`, `hframe`, and `hfiber`; the
last hypothesis is the elementary lower/upper-half ordering of the `2*k`
cell sizes. -/
theorem pv_cardinality_endgame
    (k N G P : ℕ) (hk : 4 ≤ k) (hN : 2 ^ (40 * k) ≤ N)
    (t : Fin (2 * k) → ℕ)
    (hsuper : N.choose (4 * k) ≤
      (2 ^ (8 * k)).choose (4 * k) * G)
    (hframe : G ≤ N ^ (2 * k) * P)
    (hfiber : P ≤ ∏ i, t i)
    (htN : ∀ i, t i ≤ N) :
    ∃ I : Finset (Fin (2 * k)), I.card = k ∧
      ∀ i ∈ I, N ≤ 2 ^ (40 * k) * t i := by
  have hkpos : 0 < k := by omega
  obtain ⟨alpha, I, hIcard, hIlarge, hprod⟩ :=
    exists_half_order_statistic k N hkpos t htN
  have h8 : 8 * k ≤ N := (eight_mul_le_two_pow_40_mul k).trans hN
  have hsubpow : (N - 4 * k) ^ (4 * k) ≤
      (4 * k).factorial * N.choose (4 * k) := by
    calc
      (N - 4 * k) ^ (4 * k) ≤ (N + 1 - 4 * k) ^ (4 * k) :=
        Nat.pow_le_pow_left (by omega) _
      _ ≤ N.descFactorial (4 * k) := Nat.pow_sub_le_descFactorial _ _
      _ = (4 * k).factorial * N.choose (4 * k) :=
        Nat.descFactorial_eq_factorial_mul_choose _ _
  have hchooseM : (4 * k).factorial * (2 ^ (8 * k)).choose (4 * k) ≤
      (2 ^ (8 * k)) ^ (4 * k) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ _
  have hgood : (N - 4 * k) ^ (4 * k) ≤
      (2 ^ (8 * k)) ^ (4 * k) * G := by
    calc
      (N - 4 * k) ^ (4 * k) ≤ (4 * k).factorial * N.choose (4 * k) := hsubpow
      _ ≤ (4 * k).factorial * ((2 ^ (8 * k)).choose (4 * k) * G) :=
        Nat.mul_le_mul_left _ hsuper
      _ = ((4 * k).factorial * (2 ^ (8 * k)).choose (4 * k)) * G := by ring
      _ ≤ (2 ^ (8 * k)) ^ (4 * k) * G := Nat.mul_le_mul_right G hchooseM
  have hall : (N - 4 * k) ^ (4 * k) ≤
      (2 ^ (8 * k)) ^ (4 * k) *
        (N ^ (2 * k) * (alpha ^ k * N ^ k)) := by
    calc
      (N - 4 * k) ^ (4 * k) ≤ (2 ^ (8 * k)) ^ (4 * k) * G := hgood
      _ ≤ (2 ^ (8 * k)) ^ (4 * k) * (N ^ (2 * k) * P) :=
        Nat.mul_le_mul_left _ hframe
      _ ≤ (2 ^ (8 * k)) ^ (4 * k) * (N ^ (2 * k) * ∏ i, t i) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hfiber)
      _ ≤ (2 ^ (8 * k)) ^ (4 * k) *
          (N ^ (2 * k) * (alpha ^ k * N ^ k)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hprod)
  have hMpow : (2 ^ (8 * k)) ^ (4 * k) = (2 ^ (32 * k)) ^ k := by
    calc
      (2 ^ (8 * k)) ^ (4 * k) = 2 ^ ((8 * k) * (4 * k)) :=
        (pow_mul 2 (8 * k) (4 * k)).symm
      _ = 2 ^ ((32 * k) * k) := by congr 1 <;> ring
      _ = (2 ^ (32 * k)) ^ k := pow_mul 2 (32 * k) k
  have hNpow : N ^ (2 * k) * N ^ k = (N ^ 3) ^ k := by
    calc
      N ^ (2 * k) * N ^ k = N ^ (2 * k + k) := (pow_add N _ _).symm
      _ = N ^ (3 * k) := by congr 1 <;> omega
      _ = (N ^ 3) ^ k := pow_mul N 3 k
  have hpower : ((N - 4 * k) ^ 4) ^ k ≤
      (2 ^ (32 * k) * alpha * N ^ 3) ^ k := by
    calc
      ((N - 4 * k) ^ 4) ^ k = (N - 4 * k) ^ (4 * k) := by rw [← pow_mul]
      _ ≤ (2 ^ (8 * k)) ^ (4 * k) *
          (N ^ (2 * k) * (alpha ^ k * N ^ k)) := hall
      _ = (2 ^ (32 * k) * alpha * N ^ 3) ^ k := by
        rw [hMpow, mul_pow, mul_pow]
        rw [← hNpow]
        ring
  have hdense : N ≤ 2 ^ (40 * k) * alpha :=
    density_of_pv_power_bound_le k N alpha hkpos h8 hpower
  refine ⟨I, hIcard, ?_⟩
  intro i hi
  exact hdense.trans (Nat.mul_le_mul_left _ (hIlarge i hi))

/-! ## Assembly of the Pór--Valtr incidence argument -/

theorem exists_orderedStrongPositiveFractionConfiguration
    (k : ℕ) (hk : 4 ≤ k) (X : Finset (Point 2))
    (hcard : 2 ^ (40 * k) ≤ X.card)
    (hgp : InGeneralPosition 2 X) :
    Nonempty (OrderedStrongPositiveFractionConfiguration k X) := by
  classical
  obtain ⟨t, ht⟩ := exists_genericCoordinate_injOn X
  let good : Finset (Point 2) → Prop := PVGood t k
  let G : Finset (Finset (Point 2)) :=
    (X.powersetCard (4 * k)).filter good
  let Frame := PVFrame k X
  let frames : Finset Frame := Finset.univ
  let supports : Finset (Point 2) → Frame → Prop :=
    PVSupports t (show 2 ≤ k by omega)
  have hm : 4 * k ≤ 2 ^ (8 * k) := by
    have h8 : 8 * k ≤ 2 ^ (8 * k) :=
      Nat.le_of_lt (8 * k).lt_two_pow_self
    omega
  have hmX : 2 ^ (8 * k) ≤ X.card := by
    exact (Nat.pow_le_pow_right (by norm_num) (by omega : 8 * k ≤ 40 * k)).trans hcard
  have hlocal : ∀ Z ∈ X.powersetCard (2 ^ (8 * k)),
      ∃ Q ∈ X.powersetCard (4 * k), good Q ∧ Q ⊆ Z := by
    intro Z hZ
    have hZX := (Finset.mem_powersetCard.mp hZ).1
    have hZcard := (Finset.mem_powersetCard.mp hZ).2
    simpa [good] using exists_pvGood_subset (t := t) (show 2 ≤ k by omega)
      ht hgp hZX hZcard
  have hsuper : X.card.choose (4 * k) ≤
      (2 ^ (8 * k)).choose (4 * k) * G.card := by
    simpa [G, good] using supersaturation_double_count X
      (2 ^ (8 * k)) (4 * k) good hm hmX hlocal
  have hGnonempty : G.Nonempty := by
    obtain ⟨Z, hZX, hZcard⟩ := Finset.exists_subset_card_eq hmX
    obtain ⟨Q, hQpow, hgood, hQZ⟩ :=
      hlocal Z (Finset.mem_powersetCard.mpr ⟨hZX, hZcard⟩)
    exact ⟨Q, by simp [G, hQpow, hgood]⟩
  have htwo : ∀ Q ∈ G, 2 ≤ (frames.filter (supports Q)).card := by
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    obtain ⟨A, hfalse, htrue⟩ := pvGood_supports_two_frames
      (t := t) (show 2 ≤ k by omega)
      (Finset.mem_powersetCard.mp hQdata.1).1 hQdata.2
    let f0 : Frame := (false, A)
    let f1 : Frame := (true, A)
    have hf0 : f0 ∈ frames.filter (supports Q) := by
      simp [frames, supports, f0, hfalse]
    have hf1 : f1 ∈ frames.filter (supports Q) := by
      simp [frames, supports, f1, htrue]
    have hne : f0 ≠ f1 := by
      intro h
      have hh : false = true := congrArg Prod.fst h
      simp at hh
    have hpair : ({f0, f1} : Finset Frame) ⊆ frames.filter (supports Q) := by
      intro f hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl <;> assumption
    simpa [hne] using Finset.card_le_card hpair
  have hframes : frames.card ≤ 2 * X.card ^ (2 * k) := by
    simp [frames, Frame, PVFrame]
  obtain ⟨F, hF, hframe⟩ := frame_incidence_averaging
    G frames supports X.card (2 * k) hGnonempty htwo hframes
  let fiber : Finset (Finset (Point 2)) := G.filter (fun Q => supports Q F)
  have hfiber_nonempty : fiber.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hzero
    have hz : fiber.card = 0 := Nat.eq_zero_of_not_pos hzero
    have hz' : (G.filter fun Q => supports Q F).card = 0 := by
      simpa [fiber] using hz
    rw [hz', Nat.mul_zero] at hframe
    have hGpos : 0 < G.card := hGnonempty.card_pos
    omega
  obtain ⟨Q₀, hQ₀⟩ := hfiber_nonempty
  let W : PVSupportData t (show 2 ≤ k by omega) Q₀ F :=
    Classical.choice (show supports Q₀ F by
      have hQ₀' : Q₀ ∈ G.filter (fun Q => supports Q F) := by
        simpa only [fiber] using hQ₀
      exact (Finset.mem_filter.mp hQ₀').2)
  let cell : Fin (2 * k) → Finset (Point 2) :=
    fun i => pvFrameCell (show 2 ≤ k by omega) F i
  have hfiber : fiber.card ≤ ∏ i, (cell i).card := by
    let V := (i : Fin (2 * k)) → ↥(cell i)
    let witness : (Q : ↥fiber) →
        PVSupportData t (show 2 ≤ k by omega) (Q : Finset (Point 2)) F := fun Q =>
      Classical.choice (show supports (Q : Finset (Point 2)) F by
        have hQ' : (Q : Finset (Point 2)) ∈ G.filter (fun R => supports R F) := by
          simpa only [fiber] using Q.property
        exact (Finset.mem_filter.mp hQ').2)
    let chosen : (Q : ↥fiber) → Fin (2 * k) → Point 2 := fun Q i =>
      (witness Q).q ⟨2 * i + 1, by omega⟩
    have hchosen (Q : ↥fiber) :
        (∀ i, chosen Q i ∈ (Q : Finset (Point 2)) ∧ chosen Q i ∈ cell i) ∧
        (Q : Finset (Point 2)) =
          (Finset.univ.image fun i => (F.2 i : Point 2)) ∪
            Finset.univ.image (chosen Q) := by
      constructor
      · intro i
        constructor
        · rw [← (witness Q).q_image]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        · exact (witness Q).odd_mem_cell i
      · rw [← (witness Q).q_image,
          ← image_even_union_image_odd (show 1 ≤ k by omega) (witness Q).q]
        congr 1
        ext z
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor <;> rintro ⟨i, rfl⟩
        · exact ⟨i, (witness Q).anchor_even i⟩
        · exact ⟨i, (witness Q).anchor_even i |>.symm⟩
    let encode : ↥fiber → V := fun Q i => ⟨chosen Q i, (hchosen Q).1 i |>.2⟩
    have hencode : Function.Injective encode := by
      intro Q R hQR
      apply Subtype.ext
      rw [(hchosen Q).2, (hchosen R).2]
      congr 1
      ext z
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor <;> rintro ⟨i, rfl⟩
      · exact ⟨i, (congrArg Subtype.val (congrFun hQR i)).symm⟩
      · exact ⟨i, congrArg Subtype.val (congrFun hQR i)⟩
    have hc := Fintype.card_le_of_injective encode hencode
    calc
      fiber.card = Fintype.card ↥fiber := (Fintype.card_coe fiber).symm
      _ ≤ Fintype.card V := hc
      _ = ∏ i, (cell i).card := by simp [V, Fintype.card_pi]
  have htN : ∀ i, (cell i).card ≤ X.card := by
    intro i
    apply Finset.card_le_card
    simpa only [cell, pvFrameCell] using
      (Finset.filter_subset (fun z => z ∈ SupportCell
        (pvFrameSigma (show 2 ≤ k by omega) F)
        (pvFrameStart F) (pvFrameEnd (show 0 < k by omega) F) i) X)
  obtain ⟨I, hIcard, hIdense⟩ := pv_cardinality_endgame
    k X.card G.card fiber.card hk hcard (fun i => (cell i).card) hsuper
    (by simpa [fiber] using hframe) hfiber htN
  let eI : Fin k ≃o ↥I := I.orderIsoOfFin hIcard
  let idx : Fin k → Fin (2 * k) := fun i => (eI i : Fin (2 * k))
  have hidxinj : Function.Injective idx := by
    intro i j hij
    apply eI.injective
    apply Subtype.ext
    simpa only [idx] using hij
  let selectedCell : Fin k → Finset (Point 2) := fun i => cell (idx i)
  let SF : PositiveFractionSupportFrame k X :=
    { sigma := pvFrameSigma (show 2 ≤ k by omega) F
      edgeStart := fun i => pvFrameStart F (idx i)
      edgeEnd := fun i => pvFrameEnd (show 0 < k by omega) F (idx i)
      cell := selectedCell
      cell_subset := by
        intro i
        simpa only [selectedCell, cell, pvFrameCell] using
          (Finset.filter_subset (fun z => z ∈ SupportCell
            (pvFrameSigma (show 2 ≤ k by omega) F)
            (pvFrameStart F) (pvFrameEnd (show 0 < k by omega) F) (idx i)) X)
      cell_dense := by
        intro i
        exact hIdense (idx i) (eI i).property
      cell_sign := by
        intro i z hz
        have hz' : z ∈ X.filter (fun w => w ∈ SupportCell
            (pvFrameSigma (show 2 ≤ k by omega) F)
            (pvFrameStart F) (pvFrameEnd (show 0 < k by omega) F) (idx i)) := by
          simpa only [selectedCell, cell, pvFrameCell] using hz
        obtain ⟨_, hown, hother⟩ := Finset.mem_filter.mp hz'
        refine ⟨hown, ?_⟩
        intro j hji
        exact hother (idx j) (fun heq => hji (hidxinj heq)) }
  refine ⟨{
    toStrongPositiveFractionConfiguration := SF.toStrongConfiguration
    supportSize := 2 * k
    supportSize_pos := by omega
    supportIndex := idx
    supportIndex_strictMono := by
      intro i j hij
      exact eI.strictMono hij
    supportSigma := pvFrameSigma (show 2 ≤ k by omega) F
    supportSigma_ne_zero := by
      rw [W.frame_sigma]
      cases W.upper <;> norm_num [pvSigma]
    supportStart := pvFrameStart F
    supportEnd := pvFrameEnd (show 0 < k by omega) F
    cell_support_sign := by
      intro i z hz
      change z ∈ SF.cell i at hz
      change z ∈ selectedCell i at hz
      have hz' : z ∈ X.filter (fun w => w ∈ SupportCell
          (pvFrameSigma (show 2 ≤ k by omega) F)
          (pvFrameStart F) (pvFrameEnd (show 0 < k by omega) F) (idx i)) := by
        simpa only [selectedCell, cell, pvFrameCell] using hz
      exact (Finset.mem_filter.mp hz').2
    representative := fun i => W.q ⟨2 * (idx i) + 1, by omega⟩
    representative_mem := by
      intro i
      change W.q ⟨2 * (idx i) + 1, by omega⟩ ∈ SF.cell i
      change W.q ⟨2 * (idx i) + 1, by omega⟩ ∈ selectedCell i
      simpa only [selectedCell, cell] using W.odd_mem_cell (idx i)
    representative_orient := by
      intro i j l hij hjl
      rw [W.frame_sigma]
      apply W.q_orient
      · have := eI.strictMono hij
        have hval : (idx i : ℕ) < (idx j : ℕ) := by
          simpa [idx] using this
        exact Fin.mk_lt_mk.mpr (by omega)
      · have := eI.strictMono hjl
        have hval : (idx j : ℕ) < (idx l : ℕ) := by
          simpa [idx] using this
        exact Fin.mk_lt_mk.mpr (by omega) }⟩

theorem exists_strongPositiveFractionConfiguration
    (k : ℕ) (hk : 4 ≤ k) (X : Finset (Point 2))
    (hcard : 2 ^ (40 * k) ≤ X.card)
    (hgp : InGeneralPosition 2 X) :
    Nonempty (StrongPositiveFractionConfiguration k X) := by
  obtain ⟨C⟩ := exists_orderedStrongPositiveFractionConfiguration k hk X hcard hgp
  exact ⟨C.toStrongPositiveFractionConfiguration⟩

/-- The positive-fraction theorem in its elementary three-cell base case.
Here every transversal has three points, so general position is exactly the
geometric input needed for convexity.  The cells are chosen substantially
larger than the required `2^(-120)` fraction. -/
theorem exists_positiveFractionConfiguration_three
    (X : Finset (Point 2))
    (hcard : 2 ^ (40 * 3) ≤ X.card)
    (hgp : InGeneralPosition 2 X) :
    Nonempty (PositiveFractionConfiguration 3 X) := by
  let q := X.card / 3
  have hthreeq : 3 * q ≤ X.card := by
    dsimp [q]
    exact Nat.mul_div_le _ _
  obtain ⟨A, hAX, hAcard⟩ :=
    Finset.exists_subset_card_eq (show q ≤ X.card by omega)
  have hq_remA : q ≤ (X \ A).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAX, hAcard]
    omega
  obtain ⟨B, hBremA, hBcard⟩ := Finset.exists_subset_card_eq hq_remA
  have hq_remB : q ≤ ((X \ A) \ B).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBremA, hBcard]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAX, hAcard]
    omega
  obtain ⟨C, hCremB, hCcard⟩ := Finset.exists_subset_card_eq hq_remB
  have hBX : B ⊆ X := hBremA.trans (Finset.sdiff_subset)
  have hCX : C ⊆ X :=
    hCremB.trans (Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    exact (Finset.mem_sdiff.mp (hBremA hzB)).2 hzA
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro z hzA hzC
    have hz := Finset.mem_sdiff.mp
      (Finset.sdiff_subset (hCremB hzC))
    exact hz.2 hzA
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro z hzB hzC
    exact (Finset.mem_sdiff.mp (hCremB hzC)).2 hzB
  let cells : Fin 3 → Finset (Point 2) := ![A, B, C]
  have hcells_subset : ∀ i, cells i ⊆ X := by
    intro i
    fin_cases i
    · simpa [cells] using hAX
    · simpa [cells] using hBX
    · simpa [cells] using hCX
  have hcells_card : ∀ i, (cells i).card = q := by
    intro i
    fin_cases i <;> simp [cells, hAcard, hBcard, hCcard]
  have hcells_disjoint : ∀ ⦃i j⦄, i ≠ j → Disjoint (cells i) (cells j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [cells, hAB, hAC, hBC, Disjoint.symm]
  have hdensity : ∀ i, HasPositiveFractionDensity 3 X (cells i) := by
    intro i
    rw [HasPositiveFractionDensity, hcells_card]
    have hsmall : X.card ≤ 6 * q := by
      have hq : 1 ≤ q := by
        dsimp [q]
        have : 3 ≤ X.card := le_trans (by norm_num) hcard
        omega
      omega
    exact hsmall.trans (Nat.mul_le_mul_right q (by norm_num))
  refine ⟨⟨cells, hcells_subset, hcells_disjoint, hdensity, ?_⟩⟩
  intro p hp
  have hp_injective : Function.Injective p := by
    intro i j hpij
    by_contra hij
    have hd := hcells_disjoint hij
    exact (Finset.disjoint_left.mp hd) (hp i) (hpij.symm ▸ hp j)
  have hsub : Finset.univ.image p ⊆ X := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact hcells_subset i (hp i)
  have himage_card : (Finset.univ.image p).card = 2 + 1 := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · exact hp_injective.injOn
  exact affineIndependent_inConvexPosition (hgp _ hsub himage_card)

/-- The unconditional planar Pór--Valtr positive-fraction theorem. -/
theorem exists_positiveFractionConfiguration
    (k : ℕ) (hk : 3 ≤ k) (X : Finset (Point 2))
    (hcard : 2 ^ (40 * k) ≤ X.card)
    (hgp : InGeneralPosition 2 X) :
    Nonempty (PositiveFractionConfiguration k X) := by
  by_cases hk3 : k = 3
  · subst k
    exact exists_positiveFractionConfiguration_three X hcard hgp
  · have hk4 : 4 ≤ k := by omega
    obtain ⟨C⟩ := exists_strongPositiveFractionConfiguration k hk4 X hcard hgp
    exact ⟨C.toPositiveFractionConfiguration⟩

end

end Erdos651
