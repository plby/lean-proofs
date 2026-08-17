/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Definitions

/-!
# Elementary convex-geometric infrastructure for Erdős Problem 651

This file records exact finite-set facts used repeatedly below: general
and convex position are hereditary, convex position is Mathlib's convex
independence, smaller exact-cardinality subsets can be selected, pointwise
separation certifies convex position, and convex position lifts through an
affine projection that is injective on the selected finite set.
-/

namespace Erdos651

open Affine Function Set

noncomputable section

section Heredity

/-- General position is inherited by a finite subset. -/
theorem InGeneralPosition.mono {d : ℕ} {X Y : Finset (Point d)}
    (hX : InGeneralPosition d X) (hYX : Y ⊆ X) :
    InGeneralPosition d Y := by
  intro S hSY hcard
  exact hX S (hSY.trans hYX) hcard

/-- A set with at most `d` points is automatically in general position. -/
theorem inGeneralPosition_of_card_le {d : ℕ} {X : Finset (Point d)}
    (hcard : X.card ≤ d) : InGeneralPosition d X := by
  intro S hSX hS
  have := Finset.card_le_card hSX
  omega

/-- Convex position is inherited by a finite subset. -/
theorem InConvexPosition.mono {d : ℕ} {X Y : Finset (Point d)}
    (hX : InConvexPosition X) (hYX : Y ⊆ X) : InConvexPosition Y := by
  intro x hxY hxHull
  apply hX x (hYX hxY)
  exact convexHull_mono (by
    intro y hy
    exact Finset.erase_subset_erase x hYX hy) hxHull

/-- The problem's finite-set definition of convex position is exactly
Mathlib's convex independence for the subtype of its points. -/
theorem inConvexPosition_iff_convexIndependent {d : ℕ}
    {X : Finset (Point d)} :
    InConvexPosition X ↔
      ConvexIndependent ℝ (fun x : (X : Set (Point d)) ↦ (x : Point d)) := by
  simpa only [InConvexPosition, Finset.coe_erase, Finset.mem_coe] using
    (convexIndependent_set_iff_notMem_convexHull_sdiff
      (𝕜 := ℝ) (s := (X : Set (Point d)))).symm

/-- The coercion family of a convex-position finset is convex independent. -/
theorem InConvexPosition.convexIndependent {d : ℕ}
    {X : Finset (Point d)} (hX : InConvexPosition X) :
    ConvexIndependent ℝ (fun x : (X : Set (Point d)) ↦ (x : Point d)) :=
  inConvexPosition_iff_convexIndependent.mp hX

/-- Convex independence of the coercion family gives convex position. -/
theorem ConvexIndependent.inConvexPosition {d : ℕ}
    {X : Finset (Point d)}
    (hX : ConvexIndependent ℝ
      (fun x : (X : Set (Point d)) ↦ (x : Point d))) :
    InConvexPosition X :=
  inConvexPosition_iff_convexIndependent.mpr hX

end Heredity

section FiniteSelection

/-- A convex-position set contains a convex-position subset of every
smaller prescribed cardinality. -/
theorem InConvexPosition.exists_subset_card {d m : ℕ}
    {X : Finset (Point d)} (hX : InConvexPosition X) (hm : m ≤ X.card) :
    ∃ Y : Finset (Point d), Y ⊆ X ∧ Y.card = m ∧ InConvexPosition Y := by
  obtain ⟨Y, hYX, hYcard⟩ := Finset.exists_subset_card_eq hm
  exact ⟨Y, hYX, hYcard, hX.mono hYX⟩

/-- A general-position set contains a general-position subset of every
smaller prescribed cardinality. -/
theorem InGeneralPosition.exists_subset_card {d m : ℕ}
    {X : Finset (Point d)} (hX : InGeneralPosition d X) (hm : m ≤ X.card) :
    ∃ Y : Finset (Point d), Y ⊆ X ∧ Y.card = m ∧
      InGeneralPosition d Y := by
  obtain ⟨Y, hYX, hYcard⟩ := Finset.exists_subset_card_eq hm
  exact ⟨Y, hYX, hYcard, hX.mono hYX⟩

/-- Any ambient superset contains every convex subset already present. -/
theorem ContainsConvexSubset.mono_ambient {d n : ℕ}
    {X Z : Finset (Point d)} (hXZ : X ⊆ Z)
    (hX : ContainsConvexSubset d n X) : ContainsConvexSubset d n Z := by
  obtain ⟨Y, hYX, hYcard, hYconv⟩ := hX
  exact ⟨Y, hYX.trans hXZ, hYcard, hYconv⟩

/-- From an `n`-point convex subset one may retain any prescribed number
`m ≤ n` of points. -/
theorem ContainsConvexSubset.mono_card {d m n : ℕ}
    {X : Finset (Point d)} (hmn : m ≤ n)
    (hX : ContainsConvexSubset d n X) : ContainsConvexSubset d m X := by
  obtain ⟨Y, hYX, hYcard, hYconv⟩ := hX
  obtain ⟨Z, hZY, hZcard, hZconv⟩ :=
    hYconv.exists_subset_card (hYcard ▸ hmn)
  exact ⟨Z, hZY.trans hYX, hZcard, hZconv⟩

/-- A convex-position ambient set itself supplies every smaller convex
subset requested by `ContainsConvexSubset`. -/
theorem InConvexPosition.containsConvexSubset {d n : ℕ}
    {X : Finset (Point d)} (hX : InConvexPosition X) (hn : n ≤ X.card) :
    ContainsConvexSubset d n X := by
  exact hX.exists_subset_card hn

/-- Cardinality is a necessary condition for containing an `n`-point
convex subset. -/
theorem ContainsConvexSubset.card_le {d n : ℕ} {X : Finset (Point d)}
    (hX : ContainsConvexSubset d n X) : n ≤ X.card := by
  obtain ⟨Y, hYX, hYcard, -⟩ := hX
  simpa only [hYcard] using Finset.card_le_card hYX

/-- Forcing convex `n`-subsets also forces convex `m`-subsets for `m ≤ n`. -/
theorem ForcesConvexSubset.mono_card {d m n N : ℕ} (hmn : m ≤ n)
    (hN : ForcesConvexSubset d n N) : ForcesConvexSubset d m N := by
  intro X hcard hgp
  exact (hN X hcard hgp).mono_card hmn

end FiniteSelection

section ConvexCertificates

/-- A pointwise family of convex supersets of the other points certifies
convex position. -/
theorem inConvexPosition_of_convex_separators {d : ℕ}
    {X : Finset (Point d)}
    (hsep : ∀ x ∈ X, ∃ C : Set (Point d),
      Convex ℝ C ∧ (↑(X.erase x) : Set (Point d)) ⊆ C ∧ x ∉ C) :
    InConvexPosition X := by
  intro x hxX hxHull
  obtain ⟨C, hCconv, herase, hxC⟩ := hsep x hxX
  exact hxC (convexHull_min herase hCconv hxHull)

/-- Strict exposure of each point by a linear functional certifies convex
position. -/
theorem inConvexPosition_of_strictly_exposed {d : ℕ}
    {X : Finset (Point d)}
    (hexpose : ∀ x ∈ X, ∃ ℓ : Point d →ₗ[ℝ] ℝ,
      ∀ y ∈ X, y ≠ x → ℓ y < ℓ x) :
    InConvexPosition X := by
  apply inConvexPosition_of_convex_separators
  intro x hxX
  obtain ⟨ℓ, hℓ⟩ := hexpose x hxX
  refine ⟨ℓ ⁻¹' Set.Iio (ℓ x), ?_, ?_, ?_⟩
  · exact (convex_Iio (ℓ x)).linear_preimage ℓ
  · intro y hy
    exact hℓ y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)
  · simp

/-- A two-block union is in convex position whenever every point of the
union has a strict exposing functional against all the other points. -/
theorem inConvexPosition_union_of_strictly_exposed {d : ℕ}
    {X Y : Finset (Point d)}
    (hexpose : ∀ x ∈ X ∪ Y, ∃ ℓ : Point d →ₗ[ℝ] ℝ,
      ∀ y ∈ X ∪ Y, y ≠ x → ℓ y < ℓ x) :
    InConvexPosition (X ∪ Y) :=
  inConvexPosition_of_strictly_exposed hexpose

/-- Extreme-point certificates for all members of a finite set imply
convex position. -/
theorem inConvexPosition_of_extremePoints {d : ℕ}
    {X : Finset (Point d)}
    (hextreme : ∀ x ∈ X,
      x ∈ (convexHull ℝ (X : Set (Point d))).extremePoints ℝ) :
    InConvexPosition X := by
  apply inConvexPosition_of_convex_separators
  intro x hxX
  let K : Set (Point d) := convexHull ℝ (X : Set (Point d))
  have hxext : x ∈ K.extremePoints ℝ := hextreme x hxX
  have hKconv : Convex ℝ K := convex_convexHull ℝ _
  have hremove : Convex ℝ (K \ {x}) :=
    (hKconv.mem_extremePoints_iff_convex_sdiff.mp hxext).2
  refine ⟨K \ {x}, hremove, ?_, ?_⟩
  · intro y hy
    have hyX : y ∈ (X : Set (Point d)) := Finset.mem_of_mem_erase hy
    refine ⟨subset_convexHull ℝ _ hyX, ?_⟩
    exact Finset.ne_of_mem_erase hy
  · exact fun hx ↦ hx.2 rfl

end ConvexCertificates

section AffineTransport

variable {d e : ℕ}

/-- Erasing commutes with the image of a finset when the map is injective
on that finset.  The library's global-injectivity version is too strong for
projections, which are only required to separate the selected points. -/
theorem finset_image_erase_of_injOn {X : Finset (Point d)}
    (f : Point d → Point e) (hf : Set.InjOn f X) {x : Point d} (hx : x ∈ X) :
    (X.erase x).image f = (X.image f).erase (f x) := by
  ext z
  constructor
  · simp only [Finset.mem_image, Finset.mem_erase]
    rintro ⟨y, ⟨hyx, hyX⟩, rfl⟩
    refine ⟨?_, ⟨y, hyX, rfl⟩⟩
    exact fun h ↦ hyx (hf hyX hx h)
  · simp only [Finset.mem_image, Finset.mem_erase]
    rintro ⟨hfy, ⟨y, hyX, rfl⟩⟩
    exact ⟨y, ⟨fun hyx ↦ hfy (congrArg f hyx), hyX⟩, rfl⟩

/-- Affine maps commute exactly with the convex hull of a finset. -/
theorem AffineMap.image_convexHull_finset (f : Point d →ᵃ[ℝ] Point e)
    (X : Finset (Point d)) :
    f '' convexHull ℝ (X : Set (Point d)) =
      convexHull ℝ (f '' (X : Set (Point d))) :=
  f.image_convexHull _

/-- Convex position lifts through an affine projection, provided distinct
selected points have distinct images. -/
theorem InConvexPosition.of_image_affineMap {X : Finset (Point d)}
    (f : Point d →ᵃ[ℝ] Point e) (hf : Set.InjOn f X)
    (himage : InConvexPosition (X.image f)) : InConvexPosition X := by
  intro x hxX hxHull
  apply himage (f x) (Finset.mem_image_of_mem f hxX)
  rw [← finset_image_erase_of_injOn f hf hxX,
    Finset.coe_image, ← f.image_convexHull]
  exact ⟨x, hxHull, rfl⟩

/-- A globally injective affine map preserves convex position. -/
theorem InConvexPosition.image_affineMap {X : Finset (Point d)}
    (hX : InConvexPosition X) (f : Point d →ᵃ[ℝ] Point e)
    (hf : Function.Injective f) : InConvexPosition (X.image f) := by
  intro z hzImage hzHull
  obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.mp hzImage
  apply hX x hxX
  rw [← Finset.image_erase hf X x, Finset.coe_image,
    ← f.image_convexHull] at hzHull
  obtain ⟨y, hyHull, hyx⟩ := hzHull
  simpa only [hf hyx] using hyHull

/-- Affine equivalences preserve convex position in both directions. -/
theorem AffineEquiv.inConvexPosition_image_iff
    (f : Point d ≃ᵃ[ℝ] Point e) (X : Finset (Point d)) :
    InConvexPosition (X.image f) ↔ InConvexPosition X := by
  constructor
  · exact fun h ↦ h.of_image_affineMap f.toAffineMap f.injective.injOn
  · exact fun h ↦ h.image_affineMap f.toAffineMap f.injective

/-- If the image of a finite set is in general position, then so is the
original set. -/
theorem InGeneralPosition.of_image_affineMap {X : Finset (Point d)}
    (f : Point d →ᵃ[ℝ] Point d) (hf : Set.InjOn f X)
    (himage : InGeneralPosition d (X.image f)) : InGeneralPosition d X := by
  intro S hSX hScard
  have hfS : Set.InjOn f S := hf.mono (by
    intro x hx
    exact hSX hx)
  have hsub : S.image f ⊆ X.image f := by
    intro z hz
    obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image_of_mem f (hSX hsS)
  have hcard : (S.image f).card = d + 1 := by
    rw [Finset.card_image_of_injOn hfS, hScard]
  have hAI := himage (S.image f) hsub hcard
  let emb : S ↪ (S.image f : Set (Point d)) :=
    ⟨fun x ↦ ⟨f x, Finset.mem_image_of_mem f x.property⟩,
      fun x y hxy ↦ Subtype.ext
        (hfS x.property y.property (Subtype.ext_iff.mp hxy))⟩
  have hcomp := hAI.comp_embedding emb
  have heq :
      ((fun p : (S.image f : Set (Point d)) ↦ (p : Point d)) ∘ emb) =
        (f ∘ fun p : S ↦ (p : Point d)) := by
    funext p
    rfl
  have hmapped : AffineIndependent ℝ
      (f ∘ fun p : S ↦ (p : Point d)) := heq ▸ hcomp
  exact AffineIndependent.of_comp f hmapped

end AffineTransport

section OrientationRamsey

/-- Signed volume of an ordered tetrahedron in `Point 3`. -/
noncomputable def orientedVolume3 (a b c d : Point 3) : ℝ :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![b - a, c - a, d - a]

private theorem det3_sub_zero (x y z w : Point 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![x - y, z, w] =
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![x, z, w] -
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![y, z, w] := by
  let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
  have h := D.map_update_sub (v' := ![0, z, w]) (0 : Fin 3) x y
  have h₀ : Function.update ![0, z, w] (0 : Fin 3) (x - y) = ![x - y, z, w] := by
    funext i
    fin_cases i <;> rfl
  have h₁ : Function.update ![0, z, w] (0 : Fin 3) x = ![x, z, w] := by
    funext i
    fin_cases i <;> rfl
  have h₂ : Function.update ![0, z, w] (0 : Fin 3) y = ![y, z, w] := by
    funext i
    fin_cases i <;> rfl
  simpa only [h₀, h₁, h₂] using h

private theorem det3_sub_one (x y z w : Point 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![z, x - y, w] =
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![z, x, w] -
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![z, y, w] := by
  let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
  have h := D.map_update_sub (v' := ![z, 0, w]) (1 : Fin 3) x y
  have h₀ : Function.update ![z, 0, w] (1 : Fin 3) (x - y) = ![z, x - y, w] := by
    funext i
    fin_cases i <;> rfl
  have h₁ : Function.update ![z, 0, w] (1 : Fin 3) x = ![z, x, w] := by
    funext i
    fin_cases i <;> rfl
  have h₂ : Function.update ![z, 0, w] (1 : Fin 3) y = ![z, y, w] := by
    funext i
    fin_cases i <;> rfl
  simpa only [h₀, h₁, h₂] using h

private theorem det3_neg_two (x y z : Point 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![x, y, -z] =
      -(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![x, y, z] := by
  let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
  have h := D.map_update_neg (v' := ![x, y, 0]) (2 : Fin 3) z
  have h₀ : Function.update ![x, y, 0] (2 : Fin 3) (-z) = ![x, y, -z] := by
    funext i
    fin_cases i <;> rfl
  have h₁ : Function.update ![x, y, 0] (2 : Fin 3) z = ![x, y, z] := by
    funext i
    fin_cases i <;> rfl
  simpa only [h₀, h₁] using h

private theorem det3_sub_two (x y z w : Point 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![z, w, x - y] =
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![z, w, x] -
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![z, w, y] := by
  let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
  have h := D.map_update_sub (v' := ![z, w, 0]) (2 : Fin 3) x y
  have h₀ : Function.update ![z, w, 0] (2 : Fin 3) (x - y) = ![z, w, x - y] := by
    funext i
    fin_cases i <;> rfl
  have h₁ : Function.update ![z, w, 0] (2 : Fin 3) x = ![z, w, x] := by
    funext i
    fin_cases i <;> rfl
  have h₂ : Function.update ![z, w, 0] (2 : Fin 3) y = ![z, w, y] := by
    funext i
    fin_cases i <;> rfl
  simpa only [h₀, h₁, h₂] using h

/-- The linear functional whose level hyperplane passes through `a,b,c`. -/
noncomputable def facetFunctional3 (a b c : Point 3) : Point 3 →ₗ[ℝ] ℝ where
  toFun x := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![b - a, c - a, x]
  map_add' x y := by
    let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
    have h := D.map_update_add (v := ![b - a, c - a, 0]) (2 : Fin 3) x y
    have h₀ : Function.update ![b - a, c - a, 0] (2 : Fin 3) (x + y) =
        ![b - a, c - a, x + y] := by funext i; fin_cases i <;> rfl
    have h₁ : Function.update ![b - a, c - a, 0] (2 : Fin 3) x =
        ![b - a, c - a, x] := by funext i; fin_cases i <;> rfl
    have h₂ : Function.update ![b - a, c - a, 0] (2 : Fin 3) y =
        ![b - a, c - a, y] := by funext i; fin_cases i <;> rfl
    simpa only [h₀, h₁, h₂] using h
  map_smul' r x := by
    let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
    have h := D.map_update_smul (v := ![b - a, c - a, 0]) (2 : Fin 3) r x
    have h₀ : Function.update ![b - a, c - a, 0] (2 : Fin 3) (r • x) =
        ![b - a, c - a, r • x] := by funext i; fin_cases i <;> rfl
    have h₁ : Function.update ![b - a, c - a, 0] (2 : Fin 3) x =
        ![b - a, c - a, x] := by funext i; fin_cases i <;> rfl
    simpa only [h₀, h₁, RingHom.id_apply] using h

theorem facetFunctional3_sub (a b c x y : Point 3) :
    facetFunctional3 a b c x - facetFunctional3 a b c y =
      orientedVolume3 a b c (x - y + a) := by
  change (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![b - a, c - a, x] -
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![b - a, c - a, y] =
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
          ![b - a, c - a, x - y + a - a]
  rw [show x - y + a - a = x - y by module, det3_sub_two]

theorem orientedVolume3_rotate (a b c d : Point 3) :
    orientedVolume3 b c d a = -orientedVolume3 a b c d := by
  dsimp only [orientedVolume3]
  let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
  let u := b - a
  let v := c - a
  let w := d - a
  have hcb : c - b = v - u := by simp only [u, v]; module
  have hdb : d - b = w - u := by simp only [u, w]; module
  have hab : a - b = -u := by simp only [u]; module
  have hvuu : D ![v, u, u] = 0 :=
    D.map_eq_zero_of_eq _ (i := (1 : Fin 3)) (j := (2 : Fin 3)) rfl (by decide)
  have huwu : D ![u, w, u] = 0 :=
    D.map_eq_zero_of_eq _ (i := (0 : Fin 3)) (j := (2 : Fin 3)) rfl (by decide)
  have huuu : D ![u, u, u] = 0 :=
    D.map_eq_zero_of_eq _ (i := (0 : Fin 3)) (j := (1 : Fin 3)) rfl (by decide)
  have hcycle : D ![v, w, u] = D ![u, v, w] := by
    have h₁ := D.map_swap (v := ![u, v, w])
      (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
    have hs₁ : (![u, v, w] ∘ Equiv.swap (0 : Fin 3) 1) = ![v, u, w] := by
      funext i
      fin_cases i <;> rfl
    rw [hs₁] at h₁
    have h₂ := D.map_swap (v := ![v, u, w])
      (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide)
    have hs₂ : (![v, u, w] ∘ Equiv.swap (1 : Fin 3) 2) = ![v, w, u] := by
      funext i
      fin_cases i <;> rfl
    rw [hs₂] at h₂
    rw [h₂, h₁, neg_neg]
  rw [hcb, hdb, hab]
  calc
    D ![v - u, w - u, -u] =
        D ![v, w - u, -u] - D ![u, w - u, -u] := det3_sub_zero _ _ _ _
    _ = (D ![v, w, -u] - D ![v, u, -u]) -
        (D ![u, w, -u] - D ![u, u, -u]) := by
          exact congrArg₂ (fun r s : ℝ ↦ r - s)
            (det3_sub_one w u v (-u)) (det3_sub_one w u u (-u))
    _ = (-D ![v, w, u] - -D ![v, u, u]) -
        (-D ![u, w, u] - -D ![u, u, u]) := by
          exact congrArg₂ (fun r s : ℝ ↦ r - s)
            (congrArg₂ (fun r s : ℝ ↦ r - s)
              (det3_neg_two v w u) (det3_neg_two v u u))
            (congrArg₂ (fun r s : ℝ ↦ r - s)
              (det3_neg_two u w u) (det3_neg_two u u u))
    _ = -D ![u, v, w] := by rw [hvuu, huwu, huuu, hcycle]; ring

theorem orientedVolume3_cycle_last (a b c d : Point 3) :
    orientedVolume3 a c d b = orientedVolume3 a b c d := by
  let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
  have h₁ : D ![c - a, b - a, d - a] = -D ![b - a, c - a, d - a] := by
    have h := D.map_swap (v := ![b - a, c - a, d - a])
      (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
    have hv : (![b - a, c - a, d - a] ∘ Equiv.swap (0 : Fin 3) 1) =
        ![c - a, b - a, d - a] := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at h
    exact h
  have h₂ : D ![c - a, d - a, b - a] = -D ![c - a, b - a, d - a] := by
    have h := D.map_swap (v := ![c - a, b - a, d - a])
      (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide)
    have hv : (![c - a, b - a, d - a] ∘ Equiv.swap (1 : Fin 3) 2) =
        ![c - a, d - a, b - a] := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at h
    exact h
  dsimp only [orientedVolume3]
  rw [h₂, h₁, neg_neg]

theorem orientedVolume3_swap_last (a b c d : Point 3) :
    orientedVolume3 a b d c = -orientedVolume3 a b c d := by
  let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
  have h := D.map_swap (v := ![b - a, c - a, d - a])
    (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  have hv : (![b - a, c - a, d - a] ∘ Equiv.swap (1 : Fin 3) 2) =
      ![b - a, d - a, c - a] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  exact h

theorem facetFunctional3_sub_base (a b c x : Point 3) :
    facetFunctional3 a b c x - facetFunctional3 a b c a =
      orientedVolume3 a b c x := by
  rw [facetFunctional3_sub]
  congr 1
  module

@[simp] theorem facetFunctional3_apply_second (a b c : Point 3) :
    facetFunctional3 a b c b = facetFunctional3 a b c a := by
  rw [← sub_eq_zero, facetFunctional3_sub_base]
  dsimp only [orientedVolume3]
  let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
  exact D.map_eq_zero_of_eq _ (i := (0 : Fin 3)) (j := 2) rfl (by decide)

@[simp] theorem facetFunctional3_apply_third (a b c : Point 3) :
    facetFunctional3 a b c c = facetFunctional3 a b c a := by
  rw [← sub_eq_zero, facetFunctional3_sub_base]
  dsimp only [orientedVolume3]
  let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
  exact D.map_eq_zero_of_eq _ (i := (1 : Fin 3)) (j := 2) rfl (by decide)

/-- All increasing quadruples of a finite ordered sequence have positive
signed volume. -/
def UniformPositiveOrientation (m : ℕ) (p : ℕ → Point 3) : Prop :=
  ∀ i j k l, i < j → j < k → k < l → l < m →
    0 < orientedVolume3 (p i) (p j) (p k) (p l)

theorem leftFacet_strict {m : ℕ} {p : ℕ → Point 3}
    (hor : UniformPositiveOrientation m p) {q r : ℕ}
    (hq : 0 < q) (hq' : q + 1 < m) (hr : r < m)
    (hr0 : r ≠ 0) (hrq : r ≠ q) (hrq1 : r ≠ q + 1) :
    facetFunctional3 (p 0) (p q) (p (q + 1)) (p 0) <
      facetFunctional3 (p 0) (p q) (p (q + 1)) (p r) := by
  rw [← sub_pos, facetFunctional3_sub_base]
  by_cases hrq' : r < q
  · rw [orientedVolume3_cycle_last]
    exact hor 0 r q (q + 1) (by omega) hrq' (by omega) hq'
  · exact hor 0 q (q + 1) r hq (by omega) (by omega) hr

theorem leftFacet_weak {m : ℕ} {p : ℕ → Point 3}
    (hor : UniformPositiveOrientation m p) {q r : ℕ}
    (hq : 0 < q) (hq' : q + 1 < m) (hr : r < m) :
    facetFunctional3 (p 0) (p q) (p (q + 1)) (p 0) ≤
      facetFunctional3 (p 0) (p q) (p (q + 1)) (p r) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact le_rfl
  rcases eq_or_ne r q with rfl | hrq
  · rw [← sub_nonneg, facetFunctional3_sub_base]
    dsimp only [orientedVolume3]
    let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
    exact le_of_eq (D.map_eq_zero_of_eq _ (i := (0 : Fin 3)) (j := 2)
      rfl (by decide)).symm
  rcases eq_or_ne r (q + 1) with rfl | hrq1
  · rw [← sub_nonneg, facetFunctional3_sub_base]
    dsimp only [orientedVolume3]
    let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
    exact le_of_eq (D.map_eq_zero_of_eq _ (i := (1 : Fin 3)) (j := 2)
      rfl (by decide)).symm
  · exact (leftFacet_strict hor hq hq' hr hr0 hrq hrq1).le

theorem rightFacet_strict {m : ℕ} {p : ℕ → Point 3}
    (hor : UniformPositiveOrientation m p) {q r : ℕ}
    (hq' : q + 1 < m - 1) (hm : 1 < m) (hr : r < m)
    (hrq : r ≠ q) (hrq1 : r ≠ q + 1) (hrlast : r ≠ m - 1) :
    facetFunctional3 (p q) (p (q + 1)) (p (m - 1)) (p r) <
      facetFunctional3 (p q) (p (q + 1)) (p (m - 1)) (p q) := by
  rw [← sub_neg, facetFunctional3_sub_base]
  by_cases hrq' : r < q
  · rw [orientedVolume3_rotate]
    exact neg_lt_zero.mpr (hor r q (q + 1) (m - 1) hrq' (by omega)
      (by omega) (by omega))
  · rw [orientedVolume3_swap_last]
    exact neg_lt_zero.mpr (hor q (q + 1) r (m - 1) (by omega) (by omega)
      (by omega) (by omega))

theorem rightFacet_weak {m : ℕ} {p : ℕ → Point 3}
    (hor : UniformPositiveOrientation m p) {q r : ℕ}
    (hq' : q + 1 < m - 1) (hm : 1 < m) (hr : r < m) :
    facetFunctional3 (p q) (p (q + 1)) (p (m - 1)) (p r) ≤
      facetFunctional3 (p q) (p (q + 1)) (p (m - 1)) (p q) := by
  rcases eq_or_ne r q with rfl | hrq
  · exact le_rfl
  rcases eq_or_ne r (q + 1) with rfl | hrq1
  · rw [← sub_nonpos, facetFunctional3_sub_base]
    dsimp only [orientedVolume3]
    let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
    exact le_of_eq (D.map_eq_zero_of_eq _ (i := (0 : Fin 3)) (j := 2) rfl (by decide))
  rcases eq_or_ne r (m - 1) with rfl | hrlast
  · rw [← sub_nonpos, facetFunctional3_sub_base]
    dsimp only [orientedVolume3]
    let D := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
    exact le_of_eq (D.map_eq_zero_of_eq _ (i := (1 : Fin 3)) (j := 2) rfl (by decide))
  · exact (rightFacet_strict hor hq' hm hr hrq hrq1 hrlast).le

end OrientationRamsey

section GenericPlaneProjection

/-- In a 3-dimensional general-position set with at least four points,
every subset of at most three points is affine-independent.  The
cardinality hypothesis is necessary because `InGeneralPosition 3` only
directly constrains four-point subsets. -/
theorem affineIndependent_of_card_le_three_of_generalPosition_three
    {X S : Finset (Point 3)} (hgp : InGeneralPosition 3 X) (hXcard : 4 ≤ X.card)
    (hSX : S ⊆ X) (hScard : S.card ≤ 3) :
    AffineIndependent ℝ (fun p : S ↦ (p : Point 3)) := by
  obtain ⟨T, hST, hTX, hTcard⟩ :=
    Finset.exists_subsuperset_card_eq hSX (by omega : S.card ≤ 4) hXcard
  have hT : AffineIndependent ℝ (fun p : T ↦ (p : Point 3)) := by
    apply hgp T hTX
    norm_num
    exact hTcard
  exact hT.mono (by
    intro p hp
    exact hST hp)

/-- A finite 3-dimensional general-position set with at least four
points admits a generic affine projection to the plane which is injective
on the set and whose image is again in general position. -/
theorem exists_generic_plane_projection
    {X : Finset (Point 3)} (hgp : InGeneralPosition 3 X) (hXcard : 4 ≤ X.card) :
    ∃ π : Point 3 →ᵃ[ℝ] Point 2,
      Set.InjOn π X ∧ InGeneralPosition 2 (X.image π) := by
  classical
  let I := (X.powerset.filter fun S ↦ S.card ≤ 3)
  let bad : I → Submodule ℝ (Point 3) := fun S ↦ vectorSpan ℝ (S.1 : Set (Point 3))
  have hbad : ∀ S : I, bad S ≠ ⊤ := by
    intro S htop
    have hSX : S.1 ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp S.2).1
    have hScard : S.1.card ≤ 3 := (Finset.mem_filter.mp S.2).2
    have hAI := affineIndependent_of_card_le_three_of_generalPosition_three
      hgp hXcard hSX hScard
    by_cases hSne : S.1.Nonempty
    · letI : Nonempty S.1 := Finset.nonempty_coe_sort.mpr hSne
      have hfin := hAI.finrank_vectorSpan_add_one
      have hrange : Set.range (fun p : S.1 ↦ (p : Point 3)) = (S.1 : Set (Point 3)) := by
        ext x
        simp
      rw [hrange] at hfin
      change vectorSpan ℝ (S.1 : Set (Point 3)) = ⊤ at htop
      rw [htop] at hfin
      have hdim : Module.finrank ℝ (Point 3) = 3 := by simp [Point]
      rw [finrank_top, hdim, Fintype.card_coe] at hfin
      omega
    · have hSempty : S.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      simpa [bad, hSempty] using htop
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  have hv0 : v ≠ 0 := by
    intro hvzero
    subst v
    let E : I := ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset X, by simp⟩⟩
    exact hv E (by simp [bad])
  let K : Submodule ℝ (Point 3) := ℝ ∙ v
  have hKfin : Module.finrank ℝ K = 1 := by
    exact finrank_span_singleton hv0
  have hQfin : Module.finrank ℝ (Point 3 ⧸ K) = 2 := by
    have hdim := K.finrank_quotient_add_finrank
    rw [hKfin] at hdim
    have hPdim : Module.finrank ℝ (Point 3) = 3 := by simp [Point]
    omega
  let e : (Point 3 ⧸ K) ≃ₗ[ℝ] Point 2 := LinearEquiv.ofFinrankEq _ _ (by
    rw [hQfin]
    simp [Point])
  let L : Point 3 →ₗ[ℝ] Point 2 := e.toLinearMap.comp K.mkQ
  let π : Point 3 →ᵃ[ℝ] Point 2 := L.toAffineMap
  have hker : LinearMap.ker L = K := by
    ext z
    simp [L, K]
  have hpreserve (S : Finset (Point 3)) (hSX : S ⊆ X) (hScard : S.card ≤ 3) :
      AffineIndependent ℝ (fun z : S ↦ π (z : Point 3)) := by
    have hAI := affineIndependent_of_card_le_three_of_generalPosition_three
      hgp hXcard hSX hScard
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst S
      exact affineIndependent_of_subsingleton ℝ _
    letI : Nonempty S := Finset.nonempty_coe_sort.mpr hS
    let a : S := ⟨hS.choose, hS.choose_spec⟩
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ a] at hAI ⊢
    simp_rw [← π.linearMap_vsub]
    apply hAI.map
    rw [show LinearMap.ker π.linear = K by simpa [π] using hker]
    have hspan_le :
        Submodule.span ℝ
            (Set.range (fun z : {z : S // z ≠ a} ↦ (z.1 : Point 3) -ᵥ (a : Point 3))) ≤
          vectorSpan ℝ (S : Set (Point 3)) := by
      rw [Submodule.span_le]
      rintro w ⟨z, rfl⟩
      exact vsub_mem_vectorSpan ℝ z.1.2 a.2
    let SS : I := ⟨S, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hSX, hScard⟩⟩
    have hvS : v ∉ vectorSpan ℝ (S : Set (Point 3)) := by
      simpa [bad] using hv SS
    exact Disjoint.mono_left hspan_le
      (Submodule.disjoint_span_singleton_of_notMem hvS)
  have hπinj : Set.InjOn π X := by
    intro x hx y hy hxy
    by_contra hne
    let S : Finset (Point 3) := {x, y}
    have hSX : S ⊆ X := by
      intro z hz
      have hz' : z = x ∨ z = y := by simpa [S] using hz
      rcases hz' with rfl | rfl
      · simpa using hx
      · simpa using hy
    have hScard : S.card ≤ 3 := by
      calc
        S.card ≤ ({y} : Finset (Point 3)).card + 1 := by
          simpa [S] using Finset.card_insert_le x ({y} : Finset (Point 3))
        _ ≤ 3 := by simp
    have hAI := hpreserve S hSX hScard
    have hxyS : x ∈ S := by simp [S]
    have hyyS : y ∈ S := by simp [S]
    exact hAI.injective (show π (⟨x, hxyS⟩ : S) = π (⟨y, hyyS⟩ : S) by exact hxy)
      |> fun h ↦ hne (congrArg Subtype.val h)
  refine ⟨π, hπinj, ?_⟩
  intro T hTsub hTcard
  let S : Finset (Point 3) := X.filter fun x ↦ π x ∈ T
  have hSX : S ⊆ X := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hImage : S.image π = T := by
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hx).2
    · intro y hy
      have hyImage := hTsub hy
      obtain ⟨x, hxX, hxy⟩ := Finset.mem_image.mp hyImage
      subst y
      exact Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hxX, hy⟩, rfl⟩
  have hπinjS : Set.InjOn π S := hπinj.mono hSX
  have hScard : S.card = 3 := by
    calc
      S.card = (S.image π).card := (Finset.card_image_of_injOn hπinjS).symm
      _ = T.card := congrArg Finset.card hImage
      _ = 3 := by omega
  have hAIS := hpreserve S hSX (by omega)
  have hpreExists (y : T) : ∃ x ∈ S, π x = (y : Point 2) := by
    have hy : (y : Point 2) ∈ S.image π := by
      rw [hImage]
      exact y.2
    exact Finset.mem_image.mp hy
  choose pre hpreS hpre using hpreExists
  let emb : T ↪ S :=
    ⟨fun y ↦ ⟨pre y, hpreS y⟩, fun y z hyz ↦ Subtype.ext (by
      calc
        (y : Point 2) = π (pre y) := (hpre y).symm
        _ = π (pre z) :=
          congrArg π (congrArg Subtype.val hyz)
        _ = (z : Point 2) := hpre z)⟩
  have hemb : (fun z : S ↦ π (z : Point 3)) ∘ emb =
      (fun z : T ↦ (z : Point 2)) := by
    funext y
    exact hpre y
  rw [← hemb]
  exact hAIS.comp_embedding emb

end GenericPlaneProjection

end

end Erdos651
