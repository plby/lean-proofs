import ErdosProblems.Erdos117.Symplectic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

/-!
# Splitting alternating forms into hyperbolic planes

The construction works in characteristic two as well as in odd characteristic.
It supplies the normal-form input needed for the spread and scalar-clique
constructions.
-/

namespace Erdos117

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def hyperbolicPlaneMap (e f : V) : (K × K) →ₗ[K] V :=
  (LinearMap.toSpanSingleton K V e).coprod (LinearMap.toSpanSingleton K V f)

@[simp] theorem hyperbolicPlaneMap_apply (e f : V) (a : K × K) :
    hyperbolicPlaneMap e f a = a.1 • e + a.2 • f := rfl

theorem hyperbolicPlaneMap_pairing (B : LinearMap.BilinForm K V) (halt : B.IsAlt)
    {e f : V} (hef : B e f = 1) (a b : K × K) :
    B (hyperbolicPlaneMap e f a) (hyperbolicPlaneMap e f b) = a.1 * b.2 - a.2 * b.1 := by
  have hfe : B f e = -1 := by rw [← halt.neg_eq, hef]
  simp only [hyperbolicPlaneMap_apply, map_add, map_smul, smul_eq_mul,
    LinearMap.add_apply, LinearMap.smul_apply, halt e, halt f, hef, hfe]
  ring

theorem hyperbolicPlaneMap_injective (B : LinearMap.BilinForm K V) (halt : B.IsAlt)
    {e f : V} (hef : B e f = 1) : Function.Injective (hyperbolicPlaneMap (K := K) e f) := by
  intro a b hab
  have h₁ := congrArg (fun x => B x (hyperbolicPlaneMap (K := K) e f (0, 1))) hab
  have h₂ := congrArg (fun x => B x (hyperbolicPlaneMap (K := K) e f (1, 0))) hab
  simp only [hyperbolicPlaneMap_pairing B halt hef, mul_one, mul_zero, sub_zero,
    zero_sub, neg_inj] at h₁ h₂
  exact Prod.ext h₁ h₂

theorem hyperbolicPlaneMap_range_nondegenerate (B : LinearMap.BilinForm K V)
    (halt : B.IsAlt) {e f : V} (hef : B e f = 1) :
    (B.restrict (hyperbolicPlaneMap (K := K) e f).range).Nondegenerate := by
  have hAlt : (B.restrict (hyperbolicPlaneMap (K := K) e f).range).IsAlt := fun x => halt x
  apply hAlt.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  obtain ⟨a, ha⟩ := x.2
  have hz (b : K × K) : B (hyperbolicPlaneMap e f a) (hyperbolicPlaneMap e f b) = 0 := by
    rw [ha]
    exact hx ⟨_, LinearMap.mem_range_self _ b⟩
  have h₁ := hz (0, 1)
  have h₂ := hz (1, 0)
  simp only [hyperbolicPlaneMap_pairing B halt hef, mul_one, mul_zero, sub_zero,
    zero_sub, neg_eq_zero] at h₁ h₂
  have ha0 : a = 0 := Prod.ext h₁ h₂
  apply Subtype.ext
  rw [← ha, ha0, map_zero]
  rfl

variable [FiniteDimensional K V]

theorem exists_hyperbolic_pair (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hV : 0 < finrank K V) : ∃ e f : V, B e f = 1 := by
  classical
  have : Nontrivial V := finrank_pos_iff.mp hV
  obtain ⟨e, he⟩ := exists_ne (0 : V)
  obtain ⟨f, hf⟩ : ∃ f : V, B e f ≠ 0 := by
    by_contra h
    push Not at h
    exact he (hB.1 e h)
  refine ⟨e, (B e f)⁻¹ • f, ?_⟩
  simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hf]

/-- Splitting off a hyperbolic plane leaves a nondegenerate alternating form
whose dimension is exactly two smaller. -/
theorem exists_hyperbolic_complement (B : LinearMap.BilinForm K V)
    (halt : B.IsAlt) (hB : B.Nondegenerate) (hV : 0 < finrank K V) :
    ∃ e f : V, B e f = 1 ∧
      let P := (hyperbolicPlaneMap (K := K) e f).range
      IsCompl P (B.orthogonal P) ∧ (B.restrict (B.orthogonal P)).Nondegenerate ∧
        finrank K P = 2 ∧ finrank K (B.orthogonal P) + 2 = finrank K V := by
  obtain ⟨e, f, hef⟩ := exists_hyperbolic_pair B hB hV
  let P := (hyperbolicPlaneMap (K := K) e f).range
  have hP := hyperbolicPlaneMap_range_nondegenerate B halt hef
  have hcompl : IsCompl P (B.orthogonal P) :=
    B.isCompl_orthogonal_of_restrict_nondegenerate halt.isRefl hP
  have horth : (B.restrict (B.orthogonal P)).Nondegenerate := by
    apply B.nondegenerate_restrict_of_disjoint_orthogonal halt.isRefl
    rw [B.orthogonal_orthogonal hB halt.isRefl]
    exact hcompl.disjoint.symm
  have hdim : finrank K P = 2 := by
    rw [LinearMap.finrank_range_of_inj (hyperbolicPlaneMap_injective B halt hef)]
    simp
  refine ⟨e, f, hef, hcompl, horth, hdim, ?_⟩
  have hle := Submodule.finrank_le P
  rw [B.finrank_orthogonal hB, hdim]
  omega

theorem even_finrank_of_nondegenerate_alt (B : LinearMap.BilinForm K V)
    (halt : B.IsAlt) (hB : B.Nondegenerate) : Even (finrank K V) := by
  generalize hd : finrank K V = d
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
    by_cases hd0 : d = 0
    · simp [hd0]
    have hpos : 0 < finrank K V := by omega
    obtain ⟨e, f, hef, hcompl, horth, hdim, hdimQ⟩ :=
      exists_hyperbolic_complement B halt hB hpos
    let P := (hyperbolicPlaneMap (K := K) e f).range
    let Q := B.orthogonal P
    have hQlt : finrank K Q < d := by dsimp [Q, P]; omega
    have hEven : Even (finrank K Q) :=
      ih (finrank K Q) hQlt (B.restrict Q) (fun x => halt x) horth rfl
    obtain ⟨m, hm⟩ := hEven
    exact ⟨m + 1, by dsimp [Q, P] at hm; omega⟩

omit [FiniteDimensional K V] in
theorem pairing_add_orthogonal (B : LinearMap.BilinForm K V) (hrefl : B.IsRefl)
    (P : Submodule K V) (x y : P × B.orthogonal P) :
    B ((x.1 : V) + x.2) ((y.1 : V) + y.2) =
      B (x.1 : V) (y.1 : V) + B (x.2 : V) (y.2 : V) := by
  have h₁ : B (x.1 : V) (y.2 : V) = 0 := y.2.2 x.1 x.1.2
  have h₂ : B (x.2 : V) (y.1 : V) = 0 := hrefl _ _ (x.2.2 y.1 y.1.2)
  simp only [map_add, LinearMap.add_apply, h₁, h₂, add_zero, zero_add]

variable {W : Type*} [AddCommGroup W] [Module K W]

omit [FiniteDimensional K V] in
theorem hyperbolic_planes_isometric (B : LinearMap.BilinForm K V)
    (C : LinearMap.BilinForm K W) (hB : B.IsAlt) (hC : C.IsAlt)
    {e f : V} {e' f' : W} (hef : B e f = 1) (hef' : C e' f' = 1) :
    ∃ i : (hyperbolicPlaneMap (K := K) e f).range ≃ₗ[K]
        (hyperbolicPlaneMap (K := K) e' f').range,
      ∀ x y, C (i x : W) (i y : W) = B (x : V) (y : V) := by
  let iV := LinearEquiv.ofInjective (hyperbolicPlaneMap (K := K) e f)
    (hyperbolicPlaneMap_injective B hB hef)
  let iW := LinearEquiv.ofInjective (hyperbolicPlaneMap (K := K) e' f')
    (hyperbolicPlaneMap_injective C hC hef')
  refine ⟨iV.symm.trans iW, ?_⟩
  intro x y
  obtain ⟨a, rfl⟩ := iV.surjective x
  obtain ⟨b, rfl⟩ := iV.surjective y
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change C (hyperbolicPlaneMap e' f' a) (hyperbolicPlaneMap e' f' b) =
    B (hyperbolicPlaneMap e f a) (hyperbolicPlaneMap e f b)
  rw [hyperbolicPlaneMap_pairing B hB hef, hyperbolicPlaneMap_pairing C hC hef']

/-- Nondegenerate alternating forms of the same finite dimension are isometric,
including in characteristic two. No classification theorem is assumed. -/
theorem alternating_isometry_of_finrank_eq [FiniteDimensional K W]
    (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (hB : B.IsAlt) (hC : C.IsAlt) (hBn : B.Nondegenerate) (hCn : C.Nondegenerate)
    (hdim : finrank K V = finrank K W) :
    ∃ i : V ≃ₗ[K] W, ∀ x y, C (i x) (i y) = B x y := by
  classical
  generalize hd : finrank K V = d
  induction d using Nat.strong_induction_on generalizing V W with
  | h d ih =>
    by_cases hd0 : d = 0
    · have : Subsingleton V := finrank_zero_iff.mp (hd.trans hd0)
      have : Subsingleton W := finrank_zero_iff.mp (hdim.symm.trans (hd.trans hd0))
      refine ⟨LinearEquiv.ofSubsingleton V W, fun x y => ?_⟩
      have hx : x = 0 := Subsingleton.elim _ _
      simp [hx]
    have hposV : 0 < finrank K V := by omega
    have hposW : 0 < finrank K W := by omega
    obtain ⟨e, f, hef, hcV, hnV, hdP, hdQ⟩ :=
      exists_hyperbolic_complement B hB hBn hposV
    obtain ⟨e', f', hef', hcW, hnW, hdP', hdQ'⟩ :=
      exists_hyperbolic_complement C hC hCn hposW
    let P := (hyperbolicPlaneMap (K := K) e f).range
    let Q := B.orthogonal P
    let P' := (hyperbolicPlaneMap (K := K) e' f').range
    let Q' := C.orthogonal P'
    have hdQQ : finrank K Q = finrank K Q' := by dsimp [Q, Q', P, P']; omega
    have hdQlt : finrank K Q < d := by dsimp [Q, P]; omega
    obtain ⟨j, hj⟩ := ih (finrank K Q) hdQlt (B.restrict Q) (C.restrict Q')
      (fun x => hB x) (fun x => hC x) hnV hnW hdQQ rfl
    obtain ⟨i, hi⟩ := hyperbolic_planes_isometric B C hB hC hef hef'
    let v : (P × Q) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl P Q hcV
    let w : (P' × Q') ≃ₗ[K] W := Submodule.prodEquivOfIsCompl P' Q' hcW
    refine ⟨v.symm.trans ((i.prodCongr j).trans w), ?_⟩
    intro x y
    obtain ⟨a, rfl⟩ := v.surjective x
    obtain ⟨b, rfl⟩ := v.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply]
    change C ((i a.1 : W) + j a.2) ((i b.1 : W) + j b.2) =
      B ((a.1 : V) + a.2) ((b.1 : V) + b.2)
    rw [pairing_add_orthogonal C hC.isRefl P' (i a.1, j a.2) (i b.1, j b.2),
      pairing_add_orthogonal B hB.isRefl P a b]
    exact congrArg₂ (· + ·) (hi a.1 b.1) (hj a.2 b.2)

/-- A nondegenerate alternating space embeds isometrically into any such space
of at least the same dimension. -/
theorem alternating_embedding_of_finrank_le [FiniteDimensional K W]
    (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (hB : B.IsAlt) (hC : C.IsAlt) (hBn : B.Nondegenerate) (hCn : C.Nondegenerate)
    (hdim : finrank K V ≤ finrank K W) :
    ∃ i : V →ₗ[K] W, ∀ x y, C (i x) (i y) = B x y := by
  classical
  generalize hd : finrank K V = d
  induction d using Nat.strong_induction_on generalizing V W with
  | h d ih =>
    by_cases hd0 : d = 0
    · have : Subsingleton V := finrank_zero_iff.mp (hd.trans hd0)
      refine ⟨0, fun x y => ?_⟩
      have hx : x = 0 := Subsingleton.elim _ _
      simp [hx]
    have hposV : 0 < finrank K V := by omega
    have hposW : 0 < finrank K W := by omega
    obtain ⟨e, f, hef, hcV, hnV, hdP, hdQ⟩ :=
      exists_hyperbolic_complement B hB hBn hposV
    obtain ⟨e', f', hef', hcW, hnW, hdP', hdQ'⟩ :=
      exists_hyperbolic_complement C hC hCn hposW
    let P := (hyperbolicPlaneMap (K := K) e f).range
    let Q := B.orthogonal P
    let P' := (hyperbolicPlaneMap (K := K) e' f').range
    let Q' := C.orthogonal P'
    have hdQQ : finrank K Q ≤ finrank K Q' := by dsimp [Q, Q', P, P']; omega
    have hdQlt : finrank K Q < d := by dsimp [Q, P]; omega
    obtain ⟨j, hj⟩ := ih (finrank K Q) hdQlt (B.restrict Q) (C.restrict Q')
      (fun x => hB x) (fun x => hC x) hnV hnW hdQQ rfl
    obtain ⟨i, hi⟩ := hyperbolic_planes_isometric B C hB hC hef hef'
    let v : (P × Q) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl P Q hcV
    let w : (P' × Q') ≃ₗ[K] W := Submodule.prodEquivOfIsCompl P' Q' hcW
    refine ⟨w.toLinearMap.comp ((i.toLinearMap.prodMap j).comp v.symm.toLinearMap), ?_⟩
    intro x y
    obtain ⟨a, rfl⟩ := v.surjective x
    obtain ⟨b, rfl⟩ := v.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.prodMap_apply]
    change C ((i a.1 : W) + j a.2) ((i b.1 : W) + j b.2) =
      B ((a.1 : V) + a.2) ((b.1 : V) + b.2)
    rw [pairing_add_orthogonal C hC.isRefl P' (i a.1, j a.2) (i b.1, j b.2),
      pairing_add_orthogonal B hB.isRefl P a b]
    exact congrArg₂ (· + ·) (hi a.1 b.1) (hj a.2 b.2)

/-- An isometric embedding has a nondegenerate image and an orthogonal
complement, with the expected dimension difference. -/
theorem exists_isometric_complement [FiniteDimensional K W]
    (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (hB : B.IsAlt) (hC : C.IsAlt) (hBn : B.Nondegenerate) (hCn : C.Nondegenerate)
    (hdim : finrank K V ≤ finrank K W) :
    ∃ i : V →ₗ[K] W, (∀ x y, C (i x) (i y) = B x y) ∧
      (C.restrict i.range).Nondegenerate ∧ IsCompl i.range (C.orthogonal i.range) ∧
      (C.restrict (C.orthogonal i.range)).Nondegenerate ∧
      finrank K i.range = finrank K V ∧
      finrank K (C.orthogonal i.range) + finrank K V = finrank K W := by
  obtain ⟨i, hi⟩ := alternating_embedding_of_finrank_le B C hB hC hBn hCn hdim
  have hinj : Function.Injective i := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hBn.1
    intro z
    rw [← hi, map_sub, hxy, sub_self]
    simp
  have hP : (C.restrict i.range).Nondegenerate := by
    have haltP : (C.restrict i.range).IsAlt := fun x => hC x
    apply haltP.isRefl.nondegenerate_iff_separatingLeft.mpr
    intro x hx
    obtain ⟨a, ha⟩ := x.2
    have ha0 : a = 0 := hBn.1 a (fun b => by
      rw [← hi, ha]
      exact hx ⟨i b, LinearMap.mem_range_self i b⟩)
    apply Subtype.ext
    rw [← ha, ha0, map_zero]
    rfl
  have hcompl := C.isCompl_orthogonal_of_restrict_nondegenerate hC.isRefl hP
  have hQ : (C.restrict (C.orthogonal i.range)).Nondegenerate := by
    apply C.nondegenerate_restrict_of_disjoint_orthogonal hC.isRefl
    rw [C.orthogonal_orthogonal hCn hC.isRefl]
    exact hcompl.disjoint.symm
  have hdimP : finrank K i.range = finrank K V := LinearMap.finrank_range_of_inj hinj
  refine ⟨i, hi, hP, hcompl, hQ, hdimP, ?_⟩
  rw [C.finrank_orthogonal hCn, hdimP]
  omega

/-- Split off the radical of an alternating form. The remaining subspace is
nondegenerate, has dimension equal to the original form's rank, and a linear
projection onto it preserves every pairing. -/
theorem exists_nondegenerate_model (B : LinearMap.BilinForm K V) (halt : B.IsAlt) :
    ∃ (W : Submodule K V) (π : V →ₗ[K] W),
      (B.restrict W).Nondegenerate ∧ finrank K W = finrank K B.range ∧
        ∀ x y, B (π x : V) (π y : V) = B x y := by
  obtain ⟨W, hW⟩ := (LinearMap.ker B).exists_isCompl
  have hzero : ∀ x ∈ W, ∀ y ∈ LinearMap.ker B, B x y = 0 := by
    intro x hx y hy
    exact halt.isRefl y x (LinearMap.congr_fun (LinearMap.mem_ker.mp hy) x)
  have hker := LinearMap.BilinForm.ker_restrict_eq_of_codisjoint hW.symm.codisjoint hzero
  have hAltW : (B.restrict W).IsAlt := fun x => halt x
  have hnondeg : (B.restrict W).Nondegenerate := by
    apply hAltW.isRefl.nondegenerate_iff_separatingLeft.mpr
    intro x hx
    have hxker : x ∈ LinearMap.ker (B.restrict W) :=
      LinearMap.mem_ker.mpr (LinearMap.ext hx)
    rw [hker] at hxker
    have hxinf : (x : V) ∈ LinearMap.ker B ⊓ W := ⟨hxker, x.2⟩
    rw [hW.inf_eq_bot] at hxinf
    exact Subtype.ext (by simpa using hxinf)
  have hdim : finrank K W = finrank K B.range := by
    have h₁ := Submodule.finrank_add_eq_of_isCompl hW
    have h₂ := B.finrank_range_add_finrank_ker
    omega
  let e : (LinearMap.ker B × W) ≃ₗ[K] V :=
    Submodule.prodEquivOfIsCompl _ _ hW
  let π : V →ₗ[K] W := (LinearMap.snd K (LinearMap.ker B) W).comp e.symm.toLinearMap
  refine ⟨W, π, hnondeg, hdim, ?_⟩
  intro x y
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  have hπ (a : LinearMap.ker B × W) : π (e a) = a.2 := by simp [π]
  rw [hπ, hπ]
  change B (a.2 : V) (b.2 : V) = B ((a.1 : V) + a.2) ((b.1 : V) + b.2)
  have h₁ : B (a.1 : V) ((b.1 : V) + b.2) = 0 :=
    LinearMap.congr_fun (LinearMap.mem_ker.mp a.1.2) _
  have h₂ : B (a.2 : V) (b.1 : V) = 0 := hzero a.2 a.2.2 b.1 b.1.2
  rw [LinearMap.BilinForm.add_left, h₁, zero_add, map_add, h₂, zero_add]

theorem even_rank_of_alt (B : LinearMap.BilinForm K V) (halt : B.IsAlt) :
    Even (finrank K B.range) := by
  obtain ⟨W, π, hW, hdim, hπ⟩ := exists_nondegenerate_model B halt
  rw [← hdim]
  exact even_finrank_of_nondegenerate_alt (B.restrict W) (fun x => halt x) hW

end Erdos117
