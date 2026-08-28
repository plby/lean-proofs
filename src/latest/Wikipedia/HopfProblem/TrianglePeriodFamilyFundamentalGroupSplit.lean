import Mathlib.GroupTheory.SemidirectProduct

/-!
# A split exact group extension as a genuine semidirect product

An injective kernel map and a homomorphic section identify the middle
group with the semidirect product for their actual conjugation action.
This is a purely algebraic construction: applications to fundamental
groups supply the independently proved exactness and conjugacy facts.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SplitGroupExtension

variable {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N)

/-- The specified conjugacy identity gives the semidirect-product homomorphism. -/
def hom (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) : N ⋊[φ] H →* E :=
  SemidirectProduct.lift i s (fun h => by
    ext n
    exact hconj h n)

@[simp] theorem hom_apply
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (x : N ⋊[φ] H) :
    hom i s φ hconj x = i x.left * s x.right := rfl

/-- Exactness makes every included kernel element project to one. -/
theorem projection_inclusion (hex : i.range = p.ker) (n : N) : p (i n) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [← hex]
  exact ⟨n, rfl⟩

theorem projection_section (hs : p.comp s = MonoidHom.id H) (h : H) : p (s h) = h :=
  DFunLike.congr_fun hs h

/-- The constructed homomorphism respects the given extension projection. -/
theorem projection_hom (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (x : N ⋊[φ] H) :
    p (hom i s φ hconj x) = x.right := by
  rw [hom_apply, map_mul, projection_inclusion i p hex, projection_section p s hs,
    one_mul]

/-- The section separates the quotient coordinates, and injectivity of
the kernel map then separates the remaining coordinates. -/
theorem hom_injective (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) :
    Function.Injective (hom i s φ hconj) := by
  intro x y hxy
  have hr : x.right = y.right := by
    simpa only [projection_hom i p s φ hs hex hconj] using congrArg p hxy
  have hl : i x.left = i y.left := by
    rw [hom_apply, hom_apply, hr] at hxy
    exact mul_right_cancel hxy
  exact SemidirectProduct.ext (hi hl) hr

/-- Removing the section part of an element puts it in the actual kernel,
so exactness supplies its normal-subgroup coordinate. -/
theorem hom_surjective (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) :
    Function.Surjective (hom i s φ hconj) := by
  intro e
  have he : e * (s (p e))⁻¹ ∈ i.range := by
    rw [hex, MonoidHom.mem_ker, map_mul, map_inv, projection_section p s hs]
    exact mul_inv_cancel (p e)
  obtain ⟨n, hn⟩ := he
  refine ⟨⟨n, p e⟩, ?_⟩
  change i n * s (p e) = e
  rw [hn, inv_mul_cancel_right]

theorem hom_bijective (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) :
    Function.Bijective (hom i s φ hconj) :=
  ⟨hom_injective i p s φ hi hs hex hconj, hom_surjective i p s φ hs hex hconj⟩

/-- A split exact extension is genuinely isomorphic to the semidirect
product for the supplied, verified conjugation action. -/
def mulEquiv (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) : N ⋊[φ] H ≃* E :=
  MulEquiv.ofBijective (hom i s φ hconj) (hom_bijective i p s φ hi hs hex hconj)

variable (hi : Function.Injective i) (hs : p.comp s = MonoidHom.id H)
    (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹)

@[simp] theorem mulEquiv_apply (x : N ⋊[φ] H) :
    mulEquiv i p s φ hi hs hex hconj x = i x.left * s x.right := rfl

@[simp] theorem mulEquiv_inl (n : N) :
    mulEquiv i p s φ hi hs hex hconj (SemidirectProduct.inl n) = i n := by
  simp

@[simp] theorem mulEquiv_inr (h : H) :
    mulEquiv i p s φ hi hs hex hconj (SemidirectProduct.inr h) = s h := by
  simp

@[simp] theorem projection_mulEquiv (x : N ⋊[φ] H) :
    p (mulEquiv i p s φ hi hs hex hconj x) = x.right :=
  projection_hom i p s φ hs hex hconj x

/-- Compatibility with the kernel injection as an equality of homomorphisms. -/
@[simp] theorem mulEquiv_comp_inl :
    (mulEquiv i p s φ hi hs hex hconj).toMonoidHom.comp SemidirectProduct.inl = i := by
  ext n
  exact mulEquiv_inl i p s φ hi hs hex hconj n

/-- Compatibility with the chosen section as an equality of homomorphisms. -/
@[simp] theorem mulEquiv_comp_inr :
    (mulEquiv i p s φ hi hs hex hconj).toMonoidHom.comp SemidirectProduct.inr = s := by
  ext h
  exact mulEquiv_inr i p s φ hi hs hex hconj h

/-- The extension projection becomes the canonical semidirect-product projection. -/
@[simp] theorem projection_comp_mulEquiv :
    p.comp (mulEquiv i p s φ hi hs hex hconj).toMonoidHom =
      SemidirectProduct.rightHom := by
  ext x
  exact projection_mulEquiv i p s φ hi hs hex hconj x

@[simp] theorem mulEquiv_symm_inclusion (n : N) :
    (mulEquiv i p s φ hi hs hex hconj).symm (i n) = SemidirectProduct.inl n := by
  apply (mulEquiv i p s φ hi hs hex hconj).injective
  rw [MulEquiv.apply_symm_apply, mulEquiv_inl]

@[simp] theorem mulEquiv_symm_section (h : H) :
    (mulEquiv i p s φ hi hs hex hconj).symm (s h) = SemidirectProduct.inr h := by
  apply (mulEquiv i p s φ hi hs hex hconj).injective
  rw [MulEquiv.apply_symm_apply, mulEquiv_inr]

/-- The quotient coordinate of the inverse is the original projection. -/
@[simp] theorem mulEquiv_symm_right (e : E) :
    ((mulEquiv i p s φ hi hs hex hconj).symm e).right = p e := by
  rw [← projection_mulEquiv i p s φ hi hs hex hconj,
    MulEquiv.apply_symm_apply]

/-- The kernel coordinate is characterized by removing the section part. -/
theorem inclusion_mulEquiv_symm_left (e : E) :
    i ((mulEquiv i p s φ hi hs hex hconj).symm e).left = e * (s (p e))⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  have he := (mulEquiv i p s φ hi hs hex hconj).apply_symm_apply e
  rwa [mulEquiv_apply, mulEquiv_symm_right] at he

end Wikipedia.HopfProblem.SplitGroupExtension
