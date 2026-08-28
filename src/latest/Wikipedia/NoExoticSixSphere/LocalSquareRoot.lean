import Wikipedia.NoExoticSixSphere.NearIdentitySquare

/-!
# A smooth square root on a neighborhood of the identity

The derivative of squaring at the identity is twice the identity. The proved
inverse-function theorem constructs its smooth inverse on an open neighborhood.
The inverse is confined to a ball where square roots are unique.
-/

open Set
open scoped ContDiff Manifold

namespace NoExoticSixSphere.NearIdentitySquare

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

structure RootData (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] where
  domain : Set A
  open_domain : IsOpen domain
  one_mem : (1 : A) ∈ domain
  root : A → A
  smooth : ContDiffOn ℝ ∞ root domain
  root_one : root 1 = 1
  square : ∀ a ∈ domain, root a * root a = a
  near_one : ∀ a ∈ domain, ‖root a - 1‖ < 1

theorem hasFDerivAt_square_one : HasFDerivAt (fun a : A ↦ a * a)
    ((2 : ℝ) • (1 : A →L[ℝ] A)) 1 := by
  convert! (hasFDerivAt_id (𝕜 := ℝ) (1 : A)).mul' (hasFDerivAt_id (𝕜 := ℝ) (1 : A)) using 1
  ext a
  simp [two_smul]

theorem nonempty_rootData [CompleteSpace A] : Nonempty (RootData A) := by
  have hf : ContDiff ℝ ∞ (fun a : A ↦ a * a) := contDiff_id.mul contDiff_id
  have hinv : (fderiv ℝ (fun a : A ↦ a * a) 1).IsInvertible := by
    rw [hasFDerivAt_square_one.fderiv]
    refine ⟨ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := A)
      (Units.mk0 (2 : ℝ) (by norm_num)), ?_⟩
    ext a
    rfl
  obtain ⟨e, he, hsource, hmap⟩ := exists_partialDiffeomorph_of_contDiffOn
    (Metric.isOpen_ball : IsOpen (Metric.ball (1 : A) (1 / 2 : ℝ)))
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)) hf.contDiffOn hinv
  have heone : e 1 = (1 : A) := by rw [hmap]; exact one_mul 1
  have hone : (1 : A) ∈ e.target := heone ▸ e.map_source' he
  refine ⟨{
    domain := e.target
    open_domain := e.open_target
    one_mem := hone
    root := e.symm
    smooth := e.contMDiffOn_invFun.contDiffOn
    root_one := ?_
    square := ?_
    near_one := ?_ }⟩
  · exact (congrArg e.symm heone).symm.trans (e.left_inv' he)
  · intro a ha
    have hr := e.right_inv' ha
    rwa [hmap] at hr
  · intro a ha
    have hr := hsource (e.map_target' ha)
    change dist (e.symm a) 1 < 1 / 2 at hr
    rw [dist_eq_norm] at hr
    linarith

namespace RootData

variable (R : RootData A)

theorem commute {a b : A} (ha : a ∈ R.domain) (h : Commute a b) : Commute (R.root a) b :=
  commute_of_square_commute (R.near_one a ha) (by rw [R.square a ha]; exact h)

theorem selfAdjoint [StarRing A] [NormedStarGroup A] {a : A}
    (ha : a ∈ R.domain) (h : IsSelfAdjoint a) : IsSelfAdjoint (R.root a) :=
  selfAdjoint_of_square (R.near_one a ha) (by rw [R.square a ha]; exact h)

end RootData

end NoExoticSixSphere.NearIdentitySquare
