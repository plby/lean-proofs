import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Naturality of fundamental-group basepoint change

Changing the basepoint along an actual path commutes with the homomorphism
induced by a continuous map.  The conjugation formula is expressed using
actual path classes, so its order agrees with mathlib's convention that
fundamental-group multiplication reverses path concatenation.
-/

noncomputable section

namespace Wikipedia.HopfProblem

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

open FundamentalGroup Path.Homotopic.Quotient

/-- Changing basepoint along `p` follows `p` backwards, then the loop,
and then `p` forwards. -/
theorem fundamentalGroup_basepoint_change_apply (p : Path x₀ x₁)
    (γ : FundamentalGroup X x₀) :
    fundamentalGroupMulEquivOfPath p γ =
      (Path.Homotopic.Quotient.mk p).symm.trans
        (γ.trans (Path.Homotopic.Quotient.mk p)) := rfl

/-- On an actual representative, basepoint change is the corresponding
literal concatenated path class. -/
theorem fundamentalGroup_basepoint_change_mk (p : Path x₀ x₁) (γ : Path x₀ x₀) :
    fundamentalGroupMulEquivOfPath p (Path.Homotopic.Quotient.mk γ) =
      Path.Homotopic.Quotient.mk (p.symm.trans (γ.trans p)) := rfl

/-- Naturality of actual basepoint change, as an equality of homomorphisms. -/
theorem fundamentalGroup_basepoint_naturality (f : C(X, Y)) (p : Path x₀ x₁) :
    (fundamentalGroupMulEquivOfPath (p.map f.continuous)).toMonoidHom.comp
        (FundamentalGroup.map f x₀) =
      (FundamentalGroup.map f x₁).comp
        (fundamentalGroupMulEquivOfPath p).toMonoidHom := by
  apply MonoidHom.ext
  intro γ
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
      change Path.Homotopic.Quotient.mk
        ((p.map f.continuous).symm.trans ((γ.map f.continuous).trans (p.map f.continuous))) =
          Path.Homotopic.Quotient.mk ((p.symm.trans (γ.trans p)).map f.continuous)
      apply congrArg Path.Homotopic.Quotient.mk
      rw [Path.map_trans, Path.map_trans, Path.map_symm]

/-- The pointwise naturality equation for actual loop classes. -/
theorem fundamentalGroup_basepoint_naturality_apply (f : C(X, Y)) (p : Path x₀ x₁)
    (γ : FundamentalGroup X x₀) :
    fundamentalGroupMulEquivOfPath (p.map f.continuous) (FundamentalGroup.map f x₀ γ) =
      FundamentalGroup.map f x₁ (fundamentalGroupMulEquivOfPath p γ) :=
  DFunLike.congr_fun (fundamentalGroup_basepoint_naturality f p) γ

/-- Surjectivity of an induced map transports along a path in its domain. -/
theorem fundamentalGroup_map_surjective_at_of_path (f : C(X, Y)) (p : Path x₀ x₁)
    (hf : Function.Surjective (FundamentalGroup.map f x₀)) :
    Function.Surjective (FundamentalGroup.map f x₁) := by
  intro γ
  obtain ⟨δ, rfl⟩ := (fundamentalGroupMulEquivOfPath (p.map f.continuous)).surjective γ
  obtain ⟨ε, hε⟩ := hf δ
  refine ⟨fundamentalGroupMulEquivOfPath p ε, ?_⟩
  exact (fundamentalGroup_basepoint_naturality_apply f p ε).symm.trans
    (congrArg (fundamentalGroupMulEquivOfPath (p.map f.continuous)) hε)

/-- Injectivity of an induced map transports along a path in its domain. -/
theorem fundamentalGroup_map_injective_at_of_path (f : C(X, Y)) (p : Path x₀ x₁)
    (hf : Function.Injective (FundamentalGroup.map f x₀)) :
    Function.Injective (FundamentalGroup.map f x₁) := by
  intro γ δ h
  obtain ⟨γ₀, rfl⟩ := (fundamentalGroupMulEquivOfPath p).surjective γ
  obtain ⟨δ₀, rfl⟩ := (fundamentalGroupMulEquivOfPath p).surjective δ
  apply congrArg (fundamentalGroupMulEquivOfPath p)
  apply hf
  apply (fundamentalGroupMulEquivOfPath (p.map f.continuous)).injective
  rw [fundamentalGroup_basepoint_naturality_apply, fundamentalGroup_basepoint_naturality_apply]
  exact h

/-- Bijectivity of an induced map transports along a path in its domain. -/
theorem fundamentalGroup_map_bijective_at_of_path (f : C(X, Y)) (p : Path x₀ x₁)
    (hf : Function.Bijective (FundamentalGroup.map f x₀)) :
    Function.Bijective (FundamentalGroup.map f x₁) :=
  ⟨fundamentalGroup_map_injective_at_of_path f p hf.1,
    fundamentalGroup_map_surjective_at_of_path f p hf.2⟩

theorem fundamentalGroup_map_surjective_iff_of_path (f : C(X, Y)) (p : Path x₀ x₁) :
    Function.Surjective (FundamentalGroup.map f x₀) ↔
      Function.Surjective (FundamentalGroup.map f x₁) :=
  ⟨fundamentalGroup_map_surjective_at_of_path f p,
    fundamentalGroup_map_surjective_at_of_path f p.symm⟩

theorem fundamentalGroup_map_injective_iff_of_path (f : C(X, Y)) (p : Path x₀ x₁) :
    Function.Injective (FundamentalGroup.map f x₀) ↔
      Function.Injective (FundamentalGroup.map f x₁) :=
  ⟨fundamentalGroup_map_injective_at_of_path f p,
    fundamentalGroup_map_injective_at_of_path f p.symm⟩

theorem fundamentalGroup_map_bijective_iff_of_path (f : C(X, Y)) (p : Path x₀ x₁) :
    Function.Bijective (FundamentalGroup.map f x₀) ↔
      Function.Bijective (FundamentalGroup.map f x₁) :=
  ⟨fundamentalGroup_map_bijective_at_of_path f p,
    fundamentalGroup_map_bijective_at_of_path f p.symm⟩

/-- In a path-connected domain, surjectivity at one basepoint holds at all basepoints. -/
theorem fundamentalGroup_map_surjective_at_of_pathConnected [PathConnectedSpace X]
    (f : C(X, Y)) (x₀ x₁ : X) (hf : Function.Surjective (FundamentalGroup.map f x₀)) :
    Function.Surjective (FundamentalGroup.map f x₁) :=
  fundamentalGroup_map_surjective_at_of_path f (PathConnectedSpace.somePath x₀ x₁) hf

theorem fundamentalGroup_map_injective_at_of_pathConnected [PathConnectedSpace X]
    (f : C(X, Y)) (x₀ x₁ : X) (hf : Function.Injective (FundamentalGroup.map f x₀)) :
    Function.Injective (FundamentalGroup.map f x₁) :=
  fundamentalGroup_map_injective_at_of_path f (PathConnectedSpace.somePath x₀ x₁) hf

theorem fundamentalGroup_map_bijective_at_of_pathConnected [PathConnectedSpace X]
    (f : C(X, Y)) (x₀ x₁ : X) (hf : Function.Bijective (FundamentalGroup.map f x₀)) :
    Function.Bijective (FundamentalGroup.map f x₁) :=
  fundamentalGroup_map_bijective_at_of_path f (PathConnectedSpace.somePath x₀ x₁) hf

/-- Basepoint change preserves and reflects trivial loop classes. -/
theorem fundamentalGroup_basepoint_change_eq_one_iff (p : Path x₀ x₁)
    (γ : FundamentalGroup X x₀) :
    fundamentalGroupMulEquivOfPath p γ = 1 ↔ γ = 1 := by
  constructor
  · intro h
    apply (fundamentalGroupMulEquivOfPath p).injective
    exact h.trans (map_one (fundamentalGroupMulEquivOfPath p)).symm
  · rintro rfl
    exact map_one _

/-- Equality of images is unchanged by transporting the source loop classes. -/
theorem fundamentalGroup_map_basepoint_change_eq_iff (f : C(X, Y)) (p : Path x₀ x₁)
    (γ δ : FundamentalGroup X x₀) :
    FundamentalGroup.map f x₁ (fundamentalGroupMulEquivOfPath p γ) =
        FundamentalGroup.map f x₁ (fundamentalGroupMulEquivOfPath p δ) ↔
      FundamentalGroup.map f x₀ γ = FundamentalGroup.map f x₀ δ := by
  rw [← fundamentalGroup_basepoint_naturality_apply,
    ← fundamentalGroup_basepoint_naturality_apply]
  exact (fundamentalGroupMulEquivOfPath (p.map f.continuous)).injective.eq_iff

/-- Membership in the kernel of the actual induced map is basepoint-independent. -/
theorem fundamentalGroup_map_basepoint_change_eq_one_iff (f : C(X, Y)) (p : Path x₀ x₁)
    (γ : FundamentalGroup X x₀) :
    FundamentalGroup.map f x₁ (fundamentalGroupMulEquivOfPath p γ) = 1 ↔
      FundamentalGroup.map f x₀ γ = 1 := by
  rw [← fundamentalGroup_basepoint_naturality_apply]
  exact fundamentalGroup_basepoint_change_eq_one_iff (p.map f.continuous) _

end Wikipedia.HopfProblem
