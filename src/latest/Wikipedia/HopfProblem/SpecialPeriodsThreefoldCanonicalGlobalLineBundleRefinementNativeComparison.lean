import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Native bundle comparison through refining trivializations

If each chart of a cocycle bundle refines a chart of another and their
actual local trivializations agree under the identity in preferred
fibre coordinates, that identity is a genuine biholomorphism of their
original total spaces.  Both directions are checked in the original
bundle atlases; neither topology nor atlas is replaced.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.RefinementNative

open HolomorphicCharacterBundle

variable {M ι κ : Type*} [TopologicalSpace M]
  (A : TransitionData M ι) (R : TransitionData M κ)

/-- The set-theoretic identity of preferred scalar coordinates.  Its
analyticity is proved below from actual refining chart identities. -/
def coordinateIdentity : A.core.TotalSpace ≃ R.core.TotalSpace where
  toFun p := ⟨p.proj, id (α := ℂ) p.2⟩
  invFun p := ⟨p.proj, id (α := ℂ) p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

@[simp] theorem coordinateIdentity_apply (p : A.core.TotalSpace) :
    coordinateIdentity A R p = ⟨p.proj, id (α := ℂ) p.2⟩ := rfl

@[simp] theorem coordinateIdentity_symm_apply (p : R.core.TotalSpace) :
    (coordinateIdentity A R).symm p = ⟨p.proj, id (α := ℂ) p.2⟩ := rfl

@[simp] theorem coordinateIdentity_proj (p : A.core.TotalSpace) :
    (coordinateIdentity A R p).proj = p.proj := rfl

@[simp] theorem coordinateIdentity_symm_proj (p : R.core.TotalSpace) :
    ((coordinateIdentity A R).symm p).proj = p.proj := rfl

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
  [A.IsHolomorphic I] [R.IsHolomorphic I]
  (r : κ → ι) (hbase : ∀ k, R.baseSet k ⊆ A.baseSet (r k))
  (hchart : ∀ k p,
    R.core.localTriv k (coordinateIdentity A R p) = A.core.localTriv (r k) p)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

include hbase hchart in
/-- The coordinate identity is holomorphic in the actual refined atlas. -/
theorem coordinateIdentity_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (coordinateIdentity A R) := by
  intro p
  let k := R.indexAt p.proj
  have hpR : p.proj ∈ R.baseSet k := R.mem_baseSet_at p.proj
  have hpA : p.proj ∈ A.baseSet (r k) := hbase k hpR
  apply ((R.core.localTriv k).contMDiffAt_iff
    (f := coordinateIdentity A R)
    (show coordinateIdentity A R p ∈ (R.core.localTriv k).source from hpR)).mpr
  refine ⟨Bundle.contMDiffAt_proj A.core.Fiber, ?_⟩
  have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω (A.core.localTriv (r k)) p :=
    (A.core.localTriv (r k)).contMDiffOn.contMDiffAt
      ((A.core.localTriv (r k)).open_source.mem_nhds hpA)
  have heq : (fun q : A.core.TotalSpace =>
      (R.core.localTriv k (coordinateIdentity A R q)).2) =
      fun q => (A.core.localTriv (r k) q).2 :=
    funext fun q => congrArg Prod.snd (hchart k q)
  rw [heq]
  exact he.snd

include hchart in
/-- The original and refined local trivializations also agree in the
inverse direction, without assuming any topological comparison. -/
theorem coordinateIdentity_symm_localTriv (k : κ) (p : R.core.TotalSpace) :
    A.core.localTriv (r k) ((coordinateIdentity A R).symm p) = R.core.localTriv k p := by
  have h := hchart k ((coordinateIdentity A R).symm p)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

include hbase hchart in
/-- The inverse coordinate identity is holomorphic in the original atlas. -/
theorem coordinateIdentity_symm_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (coordinateIdentity A R).symm := by
  intro p
  let k := R.indexAt p.proj
  have hpR : p.proj ∈ R.baseSet k := R.mem_baseSet_at p.proj
  have hpA : p.proj ∈ A.baseSet (r k) := hbase k hpR
  apply ((A.core.localTriv (r k)).contMDiffAt_iff
    (f := (coordinateIdentity A R).symm)
    (show (coordinateIdentity A R).symm p ∈ (A.core.localTriv (r k)).source from hpA)).mpr
  refine ⟨Bundle.contMDiffAt_proj R.core.Fiber, ?_⟩
  have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω (R.core.localTriv k) p :=
    (R.core.localTriv k).contMDiffOn.contMDiffAt
      ((R.core.localTriv k).open_source.mem_nhds hpR)
  have heq : (fun q : R.core.TotalSpace =>
      (A.core.localTriv (r k) ((coordinateIdentity A R).symm q)).2) =
      fun q => (R.core.localTriv k q).2 := by
    funext q
    exact congrArg Prod.snd (coordinateIdentity_symm_localTriv A R r hchart k q)
  rw [heq]
  exact he.snd

/-- The native coordinate identity is a genuine analytic diffeomorphism
when the refining original local trivializations agree. -/
def diffeomorph : Diffeomorph (I.prod I₁) (I.prod I₁)
    A.core.TotalSpace R.core.TotalSpace ω where
  toEquiv := coordinateIdentity A R
  contMDiff_toFun := coordinateIdentity_holomorphic A R I r hbase hchart
  contMDiff_invFun := coordinateIdentity_symm_holomorphic A R I r hbase hchart

@[simp] theorem diffeomorph_apply (p : A.core.TotalSpace) :
    diffeomorph A R I r hbase hchart p = ⟨p.proj, id (α := ℂ) p.2⟩ := rfl

@[simp] theorem diffeomorph_symm_apply (p : R.core.TotalSpace) :
    (diffeomorph A R I r hbase hchart).symm p = ⟨p.proj, id (α := ℂ) p.2⟩ := rfl

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.RefinementNative
