import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleGaugeHolomorphic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Holomorphic gauges between genuine cocycle line bundles

A compatible family of holomorphic nonzero local multipliers defines a
fibrewise-linear biholomorphism between the original cocycle bundles.
The cover sets agree, but the two bundles may select different preferred
charts at every point.  The forward coefficient therefore includes the
actual target transition between the two selected charts.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- A holomorphic gauge relating two cocycles on the same open sets.
The preferred chart selectors need not be equal. -/
structure Gauge (A B : TransitionData M ι) where
  baseSet_eq : A.baseSet = B.baseSet
  value : ι → M → ℂˣ
  compatible : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
    B.transition i j x * value i x = value j x * A.transition i j x
  holomorphicOn : ∀ i,
    ContMDiffOn I I₁ ω (fun x => (value i x : ℂ)) (A.baseSet i)

namespace Gauge

variable {I} {A B : TransitionData M ι} (G : Gauge I A B)

/-- The actual multiplier in the preferred coordinates of the two bundles. -/
def preferredMultiplier (x : M) : ℂˣ :=
  B.transition (A.indexAt x) (B.indexAt x) x * G.value (A.indexAt x) x

theorem preferredMultiplier_ne_zero (x : M) : (G.preferredMultiplier x : ℂ) ≠ 0 :=
  (G.preferredMultiplier x).ne_zero

/-- The forward map on the original total spaces. -/
def map (p : A.core.TotalSpace) : B.core.TotalSpace :=
  ⟨p.proj, (G.preferredMultiplier p.proj : ℂ) * id (α := ℂ) p.2⟩

/-- The inverse uses the reciprocal of the actual preferred multiplier. -/
def invMap (p : B.core.TotalSpace) : A.core.TotalSpace :=
  ⟨p.proj, (G.preferredMultiplier p.proj : ℂ)⁻¹ * id (α := ℂ) p.2⟩

@[simp] theorem map_proj (p : A.core.TotalSpace) : (G.map p).proj = p.proj := rfl

@[simp] theorem invMap_proj (p : B.core.TotalSpace) : (G.invMap p).proj = p.proj := rfl

@[simp] theorem map_mk (x : M) (v : A.core.Fiber x) :
    G.map ⟨x, v⟩ = ⟨x, (G.preferredMultiplier x : ℂ) * id (α := ℂ) v⟩ := rfl

@[simp] theorem invMap_mk (x : M) (v : B.core.Fiber x) :
    G.invMap ⟨x, v⟩ = ⟨x, (G.preferredMultiplier x : ℂ)⁻¹ * id (α := ℂ) v⟩ := rfl

@[simp] theorem invMap_map (p : A.core.TotalSpace) : G.invMap (G.map p) = p := by
  cases p with
  | mk x v =>
    change (⟨x, (G.preferredMultiplier x : ℂ)⁻¹ *
      ((G.preferredMultiplier x : ℂ) * id (α := ℂ) v)⟩ : A.core.TotalSpace) = ⟨x, v⟩
    rw [inv_mul_cancel_left₀ (G.preferredMultiplier_ne_zero x)]
    rfl

@[simp] theorem map_invMap (p : B.core.TotalSpace) : G.map (G.invMap p) = p := by
  cases p with
  | mk x v =>
    change (⟨x, (G.preferredMultiplier x : ℂ) *
      ((G.preferredMultiplier x : ℂ)⁻¹ * id (α := ℂ) v)⟩ : B.core.TotalSpace) = ⟨x, v⟩
    rw [mul_inv_cancel_left₀ (G.preferredMultiplier_ne_zero x)]
    rfl

/-- The preferred multiplier agrees with every actual local gauge after
applying the original source and target coordinate changes. -/
theorem transition_mul_preferredMultiplier (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    B.transition (B.indexAt x) i x * G.preferredMultiplier x =
      G.value i x * A.transition (A.indexAt x) i x := by
  have hxa : x ∈ B.baseSet (A.indexAt x) := by
    rw [← G.baseSet_eq]
    exact A.mem_baseSet_at x
  have hxi : x ∈ B.baseSet i := by
    rw [← G.baseSet_eq]
    exact hx
  calc
    B.transition (B.indexAt x) i x * G.preferredMultiplier x =
        (B.transition (B.indexAt x) i x *
          B.transition (A.indexAt x) (B.indexAt x) x) * G.value (A.indexAt x) x :=
      (mul_assoc _ _ _).symm
    _ = B.transition (A.indexAt x) i x * G.value (A.indexAt x) x := by
      rw [B.transition_comp _ _ _ x ⟨⟨hxa, B.mem_baseSet_at x⟩, hxi⟩]
    _ = G.value i x * A.transition (A.indexAt x) i x :=
      G.compatible _ _ x ⟨A.mem_baseSet_at x, hx⟩

/-- The forward map multiplies the coefficient in chart `i` by exactly
the specified local gauge `uᵢ`. -/
theorem map_localCoefficient (i : ι) (p : A.core.TotalSpace)
    (hp : p.proj ∈ A.baseSet i) :
    (B.core.localTriv i (G.map p)).2 =
      (G.value i p.proj : ℂ) * (A.core.localTriv i p).2 := by
  have hc := congrArg (fun u : ℂˣ => (u : ℂ))
    (G.transition_mul_preferredMultiplier i hp)
  change (B.transition (B.indexAt p.proj) i p.proj : ℂ) *
    (G.preferredMultiplier p.proj : ℂ) =
      (G.value i p.proj : ℂ) * (A.transition (A.indexAt p.proj) i p.proj : ℂ) at hc
  change (B.transition (B.indexAt p.proj) i p.proj : ℂ) *
    ((G.preferredMultiplier p.proj : ℂ) * id (α := ℂ) p.2) =
      (G.value i p.proj : ℂ) *
        ((A.transition (A.indexAt p.proj) i p.proj : ℂ) * id (α := ℂ) p.2)
  rw [← mul_assoc, hc, mul_assoc]

/-- The inverse map has the reciprocal local gauge coefficient in the
same original bundle charts. -/
theorem invMap_localCoefficient (i : ι) (p : B.core.TotalSpace)
    (hp : p.proj ∈ A.baseSet i) :
    (A.core.localTriv i (G.invMap p)).2 =
      (G.value i p.proj : ℂ)⁻¹ * (B.core.localTriv i p).2 := by
  have hc := G.map_localCoefficient i (G.invMap p) hp
  rw [G.map_invMap] at hc
  change (B.core.localTriv i p).2 =
    (G.value i p.proj : ℂ) * (A.core.localTriv i (G.invMap p)).2 at hc
  rw [hc, inv_mul_cancel_left₀ (G.value i p.proj).ne_zero]

/-- The map is a genuine equivalence of the original total spaces. -/
def equiv : A.core.TotalSpace ≃ B.core.TotalSpace where
  toFun := G.map
  invFun := G.invMap
  left_inv := G.invMap_map
  right_inv := G.map_invMap

theorem map_add (x : M) (v w : A.core.Fiber x) :
    id (α := B.core.Fiber x) (G.map ⟨x, v + w⟩).2 =
      id (α := B.core.Fiber x) (G.map ⟨x, v⟩).2 +
        id (α := B.core.Fiber x) (G.map ⟨x, w⟩).2 :=
  mul_add _ (id (α := ℂ) v) (id (α := ℂ) w)

theorem map_smul (x : M) (c : ℂ) (v : A.core.Fiber x) :
    id (α := B.core.Fiber x) (G.map ⟨x, c • v⟩).2 =
      c • id (α := B.core.Fiber x) (G.map ⟨x, v⟩).2 := by
  change (G.preferredMultiplier x : ℂ) * (c * id (α := ℂ) v) =
    c * ((G.preferredMultiplier x : ℂ) * id (α := ℂ) v)
  exact mul_left_comm _ _ _

/-- The map on each actual vector-bundle fibre is a continuous complex
linear equivalence, given by the actual preferred scalar multiplier. -/
def fiberEquiv (x : M) : A.core.Fiber x ≃L[ℂ] B.core.Fiber x where
  toFun v := (G.preferredMultiplier x : ℂ) * id (α := ℂ) v
  invFun w := (G.preferredMultiplier x : ℂ)⁻¹ * id (α := ℂ) w
  map_add' v w := mul_add _ (id (α := ℂ) v) (id (α := ℂ) w)
  map_smul' c v := mul_left_comm _ c (id (α := ℂ) v)
  left_inv v := inv_mul_cancel_left₀ (G.preferredMultiplier_ne_zero x) (id (α := ℂ) v)
  right_inv w := mul_inv_cancel_left₀ (G.preferredMultiplier_ne_zero x) (id (α := ℂ) w)
  continuous_toFun := by
    change Continuous (fun v : ℂ => (G.preferredMultiplier x : ℂ) * v)
    exact continuous_const.mul continuous_id
  continuous_invFun := by
    change Continuous (fun w : ℂ => (G.preferredMultiplier x : ℂ)⁻¹ * w)
    exact continuous_const.mul continuous_id

@[simp] theorem fiberEquiv_apply (x : M) (v : A.core.Fiber x) :
    G.fiberEquiv x v = id (α := B.core.Fiber x) (G.map ⟨x, v⟩).2 := rfl

@[simp] theorem fiberEquiv_symm_apply (x : M) (v : B.core.Fiber x) :
    (G.fiberEquiv x).symm v = id (α := A.core.Fiber x) (G.invMap ⟨x, v⟩).2 := rfl

variable [A.IsHolomorphic I] [B.IsHolomorphic I]

/-- Holomorphicity in the original total-space manifold structures,
proved using the prescribed local coefficient formulas. -/
theorem map_holomorphic : ContMDiff (I.prod I₁) (I.prod I₁) ω G.map :=
  bundleMap_holomorphic_of_local_coefficients A B I G.baseSet_eq G.map G.map_proj
    (fun i x => (G.value i x : ℂ)) G.holomorphicOn G.map_localCoefficient

/-- The reciprocal local coefficient formulas prove holomorphicity of
the inverse in the original bundle atlases. -/
theorem invMap_holomorphic : ContMDiff (I.prod I₁) (I.prod I₁) ω G.invMap := by
  apply bundleMap_holomorphic_of_local_coefficients B A I G.baseSet_eq.symm
    G.invMap G.invMap_proj (fun i x => (G.value i x : ℂ)⁻¹)
  · intro i
    rw [← G.baseSet_eq]
    exact (G.holomorphicOn i).inv₀ (fun x _ => (G.value i x).ne_zero)
  · intro i p hp
    rw [← G.baseSet_eq] at hp
    exact G.invMap_localCoefficient i p hp

/-- A compatible holomorphic gauge gives a genuine base-preserving,
fibrewise-linear biholomorphism of the independently constructed bundles. -/
def diffeomorph : Diffeomorph (I.prod I₁) (I.prod I₁)
    A.core.TotalSpace B.core.TotalSpace ω where
  toEquiv := G.equiv
  contMDiff_toFun := G.map_holomorphic
  contMDiff_invFun := G.invMap_holomorphic

@[simp] theorem diffeomorph_apply (p : A.core.TotalSpace) :
    G.diffeomorph p = G.map p := rfl

@[simp] theorem diffeomorph_symm_apply (p : B.core.TotalSpace) :
    G.diffeomorph.symm p = G.invMap p := rfl

@[simp] theorem diffeomorph_proj (p : A.core.TotalSpace) :
    (G.diffeomorph p).proj = p.proj := rfl

@[simp] theorem diffeomorph_symm_proj (p : B.core.TotalSpace) :
    (G.diffeomorph.symm p).proj = p.proj := rfl

/-- The total-space biholomorphism restricts to the explicit continuous
complex-linear equivalence on every fibre. -/
theorem diffeomorph_mk (x : M) (v : A.core.Fiber x) :
    G.diffeomorph ⟨x, v⟩ = ⟨x, G.fiberEquiv x v⟩ := rfl

theorem diffeomorph_symm_mk (x : M) (v : B.core.Fiber x) :
    G.diffeomorph.symm ⟨x, v⟩ = ⟨x, (G.fiberEquiv x).symm v⟩ := rfl

theorem diffeomorph_localCoefficient (i : ι) (p : A.core.TotalSpace)
    (hp : p.proj ∈ A.baseSet i) :
    (B.core.localTriv i (G.diffeomorph p)).2 =
      (G.value i p.proj : ℂ) * (A.core.localTriv i p).2 :=
  G.map_localCoefficient i p hp

theorem diffeomorph_symm_localCoefficient (i : ι) (p : B.core.TotalSpace)
    (hp : p.proj ∈ A.baseSet i) :
    (A.core.localTriv i (G.diffeomorph.symm p)).2 =
      (G.value i p.proj : ℂ)⁻¹ * (B.core.localTriv i p).2 :=
  G.invMap_localCoefficient i p hp

end Gauge

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
