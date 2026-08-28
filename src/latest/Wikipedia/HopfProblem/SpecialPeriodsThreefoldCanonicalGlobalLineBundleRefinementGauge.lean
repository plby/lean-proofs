import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleRefinementNative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleGauge

/-!
# Holomorphic gauge comparisons between bundles on different covers

Local holomorphic units on pairwise intersections of two independent
covers can compare their native line bundles. The construction refines
both bundles to the common cover, applies the already proved gauge
biholomorphism there, and returns to the original target bundle. Its
local coefficients are exactly the specified units in the two original
bundle charts.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι κ : Type*} [TopologicalSpace M]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- A comparison by holomorphic units on intersections of two possibly
different covers. No equality of cover sets or chart selectors is required. -/
structure CrossGauge (A : TransitionData M ι) (B : TransitionData M κ) where
  value : (ι × κ) → M → ℂˣ
  compatible : ∀ (i j : ι × κ) (x : M),
    x ∈ (A.baseSet i.1 ∩ B.baseSet i.2) ∩ (A.baseSet j.1 ∩ B.baseSet j.2) →
      B.transition i.2 j.2 x * value i x = value j x * A.transition i.1 j.1 x
  holomorphicOn : ∀ i,
    ContMDiffOn I I₁ ω (fun x => (value i x : ℂ)) (A.baseSet i.1 ∩ B.baseSet i.2)

namespace CrossGauge

variable {I} {A : TransitionData M ι} {B : TransitionData M κ} (G : CrossGauge I A B)

/-- The prescribed units give the existing same-cover gauge on the two
actual common-cover refinements. -/
def toGauge : Gauge I (leftRefinement A B) (rightRefinement A B) where
  baseSet_eq := rfl
  value := G.value
  compatible := G.compatible
  holomorphicOn := G.holomorphicOn

/-- Reversing a cross-cover comparison uses the reciprocal unit and
reverses the chart pair. -/
def symm : CrossGauge I B A where
  value i x := (G.value (i.2, i.1) x)⁻¹
  compatible i j x hx := by
    have h := G.compatible (i.2, i.1) (j.2, j.1) x
      ⟨⟨hx.1.2, hx.1.1⟩, ⟨hx.2.2, hx.2.1⟩⟩
    have h' := congrArg (fun u : ℂˣ =>
      (G.value (j.2, j.1) x)⁻¹ * u * (G.value (i.2, i.1) x)⁻¹) h
    simpa [mul_assoc] using h'.symm
  holomorphicOn i := by
    simpa only [Units.val_inv_eq_inv_val, inter_comm] using
      (G.holomorphicOn (i.2, i.1)).inv₀
        (fun x _ => (G.value (i.2, i.1) x).ne_zero)

/-- Since the two refinements use the same paired preferred chart, the
preferred multiplier is exactly the specified cross-cover gauge unit. -/
theorem toGauge_preferredMultiplier (x : M) :
    G.toGauge.preferredMultiplier x = G.value (A.indexAt x, B.indexAt x) x := by
  change B.transition (B.indexAt x) (B.indexAt x) x *
    G.value (A.indexAt x, B.indexAt x) x = _
  rw [B.transition_self _ _ (B.mem_baseSet_at x), one_mul]

/-- The corresponding continuous complex-linear equivalence of the
two original fibres. -/
def fiberEquiv (x : M) : A.core.Fiber x ≃L[ℂ] B.core.Fiber x :=
  ((leftRefinementFiberEquiv A B x).trans (G.toGauge.fiberEquiv x)).trans
    (rightRefinementFiberEquiv A B x).symm

theorem fiberEquiv_apply (x : M) (v : A.core.Fiber x) :
    G.fiberEquiv x v = (G.value (A.indexAt x, B.indexAt x) x : ℂ) * id (α := ℂ) v := by
  change (G.toGauge.preferredMultiplier x : ℂ) * id (α := ℂ) v = _
  rw [G.toGauge_preferredMultiplier]

theorem fiberEquiv_symm_apply (x : M) (v : B.core.Fiber x) :
    (G.fiberEquiv x).symm v =
      (G.value (A.indexAt x, B.indexAt x) x : ℂ)⁻¹ * id (α := ℂ) v := by
  change (G.toGauge.preferredMultiplier x : ℂ)⁻¹ * id (α := ℂ) v = _
  rw [G.toGauge_preferredMultiplier]

variable [A.IsHolomorphic I] [B.IsHolomorphic I]

/-- A cross-cover gauge gives a genuine fibrewise-linear
biholomorphism between the original independently constructed bundles. -/
def diffeomorph : Diffeomorph (I.prod I₁) (I.prod I₁)
    A.core.TotalSpace B.core.TotalSpace ω :=
  ((leftRefinementDiffeomorph A B I).trans G.toGauge.diffeomorph).trans
    (rightRefinementDiffeomorph A B I).symm

@[simp] theorem diffeomorph_proj (p : A.core.TotalSpace) :
    (G.diffeomorph p).proj = p.proj := rfl

@[simp] theorem diffeomorph_symm_proj (p : B.core.TotalSpace) :
    (G.diffeomorph.symm p).proj = p.proj := rfl

theorem diffeomorph_mk (x : M) (v : A.core.Fiber x) :
    G.diffeomorph ⟨x, v⟩ = ⟨x, G.fiberEquiv x v⟩ := rfl

theorem diffeomorph_symm_mk (x : M) (v : B.core.Fiber x) :
    G.diffeomorph.symm ⟨x, v⟩ = ⟨x, (G.fiberEquiv x).symm v⟩ := rfl

/-- Exact forward coefficient in an original source chart and an
independently indexed original target chart. -/
theorem diffeomorph_localCoefficient (i : ι) (j : κ) (p : A.core.TotalSpace)
    (hp : p.proj ∈ A.baseSet i ∩ B.baseSet j) :
    (B.core.localTriv j (G.diffeomorph p)).2 =
      (G.value (i, j) p.proj : ℂ) * (A.core.localTriv i p).2 := by
  calc
    (B.core.localTriv j (G.diffeomorph p)).2 =
        ((rightRefinement A B).core.localTriv (i, j)
          (G.toGauge.diffeomorph (leftRefinementDiffeomorph A B I p))).2 :=
      congrArg Prod.snd (rightRefinementDiffeomorph_symm_localTriv A B I (i, j) _)
    _ = (G.value (i, j) p.proj : ℂ) *
        ((leftRefinement A B).core.localTriv (i, j)
          (leftRefinementDiffeomorph A B I p)).2 :=
      G.toGauge.diffeomorph_localCoefficient (i, j) _ hp
    _ = _ := congrArg (fun q : M × ℂ => (G.value (i, j) p.proj : ℂ) * q.2)
      (leftRefinementDiffeomorph_localTriv A B I (i, j) p)

/-- Exact reciprocal coefficient for the inverse in the same two
original bundle charts. -/
theorem diffeomorph_symm_localCoefficient (i : ι) (j : κ) (p : B.core.TotalSpace)
    (hp : p.proj ∈ A.baseSet i ∩ B.baseSet j) :
    (A.core.localTriv i (G.diffeomorph.symm p)).2 =
      (G.value (i, j) p.proj : ℂ)⁻¹ * (B.core.localTriv j p).2 := by
  calc
    (A.core.localTriv i (G.diffeomorph.symm p)).2 =
        ((leftRefinement A B).core.localTriv (i, j)
          (G.toGauge.diffeomorph.symm (rightRefinementDiffeomorph A B I p))).2 :=
      congrArg Prod.snd (leftRefinementDiffeomorph_symm_localTriv A B I (i, j) _)
    _ = (G.value (i, j) p.proj : ℂ)⁻¹ *
        ((rightRefinement A B).core.localTriv (i, j)
          (rightRefinementDiffeomorph A B I p)).2 :=
      G.toGauge.diffeomorph_symm_localCoefficient (i, j) _ hp
    _ = _ := congrArg (fun q : M × ℂ => (G.value (i, j) p.proj : ℂ)⁻¹ * q.2)
      (rightRefinementDiffeomorph_localTriv A B I (i, j) p)

theorem diffeomorph_add (x : M) (v w : A.core.Fiber x) :
    id (α := B.core.Fiber x) (G.diffeomorph ⟨x, v + w⟩).2 =
      id (α := B.core.Fiber x) (G.diffeomorph ⟨x, v⟩).2 +
        id (α := B.core.Fiber x) (G.diffeomorph ⟨x, w⟩).2 :=
  (G.fiberEquiv x).map_add v w

theorem diffeomorph_smul (x : M) (c : ℂ) (v : A.core.Fiber x) :
    id (α := B.core.Fiber x) (G.diffeomorph ⟨x, c • v⟩).2 =
      c • id (α := B.core.Fiber x) (G.diffeomorph ⟨x, v⟩).2 :=
  (G.fiberEquiv x).map_smul c v

/-- The reciprocal cross-gauge gives the actual inverse map on the
original total spaces. -/
theorem symm_diffeomorph_apply (p : B.core.TotalSpace) :
    G.symm.diffeomorph p = G.diffeomorph.symm p := by
  cases p with
  | mk x v =>
    change (⟨x, (G.symm.toGauge.preferredMultiplier x : ℂ) * id (α := ℂ) v⟩ :
      A.core.TotalSpace) = ⟨x, (G.toGauge.preferredMultiplier x : ℂ)⁻¹ * id (α := ℂ) v⟩
    rw [G.symm.toGauge_preferredMultiplier, G.toGauge_preferredMultiplier]
    simp only [symm, Units.val_inv_eq_inv_val]

end CrossGauge

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
