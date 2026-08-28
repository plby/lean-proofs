import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMaps

/-!
# Composing actual native line-bundle comparisons

Local gauge units can be recovered from an actual holomorphic native
fibrewise multiplier map.  Consequently compositions of the proved
native bundle biholomorphisms give genuine cross-cover gauges.  The
construction uses holomorphicity of those actual total-space maps;
it does not require the discontinuously selected preferred multiplier
to be holomorphic as a scalar function on the base.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι κ ν : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners ℂ E H}

local notation "I₁" => modelWithCornersSelf ℂ ℂ

namespace CrossGauge

variable (A : TransitionData M ι) (B : TransitionData M κ)
  [A.IsHolomorphic I] [B.IsHolomorphic I]

/-- An actual holomorphic native multiplier map supplies all local
holomorphic units and their cocycle compatibility. -/
def ofPreferredMap (h : M → ℂˣ)
    (hh : ContMDiff (I.prod I₁) (I.prod I₁) ω (OpenMaps.preferredMap A B h)) :
    CrossGauge I A B where
  value := OpenMaps.chartUnit A B h
  compatible := OpenMaps.chartUnit_compatible A B h
  holomorphicOn i := by
    simpa only [TopologicalSpace.Opens.coe_top, Set.inter_univ, Set.preimage_univ] using
      OpenMaps.chartUnit_holomorphicOn A B h I ⊤ hh.contMDiffOn i

theorem ofPreferredMap_value_preferred (h : M → ℂˣ)
    (hh : ContMDiff (I.prod I₁) (I.prod I₁) ω (OpenMaps.preferredMap A B h)) (x : M) :
    (ofPreferredMap A B h hh).value (A.indexAt x, B.indexAt x) x = h x := by
  change B.transition (B.indexAt x) (B.indexAt x) x * h x *
    A.transition (A.indexAt x) (A.indexAt x) x = h x
  rw [B.transition_self _ _ (B.mem_baseSet_at x),
    A.transition_self _ _ (A.mem_baseSet_at x), one_mul, mul_one]

/-- Recovering the local units does not alter the original native map. -/
theorem ofPreferredMap_diffeomorph_apply (h : M → ℂˣ)
    (hh : ContMDiff (I.prod I₁) (I.prod I₁) ω (OpenMaps.preferredMap A B h))
    (p : A.core.TotalSpace) :
    (ofPreferredMap A B h hh).diffeomorph p = OpenMaps.preferredMap A B h p := by
  cases p with
  | mk x v =>
    rw [diffeomorph_mk, fiberEquiv_apply, ofPreferredMap_value_preferred]
    rfl

variable {A B} {C : TransitionData M ν} [C.IsHolomorphic I]
  (G : CrossGauge I A B) (J : CrossGauge I B C)

private def compositionMultiplier (x : M) : ℂˣ :=
  J.value (B.indexAt x, C.indexAt x) x * G.value (A.indexAt x, B.indexAt x) x

private theorem compositionMultiplier_map (p : A.core.TotalSpace) :
    OpenMaps.preferredMap A C (compositionMultiplier G J) p =
      J.diffeomorph (G.diffeomorph p) := by
  cases p with
  | mk x v =>
    rw [G.diffeomorph_mk, J.diffeomorph_mk, J.fiberEquiv_apply, G.fiberEquiv_apply]
    change (⟨x, ((J.value (B.indexAt x, C.indexAt x) x : ℂ) *
        (G.value (A.indexAt x, B.indexAt x) x : ℂ)) * id (α := ℂ) v⟩ : C.core.TotalSpace) =
      ⟨x, (J.value (B.indexAt x, C.indexAt x) x : ℂ) *
        ((G.value (A.indexAt x, B.indexAt x) x : ℂ) * id (α := ℂ) v)⟩
    rw [mul_assoc]

private theorem compositionMultiplier_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω
      (OpenMaps.preferredMap A C (compositionMultiplier G J)) := by
  have he : OpenMaps.preferredMap A C (compositionMultiplier G J) =
      J.diffeomorph ∘ G.diffeomorph := funext (compositionMultiplier_map G J)
  rw [he]
  exact J.diffeomorph.contMDiff.comp G.diffeomorph.contMDiff

/-- Composition is implemented by the original holomorphic maps, with
its local gauge compatibility proved by their native chart formulas. -/
def trans : CrossGauge I A C :=
  ofPreferredMap A C (compositionMultiplier G J) (compositionMultiplier_holomorphic G J)

theorem trans_diffeomorph_apply (p : A.core.TotalSpace) :
    (G.trans J).diffeomorph p = J.diffeomorph (G.diffeomorph p) :=
  (ofPreferredMap_diffeomorph_apply A C _ _ p).trans (compositionMultiplier_map G J p)

theorem trans_fiberEquiv_apply (x : M) (v : A.core.Fiber x) :
    (G.trans J).fiberEquiv x v = J.fiberEquiv x (G.fiberEquiv x v) :=
  congrArg (fun p : C.core.TotalSpace => id (α := ℂ) p.2)
    (G.trans_diffeomorph_apply J ⟨x, v⟩)

end CrossGauge

namespace Gauge

variable {A B : TransitionData M ι} [A.IsHolomorphic I] [B.IsHolomorphic I]
  (G : Gauge I A B)

/-- A same-cover gauge is a cross-cover gauge of the same original
bundles; no equality of their preferred chart selectors is needed. -/
def toCrossGauge : CrossGauge I A B :=
  CrossGauge.ofPreferredMap A B G.preferredMultiplier G.map_holomorphic

theorem toCrossGauge_diffeomorph_apply (p : A.core.TotalSpace) :
    G.toCrossGauge.diffeomorph p = G.diffeomorph p :=
  CrossGauge.ofPreferredMap_diffeomorph_apply A B G.preferredMultiplier G.map_holomorphic p

theorem toCrossGauge_fiberEquiv_apply (x : M) (v : A.core.Fiber x) :
    G.toCrossGauge.fiberEquiv x v = G.fiberEquiv x v :=
  congrArg (fun p : B.core.TotalSpace => id (α := ℂ) p.2)
    (G.toCrossGauge_diffeomorph_apply ⟨x, v⟩)

end Gauge

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
