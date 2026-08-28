import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleRefinementGauge
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreSections

/-!
# Gauge units extracted from actual bundle maps on an open set

A unit multiplier in the preferred fibres defines a fibrewise-linear
map between two independently constructed native line bundles. If that
actual total-space map is holomorphic over an open set, its local gauge
coefficients are holomorphic on every chart-pair intersection there.
The coefficients are obtained by applying the map to the actual source
chart frame and then reading the actual target chart coefficient.
Their cross-gauge compatibility follows from the original bundle
cocycles, without a separate compatibility assumption on the map.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.OpenMaps

open HolomorphicCharacterBundle

variable {M ι η : Type*} [TopologicalSpace M]
    (A : TransitionData M ι) (B : TransitionData M η) (h : M → ℂˣ)

/-- The actual total-space map with the specified preferred-fibre multiplier. -/
def preferredMap (p : A.core.TotalSpace) : B.core.TotalSpace :=
  ⟨p.proj, (h p.proj : ℂ) * id (α := ℂ) p.2⟩

@[simp] theorem preferredMap_proj (p : A.core.TotalSpace) :
    (preferredMap A B h p).proj = p.proj := rfl

@[simp] theorem preferredMap_mk (x : M) (v : A.core.Fiber x) :
    preferredMap A B h ⟨x, v⟩ = ⟨x, (h x : ℂ) * id (α := ℂ) v⟩ := rfl

/-- Each map on the actual fibres is a continuous complex-linear equivalence. -/
def fiberEquiv (x : M) : A.core.Fiber x ≃L[ℂ] B.core.Fiber x where
  toFun v := (h x : ℂ) * id (α := ℂ) v
  invFun w := (h x : ℂ)⁻¹ * id (α := ℂ) w
  map_add' v w := mul_add _ (id (α := ℂ) v) (id (α := ℂ) w)
  map_smul' c v := mul_left_comm _ c (id (α := ℂ) v)
  left_inv v := inv_mul_cancel_left₀ (h x).ne_zero (id (α := ℂ) v)
  right_inv w := mul_inv_cancel_left₀ (h x).ne_zero (id (α := ℂ) w)
  continuous_toFun := by
    change Continuous (fun v : ℂ => (h x : ℂ) * v)
    exact continuous_const.mul continuous_id
  continuous_invFun := by
    change Continuous (fun w : ℂ => (h x : ℂ)⁻¹ * w)
    exact continuous_const.mul continuous_id

theorem preferredMap_fiberEquiv (x : M) (v : A.core.Fiber x) :
    preferredMap A B h ⟨x, v⟩ = ⟨x, fiberEquiv A B h x v⟩ := rfl

/-- The actual source chart frame, obtained by inverting its fibre coefficient `1`. -/
def localFrame (i : ι) (x : M) : A.core.Fiber x := (A.core.localTriv i).symm x 1

def localFrameMap (i : ι) (x : M) : A.core.TotalSpace := ⟨x, localFrame A i x⟩

@[simp] theorem localFrameMap_proj (i : ι) (x : M) :
    (localFrameMap A i x).proj = x := rfl

theorem localFrame_localTriv (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    A.core.localTriv i (localFrameMap A i x) = (x, 1) :=
  (A.core.localTriv i).apply_mk_symm hx 1

theorem localFrame_preferred (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    id (α := ℂ) (localFrame A i x) = (A.transition i (A.indexAt x) x : ℂ) := by
  calc
    id (α := ℂ) (localFrame A i x) = (A.transition i (A.indexAt x) x : ℂ) * 1 :=
      A.core_localTriv_fiber_symm i hx 1
    _ = _ := mul_one _

/-- The target coefficient of the image of source chart coefficient `1`. -/
def chartUnit (i : ι × η) (x : M) : ℂˣ :=
  B.transition (B.indexAt x) i.2 x * h x * A.transition i.1 (A.indexAt x) x

theorem chartUnit_mul_source_transition (i : ι × η) {x : M}
    (hx : x ∈ A.baseSet i.1) :
    chartUnit A B h i x * A.transition (A.indexAt x) i.1 x =
      B.transition (B.indexAt x) i.2 x * h x := by
  have hA : A.transition i.1 (A.indexAt x) x * A.transition (A.indexAt x) i.1 x = 1 :=
    (A.transition_comp (A.indexAt x) i.1 (A.indexAt x) x
      ⟨⟨A.mem_baseSet_at x, hx⟩, A.mem_baseSet_at x⟩).trans
        (A.transition_self _ _ (A.mem_baseSet_at x))
  change (B.transition (B.indexAt x) i.2 x * h x * A.transition i.1 (A.indexAt x) x) *
    A.transition (A.indexAt x) i.1 x = _
  rw [mul_assoc, hA, mul_one]

/-- The formula for the local gauge is the literal target chart reading
of the image of the genuine source frame. -/
theorem chartUnit_eq_frameImage (i : ι × η) {x : M}
    (hx : x ∈ A.baseSet i.1 ∩ B.baseSet i.2) :
    (chartUnit A B h i x : ℂ) =
      (B.core.localTriv i.2 (preferredMap A B h (localFrameMap A i.1 x))).2 := by
  change (B.transition (B.indexAt x) i.2 x : ℂ) * (h x : ℂ) *
      (A.transition i.1 (A.indexAt x) x : ℂ) =
    (B.transition (B.indexAt x) i.2 x : ℂ) *
      ((h x : ℂ) * id (α := ℂ) (localFrame A i.1 x))
  rw [localFrame_preferred A i.1 hx.1, mul_assoc]

/-- The actual map multiplies every source coefficient by its extracted
chart unit, in the independently chosen original bundle charts. -/
theorem preferredMap_localCoefficient (i : ι × η) (p : A.core.TotalSpace)
    (hp : p.proj ∈ A.baseSet i.1 ∩ B.baseSet i.2) :
    (B.core.localTriv i.2 (preferredMap A B h p)).2 =
      (chartUnit A B h i p.proj : ℂ) * (A.core.localTriv i.1 p).2 := by
  have he := congrArg (fun u : ℂˣ => (u : ℂ))
    (chartUnit_mul_source_transition A B h i hp.1)
  change (chartUnit A B h i p.proj : ℂ) * (A.transition (A.indexAt p.proj) i.1 p.proj : ℂ) =
    (B.transition (B.indexAt p.proj) i.2 p.proj : ℂ) * (h p.proj : ℂ) at he
  change (B.transition (B.indexAt p.proj) i.2 p.proj : ℂ) *
      ((h p.proj : ℂ) * id (α := ℂ) p.2) =
    (chartUnit A B h i p.proj : ℂ) *
      ((A.transition (A.indexAt p.proj) i.1 p.proj : ℂ) * id (α := ℂ) p.2)
  rw [← mul_assoc, ← he, mul_assoc]

/-- Compatibility of the extracted units is a consequence of the two
actual bundle cocycles. It is not an extra hypothesis on the bundle map. -/
theorem chartUnit_compatible (i j : ι × η) (x : M)
    (hx : x ∈ (A.baseSet i.1 ∩ B.baseSet i.2) ∩ (A.baseSet j.1 ∩ B.baseSet j.2)) :
    B.transition i.2 j.2 x * chartUnit A B h i x =
      chartUnit A B h j x * A.transition i.1 j.1 x := by
  have hB := B.transition_comp (B.indexAt x) i.2 j.2 x
    ⟨⟨B.mem_baseSet_at x, hx.1.2⟩, hx.2.2⟩
  have hA := A.transition_comp i.1 j.1 (A.indexAt x) x
    ⟨⟨hx.1.1, hx.2.1⟩, A.mem_baseSet_at x⟩
  calc
    B.transition i.2 j.2 x * chartUnit A B h i x =
        (B.transition i.2 j.2 x * B.transition (B.indexAt x) i.2 x) * h x *
          A.transition i.1 (A.indexAt x) x := by simp only [chartUnit, mul_assoc]
    _ = B.transition (B.indexAt x) j.2 x * h x * A.transition i.1 (A.indexAt x) x := by
      rw [hB]
    _ = (B.transition (B.indexAt x) j.2 x * h x) *
        (A.transition j.1 (A.indexAt x) x * A.transition i.1 j.1 x) := by rw [hA]
    _ = chartUnit A B h j x * A.transition i.1 j.1 x := (mul_assoc _ _ _).symm

/-- Equality of preferred multipliers gives equality of the extracted
units wherever the original maps agree in that fibre. -/
theorem chartUnit_eq_of_multiplier_eq {h' : M → ℂˣ} (i : ι × η) {x : M}
    (hx : h x = h' x) : chartUnit A B h i x = chartUnit A B h' i x := by
  simp only [chartUnit, hx]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The actual source frame is holomorphic on its own original chart. -/
theorem localFrameMap_holomorphicOn [A.IsHolomorphic I] (i : ι) :
    ContMDiffOn I (I.prod I₁) ω (localFrameMap A i) (A.baseSet i) := by
  apply ((A.core.localTriv i).contMDiffOn_iff
    (f := localFrameMap A i) (fun _ hx => hx)).mpr
  refine ⟨contMDiffOn_id, ?_⟩
  apply (contMDiffOn_const (c := (1 : ℂ))).congr
  intro x hx
  exact congrArg Prod.snd (localFrame_localTriv A i hx)

/-- Holomorphicity of the actual native total-space map implies
holomorphicity of every extracted local unit on the relevant coarse open.
The preferred multiplier itself need not be holomorphic in base coordinates. -/
theorem chartUnit_holomorphicOn [A.IsHolomorphic I] [B.IsHolomorphic I]
    (U : Opens M)
    (hmap : ContMDiffOn (I.prod I₁) (I.prod I₁) ω (preferredMap A B h)
      ((Bundle.TotalSpace.proj : A.core.TotalSpace → M) ⁻¹' (U : Set M)))
    (i : ι × η) :
    ContMDiffOn I I₁ ω (fun x => (chartUnit A B h i x : ℂ))
      ((A.baseSet i.1 ∩ B.baseSet i.2) ∩ U) := by
  have hs : ContMDiffOn I (I.prod I₁) ω
      (preferredMap A B h ∘ localFrameMap A i.1)
      ((A.baseSet i.1 ∩ B.baseSet i.2) ∩ U) :=
    hmap.comp ((localFrameMap_holomorphicOn A I i.1).mono (fun _ hx => hx.1.1))
      (fun _ hx => hx.2)
  have hc := (((B.core.localTriv i.2).contMDiffOn_iff
    (f := preferredMap A B h ∘ localFrameMap A i.1)
    (fun _ hx => hx.1.2)).mp hs).2
  apply hc.congr
  intro x hx
  exact chartUnit_eq_frameImage A B h i hx.1

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.OpenMaps
