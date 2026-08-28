import Mathlib.Topology.Homotopy.Lifting

/-!
# Lifting a shrinking homotopy through the actual covering

The homotopy lifting property supplies the upstairs homotopy.  Uniqueness
of path lifts makes it fix the lifted zero fibre and commute with every
deck transformation.  Size inequalities are preserved because the
lifted map has the prescribed projection.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspPositiveRetraction.Covering

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
variable {q : E → B} (hq : IsCoveringMap q)
variable (H : C(unitInterval × B, B)) (hzero : ∀ b, H (0, b) = b)

def pullback : C(unitInterval × E, B) where
  toFun p := H (p.1, q p.2)
  continuous_toFun := H.continuous.comp
    (continuous_fst.prodMk (hq.isLocalHomeomorph.continuous.comp continuous_snd))

/-- The actual lift starting at the identity of the covering space. -/
def lift : C(unitInterval × E, E) :=
  hq.liftHomotopy (pullback hq H) (ContinuousMap.id E) (fun x => hzero (q x))

@[simp] theorem lift_zero (x : E) : lift hq H hzero (0, x) = x :=
  hq.liftHomotopy_zero _ _ _ x

theorem lift_projection (s : unitInterval) (x : E) :
    q (lift hq H hzero (s, x)) = H (s, q x) :=
  congr_fun (hq.liftHomotopy_lifts (pullback hq H) (ContinuousMap.id E)
    (fun y => hzero (q y))) (s, x)

/-- A stationary point downstairs has a stationary lifted path. -/
theorem lift_fixed (x : E) (hx : ∀ s : unitInterval, H (s, q x) = q x)
    (s : unitInterval) : lift hq H hzero (s, x) = x := by
  have hc : Continuous (fun t : unitInterval => lift hq H hzero (t, x)) :=
    (lift hq H hzero).continuous.comp (continuous_id.prodMk continuous_const)
  have h := hq.const_of_comp hc
    (fun t t' => by simp only [lift_projection hq H hzero, hx]) s 0
  exact h.trans (lift_zero hq H hzero x)

/-- Deck equivariance follows from uniqueness, not an equivariant choice
of local lifts. -/
theorem lift_equivariant {G : Type*} [Group G] [MulAction G E]
    [ContinuousConstSMul G E] (hdeck : ∀ (g : G) (x : E), q (g • x) = q x)
    (g : G) (s : unitInterval) (x : E) :
    lift hq H hzero (s, g • x) = g • lift hq H hzero (s, x) := by
  have hleft : Continuous (fun t : unitInterval => lift hq H hzero (t, g • x)) :=
    (lift hq H hzero).continuous.comp (continuous_id.prodMk continuous_const)
  have hright : Continuous (fun t : unitInterval => g • lift hq H hzero (t, x)) :=
    (continuous_const_smul g).comp
      ((lift hq H hzero).continuous.comp (continuous_id.prodMk continuous_const))
  have he : q ∘ (fun t : unitInterval => lift hq H hzero (t, g • x)) =
      q ∘ (fun t : unitInterval => g • lift hq H hzero (t, x)) := by
    funext t
    simp only [Function.comp_apply, lift_projection hq H hzero, hdeck]
  exact congr_fun (hq.eq_of_comp_eq hleft hright he 0 (by simp only [lift_zero])) s

theorem lift_height_le (f : B → ℝ)
    (hsize : ∀ (s : unitInterval) b, f (H (s, b)) ≤ f b)
    (s : unitInterval) (x : E) :
    f (q (lift hq H hzero (s, x))) ≤ f (q x) := by
  rw [lift_projection hq H hzero]
  exact hsize s (q x)

/-- The lifted homotopy restricts to every preserved closed sublevel. -/
def liftSublevel (f : B → ℝ) (η : ℝ)
    (hsize : ∀ (s : unitInterval) b, f (H (s, b)) ≤ f b) :
    C(unitInterval × {x : E // f (q x) ≤ η}, {x : E // f (q x) ≤ η}) where
  toFun p := ⟨lift hq H hzero (p.1, p.2.1),
    (lift_height_le hq H hzero f hsize p.1 p.2.1).trans p.2.2⟩
  continuous_toFun := ((lift hq H hzero).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

@[simp] theorem liftSublevel_zero (f : B → ℝ) (η : ℝ)
    (hsize : ∀ (s : unitInterval) b, f (H (s, b)) ≤ f b)
    (x : {x : E // f (q x) ≤ η}) : liftSublevel hq H hzero f η hsize (0, x) = x :=
  Subtype.ext (lift_zero hq H hzero x)

theorem liftSublevel_fixed (f : B → ℝ) (η : ℝ)
    (hsize : ∀ (s : unitInterval) b, f (H (s, b)) ≤ f b)
    (hfix : ∀ (s : unitInterval) b, f b = 0 → H (s, b) = b)
    (s : unitInterval) (x : {x : E // f (q x) ≤ η}) (hx : f (q x) = 0) :
    liftSublevel hq H hzero f η hsize (s, x) = x :=
  Subtype.ext (lift_fixed hq H hzero x (fun t => hfix t (q x) hx) s)

theorem liftSublevel_one_zero (f : B → ℝ) (η : ℝ)
    (hsize : ∀ (s : unitInterval) b, f (H (s, b)) ≤ f b)
    (hone : ∀ b, f b ≤ η → f (H (1, b)) = 0)
    (x : {x : E // f (q x) ≤ η}) :
    f (q (liftSublevel hq H hzero f η hsize (1, x))) = 0 := by
  change f (q (lift hq H hzero (1, x.1))) = 0
  rw [lift_projection hq H hzero]
  exact hone (q x) x.2

end Wikipedia.HopfProblem.CuspPositiveRetraction.Covering
