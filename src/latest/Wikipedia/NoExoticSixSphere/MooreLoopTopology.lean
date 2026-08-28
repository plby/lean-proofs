import Wikipedia.NoExoticSixSphere.MooreLoop

/-!
# Continuous Moore-loop multiplication and normalization

The topology records both the duration and the compact-open curve. The
piecewise concatenation is jointly continuous, including at its moving
join. Normalization produces an actual native path on the unit interval.
No homotopy equivalence is asserted here.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.Moore.Loop

variable {Y : Type*} [TopologicalSpace Y] {y₀ : Y}

theorem continuous_duration : Continuous (duration : Loop y₀ → ℝ) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_curve : Continuous (curve : Loop y₀ → C(ℝ, Y)) :=
  continuous_snd.comp continuous_subtype_val

instance [T2Space Y] : T2Space (Loop y₀) :=
  T2Space.of_injective_continuous (f := fun p : Loop y₀ ↦ p.val)
    Subtype.val_injective continuous_subtype_val

theorem continuous_curve_apply {T : Type*} [TopologicalSpace T]
    (p : T → Loop y₀) (hp : Continuous p) (t : T → ℝ) (ht : Continuous t) :
    Continuous (fun x ↦ (p x).curve (t x)) :=
  continuous_eval.comp ((continuous_curve.comp hp).prodMk ht)

theorem continuous_concatenate_evaluation :
    Continuous (fun u : (Loop y₀ × Loop y₀) × ℝ ↦
      (concatenate u.1.1 u.1.2).curve u.2) := by
  have hp : Continuous (fun u : (Loop y₀ × Loop y₀) × ℝ ↦ u.1.1) :=
    continuous_fst.comp continuous_fst
  have hq : Continuous (fun u : (Loop y₀ × Loop y₀) × ℝ ↦ u.1.2) :=
    continuous_snd.comp continuous_fst
  have hd := continuous_duration.comp hp
  have hleft := continuous_curve_apply _ hp (fun u ↦ u.2) continuous_snd
  have hright := continuous_curve_apply _ hq
    (fun u ↦ u.2 - u.1.1.duration) (continuous_snd.sub hd)
  apply hleft.if_le hright continuous_snd hd
  intro u hu
  change u.2 = u.1.1.duration at hu
  rw [hu, sub_self, curve_duration, curve_zero]

theorem continuous_concatenate :
    Continuous (fun p : Loop y₀ × Loop y₀ ↦ concatenate p.1 p.2) := by
  have hd : Continuous (fun p : Loop y₀ × Loop y₀ ↦
      (concatenate p.1 p.2).duration) :=
    (continuous_duration.comp continuous_fst).add
      (continuous_duration.comp continuous_snd)
  have hc : Continuous (fun p : Loop y₀ × Loop y₀ ↦
      (concatenate p.1 p.2).curve) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_concatenate_evaluation
  exact (hd.prodMk hc).subtype_mk _

instance : ContinuousMul (Loop y₀) := ⟨continuous_concatenate⟩

def toPath (p : Loop y₀) : Path y₀ y₀ where
  toFun t := p.curve (p.duration * (t : ℝ))
  continuous_toFun := p.curve.continuous.comp
    (continuous_const.mul continuous_subtype_val)
  source' := by
    change p.curve (p.duration * 0) = y₀
    rw [mul_zero, curve_zero]
  target' := by
    change p.curve (p.duration * 1) = y₀
    rw [mul_one, curve_duration]

theorem toPath_apply (p : Loop y₀) (t : I) : toPath p t = p.curve (p.duration * (t : ℝ)) := rfl

theorem continuous_toPath : Continuous (toPath : Loop y₀ → Path y₀ y₀) := by
  apply Path.continuous_uncurry_iff.mp
  exact continuous_curve_apply _ continuous_fst
    (fun u : Loop y₀ × I ↦ u.1.duration * (u.2 : ℝ))
    ((continuous_duration.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))

theorem toPath_one : toPath (1 : Loop y₀) = Path.refl y₀ := by
  apply Path.ext
  funext t
  rfl

end NoExoticSixSphere.Moore.Loop
