import Wikipedia.NoExoticSixSphere.MooreLoopCommutatorAxes
import Wikipedia.NoExoticSixSphere.MooreLoopMultiplication

/-!
# Normalizing the actual Moore commutator

Adjust durations successively at the three multiplication vertices.
At time one this gives exactly the left-associated native path
commutator. The construction is continuous also at zero durations and
fixes the common constant path throughout. It does not give strict
inverses in the Moore-loop monoid.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.Moore.Loop

variable {Y : Type*} [TopologicalSpace Y] {y₀ : Y}

theorem curve_eq_basepoint_of_toPath_eq_refl (p : Loop y₀)
    (hp : toPath p = Path.refl y₀) (t : ℝ) : p.curve t = y₀ := by
  rw [← toPath_extend_retime p t, hp]
  rfl

theorem toPath_mul_eq_refl (p q : Loop y₀)
    (hp : toPath p = Path.refl y₀) (hq : toPath q = Path.refl y₀) :
    toPath (p * q) = Path.refl y₀ := by
  apply Path.ext
  funext t
  rw [toPath_apply, curve_mul]
  split_ifs
  · exact curve_eq_basepoint_of_toPath_eq_refl p hp _
  · exact curve_eq_basepoint_of_toPath_eq_refl q hq _

def adjustedProduct (s : I) (p q : Loop y₀) : Loop y₀ :=
  adjustment (s, adjustment (s, p) * adjustment (s, q))

theorem continuous_adjustedProduct :
    Continuous (fun u : I × (Loop y₀ × Loop y₀) ↦ adjustedProduct u.1 u.2.1 u.2.2) := by
  have hl : Continuous (fun u : I × (Loop y₀ × Loop y₀) ↦ adjustment (u.1, u.2.1)) :=
    continuous_adjustment.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hr : Continuous (fun u : I × (Loop y₀ × Loop y₀) ↦ adjustment (u.1, u.2.2)) :=
    continuous_adjustment.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  exact continuous_adjustment.comp (continuous_fst.prodMk (hl.mul hr))

theorem adjustedProduct_zero (p q : Loop y₀) : adjustedProduct 0 p q = p * q := by
  simp only [adjustedProduct, adjustment_zero]

theorem adjustedProduct_one (p q : Loop y₀) :
    adjustedProduct 1 p q = ofPath ((toPath p).trans (toPath q)) := by
  simp only [adjustedProduct, adjustment_one, toPath_ofPath_mul]

theorem toPath_adjustedProduct_eq_refl (s : I) (p q : Loop y₀)
    (hp : toPath p = Path.refl y₀) (hq : toPath q = Path.refl y₀) :
    toPath (adjustedProduct s p q) = Path.refl y₀ := by
  change toPath (adjustment (s, adjustment (s, p) * adjustment (s, q))) = _
  rw [normalization_adjustment]
  exact toPath_mul_eq_refl _ _ ((normalization_adjustment _).trans hp)
    ((normalization_adjustment _).trans hq)

def commutatorDeformation (u : I × (Loop y₀ × Loop y₀)) : Loop y₀ :=
  adjustedProduct u.1
    (adjustedProduct u.1 (adjustedProduct u.1 u.2.1 u.2.2) (reverse u.2.1))
    (reverse u.2.2)

theorem continuous_commutatorDeformation :
    Continuous (commutatorDeformation (y₀ := y₀)) := by
  have hl : Continuous (fun u : I × (Loop y₀ × Loop y₀) ↦ reverse u.2.1) :=
    continuous_reverse.comp (continuous_fst.comp continuous_snd)
  have hr : Continuous (fun u : I × (Loop y₀ × Loop y₀) ↦ reverse u.2.2) :=
    continuous_reverse.comp (continuous_snd.comp continuous_snd)
  have hm := continuous_adjustedProduct.comp
    (continuous_fst.prodMk (continuous_adjustedProduct.prodMk hl))
  exact continuous_adjustedProduct.comp (continuous_fst.prodMk (hm.prodMk hr))

theorem commutatorDeformation_zero (p : Loop y₀ × Loop y₀) :
    commutatorDeformation (0, p) = commutatorMap p := by
  simp only [commutatorDeformation, adjustedProduct_zero]
  rfl

def pathCommutator : C(Loop y₀ × Loop y₀, Path y₀ y₀) :=
  ⟨fun p ↦ (((toPath p.1).trans (toPath p.2)).trans (toPath p.1).symm).trans
      (toPath p.2).symm,
    (((continuous_toPath.comp continuous_fst).path_trans
      (continuous_toPath.comp continuous_snd)).path_trans
        (Path.continuous_symm.comp (continuous_toPath.comp continuous_fst))).path_trans
          (Path.continuous_symm.comp (continuous_toPath.comp continuous_snd))⟩

theorem commutatorDeformation_one (p : Loop y₀ × Loop y₀) :
    toPath (commutatorDeformation (1, p)) = pathCommutator p := by
  simp only [commutatorDeformation, adjustedProduct_one, toPath_ofPath, toPath_reverse]
  rfl

theorem commutatorDeformation_identity (s : I) :
    toPath (commutatorDeformation (s, ((1 : Loop y₀), 1))) = Path.refl y₀ := by
  change toPath (adjustedProduct s
    (adjustedProduct s (adjustedProduct s 1 1) (reverse 1)) (reverse 1)) = _
  rw [reverse_one]
  apply toPath_adjustedProduct_eq_refl _ _ _ _ toPath_one
  apply toPath_adjustedProduct_eq_refl _ _ _ _ toPath_one
  exact toPath_adjustedProduct_eq_refl _ _ _ toPath_one toPath_one

def commutatorNormalizationHomotopy :
    (normalizationMap.comp (commutatorMap (y₀ := y₀))).HomotopyRel
      pathCommutator {(1, 1)} where
  toFun u := toPath (commutatorDeformation u)
  continuous_toFun := continuous_toPath.comp continuous_commutatorDeformation
  map_zero_left p := congrArg toPath (commutatorDeformation_zero p)
  map_one_left := commutatorDeformation_one
  prop' := by
    intro s p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change toPath (commutatorDeformation (s, ((1 : Loop y₀), 1))) =
      toPath (commutatorMap (1, 1))
    rw [commutatorDeformation_identity, commutator_one_left, reverse_one, mul_one, toPath_one]

end NoExoticSixSphere.Moore.Loop
