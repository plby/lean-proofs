import Wikipedia.NoExoticSixSphere.CircleCylinderSeam

/-!
# Folding the actual circle double onto its positive half

The literal coordinate fold `(c₀, c₁) ↦ (c₀, |c₁|)` preserves the
circle clock and therefore the doubled map. It gives a continuous
retraction of its native regular fiber onto the nonnegative-time half.
No connectivity assumption is made on either endpoint or on the double.
-/

noncomputable section

open Function Set
open scoped Manifold

namespace NoExoticSixSphere.CircleCylinder

def ambientFold (v : V) : V :=
  WithLp.toLp 2 (Fin.cons (v 0) (fun _ : Fin 1 ↦ |v 1|))

theorem norm_ambientFold (v : V) : ‖ambientFold v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [ambientFold, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, star_trivial,
    Fin.sum_univ_zero, add_zero]
  change v 0 * v 0 + |v 1| * |v 1| = v 0 * v 0 + v 1 * v 1
  nlinarith [sq_abs (v 1)]

def fold (c : Sphere 1) : Sphere 1 := ⟨ambientFold c.val, by
  rw [Metric.mem_sphere, dist_zero_right]
  exact (norm_ambientFold c.val).trans (ClosedHemisphere.unit_norm c)⟩

theorem fold_head (c : Sphere 1) : (fold c).val 0 = c.val 0 := rfl

theorem seam_fold (c : Sphere 1) : seam (fold c) = |seam c| := rfl

theorem clock_fold (c : Sphere 1) : clock (fold c) = clock c := by
  simp only [clock_apply, fold_head]

theorem continuous_ambientFold : Continuous ambientFold := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact head.continuous
  · exact seamLinear.continuous.abs

theorem continuous_fold : Continuous fold :=
  (continuous_ambientFold.comp continuous_subtype_val).subtype_mk _

theorem fold_eq_self (c : Sphere 1) (hc : 0 ≤ seam c) : fold c = c := by
  apply Subtype.ext
  ext i
  fin_cases i
  · rfl
  · exact abs_of_nonneg hc

theorem fold_idempotent (c : Sphere 1) : fold (fold c) = fold c :=
  fold_eq_self (fold c) ((seam_fold c).symm ▸ abs_nonneg (seam c))

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem map_fold (p : Sphere 1 × Sphere m) : map d (fold p.1, p.2) = map d p := by
  change d.map (clock (fold p.1), p.2) = d.map (clock p.1, p.2)
  rw [clock_fold]

def fiberFold : C(Fiber d, Fiber d) where
  toFun p := ⟨(fold p.val.1, p.val.2), (map_fold d p.val).trans p.property⟩
  continuous_toFun := (((continuous_fold.comp continuous_fst).prodMk continuous_snd).comp
    continuous_subtype_val).subtype_mk _

theorem time_fiberFold (p : Fiber d) : time d (fiberFold d p) = |time d p| := rfl

theorem fiberFold_eq_self (p : Fiber d) (hp : 0 ≤ time d p) : fiberFold d p = p :=
  Subtype.ext (Prod.ext (fold_eq_self p.val.1 hp) rfl)

abbrev PositiveHalf := {p : Fiber d // 0 ≤ time d p}

def positiveRetraction : C(Fiber d, PositiveHalf d) where
  toFun p := ⟨fiberFold d p, (time_fiberFold d p).symm ▸ abs_nonneg (time d p)⟩
  continuous_toFun := (fiberFold d).continuous.subtype_mk _

theorem positiveRetraction_val (p : Fiber d) :
    (positiveRetraction d p).val = fiberFold d p := rfl

theorem positiveRetraction_retract (p : PositiveHalf d) :
    positiveRetraction d p.val = p := Subtype.ext (fiberFold_eq_self d p.val p.property)

theorem positiveRetraction_surjective : Surjective (positiveRetraction d) :=
  fun p ↦ ⟨p.val, positiveRetraction_retract d p⟩

end NoExoticSixSphere.CircleCylinder
