import Wikipedia.NoExoticSixSphere.OrthogonalRotations

/-!
# Local paths changing a column of an orthogonal operator

The reflection construction gives paths through actual orthogonal operators,
and left multiplication changes a prescribed column to any sufficiently nearby
unit-vector family. All paths depend continuously on the base point.
-/

open unitInterval

namespace NoExoticSixSphere.OrthogonalPaths

open GLOrthonormalization

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

/-- Package a genuine linear isometry equivalence in the orthogonal operator space. -/
noncomputable def ofEquiv (e : Vector n ≃ₗᵢ[ℝ] Vector n) : OrthogonalOperators n :=
  ⟨⟨e.toContinuousLinearEquiv.toContinuousLinearMap, ⟨e.toContinuousLinearEquiv, rfl⟩⟩, e.norm_map⟩

/-- The identity orthogonal operator. -/
noncomputable def identity (n : ℕ) : OrthogonalOperators n := ofEquiv (LinearIsometryEquiv.refl ℝ _)

/-- Compose actual orthogonal operators. -/
noncomputable def mul (a b : OrthogonalOperators n) : OrthogonalOperators n :=
  ⟨⟨a.1.1.comp b.1.1, a.1.2.comp b.1.2⟩, fun w ↦ (a.2 (b.1.1 w)).trans (b.2 w)⟩

/-- Identity multiplication does not change the underlying operator. -/
theorem identity_mul (a : OrthogonalOperators n) : mul (identity n) a = a := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  rfl

/-- Multiplication is continuous for the actual operator-norm topology. -/
theorem continuous_mul (a b : X → OrthogonalOperators n) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x ↦ mul (a x) (b x)) := by
  have hA : Continuous (fun x ↦ (a x).1.1) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp ha)
  have hB : Continuous (fun x ↦ (b x).1.1) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp hb)
  exact ((hA.clm_comp hB).subtype_mk _).subtype_mk _

/-- Pointwise multiplication of two continuous orthogonal families. -/
noncomputable def mulMap (a b : C(X, OrthogonalOperators n)) : C(X, OrthogonalOperators n) :=
  ⟨fun x ↦ mul (a x) (b x), continuous_mul a b a.continuous b.continuous⟩

/-- Left multiplication of a fixed family by an orthogonal homotopy is an orthogonal homotopy. -/
noncomputable def mulHomotopy {a b : C(X, OrthogonalOperators n)} (H : a.Homotopy b)
    (c : C(X, OrthogonalOperators n)) : (mulMap a c).Homotopy (mulMap b c) where
  toFun p := mul (H p) (c p.2)
  continuous_toFun := continuous_mul H (fun p ↦ c p.2) H.continuous
    (c.continuous.comp continuous_snd)
  map_zero_left x := by change mul (H (0, x)) (c x) = _; rw [H.apply_zero]; rfl
  map_one_left x := by change mul (H (1, x)) (c x) = _; rw [H.apply_one]; rfl

/-- Nearby unit-vector families determine a continuous family of actual rotations. -/
noncomputable def localRotations (f g : C(X, UnitSphere (Vector n)))
    (h : ∀ x, dist (g x : Vector n) (f x : Vector n) < 1) : C(X, OrthogonalOperators n) where
  toFun x := ofEquiv (localRotationEquiv (f x : Vector n) (g x : Vector n))
  continuous_toFun := by
    have hc := continuous_localRotationOperator (fun x ↦ (f x : Vector n))
      (fun x ↦ (g x : Vector n)) (continuous_subtype_val.comp f.continuous)
      (continuous_subtype_val.comp g.continuous)
      (fun x ↦ nearby_unit_ne_zero (f x) (g x) (h x))
      (fun x ↦ nearby_sum_ne_zero (f x) (g x) (h x))
    exact (hc.subtype_mk _).subtype_mk _

/-- These local rotations have exactly the prescribed effect on the initial unit vectors. -/
theorem localRotations_apply (f g : C(X, UnitSphere (Vector n)))
    (h : ∀ x, dist (g x : Vector n) (f x : Vector n) < 1) (x : X) :
    (localRotations f g h x).1.1 (f x : Vector n) = (g x : Vector n) :=
  localRotationEquiv_apply (f x) (g x)

/-- A continuous path from identity to the local rotations, through orthogonal operators. -/
noncomputable def localRotationHomotopy (f g : C(X, UnitSphere (Vector n)))
    (h : ∀ x, dist (g x : Vector n) (f x : Vector n) < 1) :
    (ContinuousMap.const X (identity n)).Homotopy (localRotations f g h) where
  toFun p := ofEquiv (localRotationEquiv (f p.2 : Vector n)
    ((f p.2 : Vector n) + (p.1 : ℝ) • ((g p.2 : Vector n) - (f p.2 : Vector n))))
  continuous_toFun := by
    let v : I × X → Vector n := fun p ↦ (f p.2 : Vector n)
    let w : I × X → Vector n := fun p ↦
      v p + (p.1 : ℝ) • ((g p.2 : Vector n) - v p)
    have hv : Continuous v := continuous_subtype_val.comp (f.continuous.comp continuous_snd)
    have hg : Continuous (fun p : I × X ↦ (g p.2 : Vector n)) :=
      continuous_subtype_val.comp (g.continuous.comp continuous_snd)
    have ht : Continuous (fun p : I × X ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hw : Continuous w := hv.add (ht.smul (hg.sub hv))
    have hn : ∀ p, w p ≠ 0 :=
      fun p ↦ nearby_segment_ne_zero (f p.2) (g p.2) (h p.2) p.1
    have hsum : ∀ p, v p + w p ≠ 0 := fun p ↦ nearby_sum_ne_zero (f p.2) (w p)
      (nearby_segment_dist_lt (f p.2) (g p.2) (h p.2) p.1)
    exact ((continuous_localRotationOperator v w hv hw hn hsum).subtype_mk _).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change localRotationOperator (f x : Vector n)
      ((f x : Vector n) + (0 : ℝ) • ((g x : Vector n) - (f x : Vector n))) = 1
    rw [zero_smul, add_zero, localRotationOperator_self]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change localRotationOperator (f x : Vector n)
      ((f x : Vector n) + (1 : ℝ) • ((g x : Vector n) - (f x : Vector n))) =
        localRotationOperator (f x : Vector n) (g x : Vector n)
    rw [one_smul, ← add_sub_assoc, add_sub_cancel_left]

/-- An orthogonal family can be homotoped so that one prescribed column becomes a nearby family. -/
theorem exists_nearbyColumnHomotopy (v : UnitSphere (Vector n))
    (a : C(X, OrthogonalOperators n)) (f g : C(X, UnitSphere (Vector n)))
    (ha : ∀ x, (a x).1.1 (v : Vector n) = (f x : Vector n))
    (h : ∀ x, dist (g x : Vector n) (f x : Vector n) < 1) :
    ∃ b : C(X, OrthogonalOperators n), a.Homotopic b ∧
      ∀ x, (b x).1.1 (v : Vector n) = (g x : Vector n) := by
  let b := mulMap (localRotations f g h) a
  have hi : mulMap (ContinuousMap.const X (identity n)) a = a := by
    apply ContinuousMap.ext
    intro x
    exact identity_mul (a x)
  refine ⟨b, ⟨((mulHomotopy (localRotationHomotopy f g h) a).cast hi rfl)⟩, ?_⟩
  intro x
  change (localRotations f g h x).1.1 ((a x).1.1 (v : Vector n)) = _
  rw [ha x]
  exact localRotations_apply f g h x

end NoExoticSixSphere.OrthogonalPaths
