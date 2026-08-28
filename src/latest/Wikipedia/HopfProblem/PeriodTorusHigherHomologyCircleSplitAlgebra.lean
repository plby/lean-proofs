import Mathlib.LinearAlgebra.Prod

/-!
# The splitting determined by an exact sequence and a retraction

If `i : A → B` has retraction `p : B → A`, and `d : B → C` is surjective
with kernel the image of `i`, then `(p, d)` identifies `B` with `A × C`.
The forward map is prescribed, so the resulting splitting is determined
by the retraction, rather than by a choice of lifts under `d`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {A B C : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℤ A] [Module ℤ B] [Module ℤ C]

private theorem splitExactPair_injective
    (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C)
    (hpi : p.comp i = LinearMap.id) (hex : LinearMap.range i = LinearMap.ker d) :
    Function.Injective (p.prod d) := by
  intro b b' h
  have hp : p b = p b' := congrArg Prod.fst h
  have hd : d b = d b' := congrArg Prod.snd h
  have hb : b - b' ∈ LinearMap.ker d := by
    change d (b - b') = 0
    rw [map_sub, hd, sub_self]
  rw [← hex] at hb
  obtain ⟨a, ha⟩ := hb
  have hpa : p (i a) = a := LinearMap.congr_fun hpi a
  have ha0 : a = 0 := by
    calc
      a = p (i a) := hpa.symm
      _ = p (b - b') := congrArg p ha
      _ = 0 := by rw [map_sub, hp, sub_self]
  have hdiff : b - b' = 0 := by rw [← ha, ha0, map_zero]
  exact sub_eq_zero.mp hdiff

private theorem splitExactPair_surjective
    (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C)
    (hpi : p.comp i = LinearMap.id) (hex : LinearMap.range i = LinearMap.ker d)
    (hsurj : Function.Surjective d) : Function.Surjective (p.prod d) := by
  rintro ⟨a, c⟩
  obtain ⟨b, hb⟩ := hsurj c
  refine ⟨b + i (a - p b), ?_⟩
  apply Prod.ext
  · change p (b + i (a - p b)) = a
    have hpa : p (i (a - p b)) = a - p b :=
      LinearMap.congr_fun hpi (a - p b)
    rw [map_add, hpa, ← add_sub_assoc, add_comm (p b) a, add_sub_cancel_right]
  · change d (b + i (a - p b)) = c
    have hi : i (a - p b) ∈ LinearMap.range i := ⟨a - p b, rfl⟩
    rw [hex] at hi
    have hdi : d (i (a - p b)) = 0 := hi
    rw [map_add, hdi, add_zero, hb]

/-- The canonical splitting whose coordinates are the retraction and the quotient map. -/
def splitExactEquiv
    (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C)
    (hpi : p.comp i = LinearMap.id) (hex : LinearMap.range i = LinearMap.ker d)
    (hsurj : Function.Surjective d) : B ≃ₗ[ℤ] (A × C) :=
  ({ Equiv.ofBijective (fun b : B => (p b, d b))
       ⟨splitExactPair_injective i p d hpi hex,
         splitExactPair_surjective i p d hpi hex hsurj⟩ with
     map_add' b b' := Prod.ext (map_add p b b') (map_add d b b')
    } : B ≃+ (A × C)).toIntLinearEquiv

variable (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C)
  (hpi : p.comp i = LinearMap.id) (hex : LinearMap.range i = LinearMap.ker d)
  (hsurj : Function.Surjective d)

@[simp] theorem splitExactEquiv_apply (b : B) :
    splitExactEquiv i p d hpi hex hsurj b = (p b, d b) := rfl

@[simp] theorem splitExactEquiv_fst (b : B) :
    (splitExactEquiv i p d hpi hex hsurj b).1 = p b := rfl

@[simp] theorem splitExactEquiv_snd (b : B) :
    (splitExactEquiv i p d hpi hex hsurj b).2 = d b := rfl

@[simp] theorem splitExactEquiv_symm_fst (ac : A × C) :
    p ((splitExactEquiv i p d hpi hex hsurj).symm ac) = ac.1 :=
  congrArg Prod.fst ((splitExactEquiv i p d hpi hex hsurj).apply_symm_apply ac)

@[simp] theorem splitExactEquiv_symm_snd (ac : A × C) :
    d ((splitExactEquiv i p d hpi hex hsurj).symm ac) = ac.2 :=
  congrArg Prod.snd ((splitExactEquiv i p d hpi hex hsurj).apply_symm_apply ac)

/-- The section becomes the inclusion of the first factor. -/
@[simp] theorem splitExactEquiv_apply_inclusion (a : A) :
    splitExactEquiv i p d hpi hex hsurj (i a) = (a, 0) := by
  have hpa : p (i a) = a := LinearMap.congr_fun hpi a
  have hi : i a ∈ LinearMap.range i := ⟨a, rfl⟩
  rw [hex] at hi
  have hdi : d (i a) = 0 := hi
  rw [splitExactEquiv_apply, hpa, hdi]

@[simp] theorem splitExactEquiv_symm_apply_inl (a : A) :
    (splitExactEquiv i p d hpi hex hsurj).symm (a, 0) = i a := by
  apply (splitExactEquiv i p d hpi hex hsurj).injective
  rw [LinearEquiv.apply_symm_apply, splitExactEquiv_apply_inclusion]

/-- The image of the section is identified with the first product factor. -/
theorem splitExactEquiv_image_range_inclusion :
    splitExactEquiv i p d hpi hex hsurj '' Set.range i = {ac : A × C | ac.2 = 0} := by
  ext ac
  constructor
  · rintro ⟨b, ⟨a, rfl⟩, rfl⟩
    exact congrArg Prod.snd (splitExactEquiv_apply_inclusion i p d hpi hex hsurj a)
  · intro hac
    refine ⟨i ac.1, ⟨ac.1, rfl⟩, ?_⟩
    rw [splitExactEquiv_apply_inclusion]
    exact Prod.ext rfl hac.symm

/-- The quotient coordinate vanishes precisely on the image of the section. -/
theorem splitExactEquiv_mem_range_inclusion_iff (b : B) :
    b ∈ LinearMap.range i ↔ (splitExactEquiv i p d hpi hex hsurj b).2 = 0 := by
  rw [hex]
  rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
