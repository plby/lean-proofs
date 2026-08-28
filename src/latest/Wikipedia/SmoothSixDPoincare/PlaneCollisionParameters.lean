import Wikipedia.SmoothSixDPoincare.PlaneAffinePerturbation

/-!
# Parameters producing self-intersections of an affine plane perturbation

For two different source points, one coordinate difference is nonzero.
The equality of their images then determines one of the two parameter columns.
These two explicit parametrizations are smooth on their open domains.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.PlaneImmersion

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def firstCollisionDomain : Set (Plane × (Plane × F)) :=
  {q | q.1.1 - q.2.1.1 ≠ 0}

def secondCollisionDomain : Set (Plane × (Plane × F)) :=
  {q | q.1.2 - q.2.1.2 ≠ 0}

def firstCollision (f : Plane → F) (q : Plane × (Plane × F)) : F × F :=
  ((q.1.1 - q.2.1.1)⁻¹ • (f q.2.1 - f q.1 - (q.1.2 - q.2.1.2) • q.2.2), q.2.2)

def secondCollision (f : Plane → F) (q : Plane × (Plane × F)) : F × F :=
  (q.2.2, (q.1.2 - q.2.1.2)⁻¹ • (f q.2.1 - f q.1 - (q.1.1 - q.2.1.1) • q.2.2))

omit [NormedSpace ℝ F] in
theorem isOpen_firstCollisionDomain : IsOpen (firstCollisionDomain (F := F)) :=
  isOpen_ne.preimage (continuous_fst.fst.sub continuous_snd.fst.fst)

omit [NormedSpace ℝ F] in
theorem isOpen_secondCollisionDomain : IsOpen (secondCollisionDomain (F := F)) :=
  isOpen_ne.preimage (continuous_fst.snd.sub continuous_snd.fst.snd)

theorem contDiffOn_firstCollision {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (firstCollision f) firstCollisionDomain := by
  have h₁ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.1 - q.2.1.1) :=
    contDiff_fst.fst.sub contDiff_snd.fst.fst
  have h₂ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.2 - q.2.1.2) :=
    contDiff_fst.snd.sub contDiff_snd.fst.snd
  exact ((h₁.contDiffOn.inv (fun _ h => h)).smul
    (((hf.comp contDiff_snd.fst).sub (hf.comp contDiff_fst)).sub
      (h₂.smul contDiff_snd.snd)).contDiffOn).prodMk contDiff_snd.snd.contDiffOn

theorem contDiffOn_secondCollision {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (secondCollision f) secondCollisionDomain := by
  have h₁ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.1 - q.2.1.1) :=
    contDiff_fst.fst.sub contDiff_snd.fst.fst
  have h₂ : ContDiff ℝ ∞ (fun q : Plane × (Plane × F) => q.1.2 - q.2.1.2) :=
    contDiff_fst.snd.sub contDiff_snd.fst.snd
  exact contDiff_snd.snd.contDiffOn.prodMk ((h₂.contDiffOn.inv (fun _ h => h)).smul
    (((hf.comp contDiff_snd.fst).sub (hf.comp contDiff_fst)).sub
      (h₁.smul contDiff_snd.snd)).contDiffOn)

theorem mem_collision_of_eq (f : Plane → F) (A : F × F) {x y : Plane}
    (hxy : x ≠ y) (heq : perturb f A x = perturb f A y) :
    A ∈ firstCollision f '' firstCollisionDomain ∪
      secondCollision f '' secondCollisionDomain := by
  have hlinear : linearMap A (x - y) = f y - f x := by
    rw [map_sub]
    change f x + linearMap A x = f y + linearMap A y at heq
    exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa only [add_comm] using heq)
  change (x.1 - y.1) • A.1 + (x.2 - y.2) • A.2 = f y - f x at hlinear
  by_cases hfirst : x.1 - y.1 = 0
  · have hsecond : x.2 - y.2 ≠ 0 := by
      intro h
      exact hxy (Prod.ext (sub_eq_zero.mp hfirst) (sub_eq_zero.mp h))
    apply Or.inr
    refine ⟨(x, (y, A.1)), hsecond, Prod.ext rfl ?_⟩
    change (x.2 - y.2)⁻¹ • (f y - f x - (x.1 - y.1) • A.1) = A.2
    rw [← eq_sub_of_add_eq' hlinear, inv_smul_smul₀ hsecond]
  · apply Or.inl
    refine ⟨(x, (y, A.2)), hfirst, Prod.ext ?_ rfl⟩
    change (x.1 - y.1)⁻¹ • (f y - f x - (x.2 - y.2) • A.2) = A.1
    rw [← eq_sub_of_add_eq hlinear, inv_smul_smul₀ hfirst]

theorem injective_perturb_of_not_collision (f : Plane → F) {A : F × F}
    (hA : A ∉ firstCollision f '' firstCollisionDomain ∪
      secondCollision f '' secondCollisionDomain) : Function.Injective (perturb f A) := by
  intro x y heq
  by_contra hxy
  exact hA (mem_collision_of_eq f A hxy heq)

end Wikipedia.SmoothSixDPoincare.PlaneImmersion
