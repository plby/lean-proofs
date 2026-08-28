import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusQuotient

/-!
# A product model for the mapping torus of a finite circle twist

The map on actual cylinder representatives is
`(t,(a,x)) ↦ ([a,x], a + t/m)`.  Its first coordinate is the literal finite
orbit projection.  The second coordinate cancels the circle displacement of
each integer mapping-torus deck transformation.  Equality of the two images
gives a concrete integer deck witness, so this is a homeomorphism of the
original quotient spaces, not an assumed trivialization of a circle bundle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open MappingTorus (Torus mk deck mk_surjective mk_eq_mk_iff)
open Elliptic.HigherHomology.MappingTorusQuotient

variable {X : Type*} [TopologicalSpace X]

/-- The actual finite quotient together with the invariant circle coordinate. -/
def twistCylinderMap (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    (p : ℝ × (Circle × X)) : ProductQuotient m B hB × Circle :=
  (project m B hB p.2, p.2.1 + (((p.1 / m : ℝ) : Circle)))

theorem twistCylinderMap_continuous (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) : Continuous (twistCylinderMap m B hB) :=
  ((project_continuous m B hB).comp continuous_snd).prodMk
    ((continuous_fst.comp continuous_snd).add
      ((AddCircle.continuous_mk' (1 : ℝ)).comp
        (continuous_fst.div_const (m : ℝ))))

/-- Both coordinates are invariant under every literal integer deck shift. -/
theorem twistCylinderMap_deck (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (n : ℤ) (p : ℝ × (Circle × X)) :
    twistCylinderMap m B hB (deck (twist m B) n p) =
      twistCylinderMap m B hB p := by
  rcases p with ⟨t, a, x⟩
  simp only [twistCylinderMap, deck, twist_zpow_apply]
  apply Prod.ext
  · exact (project_eq_iff m B hB _ _).mpr ⟨-n, rfl⟩
  · change (a + ((((-n : ℤ) : ℝ) / m : ℝ) : Circle)) +
        (((t + (n : ℝ)) / m : ℝ) : Circle) = a + ((t / m : ℝ) : Circle)
    rw [add_assoc, ← AddCircle.coe_add]
    congr 2
    push_cast
    ring

/-- The map induced on the actual mapping-torus quotient. -/
def twistProductMap (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Torus (twist m B) → ProductQuotient m B hB × Circle :=
  Quotient.lift (twistCylinderMap m B hB) (by
    rintro p q ⟨n, rfl⟩
    exact (twistCylinderMap_deck m B hB n p).symm)

@[simp] theorem twistProductMap_mk (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (t : ℝ) (a : Circle) (x : X) :
    twistProductMap m B hB (mk (twist m B) (t, (a, x))) =
      (project m B hB (a, x), a + ((t / m : ℝ) : Circle)) := rfl

theorem twistProductMap_continuous (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) : Continuous (twistProductMap m B hB) :=
  (twistCylinderMap_continuous m B hB).quotient_lift _

/-- Equal product coordinates determine an actual integer deck transformation. -/
theorem twistProductMap_injective (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) : Function.Injective (twistProductMap m B hB) := by
  intro p q hpq
  obtain ⟨⟨t, a, x⟩, rfl⟩ := mk_surjective (twist m B) p
  obtain ⟨⟨s, b, y⟩, rfl⟩ := mk_surjective (twist m B) q
  have hq : project m B hB (a, x) = project m B hB (b, y) :=
    congrArg Prod.fst hpq
  have hc : a + ((t / m : ℝ) : Circle) = b + ((s / m : ℝ) : Circle) :=
    congrArg Prod.snd hpq
  obtain ⟨n, hn⟩ := (project_eq_iff m B hB _ _).mp hq
  have ha : a = b + (((n : ℝ) / m : ℝ) : Circle) := congrArg Prod.fst hn
  have ht : ((s / m : ℝ) : Circle) =
      ((t / m + (n : ℝ) / m : ℝ) : Circle) := by
    apply add_left_cancel (a := b)
    rw [AddCircle.coe_add]
    rw [ha, add_assoc] at hc
    exact hc.symm.trans (by abel)
  obtain ⟨k, hk⟩ := (circle_scaled_eq_iff m s t n).mp ht
  apply Eq.symm
  apply (mk_eq_mk_iff (twist m B) (s, (b, y)) (t, (a, x))).mpr
  refine ⟨-(n + (m : ℤ) * k), ?_, ?_⟩
  · push_cast at hk ⊢
    linarith
  · rw [neg_neg, fibre_zpow_add_mul_period m (twist m B)
      (twist_pow_order m B hB), twist_zpow_apply]
    exact hn

/-- A real lift of the difference of the two circle coordinates gives a preimage. -/
theorem twistProductMap_surjective (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) : Function.Surjective (twistProductMap m B hB) := by
  rintro ⟨q, c⟩
  obtain ⟨⟨a, x⟩, rfl⟩ := project_surjective m B hB q
  obtain ⟨u, hu⟩ := QuotientAddGroup.mk_surjective (c - a)
  change (u : Circle) = c - a at hu
  refine ⟨mk (twist m B) (u * m, (a, x)), ?_⟩
  rw [twistProductMap_mk]
  apply Prod.ext
  · rfl
  · have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
    change a + (((u * m) / m : ℝ) : Circle) = c
    rw [mul_div_cancel_right₀ u hm, hu]
    abel

/-- The explicit continuous bijection is a homeomorphism of the genuine compact
mapping torus and the genuine Hausdorff finite quotient times a circle. -/
def twistProductHomeomorph (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    [CompactSpace X] [T2Space X] :
    Torus (twist m B) ≃ₜ ProductQuotient m B hB × Circle :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (twistProductMap m B hB)
      ⟨twistProductMap_injective m B hB, twistProductMap_surjective m B hB⟩)
    (twistProductMap_continuous m B hB)

@[simp] theorem twistProductHomeomorph_mk (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) [CompactSpace X] [T2Space X]
    (t : ℝ) (a : Circle) (x : X) :
    twistProductHomeomorph m B hB (mk (twist m B) (t, (a, x))) =
      (project m B hB (a, x), a + ((t / m : ℝ) : Circle)) := rfl

/-- The inverse has the literal cylinder formula whenever its circle coordinate
is written using a real lift; different lifts give the same quotient point. -/
theorem twistProductHomeomorph_symm_pair (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) [CompactSpace X] [T2Space X]
    (t : ℝ) (a : Circle) (x : X) :
    (twistProductHomeomorph m B hB).symm
      (project m B hB (a, x), a + ((t / m : ℝ) : Circle)) =
        mk (twist m B) (t, (a, x)) := by
  apply (twistProductHomeomorph m B hB).injective
  rw [Homeomorph.apply_symm_apply, twistProductHomeomorph_mk]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct
