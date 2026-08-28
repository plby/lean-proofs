import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusQuotientAction
import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusQuotientCircle
import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusQuotientConjugacy
import Wikipedia.HopfProblem.EllipticFiniteQuotient

/-!
# The finite twist quotient is an actual mapping torus

The cyclic action on `AddCircle 1 × X` translates the first factor by
`1 / m` and applies the finite-order homeomorphism `B` to the second.
The representative formula `[t,x] ↦ [(t/m,x)]` induces a continuous
bijection from the literal mapping torus of `B.symm`.  For compact Hausdorff
fibre it is a homeomorphism of the actual quotient topologies.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.MappingTorusQuotient

open MappingTorus

variable {X : Type*} [TopologicalSpace X]

/-- The actual orbit quotient for the selected finite twist action. -/
abbrev ProductQuotient (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :=
  letI := productAction m B hB
  FiniteQuotient.Space (Multiplicative (ZMod m)) (Circle × X)

/-- The literal finite-orbit projection. -/
def project (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    (p : Circle × X) : ProductQuotient m B hB := by
  letI := productAction m B hB
  exact FiniteQuotient.project (Multiplicative (ZMod m)) (Circle × X) p

theorem project_surjective (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Function.Surjective (project m B hB) := by
  let := productAction m B hB
  exact FiniteQuotient.project_surjective (Multiplicative (ZMod m)) (Circle × X)

theorem project_continuous (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Continuous (project m B hB) := by
  let := productAction m B hB
  exact FiniteQuotient.project_continuous (Multiplicative (ZMod m)) (Circle × X)

/-- Finite orbit equality has the exact integer-power representative
formula, with no equivalence of quotients assumed. -/
theorem project_eq_iff (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    (p q : Circle × X) :
    project m B hB p = project m B hB q ↔
      ∃ n : ℤ, p = (q.1 + (((n : ℝ) / m : ℝ) : Circle), (B ^ n) q.2) := by
  let := productAction m B hB
  change FiniteQuotient.project (Multiplicative (ZMod m)) (Circle × X) p =
    FiniteQuotient.project (Multiplicative (ZMod m)) (Circle × X) q ↔ _
  rw [FiniteQuotient.project_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    have he : Multiplicative.ofAdd ((g.toAdd.val : ℤ) : ZMod m) = g := by
      apply Multiplicative.ext
      simp
    have hs := ofAdd_intCast_smul m B hB (g.toAdd.val : ℤ) q.1 q.2
    rw [he] at hs
    exact ⟨g.toAdd.val, hg.symm.trans hs⟩
  · rintro ⟨n, hp⟩
    refine ⟨Multiplicative.ofAdd (n : ZMod m), ?_⟩
    change Multiplicative.ofAdd (n : ZMod m) • (q.1, q.2) = p
    rw [ofAdd_intCast_smul]
    exact hp.symm

/-- The concrete map on real-cylinder representatives. -/
def cylinderMap (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    (p : ℝ × X) : ProductQuotient m B hB :=
  project m B hB (((p.1 / m : ℝ) : Circle), p.2)

theorem cylinderMap_continuous (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Continuous (cylinderMap m B hB) :=
  (project_continuous m B hB).comp
    (((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_fst.div_const (m : ℝ))).prodMk
      continuous_snd)

/-- The representative map respects every actual integer deck
transformation of the inverse-monodromy mapping torus. -/
theorem cylinderMap_deck (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    (n : ℤ) (p : ℝ × X) :
    cylinderMap m B hB (deck B.symm n p) = cylinderMap m B hB p := by
  apply (project_eq_iff m B hB _ _).mpr
  refine ⟨n, ?_⟩
  apply Prod.ext
  · change (((p.1 + (n : ℝ)) / m : ℝ) : Circle) =
      ((p.1 / m : ℝ) : Circle) + (((n : ℝ) / m : ℝ) : Circle)
    rw [add_div, AddCircle.coe_add]
  · change (B.symm ^ (-n)) p.2 = (B ^ n) p.2
    rw [symm_zpow_neg]

/-- The induced map from the actual mapping-torus quotient. -/
def mappingTorusMap (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Torus B.symm → ProductQuotient m B hB :=
  Quotient.lift (cylinderMap m B hB) (by
    rintro p q ⟨n, rfl⟩
    exact (cylinderMap_deck m B hB n p).symm)

@[simp] theorem mappingTorusMap_mk (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) (t : ℝ) (x : X) :
    mappingTorusMap m B hB (mk B.symm (t, x)) =
      project m B hB (((t / m : ℝ) : Circle), x) := rfl

theorem mappingTorusMap_continuous (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) : Continuous (mappingTorusMap m B hB) :=
  (cylinderMap_continuous m B hB).quotient_lift _

/-- Equal finite-orbit images give a literal integer mapping-torus deck
shift.  The missing multiples of `m` act trivially on the fibre. -/
theorem mappingTorusMap_injective (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) : Function.Injective (mappingTorusMap m B hB) := by
  intro p q h
  obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective B.symm p
  obtain ⟨⟨s, y⟩, rfl⟩ := mk_surjective B.symm q
  change project m B hB (((t / m : ℝ) : Circle), x) =
    project m B hB (((s / m : ℝ) : Circle), y) at h
  obtain ⟨n, hn⟩ := (project_eq_iff m B hB _ _).mp h
  have hf := congrArg Prod.fst hn
  change ((t / m : ℝ) : Circle) =
    ((s / m : ℝ) : Circle) + (((n : ℝ) / m : ℝ) : Circle) at hf
  rw [← AddCircle.coe_add] at hf
  obtain ⟨k, hk⟩ := (circle_scaled_eq_iff m t s n).mp hf
  have hx : x = (B ^ n) y := congrArg Prod.snd hn
  apply Eq.symm
  apply (mk_eq_mk_iff B.symm (s, y) (t, x)).mpr
  refine ⟨n + (m : ℤ) * k, hk, ?_⟩
  rw [symm_zpow_neg, fibre_zpow_add_mul_period m B hB]
  exact hx

theorem mappingTorusMap_surjective (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) : Function.Surjective (mappingTorusMap m B hB) := by
  intro q
  obtain ⟨⟨a, x⟩, rfl⟩ := project_surjective m B hB q
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective a
  refine ⟨mk B.symm (t * m, x), ?_⟩
  rw [mappingTorusMap_mk]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hm, mul_one]

instance productQuotient_t2 (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    [CompactSpace X] [T2Space X] : T2Space (ProductQuotient m B hB) := by
  let := productAction m B hB
  let := productAction_continuousConstSMul m B hB
  exact FiniteQuotient.spaceT2Space (Multiplicative (ZMod m)) (Circle × X)

/-- Compactness and the Hausdorff finite quotient upgrade the explicit
continuous bijection to a genuine homeomorphism. -/
def toProductHomeomorph (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    [CompactSpace X] [T2Space X] : Torus B.symm ≃ₜ ProductQuotient m B hB :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (mappingTorusMap m B hB)
      ⟨mappingTorusMap_injective m B hB, mappingTorusMap_surjective m B hB⟩)
    (mappingTorusMap_continuous m B hB)

/-- The actual finite twist quotient is the mapping torus of `B.symm`. -/
def mappingTorusHomeomorph (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    [CompactSpace X] [T2Space X] : ProductQuotient m B hB ≃ₜ Torus B.symm :=
  (toProductHomeomorph m B hB).symm

@[simp] theorem mappingTorusHomeomorph_symm_mk (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) [CompactSpace X] [T2Space X] (t : ℝ) (x : X) :
    (mappingTorusHomeomorph m B hB).symm (mk B.symm (t, x)) =
      project m B hB (((t / m : ℝ) : Circle), x) := rfl

/-- On every real representative of the circle factor the forward
homeomorphism multiplies the time by the finite order. -/
theorem mappingTorusHomeomorph_project (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) [CompactSpace X] [T2Space X] (t : ℝ) (x : X) :
    mappingTorusHomeomorph m B hB (project m B hB ((t : Circle), x)) =
      mk B.symm (t * m, x) := by
  apply (mappingTorusHomeomorph m B hB).symm.injective
  rw [Homeomorph.symm_apply_apply, mappingTorusHomeomorph_symm_mk]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hm, mul_one]

end Wikipedia.HopfProblem.Elliptic.HigherHomology.MappingTorusQuotient
