import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearizationNative

/-!
# Literal translations of the original affine mapping torus

The difference between the native logarithmic gauge and the linear gauge
has a homogeneous real recurrence.  Translation by any real multiple of
that difference commutes with the original integer deck transformations.
Its inverse is the negative translation on the same quotient space.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap Matrix

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic MappingTorus
open TrianglePeriodFamily.Boundary
open TrianglePeriodFamily.Boundary.EllipticGaugeLinearization

/-- The original affine map acts linearly on an added real-period vector. -/
theorem flatTorusAffine_add_mkQ (j : Kind) (v : Lattice) (x : RealTorus₄)
    (u : RealCoordinates) :
    flatTorusAffine j v (x + standardLattice.mkQ u) =
      flatTorusAffine j v x + standardLattice.mkQ (flatLinear j u) := by
  obtain ⟨a, rfl⟩ := standardLattice.mkQ_surjective x
  rw [← map_add, flatTorusAffine_mkQ, flatTorusAffine_mkQ, ← map_add]
  apply congrArg standardLattice.mkQ
  simp only [flatAffine, map_add]
  abel

/-- Unit-deck commutation implies commutation with every integer deck map. -/
theorem commute_deck_of_one {X : Type*} [TopologicalSpace X] (B : X ≃ₜ X)
    (F : ℝ × X → ℝ × X)
    (hF : ∀ p, F (deck B 1 p) = deck B 1 (F p)) (k : ℤ) (p : ℝ × X) :
    F (deck B k p) = deck B k (F p) := by
  have hneg (q : ℝ × X) : F (deck B (-1) q) = deck B (-1) (F q) := by
    have h := congrArg (deck B (-1)) (hF (deck B (-1) q))
    simpa only [← deck_add, add_neg_cancel, neg_add_cancel, deck_zero] using h.symm
  have hall : ∀ k : ℤ, ∀ p : ℝ × X, F (deck B k p) = deck B k (F p) := by
    intro k
    induction k using Int.induction_on with
    | zero => intro p; simp only [deck_zero]
    | succ k ih => intro p; rw [deck_add, ih, hF, deck_add]
    | pred k ih => intro p; rw [sub_eq_add_neg, deck_add, ih, hneg, deck_add]
  exact hall k p

/-- Translation of the real cylinder, retaining its exact real time. -/
def cylinderTranslation (h : C(ℝ, RealCoordinates)) (s : ℝ) :
    C(ℝ × RealTorus₄, ℝ × RealTorus₄) where
  toFun p := (p.1, p.2 + standardLattice.mkQ (s • h p.1))
  continuous_toFun := by
    have hs : Continuous (fun _ : ℝ × RealTorus₄ => s) := continuous_const
    exact continuous_fst.prodMk (continuous_snd.add
      (standardLattice.continuous_mkQ.comp
        (hs.smul (h.continuous.comp continuous_fst))))

@[simp] theorem cylinderTranslation_apply (h : C(ℝ, RealCoordinates)) (s t : ℝ)
    (x : RealTorus₄) :
    cylinderTranslation h s (t, x) = (t, x + standardLattice.mkQ (s • h t)) := rfl

theorem cylinderTranslation_add (h : C(ℝ, RealCoordinates)) (s r : ℝ)
    (p : ℝ × RealTorus₄) :
    cylinderTranslation h (s + r) p = cylinderTranslation h s (cylinderTranslation h r p) := by
  rcases p with ⟨t, x⟩
  simp only [cylinderTranslation_apply, add_smul, map_add]
  congr 1
  abel

@[simp] theorem cylinderTranslation_zero (h : C(ℝ, RealCoordinates))
    (p : ℝ × RealTorus₄) : cylinderTranslation h 0 p = p := by
  rcases p with ⟨t, x⟩
  simp only [cylinderTranslation_apply, zero_smul, map_zero, add_zero]

variable (j : Kind) (v : Lattice) (h : C(ℝ, RealCoordinates))
  (hh : ∀ t, flatLinear j (h (t + 1)) = h t)

include hh

/-- The homogeneous real recurrence is exactly commutation with the actual affine deck map. -/
theorem cylinderTranslation_deck_one (s : ℝ) (p : ℝ × RealTorus₄) :
    cylinderTranslation h s (deck (flatTorusAffine j v) 1 p) =
      deck (flatTorusAffine j v) 1 (cylinderTranslation h s p) := by
  rcases p with ⟨t, x⟩
  simp only [deck, Int.cast_one, zpow_neg_one, cylinderTranslation_apply]
  apply Prod.ext
  · rfl
  change (flatTorusAffine j v).symm x + standardLattice.mkQ (s • h (t + 1)) =
    (flatTorusAffine j v).symm (x + standardLattice.mkQ (s • h t))
  apply (flatTorusAffine j v).injective
  rw [flatTorusAffine_add_mkQ, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply, map_smul, hh]

/-- All integer deck relations are respected before taking the quotient. -/
theorem cylinderTranslation_deck (s : ℝ) (k : ℤ) (p : ℝ × RealTorus₄) :
    cylinderTranslation h s (deck (flatTorusAffine j v) k p) =
      deck (flatTorusAffine j v) k (cylinderTranslation h s p) :=
  commute_deck_of_one (flatTorusAffine j v) (cylinderTranslation h s)
    (cylinderTranslation_deck_one j v h hh s) k p

/-- The literal translation descended to the original affine mapping torus. -/
def boundaryTranslation (s : ℝ) :
    C(Torus (flatTorusAffine j v), Torus (flatTorusAffine j v)) :=
  Cylinder.descend (flatTorusAffine j v)
    ⟨fun p => mk (flatTorusAffine j v) (cylinderTranslation h s p),
      (mk_continuous _).comp (cylinderTranslation h s).continuous⟩
    (fun k p => by
      change mk (flatTorusAffine j v) (cylinderTranslation h s
        (deck (flatTorusAffine j v) k p)) =
        mk (flatTorusAffine j v) (cylinderTranslation h s p)
      rw [cylinderTranslation_deck j v h hh, mk_deck])

@[simp] theorem boundaryTranslation_mk (s t : ℝ) (x : RealTorus₄) :
    boundaryTranslation j v h hh s (mk (flatTorusAffine j v) (t, x)) =
      mk (flatTorusAffine j v) (t, x + standardLattice.mkQ (s • h t)) := rfl

/-- The base circle is fixed pointwise. -/
theorem boundaryTranslation_base (s : ℝ) (x : Torus (flatTorusAffine j v)) :
    base (flatTorusAffine j v) (boundaryTranslation j v h hh s x) =
      base (flatTorusAffine j v) x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := mk_surjective (flatTorusAffine j v) x
  rfl

@[simp] theorem boundaryTranslation_zero (x : Torus (flatTorusAffine j v)) :
    boundaryTranslation j v h hh 0 x = x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := mk_surjective (flatTorusAffine j v) x
  simp only [boundaryTranslation_mk, zero_smul, map_zero, add_zero]

/-- The parameter is an actual additive action, not only a path of maps. -/
theorem boundaryTranslation_add (s r : ℝ) (x : Torus (flatTorusAffine j v)) :
    boundaryTranslation j v h hh (s + r) x =
      boundaryTranslation j v h hh s (boundaryTranslation j v h hh r x) := by
  obtain ⟨p, rfl⟩ := mk_surjective (flatTorusAffine j v) x
  exact congrArg (mk (flatTorusAffine j v)) (cylinderTranslation_add h s r p)

/-- Joint continuity follows from the original open quotient, with the full real vector retained. -/
theorem boundaryTranslation_joint_continuous :
    Continuous (fun p : ℝ × Torus (flatTorusAffine j v) =>
      boundaryTranslation j v h hh p.1 p.2) := by
  apply (IsOpenQuotientMap.id.prodMap
    (Cylinder.projection_isOpenQuotientMap (flatTorusAffine j v))).continuous_comp_iff.mp
  change Continuous (fun p : ℝ × (ℝ × RealTorus₄) =>
    mk (flatTorusAffine j v)
      (p.2.1, p.2.2 + standardLattice.mkQ (p.1 • h p.2.1)))
  exact (mk_continuous _).comp ((continuous_fst.comp continuous_snd).prodMk
    ((continuous_snd.comp continuous_snd).add (standardLattice.continuous_mkQ.comp
      (continuous_fst.smul (h.continuous.comp (continuous_fst.comp continuous_snd))))))

/-- Each time is a homeomorphism, with its explicit inverse at the negative time. -/
def boundaryHomeomorph (s : ℝ) :
    Torus (flatTorusAffine j v) ≃ₜ Torus (flatTorusAffine j v) where
  toFun := boundaryTranslation j v h hh s
  invFun := boundaryTranslation j v h hh (-s)
  left_inv x := by rw [← boundaryTranslation_add, neg_add_cancel, boundaryTranslation_zero]
  right_inv x := by rw [← boundaryTranslation_add, add_neg_cancel, boundaryTranslation_zero]
  continuous_toFun := (boundaryTranslation j v h hh s).continuous
  continuous_invFun := (boundaryTranslation j v h hh (-s)).continuous

@[simp] theorem boundaryHomeomorph_apply (s : ℝ) (x : Torus (flatTorusAffine j v)) :
    boundaryHomeomorph j v h hh s x = boundaryTranslation j v h hh s x := rfl

@[simp] theorem boundaryHomeomorph_symm_apply (s : ℝ) (x : Torus (flatTorusAffine j v)) :
    (boundaryHomeomorph j v h hh s).symm x = boundaryTranslation j v h hh (-s) x := rfl

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
