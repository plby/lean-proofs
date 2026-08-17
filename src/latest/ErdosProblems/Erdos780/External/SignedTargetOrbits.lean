import ErdosProblems.Erdos780.External.TargetOrbits
import ErdosProblems.Erdos780.External.PositiveTarget
import ErdosProblems.Erdos780.External.LabelChainMap
import ErdosProblems.Erdos780.External.SignedMap
import ErdosProblems.Erdos780.External.TargetOrientation

open scoped BigOperators

namespace SignedTargetOrbits

open TargetChains TargetOrbits

variable {p m alpha : ℕ} [NeZero p]

noncomputable local instance : LinearOrder (Label p m) :=
  LabelChainMap.targetLinearOrder

noncomputable abbrev PChain (p m : ℕ) := PositiveTarget.Chain ℤ (Label p m)

/-- The actual exterior-algebra action induced by translation of target vertices. -/
noncomputable def targetAct (a : ZMod p) : PChain p m →ₗ[ℤ] PChain p m :=
  PositiveTarget.map (LabelChainMap.targetShift (m := m) a)

theorem targetShift_injective (a : ZMod p) :
    Function.Injective (LabelChainMap.targetShift (m := m) a) := by
  intro x y h
  apply Prod.ext
  · exact add_left_cancel (congrArg Prod.fst h)
  · simpa [LabelChainMap.targetShift] using congrArg Prod.snd h

@[simp] theorem image_targetShift (a : ZMod p) (s : Finset (Label p m)) :
    s.image (LabelChainMap.targetShift a) = shiftFinset a s := by
  ext v
  simp only [Finset.mem_image, mem_shiftFinset]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [LabelChainMap.targetShift]
  · intro hv
    refine ⟨(-a + v.1, v.2), hv, ?_⟩
    ext <;> simp [LabelChainMap.targetShift]

noncomputable def orientation (a : ZMod p) (s : Finset (Label p m)) : ℤˣ :=
  Finset.imageSign s (LabelChainMap.targetShift a)
    (targetShift_injective a).injOn

theorem shiftFinset_nonempty (a : ZMod p) {s : Finset (Label p m)}
    (hs : s.Nonempty) : (shiftFinset a s).Nonempty := by
  rcases hs with ⟨v, hv⟩
  exact ⟨labelShift a v, Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩

noncomputable def positiveSingle (s : Finset (Label p m))
    (hs : s.Nonempty) : PChain p m :=
  ⟨Finsupp.single s 1, by
    change (Finsupp.single s (1 : ℤ)) ∅ = 0
    simp [Finset.nonempty_iff_ne_empty.mp hs]⟩

@[simp] theorem positiveSingle_coe (s : Finset (Label p m)) (hs : s.Nonempty) :
    (positiveSingle s hs : TargetChains.FullChain ℤ (Label p m)) =
      Finsupp.single s 1 := rfl

@[simp] theorem targetAct_positiveSingle (a : ZMod p)
    (s : Finset (Label p m)) (hs : s.Nonempty) :
    targetAct a (positiveSingle s hs) =
      (orientation a s : ℤ) •
        positiveSingle (shiftFinset a s)
          (shiftFinset_nonempty a hs) := by
  apply Subtype.ext
  simp only [targetAct, PositiveTarget.map, TargetChains.reducedMap,
    LinearMap.comp_apply]
  rw [show TargetChains.positiveInclusion ℤ (Label p m)
      (positiveSingle s hs) = Finsupp.single s 1 by rfl]
  have hmap : TargetChains.map (LabelChainMap.targetShift a)
      (Finsupp.single s 1) =
      Finsupp.single (shiftFinset a s) (orientation a s : ℤ) := by
    have h := TargetChains.map_single_of_injOn
      (LabelChainMap.targetShift a) s (targetShift_injective a).injOn
    have himage :
        @Finset.image _ _ LabelChainMap.targetLinearOrder.toDecidableEq
          (LabelChainMap.targetShift a) s = shiftFinset a s := by
      ext v
      simp only [Finset.mem_image, mem_shiftFinset]
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa [LabelChainMap.targetShift]
      · intro hv
        refine ⟨(-a + v.1, v.2), hv, ?_⟩
        ext <;> simp [LabelChainMap.targetShift]
    rw [himage] at h
    exact h
  rw [hmap]
  have hne : shiftFinset a s ≠ ∅ := by
    exact Finset.nonempty_iff_ne_empty.mp (shiftFinset_nonempty a hs)
  change (Finsupp.single (shiftFinset a s) (orientation a s : ℤ) -
      Finsupp.single ∅
        ((Finsupp.single (shiftFinset a s) (orientation a s : ℤ)) ∅)) = _
  ext t
  by_cases ht : t = ∅ <;> simp [ht, hne, positiveSingle]

/-- Translation on the sigma-indexed positive allowed faces. -/
noncomputable def shiftTotalFace (a : ZMod p)
    (s : TotalFace p m alpha) : TotalFace p m alpha :=
  ⟨s.1, shiftFace a s.2⟩

@[simp] theorem shiftTotalFace_zero (s : TotalFace p m alpha) :
    shiftTotalFace 0 s = s := by
  rcases s with ⟨q, s⟩
  simp [shiftTotalFace]

@[simp] theorem shiftTotalFace_add (a b : ZMod p)
    (s : TotalFace p m alpha) :
    shiftTotalFace a (shiftTotalFace b s) = shiftTotalFace (a + b) s := by
  rcases s with ⟨q, s⟩
  simp [shiftTotalFace]

def totalFaceVal (s : TotalFace p m alpha) : Finset (Label p m) := s.2.1

theorem totalFaceVal_injective :
    Function.Injective (totalFaceVal (p := p) (m := m) (alpha := alpha)) := by
  rintro ⟨q, s⟩ ⟨r, t⟩ h
  have hq : q = r := by
    have hs := s.2.1
    have ht := t.2.1
    change s.1 = t.1 at h
    rw [h] at hs
    omega
  apply Sigma.ext hq
  cases hq
  exact heq_of_eq (Subtype.ext h)

theorem totalFaceVal_ne_empty (s : TotalFace p m alpha) :
    totalFaceVal s ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp (allowedFace_nonempty s.2)

/-- Include allowed total chains into the actual positive exterior target. -/
noncomputable def totalInclusion : TotalChain p m alpha →ₗ[ℤ] PChain p m where
  toFun c := ⟨Finsupp.mapDomain totalFaceVal c, by
    change Finsupp.mapDomain totalFaceVal c ∅ = 0
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨s, hs⟩
    exact totalFaceVal_ne_empty s hs⟩
  map_add' c d := by
    apply Subtype.ext
    exact Finsupp.mapDomain_add
  map_smul' r c := by
    apply Subtype.ext
    change Finsupp.mapDomain totalFaceVal (r • c) =
      r • Finsupp.mapDomain totalFaceVal c
    exact Finsupp.mapDomain_smul
      (f := totalFaceVal (p := p) (m := m) (alpha := alpha)) r c

theorem totalInclusion_injective :
    Function.Injective
      (totalInclusion (p := p) (m := m) (alpha := alpha)) := by
  intro c d h
  apply Finsupp.mapDomain_injective totalFaceVal_injective
  exact congrArg Subtype.val h

@[simp] theorem totalInclusion_single (s : TotalFace p m alpha) (r : ℤ) :
    totalInclusion (Finsupp.single s r) =
      r • positiveSingle s.2.1 (allowedFace_nonempty s.2) := by
  apply Subtype.ext
  simp [totalInclusion, positiveSingle, totalFaceVal]

/-- The restriction of the actual exterior action to allowed total chains,
written on the canonical Finset basis with its genuine permutation sign. -/
noncomputable def totalTargetAct (a : ZMod p) :
    TotalChain p m alpha →ₗ[ℤ] TotalChain p m alpha :=
  Finsupp.linearCombination ℤ fun s ↦
    (orientation a s.2.1 : ℤ) •
      Finsupp.single (shiftTotalFace a s) 1

@[simp] theorem totalTargetAct_single (a : ZMod p)
    (s : TotalFace p m alpha) (r : ℤ) :
    totalTargetAct a (Finsupp.single s r) =
      (r * (orientation a s.2.1 : ℤ)) •
        Finsupp.single (shiftTotalFace a s) 1 := by
  rw [totalTargetAct, Finsupp.linearCombination_single]
  simp [smul_smul, mul_comm]

@[simp] theorem totalTargetAct_apply (a : ZMod p)
    (c : TotalChain p m alpha) (t : TotalFace p m alpha) :
    totalTargetAct a c t =
      (orientation a (shiftTotalFace (-a) t |>.2.1) : ℤ) *
        c (shiftTotalFace (-a) t) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd, mul_add]
  | single s r =>
      rw [totalTargetAct_single]
      by_cases h : t = shiftTotalFace a s
      · subst t
        have hs : shiftTotalFace (-a) (shiftTotalFace a s) = s := by
          rw [shiftTotalFace_add]
          simp
        rw [hs]
        simp [mul_comm]
      · have hne : shiftTotalFace (-a) t ≠ s := by
          intro he
          apply h
          rw [← he, shiftTotalFace_add]
          simp
        simp [h, hne]

/-- This is the key geometric certification: the signed action above is not
defined by conjugation; its inclusion is literally `PositiveTarget.map`. -/
theorem totalInclusion_targetAct (a : ZMod p) (c : TotalChain p m alpha) :
    totalInclusion (totalTargetAct a c) = targetAct a (totalInclusion c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add, hc, hd]
  | single s r =>
      rw [totalTargetAct_single]
      calc
        totalInclusion
            ((r * (orientation a s.2.1 : ℤ)) •
              Finsupp.single (shiftTotalFace a s) 1) =
            (r * (orientation a s.2.1 : ℤ)) •
              positiveSingle (shiftFinset a s.2.1)
                (shiftFinset_nonempty a (allowedFace_nonempty s.2)) := by
              rw [map_smul, totalInclusion_single]
              simp [shiftTotalFace, shiftFace]
        _ = targetAct a
            (r • positiveSingle s.2.1 (allowedFace_nonempty s.2)) := by
              rw [map_smul, targetAct_positiveSingle]
              simp [smul_smul]
        _ = targetAct a (totalInclusion (Finsupp.single s r)) := by
              rw [totalInclusion_single]

/-! ## Orientation-correct coordinates on all positive degrees -/

/-- Reverse the orbit parameter so that actual translation by `+1` acts on
coordinates by reading at `a + 1`, exactly `CyclicAlgebra.g`. -/
noncomputable def negTotalOrbitEquiv (hp : p.Prime) :
    TotalOrbit p m alpha × ZMod p ≃ TotalFace p m alpha :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.neg (ZMod p))).trans
    (totalOrbitEquiv hp)

@[simp] theorem negTotalOrbitEquiv_apply (hp : p.Prime)
    (O : TotalOrbit p m alpha) (a : ZMod p) :
    negTotalOrbitEquiv hp (O, a) =
      ⟨O.1, shiftFace (-a) (orbitRep O.2)⟩ := rfl

noncomputable def totalOrbitWeight (hp : p.Prime)
    (z : TotalOrbit p m alpha × ZMod p) : ℤˣ :=
  orientation (-z.2) (orbitRep z.1.2).1

/-- The total positive allowed chain module in genuinely transported wedge
orientations `targetAct (-a) [orbitRep O]`. -/
noncomputable def orientedTotalCoords (hp : p.Prime) :
    TotalChain p m alpha ≃ₗ[ℤ]
      CyclicAlgebra.FreeCyclic p (TotalOrbit p m alpha) := by
  let e : TotalOrbit p m alpha × ZMod p ≃ TotalFace p m alpha :=
    negTotalOrbitEquiv hp
  let w : TotalOrbit p m alpha × ZMod p → ℤˣ := totalOrbitWeight hp
  exact
    { toFun := fun c O a ↦ (↑((w (O, a))⁻¹) : ℤ) * c (e (O, a))
      invFun := fun x ↦
        (Finsupp.linearEquivFunOnFinite ℤ ℤ (TotalFace p m alpha)).symm
          (fun s ↦ (w (e.symm s) : ℤ) * x (e.symm s).1 (e.symm s).2)
      map_add' := by intros; funext O a; simp [mul_add]
      map_smul' := by
        intro z c
        funext O a
        change (↑((w (O, a))⁻¹) : ℤ) * (z * c (e (O, a))) =
          z * ((↑((w (O, a))⁻¹) : ℤ) * c (e (O, a)))
        ring
      left_inv := by
        intro c
        apply Finsupp.ext
        intro s
        rw [Finsupp.linearEquivFunOnFinite_symm_apply]
        change (w (e.symm s) : ℤ) *
            ((↑((w (e.symm s))⁻¹) : ℤ) * c (e (e.symm s))) = c s
        rw [e.apply_symm_apply, ← mul_assoc, Units.mul_inv, one_mul]
      right_inv := by
        intro x
        funext O a
        change (↑((w (O, a))⁻¹) : ℤ) *
            ((w (e.symm (e (O, a))) : ℤ) *
              x (e.symm (e (O, a))).1 (e.symm (e (O, a))).2) = x O a
        rw [e.symm_apply_apply, ← mul_assoc, Units.inv_mul, one_mul] }

@[simp] theorem orientedTotalCoords_apply (hp : p.Prime)
    (c : TotalChain p m alpha) (O : TotalOrbit p m alpha) (a : ZMod p) :
    orientedTotalCoords hp c O a =
      (↑((orientation (-a) (orbitRep O.2).1)⁻¹) : ℤ) *
        c ⟨O.1, shiftFace (-a) (orbitRep O.2)⟩ := rfl

/-- Coefficient form of the actual restricted `targetAct 1`. -/
noncomputable def actualTotalAct :
    TotalChain p m alpha →ₗ[ℤ] TotalChain p m alpha where
  toFun c :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (TotalFace p m alpha)).symm
      (fun t ↦ (orientation 1 (shiftTotalFace (-1) t |>.2.1) : ℤ) *
        c (shiftTotalFace (-1) t))
  map_add' c d := by
    apply (Finsupp.linearEquivFunOnFinite ℤ ℤ
      (TotalFace p m alpha)).injective
    rw [(Finsupp.linearEquivFunOnFinite ℤ ℤ
        (TotalFace p m alpha)).apply_symm_apply, map_add,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (TotalFace p m alpha)).apply_symm_apply,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (TotalFace p m alpha)).apply_symm_apply]
    funext t
    simp [mul_add]
  map_smul' z c := by
    apply (Finsupp.linearEquivFunOnFinite ℤ ℤ
      (TotalFace p m alpha)).injective
    rw [(Finsupp.linearEquivFunOnFinite ℤ ℤ
        (TotalFace p m alpha)).apply_symm_apply, map_smul,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (TotalFace p m alpha)).apply_symm_apply]
    funext t
    change _ * (z * _) = z * (_ * _)
    ring

@[simp] theorem actualTotalAct_apply (c : TotalChain p m alpha)
    (t : TotalFace p m alpha) :
    actualTotalAct c t =
      (orientation 1 (shiftTotalFace (-1) t |>.2.1) : ℤ) *
        c (shiftTotalFace (-1) t) := by
  let f : TotalFace p m alpha → ℤ := fun u ↦
    (orientation 1 (shiftTotalFace (-1) u |>.2.1) : ℤ) *
      c (shiftTotalFace (-1) u)
  change ((Finsupp.linearEquivFunOnFinite ℤ ℤ
    (TotalFace p m alpha)).symm f) t = f t
  exact congrFun ((Finsupp.linearEquivFunOnFinite ℤ ℤ
    (TotalFace p m alpha)).apply_symm_apply f) t

/-- The coordinate action is the same signed restriction whose positive
inclusion is literally `PositiveTarget.map`. -/
theorem actualTotalAct_eq_totalTargetAct :
    actualTotalAct (p := p) (m := m) (alpha := alpha) = totalTargetAct 1 := by
  apply LinearMap.ext
  intro c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add, hc, hd]
  | single s r =>
      apply Finsupp.ext
      intro t
      rw [actualTotalAct_apply, totalTargetAct_single]
      by_cases h : t = shiftTotalFace 1 s
      · subst t
        have hs : shiftTotalFace (-1) (shiftTotalFace 1 s) = s := by simp
        rw [hs]
        simp [mul_comm]
      · have hne : shiftTotalFace (-1) t ≠ s := by
          intro he
          apply h
          rw [← he]
          simp
        simp [h, hne]

theorem totalInclusion_actualTotalAct (c : TotalChain p m alpha) :
    totalInclusion (actualTotalAct c) = targetAct 1 (totalInclusion c) := by
  rw [actualTotalAct_eq_totalTargetAct, totalInclusion_targetAct]

/-- **Total actual-action conjugacy.**  This is the positive-degree ambient
statement used by periodic descent; no empty face occurs in either index. -/
theorem orientedTotalCoords_actualTotalAct (hp : p.Prime)
    (c : TotalChain p m alpha) :
    orientedTotalCoords hp (actualTotalAct c) =
      CyclicAlgebra.g (orientedTotalCoords hp c) := by
  funext O a
  rw [orientedTotalCoords_apply, actualTotalAct_apply,
    CyclicAlgebra.g_apply, orientedTotalCoords_apply]
  have hshift :
      shiftTotalFace (-1)
          ⟨O.1, shiftFace (-a) (orbitRep O.2)⟩ =
        ⟨O.1, shiftFace (-(a + 1)) (orbitRep O.2)⟩ := by
    rcases O with ⟨q, O⟩
    change (⟨q, shiftFace (-1) (shiftFace (-a) (orbitRep O))⟩ :
      TotalFace p m alpha) = ⟨q, shiftFace (-(a + 1)) (orbitRep O)⟩
    apply congrArg (fun s : AllowedFace p m alpha q ↦
      (⟨q, s⟩ : TotalFace p m alpha))
    rw [shiftFace_add]
    congr 1
    abel
  rw [hshift]
  have hw := TargetOrientation.targetOrientation_add (p := p) (m := m)
    1 (-(a + 1)) (orbitRep O.2).1
  have hadd : (1 : ZMod p) + -(a + 1) = -a := by abel
  rw [hadd] at hw
  change orientation (-a) (orbitRep O.2).1 =
    orientation 1 (shiftFinset (-(a + 1)) (orbitRep O.2).1) *
      orientation (-(a + 1)) (orbitRep O.2).1 at hw
  rw [hw]
  let u := orientation 1 (shiftFace (-(a + 1)) (orbitRep O.2)).1
  let v := orientation (-(a + 1)) (orbitRep O.2).1
  have huv : (u * v)⁻¹ * u = v⁻¹ := by
    calc
      (u * v)⁻¹ * u = (v⁻¹ * u⁻¹) * u := by rw [mul_inv_rev]
      _ = v⁻¹ * (u⁻¹ * u) := by rw [mul_assoc]
      _ = v⁻¹ := by simp
  have huvZ := congrArg (fun z : ℤˣ ↦ (z : ℤ)) huv
  simp only [Units.val_mul] at huvZ
  change (↑((u * v)⁻¹) : ℤ) * ((u : ℤ) * _) =
    (↑(v⁻¹) : ℤ) * _
  rw [← mul_assoc, huvZ]

/-- General geometric translation formula.  In transported coordinates,
translation by `a` reads the old coordinate at `b + a`. -/
theorem orientedTotalCoords_totalTargetAct (hp : p.Prime)
    (a : ZMod p) (c : TotalChain p m alpha)
    (O : TotalOrbit p m alpha) (b : ZMod p) :
    orientedTotalCoords hp (totalTargetAct a c) O b =
      orientedTotalCoords hp c O (b + a) := by
  rw [orientedTotalCoords_apply, totalTargetAct_apply,
    orientedTotalCoords_apply]
  have hshift :
      shiftTotalFace (-a)
          ⟨O.1, shiftFace (-b) (orbitRep O.2)⟩ =
        ⟨O.1, shiftFace (-(b + a)) (orbitRep O.2)⟩ := by
    rcases O with ⟨q, O⟩
    change (⟨q, shiftFace (-a) (shiftFace (-b) (orbitRep O))⟩ :
      TotalFace p m alpha) = ⟨q, shiftFace (-(b + a)) (orbitRep O)⟩
    apply congrArg (fun s : AllowedFace p m alpha q ↦
      (⟨q, s⟩ : TotalFace p m alpha))
    rw [shiftFace_add]
    congr 1
    abel
  rw [hshift]
  have hw := TargetOrientation.targetOrientation_add (p := p) (m := m)
    a (-(b + a)) (orbitRep O.2).1
  have hadd : a + -(b + a) = -b := by abel
  rw [hadd] at hw
  change orientation (-b) (orbitRep O.2).1 =
    orientation a (shiftFinset (-(b + a)) (orbitRep O.2).1) *
      orientation (-(b + a)) (orbitRep O.2).1 at hw
  rw [hw]
  let u := orientation a (shiftFace (-(b + a)) (orbitRep O.2)).1
  let v := orientation (-(b + a)) (orbitRep O.2).1
  have huv : (u * v)⁻¹ * u = v⁻¹ := by
    calc
      (u * v)⁻¹ * u = (v⁻¹ * u⁻¹) * u := by rw [mul_inv_rev]
      _ = v⁻¹ * (u⁻¹ * u) := by rw [mul_assoc]
      _ = v⁻¹ := by simp
  have huvZ := congrArg (fun z : ℤˣ ↦ (z : ℤ)) huv
  simp only [Units.val_mul] at huvZ
  change (↑((u * v)⁻¹) : ℤ) * ((u : ℤ) * _) =
    (↑(v⁻¹) : ℤ) * _
  rw [← mul_assoc, huvZ]

/-- The literal geometric orbit sum of all target translations. -/
noncomputable def geometricTotalNorm :
    TotalChain p m alpha →ₗ[ℤ] TotalChain p m alpha :=
  ∑ a : ZMod p, totalTargetAct a

@[simp] theorem orientedTotalCoords_geometricTotalNorm (hp : p.Prime)
    (c : TotalChain p m alpha) :
    orientedTotalCoords hp (geometricTotalNorm c) =
      CyclicAlgebra.N (orientedTotalCoords hp c) := by
  funext O b
  change orientedTotalCoords hp
      ((∑ a : ZMod p, totalTargetAct a) c) O b = _
  rw [LinearMap.sum_apply, map_sum]
  simp only [Finset.sum_apply, orientedTotalCoords_totalTargetAct,
    CyclicAlgebra.N_apply]
  exact Fintype.sum_equiv (Equiv.addLeft b) _ _ (fun _ ↦ rfl)

/-! ## The actual two-periodic operators on the total positive module -/

/-- The actual geometric translation difference on all positive allowed
degrees at once. -/
noncomputable def actualTotalTau :
    TotalChain p m alpha →+ TotalChain p m alpha :=
  actualTotalAct.toAddMonoidHom - AddMonoidHom.id _

/-- The cyclic norm transported through the sign-corrected total
coordinates. -/
noncomputable def actualTotalNorm (hp : p.Prime) :
    TotalChain p m alpha →+ TotalChain p m alpha :=
  (orientedTotalCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.N.comp
      (orientedTotalCoords hp).toAddEquiv.toAddMonoidHom)

@[simp] theorem orientedTotalCoords_actualTotalTau (hp : p.Prime)
    (c : TotalChain p m alpha) :
    orientedTotalCoords hp (actualTotalTau c) =
      CyclicAlgebra.D (orientedTotalCoords hp c) := by
  rw [show actualTotalTau c = actualTotalAct c - c by rfl, map_sub,
    orientedTotalCoords_actualTotalAct]
  rfl

@[simp] theorem orientedTotalCoords_actualTotalNorm (hp : p.Prime)
    (c : TotalChain p m alpha) :
    orientedTotalCoords hp (actualTotalNorm hp c) =
      CyclicAlgebra.N (orientedTotalCoords hp c) := by
  change orientedTotalCoords hp ((orientedTotalCoords hp).symm
      (CyclicAlgebra.N (orientedTotalCoords hp c))) = _
  rw [(orientedTotalCoords hp).apply_symm_apply]

/-- The transported norm is the literal sum of all geometric target
translations. -/
theorem actualTotalNorm_eq_geometricTotalNorm (hp : p.Prime) :
    actualTotalNorm (m := m) (alpha := alpha) hp =
      (geometricTotalNorm (p := p) (m := m) (alpha := alpha)).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro c
  apply (orientedTotalCoords hp).injective
  change orientedTotalCoords hp (actualTotalNorm hp c) =
    orientedTotalCoords hp (geometricTotalNorm c)
  rw [orientedTotalCoords_actualTotalNorm,
    orientedTotalCoords_geometricTotalNorm]

theorem exists_actualTotalNorm_of_actualTotalTau_eq_zero (hp : p.Prime)
    {c : TotalChain p m alpha} (hc : actualTotalTau c = 0) :
    ∃ d, actualTotalNorm hp d = c := by
  have hD : CyclicAlgebra.D (orientedTotalCoords hp c) = 0 := by
    rw [← orientedTotalCoords_actualTotalTau]
    simp [hc]
  obtain ⟨y, hy⟩ := CyclicAlgebra.exists_N_of_D_eq_zero hD
  refine ⟨(orientedTotalCoords hp).symm y, ?_⟩
  apply (orientedTotalCoords hp).injective
  rw [orientedTotalCoords_actualTotalNorm,
    (orientedTotalCoords hp).apply_symm_apply, hy]

theorem exists_actualTotalTau_of_actualTotalNorm_eq_zero (hp : p.Prime)
    {c : TotalChain p m alpha} (hc : actualTotalNorm hp c = 0) :
    ∃ d, actualTotalTau d = c := by
  have hN : CyclicAlgebra.N (orientedTotalCoords hp c) = 0 := by
    rw [← orientedTotalCoords_actualTotalNorm]
    simp [hc]
  obtain ⟨y, hy⟩ := CyclicAlgebra.exists_D_of_N_eq_zero hN
  refine ⟨(orientedTotalCoords hp).symm y, ?_⟩
  apply (orientedTotalCoords hp).injective
  rw [orientedTotalCoords_actualTotalTau,
    (orientedTotalCoords hp).apply_symm_apply, hy]

theorem ker_actualTotalTau_eq_range_actualTotalNorm (hp : p.Prime) :
    AddMonoidHom.ker
        (actualTotalTau (p := p) (m := m) (alpha := alpha)) =
      AddMonoidHom.range
        (actualTotalNorm (m := m) (alpha := alpha) hp) := by
  ext c
  constructor
  · intro hc
    exact exists_actualTotalNorm_of_actualTotalTau_eq_zero hp hc
  · rintro ⟨d, rfl⟩
    change actualTotalTau (actualTotalNorm hp d) = 0
    apply (orientedTotalCoords hp).injective
    rw [map_zero, orientedTotalCoords_actualTotalTau,
      orientedTotalCoords_actualTotalNorm]
    have h := congrArg
      (fun f : CyclicAlgebra.FreeCyclic p (TotalOrbit p m alpha) →+
          CyclicAlgebra.FreeCyclic p (TotalOrbit p m alpha) ↦
        f (orientedTotalCoords hp d))
      (CyclicAlgebra.D_comp_N (p := p) (ι := TotalOrbit p m alpha))
    simpa using h

theorem ker_actualTotalNorm_eq_range_actualTotalTau (hp : p.Prime) :
    AddMonoidHom.ker
        (actualTotalNorm (m := m) (alpha := alpha) hp) =
      AddMonoidHom.range
        (actualTotalTau (p := p) (m := m) (alpha := alpha)) := by
  ext c
  constructor
  · intro hc
    exact exists_actualTotalTau_of_actualTotalNorm_eq_zero hp hc
  · rintro ⟨d, rfl⟩
    change actualTotalNorm hp (actualTotalTau d) = 0
    apply (orientedTotalCoords hp).injective
    rw [map_zero, orientedTotalCoords_actualTotalNorm,
      orientedTotalCoords_actualTotalTau]
    have h := congrArg
      (fun f : CyclicAlgebra.FreeCyclic p (TotalOrbit p m alpha) →+
          CyclicAlgebra.FreeCyclic p (TotalOrbit p m alpha) ↦
        f (orientedTotalCoords hp d))
      (CyclicAlgebra.N_comp_D (p := p) (ι := TotalOrbit p m alpha))
    simpa using h

end SignedTargetOrbits
