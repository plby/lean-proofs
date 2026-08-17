import ErdosProblems.Erdos780.External.TargetOrbits
import ErdosProblems.Erdos780.External.LabelChainMap
import ErdosProblems.Erdos780.External.SignedMap

open scoped BigOperators

namespace TargetOrientation

open TargetChains TargetOrbits LabelChainMap

variable {p m : ℕ} [NeZero p]

/-- The one shared order used by the exterior target and the orbit signs. -/
@[instance_reducible] noncomputable def sharedTargetOrder : LinearOrder (Label p m) :=
  LabelChainMap.targetLinearOrder

noncomputable local instance : LinearOrder (Label p m) :=
  LabelChainMap.targetLinearOrder

theorem targetShift_injective (a : ZMod p) :
    Function.Injective (targetShift (m := m) a) := by
  intro x y h
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    dsimp [targetShift] at h1
    exact add_left_cancel h1
  · simpa [targetShift] using congrArg Prod.snd h

@[simp] theorem image_targetShift (a : ZMod p) (s : Finset (Label p m)) :
    s.image (targetShift a) = shiftFinset a s := by
  ext v
  simp only [Finset.mem_image, mem_shiftFinset]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [targetShift]
  · intro hv
    refine ⟨(-a + v.1, v.2), hv, ?_⟩
    ext <;> simp [targetShift]

noncomputable def targetOrientation (a : ZMod p) (s : Finset (Label p m)) : ℤˣ :=
  Finset.imageSign s (targetShift a) (targetShift_injective a).injOn

theorem targetAct_single_one (a : ZMod p) (s : Finset (Label p m)) :
    targetAct a (Finsupp.single s 1) =
      Finsupp.single (shiftFinset a s) (targetOrientation a s : ℤ) := by
  change TargetChains.map (targetShift a) (Finsupp.single s 1) = _
  have h := TargetChains.map_single_of_injOn (targetShift a) s
    (targetShift_injective a).injOn
  have himage :
      @Finset.image _ _ LabelChainMap.targetLinearOrder.toDecidableEq
        (targetShift a) s = shiftFinset a s := by
    ext v
    simp only [Finset.mem_image, mem_shiftFinset]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [targetShift]
    · intro hv
      refine ⟨(-a + v.1, v.2), hv, ?_⟩
      ext <;> simp [targetShift]
  rw [himage] at h
  exact h

theorem targetAct_add (a b : ZMod p) (c : TargetChain p m) :
    targetAct a (targetAct b c) = targetAct (a + b) c := by
  change TargetChains.map (targetShift a) (TargetChains.map (targetShift b) c) =
    TargetChains.map (targetShift (a + b)) c
  apply (TargetChains.toExterior ℤ (Label p m)).injective
  rw [TargetChains.toExterior_map, TargetChains.toExterior_map,
    TargetChains.toExterior_map]
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  congr 2
  apply LinearMap.ext
  intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      change TargetChains.vertexMap (targetShift a)
          (TargetChains.vertexMap (targetShift b) x) =
        TargetChains.vertexMap (targetShift (a + b)) x at hx
      change TargetChains.vertexMap (targetShift a)
          (TargetChains.vertexMap (targetShift b) y) =
        TargetChains.vertexMap (targetShift (a + b)) y at hy
      change TargetChains.vertexMap (targetShift a)
          (TargetChains.vertexMap (targetShift b) (x + y)) =
        TargetChains.vertexMap (targetShift (a + b)) (x + y)
      rw [map_add, map_add, map_add, hx, hy]
  | single v z =>
      change TargetChains.vertexMap (targetShift a)
          (TargetChains.vertexMap (targetShift b) (Finsupp.single v z)) =
        TargetChains.vertexMap (targetShift (a + b)) (Finsupp.single v z)
      rw [TargetChains.vertexMap_single, TargetChains.vertexMap_single,
        TargetChains.vertexMap_single]
      congr 1
      ext <;> simp [targetShift, add_assoc]

theorem targetOrientation_add (a b : ZMod p) (s : Finset (Label p m)) :
    targetOrientation (a + b) s =
      targetOrientation a (shiftFinset b s) * targetOrientation b s := by
  have h := targetAct_add a b (Finsupp.single s 1)
  rw [targetAct_single_one, targetAct_single_one] at h
  have hone :
      Finsupp.single (shiftFinset b s) (targetOrientation b s : ℤ) =
        (targetOrientation b s : ℤ) •
          Finsupp.single (shiftFinset b s) 1 := by
    ext t
    by_cases ht : t = shiftFinset b s <;> simp [ht]
  rw [hone, map_smul, targetAct_single_one, shiftFinset_add] at h
  have hc := congrArg (fun c : TargetChain p m ↦ c (shiftFinset (a + b) s)) h
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same] at hc
  apply Units.ext
  change (targetOrientation (a + b) s : ℤ) = _
  simpa [mul_comm] using hc.symm

@[simp] theorem targetOrientation_zero (s : Finset (Label p m)) :
    targetOrientation 0 s = 1 := by
  have h := targetOrientation_add 0 0 s
  simp only [zero_add, shiftFinset_zero] at h
  have h' := congrArg (fun z : ℤˣ ↦ (targetOrientation 0 s)⁻¹ * z) h
  simpa using h'.symm

section FixedDegree

variable {alpha q : ℕ}

/-- Orbit coordinates with the cyclic parameter reversed.  In this convention
actual target translation by `+1` becomes `x(a) ↦ x(a+1)`. -/
noncomputable def negFaceOrbitEquiv (hp : p.Prime) :
    FaceOrbit p m alpha q × ZMod p ≃ AllowedFace p m alpha q :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.neg (ZMod p))).trans (faceOrbitEquiv hp)

@[simp] theorem negFaceOrbitEquiv_apply (hp : p.Prime)
    (O : FaceOrbit p m alpha q) (a : ZMod p) :
    negFaceOrbitEquiv hp (O, a) = shiftFace (-a) (orbitRep O) := rfl

/-- The unit by which the transported exterior orientation differs from the
canonical increasing orientation of its underlying finset. -/
noncomputable def orbitWeight (hp : p.Prime)
    (z : FaceOrbit p m alpha q × ZMod p) : ℤˣ :=
  targetOrientation (-z.2) (orbitRep z.1).1

/-- Coefficients in the genuinely transported exterior basis
`targetAct (-a) [orbitRep O]`. -/
noncomputable def orientedChainCoords (hp : p.Prime) :
    FaceChain p m alpha q ≃ₗ[ℤ]
      CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) := by
  let e : FaceOrbit p m alpha q × ZMod p ≃ AllowedFace p m alpha q :=
    negFaceOrbitEquiv (m := m) (alpha := alpha) (q := q) hp
  let w : FaceOrbit p m alpha q × ZMod p → ℤˣ :=
    orbitWeight (m := m) (alpha := alpha) (q := q) hp
  exact
    { toFun := fun c O a ↦ (↑((w (O, a))⁻¹) : ℤ) * c (e (O, a))
      invFun := fun x ↦
        (Finsupp.linearEquivFunOnFinite ℤ ℤ (AllowedFace p m alpha q)).symm
          (fun s ↦ (w (e.symm s) : ℤ) * x (e.symm s).1 (e.symm s).2)
      map_add' := by intros; funext O a; simp [mul_add]
      map_smul' := by
        intro z c
        funext O a
        change (↑((w (O, a))⁻¹) : ℤ) *
            (z * c (e (O, a))) =
          z * ((↑((w (O, a))⁻¹) : ℤ) * c (e (O, a)))
        ring
      left_inv := by
        intro c
        apply Finsupp.ext
        intro s
        rw [Finsupp.linearEquivFunOnFinite_symm_apply]
        change (w (e.symm s) : ℤ) *
            ((↑((w (e.symm s))⁻¹) : ℤ) * c (e (e.symm s))) = c s
        rw [e.apply_symm_apply]
        rw [← mul_assoc, Units.mul_inv, one_mul]
      right_inv := by
        intro x
        funext O a
        change (↑((w (O, a))⁻¹) : ℤ) *
            ((w (e.symm (e (O, a))) : ℤ) *
              x (e.symm (e (O, a))).1 (e.symm (e (O, a))).2) = x O a
        rw [e.symm_apply_apply]
        rw [← mul_assoc, Units.inv_mul, one_mul] }

@[simp] theorem orientedChainCoords_apply (hp : p.Prime)
    (c : FaceChain p m alpha q) (O : FaceOrbit p m alpha q) (a : ZMod p) :
    orientedChainCoords hp c O a =
      (↑((targetOrientation (-a) (orbitRep O).1)⁻¹) : ℤ) *
        c (shiftFace (-a) (orbitRep O)) := rfl

/-- The restriction of the *actual exterior action* `targetAct 1` to a
homogeneous allowed-face module, written coefficientwise. -/
noncomputable def actualFaceAct :
    FaceChain p m alpha q →ₗ[ℤ] FaceChain p m alpha q where
  toFun c :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (AllowedFace p m alpha q)).symm
      (fun t ↦ (targetOrientation 1 (shiftFace (-1) t).1 : ℤ) *
        c (shiftFace (-1) t))
  map_add' c d := by
    apply (Finsupp.linearEquivFunOnFinite ℤ ℤ
      (AllowedFace p m alpha q)).injective
    rw [(Finsupp.linearEquivFunOnFinite ℤ ℤ
        (AllowedFace p m alpha q)).apply_symm_apply, map_add,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (AllowedFace p m alpha q)).apply_symm_apply,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (AllowedFace p m alpha q)).apply_symm_apply]
    funext t
    simp [mul_add]
  map_smul' z c := by
    apply (Finsupp.linearEquivFunOnFinite ℤ ℤ
      (AllowedFace p m alpha q)).injective
    rw [(Finsupp.linearEquivFunOnFinite ℤ ℤ
        (AllowedFace p m alpha q)).apply_symm_apply, map_smul,
      (Finsupp.linearEquivFunOnFinite ℤ ℤ
        (AllowedFace p m alpha q)).apply_symm_apply]
    funext t
    change _ * (z * _) = z * (_ * _)
    ring

@[simp] theorem actualFaceAct_apply (c : FaceChain p m alpha q)
    (t : AllowedFace p m alpha q) :
    actualFaceAct c t =
      (targetOrientation 1 (shiftFace (-1) t).1 : ℤ) *
        c (shiftFace (-1) t) := by
  let f : AllowedFace p m alpha q → ℤ := fun u ↦
    (targetOrientation 1 (shiftFace (-1) u).1 : ℤ) *
      c (shiftFace (-1) u)
  change ((Finsupp.linearEquivFunOnFinite ℤ ℤ
    (AllowedFace p m alpha q)).symm f) t = f t
  exact congrFun ((Finsupp.linearEquivFunOnFinite ℤ ℤ
    (AllowedFace p m alpha q)).apply_symm_apply f) t

theorem actualFaceAct_single_one (s : AllowedFace p m alpha q) :
    actualFaceAct (Finsupp.single s 1) =
      Finsupp.single (shiftFace 1 s) (targetOrientation 1 s.1 : ℤ) := by
  apply Finsupp.ext
  intro t
  rw [actualFaceAct_apply]
  by_cases h : t = shiftFace 1 s
  · subst t
    have hs : shiftFace (-1) (shiftFace 1 s) = s := by simp
    rw [hs]
    simp
  · have hne : shiftFace (-1) t ≠ s := by
      intro he
      apply h
      rw [← he]
      simp
    simp [h, hne]

/-- Forget the cardinality/allowedness witness and regard a fixed-degree
allowed-face chain as an ordinary exterior target chain. -/
noncomputable def faceInclusion :
    FaceChain p m alpha q →ₗ[ℤ] TargetChain p m :=
  Finsupp.lmapDomain ℤ ℤ (fun s : AllowedFace p m alpha q ↦ s.1)

@[simp] theorem faceInclusion_single (s : AllowedFace p m alpha q) (z : ℤ) :
    faceInclusion (p := p) (m := m) (alpha := alpha) (q := q)
        (Finsupp.single s z) = Finsupp.single s.1 z := by
  simp [faceInclusion]

/-- The coefficientwise action above really is the restriction of the
concrete exterior action used by `LabelChainMap`. -/
theorem faceInclusion_actualFaceAct (c : FaceChain p m alpha q) :
    faceInclusion (actualFaceAct c) =
      LabelChainMap.targetAct 1 (faceInclusion c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single s z =>
      rw [show Finsupp.single s z = z • Finsupp.single s 1 by simp]
      simp only [map_smul]
      rw [actualFaceAct_single_one, faceInclusion_single,
        faceInclusion_single, targetAct_single_one]
      rfl

/-- **Actual-action conjugacy.**  With orbit parameter reversed and each
canonical face reoriented by its exterior permutation sign, the concrete
`targetAct (+1)` restriction is exactly `CyclicAlgebra.g`. -/
theorem orientedChainCoords_actualFaceAct (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    orientedChainCoords hp (actualFaceAct c) =
      CyclicAlgebra.g (orientedChainCoords hp c) := by
  funext O a
  rw [orientedChainCoords_apply, actualFaceAct_apply,
    CyclicAlgebra.g_apply, orientedChainCoords_apply]
  have hshift :
      shiftFace (-1) (shiftFace (-a) (orbitRep O)) =
        shiftFace (-(a + 1)) (orbitRep O) := by
    rw [shiftFace_add]
    congr 1
    abel
  rw [hshift]
  have hw := targetOrientation_add (p := p) (m := m)
    1 (-(a + 1)) (orbitRep O).1
  have hadd : (1 : ZMod p) + -(a + 1) = -a := by abel
  rw [hadd] at hw
  rw [hw]
  let u := targetOrientation 1 (shiftFace (-(a + 1)) (orbitRep O)).1
  let v := targetOrientation (-(a + 1)) (orbitRep O).1
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

/-- The concrete exterior translation difference `targetAct (+1) - id`,
restricted to a fixed allowed degree. -/
noncomputable def actualTau :
    FaceChain p m alpha q →+ FaceChain p m alpha q :=
  actualFaceAct.toAddMonoidHom - AddMonoidHom.id _

/-- The orbit norm transported through the sign-corrected coordinates. -/
noncomputable def actualNorm (hp : p.Prime) :
    FaceChain p m alpha q →+ FaceChain p m alpha q :=
  (orientedChainCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.N.comp
      (orientedChainCoords hp).toAddEquiv.toAddMonoidHom)

@[simp] theorem orientedChainCoords_actualTau (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    orientedChainCoords hp (actualTau c) =
      CyclicAlgebra.D (orientedChainCoords hp c) := by
  rw [show actualTau c = actualFaceAct c - c by rfl, map_sub,
    orientedChainCoords_actualFaceAct]
  rfl

@[simp] theorem orientedChainCoords_actualNorm (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    orientedChainCoords hp (actualNorm hp c) =
      CyclicAlgebra.N (orientedChainCoords hp c) := by
  change orientedChainCoords hp ((orientedChainCoords hp).symm
      (CyclicAlgebra.N (orientedChainCoords hp c))) = _
  rw [(orientedChainCoords hp).apply_symm_apply]

theorem exists_actualNorm_of_actualTau_eq_zero (hp : p.Prime)
    {c : FaceChain p m alpha q} (hc : actualTau c = 0) :
    ∃ d, actualNorm hp d = c := by
  have hD : CyclicAlgebra.D (orientedChainCoords hp c) = 0 := by
    rw [← orientedChainCoords_actualTau]
    simp [hc]
  obtain ⟨y, hy⟩ := CyclicAlgebra.exists_N_of_D_eq_zero hD
  refine ⟨(orientedChainCoords hp).symm y, ?_⟩
  apply (orientedChainCoords hp).injective
  rw [orientedChainCoords_actualNorm,
    (orientedChainCoords hp).apply_symm_apply, hy]

theorem exists_actualTau_of_actualNorm_eq_zero (hp : p.Prime)
    {c : FaceChain p m alpha q} (hc : actualNorm hp c = 0) :
    ∃ d, actualTau d = c := by
  have hN : CyclicAlgebra.N (orientedChainCoords hp c) = 0 := by
    rw [← orientedChainCoords_actualNorm]
    simp [hc]
  obtain ⟨y, hy⟩ := CyclicAlgebra.exists_D_of_N_eq_zero hN
  refine ⟨(orientedChainCoords hp).symm y, ?_⟩
  apply (orientedChainCoords hp).injective
  rw [orientedChainCoords_actualTau,
    (orientedChainCoords hp).apply_symm_apply, hy]

theorem ker_actualTau_eq_range_actualNorm (hp : p.Prime) :
    AddMonoidHom.ker
        (actualTau (p := p) (m := m) (alpha := alpha) (q := q)) =
      AddMonoidHom.range
        (actualNorm (m := m) (alpha := alpha) (q := q) hp) := by
  ext c
  constructor
  · intro hc
    exact exists_actualNorm_of_actualTau_eq_zero hp hc
  · rintro ⟨d, rfl⟩
    change actualTau (actualNorm hp d) = 0
    apply (orientedChainCoords hp).injective
    rw [map_zero, orientedChainCoords_actualTau,
      orientedChainCoords_actualNorm]
    have h := congrArg
      (fun f : CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) →+
          CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) ↦
        f (orientedChainCoords hp d))
      (CyclicAlgebra.D_comp_N (p := p) (ι := FaceOrbit p m alpha q))
    simpa using h

theorem ker_actualNorm_eq_range_actualTau (hp : p.Prime) :
    AddMonoidHom.ker
        (actualNorm (m := m) (alpha := alpha) (q := q) hp) =
      AddMonoidHom.range
        (actualTau (p := p) (m := m) (alpha := alpha) (q := q)) := by
  ext c
  constructor
  · intro hc
    exact exists_actualTau_of_actualNorm_eq_zero hp hc
  · rintro ⟨d, rfl⟩
    change actualNorm hp (actualTau d) = 0
    apply (orientedChainCoords hp).injective
    rw [map_zero, orientedChainCoords_actualNorm,
      orientedChainCoords_actualTau]
    have h := congrArg
      (fun f : CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) →+
          CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) ↦
        f (orientedChainCoords hp d))
      (CyclicAlgebra.N_comp_D (p := p) (ι := FaceOrbit p m alpha q))
    simpa using h

end FixedDegree

end TargetOrientation
