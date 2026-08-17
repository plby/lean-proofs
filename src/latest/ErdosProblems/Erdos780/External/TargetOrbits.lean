import ErdosProblems.Erdos780.External.TargetChains
import ErdosProblems.Erdos780.External.CyclicAlgebra

open scoped BigOperators

namespace TargetOrbits

abbrev Label (p m : ℕ) := ZMod p × Fin m

def labelShift {p m : ℕ} (a : ZMod p) : Label p m ≃ Label p m :=
  Equiv.prodCongr (Equiv.addLeft a) (Equiv.refl (Fin m))

@[simp] theorem labelShift_apply {p m : ℕ} (a : ZMod p) (v : Label p m) :
    labelShift a v = (a + v.1, v.2) := rfl

def shiftFinset {p m : ℕ} (a : ZMod p) (s : Finset (Label p m)) :
    Finset (Label p m) := s.map (labelShift a).toEmbedding

@[simp] theorem mem_shiftFinset {p m : ℕ} {a : ZMod p}
    {s : Finset (Label p m)} {v : Label p m} :
    v ∈ shiftFinset a s ↔ (-a + v.1, v.2) ∈ s := by
  constructor
  · intro hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hv
    change (a + w.1, w.2) = v at heq
    have h1 : v.1 = a + w.1 := congrArg Prod.fst heq.symm
    have h2 : v.2 = w.2 :=
      (congrArg (fun z : Label p m ↦ z.2) heq).symm
    simpa [h1, h2] using hw
  · intro hv
    refine Finset.mem_map.mpr ⟨(-a + v.1, v.2), hv, ?_⟩
    ext <;> simp <;> abel

@[simp] theorem shiftFinset_zero {p m : ℕ} (s : Finset (Label p m)) :
    shiftFinset 0 s = s := by ext v; simp

@[simp] theorem shiftFinset_add {p m : ℕ} (a b : ZMod p)
    (s : Finset (Label p m)) :
    shiftFinset a (shiftFinset b s) = shiftFinset (a + b) s := by
  ext v
  simp [neg_add_rev, add_assoc]

def fiber {p m : ℕ} (s : Finset (Label p m)) (j : Fin m) :
    Finset (Label p m) := s.filter fun v ↦ v.2 = j

def Allowed {p m : ℕ} (alpha : ℕ) (s : Finset (Label p m)) : Prop :=
  ∀ j : Fin m, (fiber s j).card ≤ if j.val < alpha then 1 else p - 1

@[simp] theorem fiber_shiftFinset {p m : ℕ} (a : ZMod p)
    (s : Finset (Label p m)) (j : Fin m) :
    fiber (shiftFinset a s) j = shiftFinset a (fiber s j) := by
  ext v
  simp [fiber]

theorem card_shiftFinset {p m : ℕ} (a : ZMod p) (s : Finset (Label p m)) :
    (shiftFinset a s).card = s.card := by simp [shiftFinset]

@[simp] theorem allowed_shiftFinset_iff {p m alpha : ℕ} (a : ZMod p)
    (s : Finset (Label p m)) :
    Allowed alpha (shiftFinset a s) ↔ Allowed alpha s := by
  constructor <;> intro h j
  · have hj := h j
    rw [fiber_shiftFinset, card_shiftFinset] at hj
    exact hj
  · simpa only [fiber_shiftFinset, card_shiftFinset] using h j

theorem mem_shiftFinset_of_mem {p m : ℕ} {a : ZMod p}
    {s : Finset (Label p m)} (hfix : shiftFinset a s = s)
    {v : Label p m} (hv : v ∈ s) : (a + v.1, v.2) ∈ s := by
  rw [← hfix]
  exact Finset.mem_map.mpr ⟨v, hv, rfl⟩

theorem orbit_mem_of_fixed {p m : ℕ} {a : ZMod p}
    {s : Finset (Label p m)} (hfix : shiftFinset a s = s)
    {v : Label p m} (hv : v ∈ s) :
    ∀ n : ℕ, ((n : ZMod p) * a + v.1, v.2) ∈ s := by
  intro n
  induction n with
  | zero => simpa using hv
  | succ n ih =>
      have hs := mem_shiftFinset_of_mem hfix ih
      convert hs using 1 <;> simp [Nat.cast_succ] <;> ring

def signFiberEmbedding {p m : ℕ} (j : Fin m) : ZMod p ↪ Label p m where
  toFun b := (b, j)
  inj' := fun _ _ h ↦ congrArg Prod.fst h

theorem full_fiber_of_fixed {p m : ℕ} [NeZero p] (hp : p.Prime) {a : ZMod p}
    (ha : a ≠ 0) {s : Finset (Label p m)} (hfix : shiftFinset a s = s)
    {v : Label p m} (hv : v ∈ s) :
    Finset.univ.map (signFiberEmbedding v.2) ⊆ fiber s v.2 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro w hw
  simp only [Finset.mem_map, Finset.mem_univ, true_and] at hw
  obtain ⟨b, rfl⟩ := hw
  simp only [fiber, Finset.mem_filter, and_true]
  let z : ZMod p := (b - v.1) * a⁻¹
  have hz := orbit_mem_of_fixed hfix hv z.val
  have hza : (z.val : ZMod p) * a + v.1 = b := by
    rw [ZMod.natCast_zmod_val]
    dsimp [z]
    rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
    abel
  change (b, v.2) ∈ s ∧ v.2 = v.2
  exact ⟨by simpa only [hza] using hz, rfl⟩

theorem shiftFinset_ne_of_nonzero {p m alpha : ℕ} (hp : p.Prime)
    {a : ZMod p} (ha : a ≠ 0) {s : Finset (Label p m)}
    (hsne : s.Nonempty) (hallowed : Allowed alpha s) :
    shiftFinset a s ≠ s := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro hfix
  obtain ⟨v, hv⟩ := hsne
  have hsub := full_fiber_of_fixed hp ha hfix hv
  have hlower := Finset.card_le_card hsub
  have hcardMap :
      (Finset.univ.map (signFiberEmbedding (p := p) (m := m) v.2)).card = p := by
    simp [ZMod.card]
  rw [hcardMap] at hlower
  have hupper := hallowed v.2
  have hp2 := hp.two_le
  split at hupper
  · omega
  · omega

def AllowedFace (p m alpha q : ℕ) :=
  {s : Finset (Label p m) // s.card = q + 1 ∧ Allowed alpha s}

noncomputable instance (p m alpha q : ℕ) [NeZero p] : Fintype (AllowedFace p m alpha q) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable def shiftFace {p m alpha q : ℕ} (a : ZMod p)
    (s : AllowedFace p m alpha q) : AllowedFace p m alpha q :=
  ⟨shiftFinset a s.1,
    by rw [card_shiftFinset, s.2.1]; exact ⟨rfl, (allowed_shiftFinset_iff a s.1).2 s.2.2⟩⟩

@[simp] theorem shiftFace_zero {p m alpha q : ℕ} (s : AllowedFace p m alpha q) :
    shiftFace 0 s = s := by apply Subtype.ext; simp [shiftFace]

@[simp] theorem shiftFace_add {p m alpha q : ℕ} (a b : ZMod p)
    (s : AllowedFace p m alpha q) :
    shiftFace a (shiftFace b s) = shiftFace (a + b) s := by
  apply Subtype.ext
  simp [shiftFace]

theorem allowedFace_nonempty {p m alpha q : ℕ} (s : AllowedFace p m alpha q) :
    s.1.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hc := s.2.1
  rw [h] at hc
  simp at hc

theorem shiftFace_eq_self_iff {p m alpha q : ℕ} (hp : p.Prime)
    (a : ZMod p) (s : AllowedFace p m alpha q) :
    shiftFace a s = s ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    apply shiftFinset_ne_of_nonzero hp ha (allowedFace_nonempty s) s.2.2
    exact congrArg Subtype.val h
  · rintro rfl
    simp

def OrbitRel {p m alpha q : ℕ}
    (x y : AllowedFace p m alpha q) : Prop :=
  ∃ a : ZMod p, shiftFace a x = y

theorem orbitRel_refl {p m alpha q : ℕ} (x : AllowedFace p m alpha q) :
    OrbitRel x x := ⟨0, by simp⟩

theorem orbitRel_symm {p m alpha q : ℕ} {x y : AllowedFace p m alpha q} :
    OrbitRel x y → OrbitRel y x := by
  rintro ⟨a, rfl⟩
  refine ⟨-a, ?_⟩
  simpa only [shiftFace_add, neg_add_cancel, shiftFace_zero]

theorem orbitRel_trans {p m alpha q : ℕ} {x y z : AllowedFace p m alpha q} :
    OrbitRel x y → OrbitRel y z → OrbitRel x z := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  exact ⟨b + a, by simp [add_comm]⟩

def orbitSetoid (p m alpha q : ℕ) : Setoid (AllowedFace p m alpha q) where
  r := OrbitRel
  iseqv := ⟨orbitRel_refl, orbitRel_symm, orbitRel_trans⟩

abbrev FaceOrbit (p m alpha q : ℕ) := Quotient (orbitSetoid p m alpha q)

noncomputable instance (p m alpha q : ℕ) [NeZero p] :
    Fintype (FaceOrbit p m alpha q) := Fintype.ofFinite _

def orbitMk {p m alpha q : ℕ} (x : AllowedFace p m alpha q) :
    FaceOrbit p m alpha q := Quotient.mk (orbitSetoid p m alpha q) x

noncomputable def orbitRep {p m alpha q : ℕ} (O : FaceOrbit p m alpha q) :
    AllowedFace p m alpha q := Quotient.out O

@[simp] theorem orbitMk_rep {p m alpha q : ℕ} (O : FaceOrbit p m alpha q) :
    orbitMk (orbitRep O) = O := by
  change Quotient.mk (orbitSetoid p m alpha q) (Quotient.out O) = O
  exact Quotient.out_eq O

theorem orbitMk_shiftFace {p m alpha q : ℕ} (a : ZMod p)
    (x : AllowedFace p m alpha q) : orbitMk (shiftFace a x) = orbitMk x := by
  change Quotient.mk (orbitSetoid p m alpha q) (shiftFace a x) =
    Quotient.mk (orbitSetoid p m alpha q) x
  exact Quotient.sound ⟨-a, by simp⟩

theorem exists_orbitCoord {p m alpha q : ℕ} (x : AllowedFace p m alpha q) :
    ∃ a : ZMod p, shiftFace a (orbitRep (orbitMk x)) = x := by
  have hq : orbitMk (orbitRep (orbitMk x)) = orbitMk x := orbitMk_rep _
  change Quotient.mk (orbitSetoid p m alpha q) (orbitRep (orbitMk x)) =
    Quotient.mk (orbitSetoid p m alpha q) x at hq
  exact Quotient.exact hq

noncomputable def orbitCoord {p m alpha q : ℕ} (x : AllowedFace p m alpha q) :
    ZMod p := Classical.choose (exists_orbitCoord x)

theorem orbitCoord_spec {p m alpha q : ℕ} (x : AllowedFace p m alpha q) :
    shiftFace (orbitCoord x) (orbitRep (orbitMk x)) = x :=
  Classical.choose_spec (exists_orbitCoord x)

theorem shiftFace_left_cancel {p m alpha q : ℕ} (hp : p.Prime)
    {a b : ZMod p} {x : AllowedFace p m alpha q}
    (h : shiftFace a x = shiftFace b x) : a = b := by
  have h' := congrArg (shiftFace (-b)) h
  simp only [shiftFace_add] at h'
  have hz : shiftFace (a - b) x = x := by
    simpa only [add_comm (-b) a, sub_eq_add_neg, neg_add_cancel, shiftFace_zero] using h'
  have hz0 := (shiftFace_eq_self_iff hp (a - b) x).1 hz
  exact sub_eq_zero.mp hz0

@[simp] theorem orbitCoord_shiftFace {p m alpha q : ℕ} (hp : p.Prime)
    (b : ZMod p) (x : AllowedFace p m alpha q) :
    orbitCoord (shiftFace b x) = b + orbitCoord x := by
  apply shiftFace_left_cancel hp (x := orbitRep (orbitMk x))
  have hs := orbitCoord_spec (shiftFace b x)
  rw [orbitMk_shiftFace] at hs
  rw [hs]
  calc
    shiftFace b x = shiftFace b
        (shiftFace (orbitCoord x) (orbitRep (orbitMk x))) := by
          rw [orbitCoord_spec]
    _ = shiftFace (b + orbitCoord x) (orbitRep (orbitMk x)) :=
      shiftFace_add _ _ _

theorem orbitCoord_rep {p m alpha q : ℕ} (hp : p.Prime)
    (O : FaceOrbit p m alpha q) : orbitCoord (orbitRep O) = 0 := by
  apply shiftFace_left_cancel hp (x := orbitRep O)
  have hs := orbitCoord_spec (orbitRep O)
  rw [orbitMk_rep] at hs
  simpa using hs

noncomputable def faceOrbitEquiv {p m alpha q : ℕ} (hp : p.Prime) :
    FaceOrbit p m alpha q × ZMod p ≃ AllowedFace p m alpha q where
  toFun z := shiftFace z.2 (orbitRep z.1)
  invFun x := (orbitMk x, orbitCoord x)
  left_inv z := by
    change (orbitMk (shiftFace z.2 (orbitRep z.1)),
      orbitCoord (shiftFace z.2 (orbitRep z.1))) = z
    apply Prod.ext
    · rw [orbitMk_shiftFace, orbitMk_rep]
    · rw [orbitCoord_shiftFace hp, orbitCoord_rep hp, add_zero]
  right_inv x := orbitCoord_spec x

abbrev FaceChain (p m alpha q : ℕ) := AllowedFace p m alpha q →₀ ℤ

noncomputable def chainCoords {p m alpha q : ℕ} (hp : p.Prime) :
    FaceChain p m alpha q ≃ₗ[ℤ] CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact
    { toFun := fun c O a ↦ c (faceOrbitEquiv hp (O, a))
      invFun := fun x ↦
        (Finsupp.linearEquivFunOnFinite ℤ ℤ (AllowedFace p m alpha q)).symm
          (fun s ↦ x (orbitMk s) (orbitCoord s))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := by
        intro c
        apply Finsupp.ext
        intro s
        change c (faceOrbitEquiv hp (orbitMk s, orbitCoord s)) = c s
        exact congrArg c ((faceOrbitEquiv hp).apply_symm_apply s)
      right_inv := by
        intro x
        funext O a
        change x (orbitMk (faceOrbitEquiv hp (O, a)))
            (orbitCoord (faceOrbitEquiv hp (O, a))) = x O a
        exact congrArg (fun z ↦ x z.1 z.2)
          ((faceOrbitEquiv hp).symm_apply_apply (O, a)) }

@[simp] theorem chainCoords_apply {p m alpha q : ℕ} (hp : p.Prime)
    (c : FaceChain p m alpha q) (O : FaceOrbit p m alpha q) (a : ZMod p) :
    chainCoords hp c O a = c (shiftFace a (orbitRep O)) := rfl

/-- The generator in the orbitwise reoriented basis.  Thus translation has
coefficient `+1` along every chosen oriented orbit. -/
noncomputable def reorientedShift {p m alpha q : ℕ} (hp : p.Prime) :
    FaceChain p m alpha q →+ FaceChain p m alpha q := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (chainCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.g.comp (chainCoords hp).toAddEquiv.toAddMonoidHom)

/-- `tau = g - 1` in the reoriented orbit basis. -/
noncomputable def tau {p m alpha q : ℕ} (hp : p.Prime) :
    FaceChain p m alpha q →+ FaceChain p m alpha q :=
  reorientedShift hp - AddMonoidHom.id _

/-- The orbit norm `1 + g + ⋯ + g^(p-1)` in the reoriented orbit basis. -/
noncomputable def normOp {p m alpha q : ℕ} (hp : p.Prime) :
    FaceChain p m alpha q →+ FaceChain p m alpha q := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (chainCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.N.comp (chainCoords hp).toAddEquiv.toAddMonoidHom)

@[simp] theorem chainCoords_reorientedShift {p m alpha q : ℕ} [NeZero p]
    (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    chainCoords hp (reorientedShift hp c) =
      CyclicAlgebra.g (chainCoords hp c) := by
  change chainCoords hp ((chainCoords hp).symm
      (CyclicAlgebra.g (chainCoords hp c))) = _
  rw [(chainCoords hp).apply_symm_apply]

@[simp] theorem chainCoords_tau {p m alpha q : ℕ} [NeZero p] (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    chainCoords hp (tau hp c) = CyclicAlgebra.D (chainCoords hp c) := by
  rw [show tau hp c = reorientedShift hp c - c by rfl, map_sub,
    chainCoords_reorientedShift]
  rfl

@[simp] theorem chainCoords_normOp {p m alpha q : ℕ} [NeZero p] (hp : p.Prime)
    (c : FaceChain p m alpha q) :
    chainCoords hp (normOp hp c) = CyclicAlgebra.N (chainCoords hp c) := by
  change chainCoords hp ((chainCoords hp).symm
      (CyclicAlgebra.N (chainCoords hp c))) = _
  rw [(chainCoords hp).apply_symm_apply]

theorem exists_normOp_of_tau_eq_zero {p m alpha q : ℕ} (hp : p.Prime)
    {c : FaceChain p m alpha q} (hc : tau hp c = 0) :
    ∃ d, normOp hp d = c := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hD : CyclicAlgebra.D (chainCoords hp c) = 0 := by
    rw [← chainCoords_tau]
    simp [hc]
  obtain ⟨y, hy⟩ := CyclicAlgebra.exists_N_of_D_eq_zero hD
  refine ⟨(chainCoords hp).symm y, ?_⟩
  apply (chainCoords hp).injective
  rw [chainCoords_normOp, (chainCoords hp).apply_symm_apply, hy]

theorem exists_tau_of_normOp_eq_zero {p m alpha q : ℕ} (hp : p.Prime)
    {c : FaceChain p m alpha q} (hc : normOp hp c = 0) :
    ∃ d, tau hp d = c := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hN : CyclicAlgebra.N (chainCoords hp c) = 0 := by
    rw [← chainCoords_normOp]
    simp [hc]
  obtain ⟨y, hy⟩ := CyclicAlgebra.exists_D_of_N_eq_zero hN
  refine ⟨(chainCoords hp).symm y, ?_⟩
  apply (chainCoords hp).injective
  rw [chainCoords_tau, (chainCoords hp).apply_symm_apply, hy]

theorem ker_tau_eq_range_normOp {p m alpha q : ℕ} (hp : p.Prime) :
    AddMonoidHom.ker (tau (m := m) (alpha := alpha) (q := q) hp) =
      AddMonoidHom.range (normOp (m := m) (alpha := alpha) (q := q) hp) := by
  ext c
  constructor
  · intro hc
    exact exists_normOp_of_tau_eq_zero hp hc
  · rintro ⟨d, rfl⟩
    change tau hp (normOp hp d) = 0
    apply (chainCoords hp).injective
    letI : NeZero p := ⟨hp.ne_zero⟩
    rw [map_zero, chainCoords_tau, chainCoords_normOp]
    have h := congrArg
      (fun f : CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) →+
          CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) ↦
        f (chainCoords hp d))
      (CyclicAlgebra.D_comp_N (p := p) (ι := FaceOrbit p m alpha q))
    simpa using h

theorem ker_normOp_eq_range_tau {p m alpha q : ℕ} (hp : p.Prime) :
    AddMonoidHom.ker (normOp (m := m) (alpha := alpha) (q := q) hp) =
      AddMonoidHom.range (tau (m := m) (alpha := alpha) (q := q) hp) := by
  ext c
  constructor
  · intro hc
    exact exists_tau_of_normOp_eq_zero hp hc
  · rintro ⟨d, rfl⟩
    change normOp hp (tau hp d) = 0
    apply (chainCoords hp).injective
    letI : NeZero p := ⟨hp.ne_zero⟩
    rw [map_zero, chainCoords_normOp, chainCoords_tau]
    have h := congrArg
      (fun f : CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) →+
          CyclicAlgebra.FreeCyclic p (FaceOrbit p m alpha q) ↦
        f (chainCoords hp d))
      (CyclicAlgebra.N_comp_D (p := p) (ι := FaceOrbit p m alpha q))
    simpa using h

/-! ## One positive allowed module containing every degree

The sigma index excludes the empty face because every `AllowedFace ... q` has
cardinality `q + 1`.  This is the ambient module used by periodic descent: the
boundary can change `q`, while cyclic translation preserves it. -/

abbrev TotalFace (p m alpha : ℕ) := Σ q : ℕ, AllowedFace p m alpha q

abbrev PositiveAllowedFinset (p m alpha : ℕ) :=
  {s : Finset (Label p m) // s.Nonempty ∧ Allowed alpha s}

/-- Forgetting degree identifies the sigma of homogeneous nonempty faces with
all nonempty allowed finsets. -/
noncomputable def totalFaceEquivPositive (p m alpha : ℕ) :
    TotalFace p m alpha ≃ PositiveAllowedFinset p m alpha := by
  let f : TotalFace p m alpha → PositiveAllowedFinset p m alpha :=
    fun z ↦ ⟨z.2.1, allowedFace_nonempty z.2, z.2.2.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨q, s⟩ ⟨r, t⟩ h
    have hst : s.1 = t.1 := congrArg Subtype.val h
    have hq : q = r := by
      have hs := s.2.1
      have ht := t.2.1
      rw [hst] at hs
      omega
    apply Sigma.ext hq
    cases hq
    exact heq_of_eq (Subtype.ext hst)
  · intro s
    have hs : 0 < s.1.card := Finset.card_pos.mpr s.2.1
    refine ⟨⟨s.1.card - 1, ⟨s.1, by omega, s.2.2⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

noncomputable instance (p m alpha : ℕ) [NeZero p] :
    Fintype (PositiveAllowedFinset p m alpha) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance (p m alpha : ℕ) [NeZero p] :
    Fintype (TotalFace p m alpha) :=
  Fintype.ofEquiv (PositiveAllowedFinset p m alpha)
    (totalFaceEquivPositive p m alpha).symm

abbrev TotalOrbit (p m alpha : ℕ) := Σ q : ℕ, FaceOrbit p m alpha q

/-- Orbit/coordinate parametrization simultaneously in every positive degree. -/
noncomputable def totalOrbitEquiv {p m alpha : ℕ} (hp : p.Prime) :
    TotalOrbit p m alpha × ZMod p ≃ TotalFace p m alpha where
  toFun z := ⟨z.1.1, faceOrbitEquiv hp (z.1.2, z.2)⟩
  invFun s := ⟨⟨s.1, orbitMk s.2⟩, orbitCoord s.2⟩
  left_inv z := by
    rcases z with ⟨⟨q, O⟩, a⟩
    change (⟨⟨q, orbitMk (faceOrbitEquiv hp (O, a))⟩,
      orbitCoord (faceOrbitEquiv hp (O, a))⟩ :
        TotalOrbit p m alpha × ZMod p) = ⟨⟨q, O⟩, a⟩
    have h := (faceOrbitEquiv hp).symm_apply_apply (O, a)
    exact congrArg (fun z : FaceOrbit p m alpha q × ZMod p ↦
      (⟨⟨q, z.1⟩, z.2⟩ : TotalOrbit p m alpha × ZMod p)) h
  right_inv s := by
    rcases s with ⟨q, s⟩
    change (⟨q, faceOrbitEquiv hp (orbitMk s, orbitCoord s)⟩ :
      TotalFace p m alpha) = ⟨q, s⟩
    exact Sigma.ext rfl (heq_of_eq ((faceOrbitEquiv hp).apply_symm_apply s))

abbrev TotalChain (p m alpha : ℕ) := TotalFace p m alpha →₀ ℤ

/-- The total positive allowed chain module is a direct union of free cyclic
orbits, with one chosen transported orientation on each orbit. -/
noncomputable def totalChainCoords {p m alpha : ℕ} (hp : p.Prime) :
    TotalChain p m alpha ≃ₗ[ℤ]
      CyclicAlgebra.FreeCyclic p (TotalOrbit p m alpha) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact
    { toFun := fun c O a ↦ c (totalOrbitEquiv hp (O, a))
      invFun := fun x ↦
        (Finsupp.linearEquivFunOnFinite ℤ ℤ (TotalFace p m alpha)).symm
          (fun s ↦ x ⟨s.1, orbitMk s.2⟩ (orbitCoord s.2))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := by
        intro c
        apply Finsupp.ext
        intro s
        change c (totalOrbitEquiv hp
          (⟨s.1, orbitMk s.2⟩, orbitCoord s.2)) = c s
        exact congrArg c ((totalOrbitEquiv hp).apply_symm_apply s)
      right_inv := by
        intro x
        funext O a
        change x ⟨(totalOrbitEquiv hp (O, a)).1,
            orbitMk (totalOrbitEquiv hp (O, a)).2⟩
            (orbitCoord (totalOrbitEquiv hp (O, a)).2) = x O a
        exact congrArg (fun z ↦ x z.1 z.2)
          ((totalOrbitEquiv hp).symm_apply_apply (O, a)) }

@[simp] theorem totalChainCoords_apply {p m alpha : ℕ} (hp : p.Prime)
    (c : TotalChain p m alpha) (O : TotalOrbit p m alpha) (a : ZMod p) :
    totalChainCoords hp c O a = c (totalOrbitEquiv hp (O, a)) := rfl

noncomputable def totalTau {p m alpha : ℕ} (hp : p.Prime) :
    TotalChain p m alpha →+ TotalChain p m alpha := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (totalChainCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.D.comp (totalChainCoords hp).toAddEquiv.toAddMonoidHom)

noncomputable def totalNorm {p m alpha : ℕ} (hp : p.Prime) :
    TotalChain p m alpha →+ TotalChain p m alpha := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (totalChainCoords hp).symm.toAddEquiv.toAddMonoidHom.comp
    (CyclicAlgebra.N.comp (totalChainCoords hp).toAddEquiv.toAddMonoidHom)

@[simp] theorem totalChainCoords_tau {p m alpha : ℕ} [NeZero p]
    (hp : p.Prime) (c : TotalChain p m alpha) :
    totalChainCoords hp (totalTau hp c) =
      CyclicAlgebra.D (totalChainCoords hp c) := by
  change totalChainCoords hp ((totalChainCoords hp).symm
    (CyclicAlgebra.D (totalChainCoords hp c))) = _
  rw [(totalChainCoords hp).apply_symm_apply]

@[simp] theorem totalChainCoords_norm {p m alpha : ℕ} [NeZero p]
    (hp : p.Prime) (c : TotalChain p m alpha) :
    totalChainCoords hp (totalNorm hp c) =
      CyclicAlgebra.N (totalChainCoords hp c) := by
  change totalChainCoords hp ((totalChainCoords hp).symm
    (CyclicAlgebra.N (totalChainCoords hp c))) = _
  rw [(totalChainCoords hp).apply_symm_apply]

end TargetOrbits
