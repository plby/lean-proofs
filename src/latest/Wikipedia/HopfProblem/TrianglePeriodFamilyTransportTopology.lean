import Wikipedia.HopfProblem.TrianglePeriodFamilyTopology
import Mathlib.Topology.Homotopy.Lifting

/-!
# Intrinsic transport in a diagonal covering quotient

Transport lifts a base path through the actual covering and keeps the
fibre coordinate constant. The fibre homeomorphisms come from the existing
local products. Equivariance of covering monodromy proves independence of
the chosen starting lift. In the same starting marking, an endpoint `g • b`
therefore acts on the fibre by `g⁻¹`.
-/

noncomputable section

open Set Topology unitInterval

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]

/-- Changing only the base representative changes the fibre marking by
the inverse group action. -/
theorem quotient_smul_fst (g : G) (b : B) (f : F) :
    quotient G B F (g • b, f) = quotient G B F (b, g⁻¹ • f) := by
  apply (quotient_eq_iff G B F _ _).mpr
  exact ⟨g, by simp⟩

variable [TopologicalSpace B] [TopologicalSpace F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    {x y z : BaseSpace G B}

/-- The actual horizontal path obtained by lifting the base path and
keeping the original fibre coordinate fixed. -/
def horizontalPath (γ : Path x y) (b : B) (hb : baseQuotient G B b = x) (f : F) :
    Path (quotient G B F (b, f))
      (quotient G B F
        ((hq.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) ⟨b, hb⟩ : B), f)) where
  toFun t := quotient G B F
    (hq.isCoveringMap.liftPath γ b (γ.source.trans hb.symm) t, f)
  continuous_toFun := (quotient_continuous G B F).comp
    ((hq.isCoveringMap.liftPath γ b (γ.source.trans hb.symm)).continuous.prodMk
      continuous_const)
  source' := by rw [hq.isCoveringMap.liftPath_zero]
  target' := rfl

@[simp] theorem horizontalPath_apply (γ : Path x y) (b : B)
    (hb : baseQuotient G B b = x) (f : F) (t : I) :
    horizontalPath hq γ b hb f t = quotient G B F
      (hq.isCoveringMap.liftPath γ b (γ.source.trans hb.symm) t, f) := rfl

@[simp] theorem projection_horizontalPath (γ : Path x y) (b : B)
    (hb : baseQuotient G B b = x) (f : F) (t : I) :
    projection G B F (horizontalPath hq γ b hb f t) = γ t :=
  congrFun (hq.isCoveringMap.liftPath_lifts γ b (γ.source.trans hb.symm)) t

@[simp] theorem horizontalPath_source (γ : Path x y) (b : B)
    (hb : baseQuotient G B b = x) (f : F) :
    horizontalPath hq γ b hb f 0 = quotient G B F (b, f) :=
  (horizontalPath hq γ b hb f).source

@[simp] theorem horizontalPath_target (γ : Path x y) (b : B)
    (hb : baseQuotient G B b = x) (f : F) :
    horizontalPath hq γ b hb f 1 = quotient G B F
      ((hq.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) ⟨b, hb⟩ : B), f) :=
  (horizontalPath hq γ b hb f).target

/-- The whole horizontal path, not just its endpoint, is invariant under
a simultaneous change of base lift and fibre coordinate. -/
theorem horizontalPath_smul (γ : Path x y) (g : G) (b : B)
    (hb : baseQuotient G B b = x) (f : F) (t : I) :
    horizontalPath hq γ (g • b) ((hq.map_smul g).trans hb) (g • f) t =
      horizontalPath hq γ b hb f t := by
  have hlift :
      (fun t => g • hq.isCoveringMap.liftPath γ b (γ.source.trans hb.symm) t) =
      hq.isCoveringMap.liftPath γ (g • b)
        (γ.source.trans ((hq.map_smul g).trans hb).symm) := by
    apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
    refine ⟨(hq.continuous_const_smul g).comp
      (hq.isCoveringMap.liftPath γ b (γ.source.trans hb.symm)).continuous, ?_, ?_⟩
    · funext t
      exact (hq.map_smul g).trans
        (congrFun (hq.isCoveringMap.liftPath_lifts γ b (γ.source.trans hb.symm)) t)
    · rw [hq.isCoveringMap.liftPath_zero]
  simp only [horizontalPath_apply]
  rw [← congrFun hlift t]
  exact quotient_smul G B F g
    (hq.isCoveringMap.liftPath γ b (γ.source.trans hb.symm) t, f)

/-- Any two representatives of a starting point give the same actual
horizontal path at every time. -/
theorem horizontalPath_eq_of_quotient_eq (γ : Path x y) (b b' : B)
    (hb : baseQuotient G B b = x) (hb' : baseQuotient G B b' = x)
    (f f' : F) (heq : quotient G B F (b, f) = quotient G B F (b', f')) (t : I) :
    horizontalPath hq γ b hb f t = horizontalPath hq γ b' hb' f' t := by
  obtain ⟨g, hg⟩ := (quotient_eq_iff G B F (b, f) (b', f')).mp heq
  have hgb : g • b' = b := congrArg Prod.fst hg
  have hgf : g • f' = f := congrArg Prod.snd hg
  subst b
  subst f
  exact horizontalPath_smul hq γ g b' hb' f' t

variable [ContinuousConstSMul G F]

/-- The existing fibre homeomorphism, with an arbitrary specified lift
of the base point and with the marking direction `F → fibre`. -/
def fibreMarking (b : baseQuotient G B ⁻¹' {x}) :
    F ≃ₜ (projection G B F ⁻¹' {x}) := by
  rcases b with ⟨b, hb⟩
  change baseQuotient G B b = x at hb
  subst x
  exact (fibreHomeomorphOver hq b).symm

@[simp] theorem fibreMarking_coe (b : baseQuotient G B ⁻¹' {x}) (f : F) :
    (fibreMarking hq b f : Space G B F) = quotient G B F ((b : B), f) := by
  rcases b with ⟨b, hb⟩
  change baseQuotient G B b = x at hb
  subst x
  exact fibreHomeomorphOver_symm_coe hq b f

@[simp] theorem fibreMarking_self (b : B) :
    fibreMarking (F := F) hq ⟨b, rfl⟩ = (fibreHomeomorphOver hq b).symm := rfl

/-- Acting simultaneously on a lift and a fibre coordinate leaves the
marked point of the actual diagonal quotient unchanged. -/
theorem fibreMarking_smul (g : G) (b : baseQuotient G B ⁻¹' {x}) (f : F) :
    fibreMarking hq (hq.toPermFiber x g b) (g • f) = fibreMarking hq b f := by
  apply Subtype.ext
  rw [fibreMarking_coe, fibreMarking_coe]
  change quotient G B F (g • (b : B), g • f) = quotient G B F ((b : B), f)
  exact quotient_smul G B F g ((b : B), f)

/-- Transport expressed using one starting lift and its actual lifted endpoint. -/
def transportFromLift (γ : Path.Homotopic.Quotient x y)
    (b : baseQuotient G B ⁻¹' {x}) :
    (projection G B F ⁻¹' {x}) ≃ₜ (projection G B F ⁻¹' {y}) :=
  (fibreMarking hq b).symm.trans (fibreMarking hq (hq.isCoveringMap.monodromy γ b))

@[simp] theorem transportFromLift_apply_marking (γ : Path.Homotopic.Quotient x y)
    (b : baseQuotient G B ⁻¹' {x}) (f : F) :
    transportFromLift hq γ b (fibreMarking hq b f) =
      fibreMarking hq (hq.isCoveringMap.monodromy γ b) f := by
  simp only [transportFromLift, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]

/-- Equivariance of actual covering monodromy removes the choice of starting lift. -/
theorem transportFromLift_independent (γ : Path.Homotopic.Quotient x y)
    (b b' : baseQuotient G B ⁻¹' {x}) :
    transportFromLift (F := F) hq γ b = transportFromLift hq γ b' := by
  obtain ⟨g, hg⟩ := hq.exists_toPermFiber_eq b b'
  subst b'
  apply Homeomorph.ext
  intro p
  obtain ⟨f, rfl⟩ := (fibreMarking hq b).surjective p
  calc
    transportFromLift hq γ b (fibreMarking hq b f) =
        fibreMarking hq (hq.isCoveringMap.monodromy γ b) f :=
      transportFromLift_apply_marking hq γ b f
    _ = fibreMarking hq (hq.isCoveringMap.monodromy γ (hq.toPermFiber x g b)) (g • f) := by
      rw [hq.monodromy_toPermFiber]
      exact (fibreMarking_smul hq g (hq.isCoveringMap.monodromy γ b) f).symm
    _ = transportFromLift hq γ (hq.toPermFiber x g b) (fibreMarking hq b f) := by
      rw [← fibreMarking_smul hq g b f, transportFromLift_apply_marking]

/-- Intrinsic fibre transport along a homotopy class of base paths. -/
def transport (γ : Path.Homotopic.Quotient x y) :
    (projection G B F ⁻¹' {x}) ≃ₜ (projection G B F ⁻¹' {y}) :=
  transportFromLift hq γ ⟨(hq.surjective x).choose, (hq.surjective x).choose_spec⟩

theorem transport_eq_transportFromLift (γ : Path.Homotopic.Quotient x y)
    (b : baseQuotient G B ⁻¹' {x}) :
    transport (F := F) hq γ = transportFromLift hq γ b :=
  transportFromLift_independent hq γ _ b

@[simp] theorem transport_apply_marking (γ : Path.Homotopic.Quotient x y)
    (b : baseQuotient G B ⁻¹' {x}) (f : F) :
    transport hq γ (fibreMarking hq b f) =
      fibreMarking hq (hq.isCoveringMap.monodromy γ b) f := by
  rw [transport_eq_transportFromLift hq γ b, transportFromLift_apply_marking]

/-- Evaluation on any quotient representative uses the actual lifted endpoint,
independently of the lift selected in the definition of `transport`. -/
@[simp] theorem transport_apply_quotient (γ : Path.Homotopic.Quotient x y)
    (b : B) (hb : baseQuotient G B b = x) (f : F) :
    (transport hq γ ⟨quotient G B F (b, f), hb⟩ : Space G B F) =
      quotient G B F ((hq.isCoveringMap.monodromy γ ⟨b, hb⟩ : B), f) := by
  have hin : (⟨quotient G B F (b, f), hb⟩ : projection G B F ⁻¹' {x}) =
      fibreMarking hq ⟨b, hb⟩ f :=
    Subtype.ext (fibreMarking_coe hq ⟨b, hb⟩ f).symm
  rw [hin, transport_apply_marking, fibreMarking_coe]

@[simp] theorem transport_refl (x : BaseSpace G B) :
    transport (F := F) hq (Path.Homotopic.Quotient.refl x) = Homeomorph.refl _ := by
  apply Homeomorph.ext
  intro p
  obtain ⟨b, hb⟩ := hq.surjective x
  obtain ⟨f, rfl⟩ := (fibreMarking hq ⟨b, hb⟩).surjective p
  rw [transport_apply_marking, hq.isCoveringMap.monodromy_refl]
  rfl

/-- Successive transports follow the actual concatenation order of paths. -/
theorem transport_trans (γ : Path.Homotopic.Quotient x y)
    (δ : Path.Homotopic.Quotient y z) :
    transport (F := F) hq (γ.trans δ) = (transport hq γ).trans (transport hq δ) := by
  apply Homeomorph.ext
  intro p
  obtain ⟨b, hb⟩ := hq.surjective x
  obtain ⟨f, rfl⟩ := (fibreMarking hq ⟨b, hb⟩).surjective p
  simp only [Homeomorph.trans_apply, transport_apply_marking,
    hq.isCoveringMap.monodromy_trans_apply]

@[simp] theorem transport_symm (γ : Path.Homotopic.Quotient x y) :
    transport (F := F) hq γ.symm = (transport hq γ).symm := by
  apply Homeomorph.ext
  intro p
  apply (transport hq γ).injective
  change ((transport hq γ.symm).trans (transport hq γ)) p =
    (transport hq γ) ((transport hq γ).symm p)
  rw [← transport_trans, Path.Homotopic.Quotient.symm_trans, transport_refl]
  simp only [Homeomorph.refl_apply, Homeomorph.apply_symm_apply, id_eq]

/-- The same starting marking converts the lifted endpoint `g • b`
into the inverse action `g⁻¹` on the original fibre. -/
theorem transport_loop_marking_of_endpoint (γ : Path.Homotopic.Quotient x x)
    (b : baseQuotient G B ⁻¹' {x}) (g : G)
    (hg : (hq.isCoveringMap.monodromy γ b : B) = g • (b : B)) (f : F) :
    transport hq γ (fibreMarking hq b f) = fibreMarking hq b (g⁻¹ • f) := by
  rw [transport_apply_marking]
  apply Subtype.ext
  rw [fibreMarking_coe, fibreMarking_coe, hg, quotient_smul_fst]

theorem fibreMarking_symm_transport_loop_of_endpoint (γ : Path.Homotopic.Quotient x x)
    (b : baseQuotient G B ⁻¹' {x}) (g : G)
    (hg : (hq.isCoveringMap.monodromy γ b : B) = g • (b : B)) (f : F) :
    (fibreMarking hq b).symm (transport hq γ (fibreMarking hq b f)) = g⁻¹ • f := by
  rw [transport_loop_marking_of_endpoint hq γ b g hg, Homeomorph.symm_apply_apply]

/-- The inverse-action formula in the original `fibreHomeomorphOver` coordinates. -/
theorem fibreHomeomorphOver_transport_loop_of_endpoint (b : B)
    (γ : Path.Homotopic.Quotient (baseQuotient G B b) (baseQuotient G B b)) (g : G)
    (hg : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = g • b) (f : F) :
    fibreHomeomorphOver hq b
      (transport hq γ ((fibreHomeomorphOver hq b).symm f)) = g⁻¹ • f := by
  simpa only [fibreMarking_self, Homeomorph.symm_symm] using
    fibreMarking_symm_transport_loop_of_endpoint hq γ ⟨b, rfl⟩ g hg f

/-- Transport for an actual path is the intrinsic transport of its homotopy class. -/
def pathTransport (γ : Path x y) :
    (projection G B F ⁻¹' {x}) ≃ₜ (projection G B F ⁻¹' {y}) :=
  transport hq (Path.Homotopic.Quotient.mk γ)

theorem pathTransport_homotopic {γ δ : Path x y} (h : γ.Homotopic δ) :
    pathTransport (F := F) hq γ = pathTransport hq δ :=
  congrArg (transport (F := F) hq) (Path.Homotopic.Quotient.eq.mpr h)

theorem transport_homotopy {γ δ : Path x y} (h : γ.Homotopic δ) :
    transport (F := F) hq (Path.Homotopic.Quotient.mk γ) =
      transport hq (Path.Homotopic.Quotient.mk δ) :=
  pathTransport_homotopic hq h

@[simp] theorem pathTransport_refl (x : BaseSpace G B) :
    pathTransport (F := F) hq (Path.refl x) = Homeomorph.refl _ :=
  transport_refl hq x

theorem pathTransport_trans (γ : Path x y) (δ : Path y z) :
    pathTransport (F := F) hq (γ.trans δ) =
      (pathTransport hq γ).trans (pathTransport hq δ) :=
  transport_trans hq (Path.Homotopic.Quotient.mk γ) (Path.Homotopic.Quotient.mk δ)

@[simp] theorem pathTransport_symm (γ : Path x y) :
    pathTransport (F := F) hq γ.symm = (pathTransport hq γ).symm :=
  transport_symm hq (Path.Homotopic.Quotient.mk γ)

@[simp] theorem pathTransport_apply_quotient (γ : Path x y)
    (b : B) (hb : baseQuotient G B b = x) (f : F) :
    (pathTransport hq γ ⟨quotient G B F (b, f), hb⟩ : Space G B F) =
      quotient G B F
        ((hq.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) ⟨b, hb⟩ : B), f) :=
  transport_apply_quotient hq (Path.Homotopic.Quotient.mk γ) b hb f

/-- The homeomorphism's value is the endpoint of the actual constant-fibre
horizontal path, not merely an abstract identification of the two fibres. -/
theorem horizontalPath_endpoint_eq_transport (γ : Path x y) (b : B)
    (hb : baseQuotient G B b = x) (f : F) :
    horizontalPath hq γ b hb f 1 =
      (pathTransport hq γ ⟨quotient G B F (b, f), hb⟩ : Space G B F) :=
  (horizontalPath_target hq γ b hb f).trans (pathTransport_apply_quotient hq γ b hb f).symm

end Wikipedia.HopfProblem.DiagonalQuotient
