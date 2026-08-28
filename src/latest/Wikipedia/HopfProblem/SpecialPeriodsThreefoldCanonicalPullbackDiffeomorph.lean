import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullback

/-!
# Canonical pullback under a genuine biholomorphism

Pullback by an analytic diffeomorphism and pullback by its inverse are
inverse maps on the actual canonical fibres.  The base-point equalities
are used explicitly when assembling the fibre maps into the existing
canonical total spaces.  This file only constructs the bundle-total-space
equivalence; it does not change the topology or assert holomorphicity.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]
  [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N]

/-- Equality-induced identification of canonical fibres.  It identifies
only equal base points, independently of the chosen scalar models. -/
def fiberTransport {x y : M} (h : x = y) :
    (Atlas.core M).Fiber x ≃L[ℂ] (Atlas.core M).Fiber y := by
  subst y
  exact ContinuousLinearEquiv.refl ℂ ((Atlas.core M).Fiber x)

/-- The scalar representation of equality transport is unchanged. -/
@[simp] theorem fiberTransport_apply {x y : M} (h : x = y)
    (v : (Atlas.core M).Fiber x) :
    id (α := ℂ) (fiberTransport h v) = id (α := ℂ) v := by
  subst y
  rfl

/-- The native chain rule applied to `e.symm ∘ e = id`.  The output fibre
of the composite is identified using this actual inverse equality. -/
theorem pullbackLinear_diffeomorph_symm_apply (e : Diffeomorph I I M N ω)
    (x : M) (v : (Atlas.core M).Fiber x) :
    pullbackLinear e x (pullbackLinear e.symm (e x) v) = v := by
  have hcomp := pullbackLinear_comp (e.mdifferentiable (by simp) x)
    (e.symm.mdifferentiable (by simp) (e x))
  have hfun : (e.symm : N → M) ∘ (e : M → N) = id :=
    funext e.symm_apply_apply
  have hid : pullbackLinear ((e.symm : N → M) ∘ (e : M → N)) x v = v := by
    calc
      pullbackLinear ((e.symm : N → M) ∘ (e : M → N)) x v =
          pullbackLinear (id : M → M) x v :=
        congrArg (fun f : M → M => id (α := ℂ) (pullbackLinear f x v)) hfun
      _ = v := congrArg (fun A : (Atlas.core M).Fiber x →L[ℂ]
          (Atlas.core M).Fiber x => A v) (pullbackLinear_id x)
  exact (congrArg (fun A => A v) hcomp).symm.trans hid

/-- The reverse identity, now at an arbitrary point of the target. -/
theorem pullbackLinear_symm_diffeomorph_apply (e : Diffeomorph I I M N ω)
    (y : N) (v : (Atlas.core N).Fiber y) :
    pullbackLinear e.symm y (pullbackLinear e (e.symm y) v) = v :=
  pullbackLinear_diffeomorph_symm_apply e.symm y v

/-- Inverse canonical pullback is pullback by the inverse diffeomorphism.
The two descriptions have base points `x` and `e.symm (e x)`, equal by
the inverse law used above. -/
theorem diffeomorphPullback_symm_apply (e : Diffeomorph I I M N ω)
    (x : M) (v : (Atlas.core M).Fiber x) :
    (diffeomorphPullback e x).symm v = pullbackLinear e.symm (e x) v := by
  apply (diffeomorphPullback e x).injective
  calc
    diffeomorphPullback e x ((diffeomorphPullback e x).symm v) = v :=
      (diffeomorphPullback e x).apply_symm_apply v
    _ = diffeomorphPullback e x (pullbackLinear e.symm (e x) v) :=
      (pullbackLinear_diffeomorph_symm_apply e x v).symm

theorem diffeomorphPullback_symm_toContinuousLinearMap
    (e : Diffeomorph I I M N ω) (x : M) :
    (diffeomorphPullback e x).symm.toContinuousLinearMap =
      pullbackLinear e.symm (e x) := by
  apply ContinuousLinearMap.ext
  intro v
  exact diffeomorphPullback_symm_apply e x v

/-- The fibre-linear equivalence over the inverse base map.  Its source is
literally the fibre at `y`, using equality transport before pullback. -/
def diffeomorphFiberPullback (e : Diffeomorph I I M N ω) (y : N) :
    (Atlas.core N).Fiber y ≃L[ℂ] (Atlas.core M).Fiber (e.symm y) :=
  (fiberTransport (e.apply_symm_apply y).symm).trans
    (diffeomorphPullback e (e.symm y))

@[simp] theorem diffeomorphFiberPullback_apply (e : Diffeomorph I I M N ω)
    (y : N) (v : (Atlas.core N).Fiber y) :
    diffeomorphFiberPullback e y v = pullbackLinear e (e.symm y) v := by
  change pullbackLinear e (e.symm y)
      (fiberTransport (e.apply_symm_apply y).symm v) = _
  exact congrArg (pullbackLinear e (e.symm y))
    (fiberTransport_apply (e.apply_symm_apply y).symm v)

/-- Canonical pullback on the existing total spaces, covering `e.symm`.
The input fibre is transported only along `e (e.symm y) = y`. -/
def diffeomorphTotalPullback (e : Diffeomorph I I M N ω)
    (v : (Atlas.core N).TotalSpace) : (Atlas.core M).TotalSpace :=
  ⟨e.symm v.proj, pullbackLinear e (e.symm v.proj)
    (fiberTransport (e.apply_symm_apply v.proj).symm v.snd)⟩

@[simp] theorem diffeomorphTotalPullback_proj (e : Diffeomorph I I M N ω)
    (v : (Atlas.core N).TotalSpace) :
    (diffeomorphTotalPullback e v).proj = e.symm v.proj := rfl

/-- Each restriction to a fibre is precisely the continuous linear
equivalence just constructed, not only a bijection of scalar sets. -/
theorem diffeomorphTotalPullback_mk_fiber (e : Diffeomorph I I M N ω)
    (y : N) (v : (Atlas.core N).Fiber y) :
    diffeomorphTotalPullback e ⟨y, v⟩ =
      ⟨e.symm y, diffeomorphFiberPullback e y v⟩ := rfl

@[simp] theorem diffeomorphTotalPullback_mk (e : Diffeomorph I I M N ω)
    (y : N) (v : (Atlas.core N).Fiber y) :
    diffeomorphTotalPullback e ⟨y, v⟩ =
      ⟨e.symm y, pullbackLinear e (e.symm y) v⟩ := by
  exact (diffeomorphTotalPullback_mk_fiber e y v).trans
    (congrArg (Bundle.TotalSpace.mk (e.symm y))
      (diffeomorphFiberPullback_apply e y v))

theorem diffeomorphTotalPullback_snd (e : Diffeomorph I I M N ω)
    (v : (Atlas.core N).TotalSpace) :
    id (α := ℂ) (diffeomorphTotalPullback e v).snd =
      id (α := ℂ) (pullbackLinear e (e.symm v.proj) v.snd) :=
  diffeomorphFiberPullback_apply e v.proj v.snd

/-- The inverse total-space map covers `e`. -/
def diffeomorphTotalPushforward (e : Diffeomorph I I M N ω)
    (v : (Atlas.core M).TotalSpace) : (Atlas.core N).TotalSpace :=
  ⟨e v.proj, (diffeomorphPullback e v.proj).symm v.snd⟩

@[simp] theorem diffeomorphTotalPushforward_proj (e : Diffeomorph I I M N ω)
    (v : (Atlas.core M).TotalSpace) :
    (diffeomorphTotalPushforward e v).proj = e v.proj := rfl

@[simp] theorem diffeomorphTotalPushforward_mk (e : Diffeomorph I I M N ω)
    (x : M) (v : (Atlas.core M).Fiber x) :
    diffeomorphTotalPushforward e ⟨x, v⟩ =
      ⟨e x, (diffeomorphPullback e x).symm v⟩ := rfl

/-- Pushforward is pullback by the actual inverse diffeomorphism. -/
theorem diffeomorphTotalPushforward_eq_pullback_symm
    (e : Diffeomorph I I M N ω) (v : (Atlas.core M).TotalSpace) :
    diffeomorphTotalPushforward e v = diffeomorphTotalPullback e.symm v := by
  rcases v with ⟨x, v⟩
  calc
    diffeomorphTotalPushforward e ⟨x, v⟩ =
        ⟨e x, pullbackLinear e.symm (e x) v⟩ :=
      congrArg (Bundle.TotalSpace.mk (e x)) (diffeomorphPullback_symm_apply e x v)
    _ = diffeomorphTotalPullback e.symm ⟨x, v⟩ :=
      (diffeomorphTotalPullback_mk e.symm x v).symm

@[simp] theorem diffeomorphTotalPullback_pushforward
    (e : Diffeomorph I I M N ω) (v : (Atlas.core M).TotalSpace) :
    diffeomorphTotalPullback e (diffeomorphTotalPushforward e v) = v := by
  rcases v with ⟨x, v⟩
  rw [diffeomorphTotalPushforward_eq_pullback_symm]
  simp only [diffeomorphTotalPullback_mk]
  apply Bundle.TotalSpace.ext
  · exact e.symm_apply_apply x
  · apply heq_of_eq
    exact (congrArg (fun z : M => id (α := ℂ)
      (pullbackLinear e z (pullbackLinear e.symm (e x) v)))
        (e.symm_apply_apply x)).trans (pullbackLinear_diffeomorph_symm_apply e x v)

@[simp] theorem diffeomorphTotalPushforward_pullback
    (e : Diffeomorph I I M N ω) (v : (Atlas.core N).TotalSpace) :
    diffeomorphTotalPushforward e (diffeomorphTotalPullback e v) = v := by
  rcases v with ⟨y, v⟩
  rw [diffeomorphTotalPushforward_eq_pullback_symm]
  simp only [diffeomorphTotalPullback_mk]
  apply Bundle.TotalSpace.ext
  · exact e.apply_symm_apply y
  · apply heq_of_eq
    exact (congrArg (fun z : N => id (α := ℂ)
      (pullbackLinear e.symm z (pullbackLinear e (e.symm y) v)))
        (e.apply_symm_apply y)).trans (pullbackLinear_symm_diffeomorph_apply e y v)

/-- Contravariant equivalence of the existing canonical total spaces.
Its fibre restrictions are complex-linear equivalences, and its base map
is `e.symm`.  The original bundle topologies and atlases are retained. -/
def diffeomorphTotalEquiv (e : Diffeomorph I I M N ω) :
    (Atlas.core N).TotalSpace ≃ (Atlas.core M).TotalSpace where
  toFun := diffeomorphTotalPullback e
  invFun := diffeomorphTotalPushforward e
  left_inv := diffeomorphTotalPushforward_pullback e
  right_inv := diffeomorphTotalPullback_pushforward e

@[simp] theorem diffeomorphTotalEquiv_apply (e : Diffeomorph I I M N ω)
    (v : (Atlas.core N).TotalSpace) :
    diffeomorphTotalEquiv e v = diffeomorphTotalPullback e v := rfl

@[simp] theorem diffeomorphTotalEquiv_symm_apply (e : Diffeomorph I I M N ω)
    (v : (Atlas.core M).TotalSpace) :
    (diffeomorphTotalEquiv e).symm v = diffeomorphTotalPushforward e v := rfl

@[simp] theorem diffeomorphTotalEquiv_proj (e : Diffeomorph I I M N ω)
    (v : (Atlas.core N).TotalSpace) :
    (diffeomorphTotalEquiv e v).proj = e.symm v.proj := rfl

@[simp] theorem diffeomorphTotalEquiv_symm_proj (e : Diffeomorph I I M N ω)
    (v : (Atlas.core M).TotalSpace) :
    ((diffeomorphTotalEquiv e).symm v).proj = e v.proj := rfl

theorem diffeomorphTotalEquiv_mk (e : Diffeomorph I I M N ω)
    (y : N) (v : (Atlas.core N).Fiber y) :
    diffeomorphTotalEquiv e ⟨y, v⟩ =
      ⟨e.symm y, diffeomorphFiberPullback e y v⟩ := rfl

theorem diffeomorphTotalEquiv_symm_mk (e : Diffeomorph I I M N ω)
    (x : M) (v : (Atlas.core M).Fiber x) :
    (diffeomorphTotalEquiv e).symm ⟨x, v⟩ =
      ⟨e x, (diffeomorphPullback e x).symm v⟩ := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback
