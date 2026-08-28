import Wikipedia.HopfProblem.OrbitPairTargetClockCollisionTransport
import Wikipedia.HopfProblem.OrbitPairPositiveScalarClock
import Wikipedia.HopfProblem.OrbitPairTrackDiffeomorphismTransport
import Wikipedia.HopfProblem.OrbitPairRetimingImmersion

/-!
# Constructed native retiming by a projected-target clock

The ambient shear `(t,z) -> (t + beta(z),z)` is a native diffeomorphism.
When its restriction to the old track has positive time-fibre derivative,
the source time map is also a native diffeomorphism. Restoring its new time
coordinate gives an exactly transported regular family. Small supported
clocks satisfy the required positivity by a proved uniform bound.

The radius is positive but not a claim of arbitrary long-time reachability.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.TargetClock

open FamilyDoublePoints SynchronizedPairs NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

def timeShear (β : N → ℝ) (hβ : ContMDiff J 𝓘(ℝ, ℝ) ∞ β) :
    Diffeomorph (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J) (ℝ × N) (ℝ × N) ∞ where
  toFun q := (q.1 + β q.2, q.2)
  invFun q := (q.1 - β q.2, q.2)
  left_inv q := Prod.ext (add_sub_cancel_right _ _) rfl
  right_inv q := Prod.ext (sub_add_cancel _ _) rfl
  contMDiff_toFun := (contMDiff_fst.add (hβ.comp contMDiff_snd)).prodMk contMDiff_snd
  contMDiff_invFun := (contMDiff_fst.sub (hβ.comp contMDiff_snd)).prodMk contMDiff_snd

def HasNativeRetiming (F : ℝ × M → N) (β : N → ℝ) (a b : ℝ) : Prop :=
  ∃ e : M → ℝ ≃ ℝ,
    ∃ Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞,
      (∀ t x, e x t = t + β (F (t, x))) ∧
      (∀ q, Ψ q = sourceEquiv e q) ∧ family F e = F ∘ Ψ.symm ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ (family F e) ∧
      (∀ t x, Injective (mfderiv I J (fun y => family F e (t, y)) x)) ∧
      RegularOn (I := I) (J := J) (family F e) {p | p.2.1 ≠ p.2.2} ∧
      (doublePoints (family F e)).Finite ∧
      doublePoints (family F e) = pairEquiv e '' doublePoints F ∧
      (∀ q, β (F q) = 0 → family F e q = F q) ∧
      (∀ t x, t ∉ Ioo a b → family F e (t, x) = F (t, x)) ∧
      (triplePoints F = ∅ → triplePoints (family F e) = ∅) ∧
      ((∀ q ∈ collisionSources F, Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F q)) →
        ∀ q ∈ collisionSources (family F e),
          Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J (family F e) q)) ∧
      ((∀ p ∈ doublePoints F, HasGlobalProjectedCollisionFiber F p) →
        ∀ p ∈ doublePoints (family F e), HasGlobalProjectedCollisionFiber (family F e) p)

theorem exists_native_target_clock
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (hreg : RegularOn (I := I) (J := J) F {p | p.2.1 ≠ p.2.2})
    (hfinite : (doublePoints F).Finite)
    {β : N → ℝ} (hβ : ContMDiff J 𝓘(ℝ, ℝ) ∞ β)
    (hpos : ∀ x t, 0 < deriv (fun s => s + β (F (s, x))) t)
    {a b : ℝ} (hfix : ∀ t x, t ∉ Ioo a b → β (F (t, x)) = 0) :
    HasNativeRetiming (I := I) (J := J) F β a b := by
  let τ : ℝ × M → ℝ := fun q => q.1 + β (F q)
  have hτ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ τ :=
    contMDiff_fst.add (hβ.comp hF)
  have hτfix : ∀ t x, t ∉ Ioo a b → τ (t, x) = t := by
    intro t x ht
    change t + β (F (t, x)) = t
    rw [hfix t x ht, add_zero]
  let e : M → ℝ ≃ ℝ := fun x => Equiv.ofBijective (fun t => τ (t, x))
    (time_profile_fibre_bijective hτ hpos hτfix x)
  have hclock : ∀ t x, e x t = t + β (F (t, x)) := fun _ _ => rfl
  obtain ⟨Ψ, hΨ⟩ := exists_time_profile_diffeomorph hτ hpos hτfix
  have hΨeq : ∀ q, Ψ q = sourceEquiv e q := fun q => hΨ q
  have hequiv : sourceEquiv e = Ψ.toEquiv := Equiv.ext (fun q => (hΨeq q).symm)
  have hfamily : family F e = F ∘ Ψ.symm := by
    change F ∘ (sourceEquiv e).symm = F ∘ Ψ.symm
    rw [hequiv]
    rfl
  have hnew : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ (family F e) := by
    rw [hfamily]
    exact hF.comp Ψ.symm.contMDiff
  have htrack : NativeFamily.track (family F e) =
      (timeShear β hβ ∘ NativeFamily.track F) ∘ Ψ.symm := by
    funext q
    have hh := hΨ (Ψ.symm q)
    rw [Diffeomorph.apply_symm_apply] at hh
    change q = ((Ψ.symm q).1 + β (F (Ψ.symm q)), (Ψ.symm q).2) at hh
    change (q.1, family F e q) =
      ((Ψ.symm q).1 + β (F (Ψ.symm q)), F (Ψ.symm q))
    rw [hfamily]
    exact Prod.ext (congrArg (fun z : ℝ × M => z.1) hh) rfl
  refine ⟨e, Ψ, hclock, hΨeq, hfamily, hnew,
    spatial_immersion_of_track_diffeomorphs hF hnew hi (timeShear β hβ) Ψ.symm htrack,
    regular_of_track_diffeomorphs hF hnew hreg (timeShear β hβ) Ψ.symm htrack,
    finite_doublePoints hclock hfinite, doublePoints_eq_image hclock,
    (fun _ h => family_fixed_of_clock_zero hclock h),
    (fun t x ht => family_fixed_of_clock_zero hclock (hfix t x ht)),
    triplePoints_eq_empty hclock, ?_, global_projected_collision_fibers hclock⟩
  intro hfull q hq
  rw [collisionSources_eq_image hclock] at hq
  obtain ⟨z, hz, heq⟩ := hq
  have hzq : Ψ z = q := (hΨeq z).trans heq
  have hqz : Ψ.symm q = z := by
    rw [← hzq, Diffeomorph.symm_apply_apply]
  have hfullOld : Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F (Ψ.symm q)) := by
    rw [hqz]
    exact hfull z hz
  have hh := retimed_injective_full_derivative Ψ.symm hF q hfullOld
  have hret : retimedFamily F Ψ.symm = family F e := hfamily.symm
  rw [hret] at hh
  exact hh

theorem exists_radius_native_target_clock
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (hreg : RegularOn (I := I) (J := J) F {p | p.2.1 ≠ p.2.2})
    (hfinite : (doublePoints F).Finite)
    {β : N → ℝ} (hβ : ContMDiff J 𝓘(ℝ, ℝ) ∞ β)
    {a b : ℝ} (hfix : ∀ t x, t ∉ Ioo a b → β (F (t, x)) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, ‖δ‖ < ε →
      HasNativeRetiming (I := I) (J := J) F (fun z => δ * β z) a b := by
  obtain ⟨ε, hε, hpositive⟩ := exists_radius_positive_scalar_clock (hβ.comp hF) hfix
  refine ⟨ε, hε, ?_⟩
  intro δ hδ
  have hβδ : ContMDiff J 𝓘(ℝ, ℝ) ∞ (fun z => δ * β z) := contMDiff_const.mul hβ
  exact exists_native_target_clock hF hi hreg hfinite hβδ
    (hpositive δ hδ) (fun t x ht => by
      change δ * β (F (t, x)) = 0
      rw [hfix t x ht, mul_zero])

end Wikipedia.HopfProblem.OrbitPair.TargetClock
