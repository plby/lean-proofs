import ErdosProblems.Erdos593.TripleSystem.ErdosRado.CanonicalLevelCode
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Pigeonhole

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# CH-free cardinal arithmetic for the canonical Erdos--Rado trace

This module records cardinal bounds supplied by the concrete canonical carrier
and by a coherent trace system.  It does not construct that system or use the
Continuum Hypothesis.  Under explicit endhomogeneity and stopping hypotheses,
the preceding module supplies level-code injectivity and this module completes
the counting argument to obtain a full-height endpoint.
-/

namespace Erdos593.TripleSystem.TriangleHost.ErdosRado

open Cardinal

/-- The canonical trace-height cutoff has cardinality `aleph1`. -/
theorem mk_traceHeight_eq_aleph_one :
    Cardinal.mk TraceHeight.ToType = Cardinal.aleph 1 := by
  rw [mk_traceHeight, Cardinal.succ_aleph0]

/-- Every ordinal strictly below the trace-height cutoff is countable. -/
theorem card_le_aleph0_of_lt_traceHeight {rho : Ordinal.{0}}
    (hrho : rho < TraceHeight) : rho.card <= Cardinal.aleph0 := by
  apply Cardinal.lt_aleph_one_iff.mp
  change rho < (Order.succ (Cardinal.aleph0 : Cardinal)).ord at hrho
  rw [Cardinal.lt_ord] at hrho
  simpa only [Cardinal.succ_aleph0] using! hrho

/-- A natural-number code indexed by a countable ordinal has cardinality at
most the continuum. -/
theorem mk_short_nat_code_le_continuum {rho : Ordinal.{0}}
    (hrho : rho < TraceHeight) :
    Cardinal.mk (rho.ToType -> Nat) <= Cardinal.continuum := by
  rw [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.lift_id,
    Cardinal.mk_toType]
  calc
    Cardinal.aleph0 ^ rho.card <= Cardinal.aleph0 ^ Cardinal.aleph0 :=
      Cardinal.power_le_power_left Cardinal.aleph0_ne_zero
        (card_le_aleph0_of_lt_traceHeight hrho)
    _ = Cardinal.continuum := Cardinal.aleph0_power_aleph0

/-- A fixed trace level is at most continuum-sized once its supplied code is
injective.  The injectivity premise is deliberately not hidden in this bound. -/
theorem mk_level_le_continuum {c : TraceColoring}
    (T : CoherentTraceSystem c) (rho : Ordinal)
    (hrho : rho < TraceHeight) (hcode : T.LevelCodeInjective rho) :
    Cardinal.mk (T.level rho) <= Cardinal.continuum :=
  (Cardinal.mk_le_of_injective hcode).trans
    (mk_short_nat_code_le_continuum hrho)

/-- A union of at most `aleph1` continuum-sized pieces is continuum-sized.
This uses only `aleph1 <= continuum`, not CH. -/
theorem mk_iUnion_le_continuum {alpha iota : Type} (f : iota -> Set alpha)
    (hiota : Cardinal.mk iota <= Cardinal.aleph 1)
    (hpiece : ∀ i, Cardinal.mk (f i) <= Cardinal.continuum) :
    Cardinal.mk (⋃ i, f i) <= Cardinal.continuum := by
  have hsup : (⨆ i, Cardinal.mk (f i)) <= Cardinal.continuum := by
    exact ciSup_le' hpiece
  calc
    Cardinal.mk (⋃ i, f i) <= Cardinal.mk iota * ⨆ i, Cardinal.mk (f i) :=
      Cardinal.mk_iUnion_le f
    _ <= Cardinal.mk iota * Cardinal.continuum :=
      mul_le_mul_right hsup (Cardinal.mk iota)
    _ <= Cardinal.aleph 1 * Cardinal.continuum :=
      mul_le_mul_left hiota _
    _ = Cardinal.continuum := Cardinal.mul_eq_right Cardinal.aleph0_le_continuum
      Cardinal.aleph_one_le_continuum
      (Cardinal.aleph0_pos.trans Cardinal.aleph0_lt_aleph_one).ne'

/-- A stopped coherent endhomogeneous trace system must contain a full-height
endpoint.  Otherwise its short levels cover the carrier but have total size
at most the continuum. -/
theorem exists_height_eq_traceHeight_of_stopped {c : TraceColoring}
    (T : CoherentTraceSystem c) (hend : T.IsEndhomogeneous)
    (hstop : ∀ (rho : Ordinal) (a : T.level rho), rho < TraceHeight →
      ¬ Nonempty (TraceCandidate c (T.levelTracePrefix rho a))) :
    ∃ a : TraceCarrier, T.height a = TraceHeight := by
  by_contra hfull
  push Not at hfull
  have hshort (a : TraceCarrier) : T.height a < TraceHeight :=
    lt_of_le_of_ne (T.height_le a) (hfull a)
  let levels : TraceHeight.ToType -> Set TraceCarrier := fun eta =>
    T.level eta.toOrd
  have hcover : (Set.univ : Set TraceCarrier) ⊆ Set.iUnion levels := by
    intro a _
    let eta : TraceHeight.ToType :=
      Ordinal.ToType.mk ⟨T.height a, hshort a⟩
    apply Set.mem_iUnion.mpr
    refine ⟨eta, ?_⟩
    change T.height a = eta.toOrd
    simp [eta]
  have hunion : Cardinal.mk (Set.iUnion levels) <= Cardinal.continuum := by
    apply mk_iUnion_le_continuum levels
    · exact mk_traceHeight_eq_aleph_one.le
    · intro eta
      have heta : (eta.toOrd : Ordinal) < TraceHeight :=
        Set.mem_Iio.mp eta.toOrd.2
      exact mk_level_le_continuum T eta.toOrd heta
        (T.levelCodeInjective_of_stopped hend hstop eta.toOrd heta)
  have hcarrier : Cardinal.mk TraceCarrier <= Cardinal.continuum := by
    calc
      Cardinal.mk TraceCarrier = Cardinal.mk (Set.univ : Set TraceCarrier) := by simp
      _ <= Cardinal.mk (Set.iUnion levels) :=
        Cardinal.mk_le_mk_of_subset hcover
      _ <= Cardinal.continuum := hunion
  rw [mk_traceCarrier] at hcarrier
  exact (not_lt_of_ge hcarrier) (Order.lt_succ Cardinal.continuum)

/-- The full-height endpoint supplied by counting carries a full
endhomogeneous trace prefix. -/
theorem exists_full_endhomogeneous_of_stopped {c : TraceColoring}
    (T : CoherentTraceSystem c) (hend : T.IsEndhomogeneous)
    (hstop : ∀ (rho : Ordinal) (a : T.level rho), rho < TraceHeight →
      ¬ Nonempty (TraceCandidate c (T.levelTracePrefix rho a))) :
    ∃ (a : TraceCarrier) (p : TracePrefix a),
      p.length = TraceHeight ∧ p.EndhomogeneousTo c := by
  obtain ⟨a, ha⟩ := exists_height_eq_traceHeight_of_stopped T hend hstop
  let aLevel : T.level TraceHeight := ⟨a, ha⟩
  exact ⟨a, T.levelTracePrefix TraceHeight aLevel, rfl,
    T.levelTracePrefix_endhomogeneous hend TraceHeight aLevel⟩

/-- Every natural-valued map on the trace carrier has an `aleph1`-sized fibre.
The conclusion uses the carrier's successor-of-continuum cardinality and the
regularity of `aleph1`; it does not specialize a finite-color theorem. -/
theorem traceCarrier_nat_fiber (f : TraceCarrier -> Nat) :
    ∃ n : Nat, Cardinal.aleph 1 <= Cardinal.mk (f ⁻¹' ({n} : Set Nat)) := by
  refine Cardinal.infinite_pigeonhole_card f (Cardinal.aleph 1) ?_
    Cardinal.aleph0_lt_aleph_one.le ?_
  · calc
      Cardinal.aleph 1 <= Cardinal.continuum := Cardinal.aleph_one_le_continuum
      _ <= Order.succ Cardinal.continuum := Order.le_succ _
      _ = Cardinal.mk TraceCarrier := mk_traceCarrier.symm
  · rw [Cardinal.isRegular_aleph_one.cof_ord, Cardinal.mk_nat]
    exact Cardinal.aleph0_lt_aleph_one

end Erdos593.TripleSystem.TriangleHost.ErdosRado
