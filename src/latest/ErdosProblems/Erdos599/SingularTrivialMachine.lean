/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularExtension

/-!
# Stationary singular target-row machines

This module records the exact situation in which the weak public fields of
`TargetRowMachine` permit a constant-state implementation.  Such an
implementation is legitimate precisely when the source row is already fixed by
the competitor-closing operation.  The result is useful both as a small
constructor and as an audit of the singular interface: reflexivity of forward
extension removes the path-transition obligation, but it does not remove the
competitor fixed-point obligation.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularExtension

universe u

variable {V I : Type u}

/-- A row is stationary for `fixed` when one competitor step leaves every
displayed source set unchanged. -/
def TargetRowStage.IsStationary (G : DWeb V) (fixed : Set G.DPath)
    (S : TargetRowStage G I) : Prop :=
  S.sources = nextTargetSources G fixed S

/-- A stationary row gives a constant-state target-row machine.  No hidden
selection occurs here: every transition displays the same certified row, the
source equation is exactly `stationary`, and forward extension is reflexive. -/
def TargetRowStage.constantMachine
    (G : DWeb V) (fixed : Set G.DPath)
    {initialSources : I → Set V} (S : TargetRowStage G I)
    (initialSources_eq : S.sources = initialSources)
    (stationary : S.IsStationary G fixed) :
    TargetRowMachine G fixed initialSources where
  State := Unit
  row _ := S
  initial := ()
  next _ := ()
  sources_initial := initialSources_eq
  sources_next _ := stationary
  forward_next _ i := G.forwardExtension_refl (S.paths i)

/-- Forgetting the extra certificate of a certified row, a stationary
certified row likewise gives a constant machine. -/
def CertifiedTargetRowStage.constantMachine
    (G : DWeb V) (fixed : Set G.DPath) {rho : I → Cardinal.{u}}
    {initialSources : I → Set V} (S : CertifiedTargetRowStage G I rho)
    (initialSources_eq : S.row.sources = initialSources)
    (stationary : S.row.IsStationary G fixed) :
    TargetRowMachine G fixed initialSources :=
  S.row.constantMachine G fixed initialSources_eq stationary

/-- The corresponding target rows for the singular matrix.  This theorem is
the fully elaborated constant-machine route from a certified initial row to
`TargetRows`; its only additional mathematical premise is the explicit
competitor fixed-point equation. -/
noncomputable def targetRows_of_stationaryCertifiedRow
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (S : CertifiedTargetRowStage G (Index kappa)
      (scale kappa huncountable hsingular))
    (hsources : S.row.sources =
      sourceLayer A₀ kappa hcard huncountable hsingular)
    (hstationary : S.row.IsStationary G fixed) :
    TargetRows G fixed A₀ kappa huncountable hsingular hcard :=
  (S.constantMachine G fixed hsources hstationary).toTargetRows

end SingularExtension
end CardinalInduction
end Erdos599

