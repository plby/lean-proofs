import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupMaps
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupConjugationLift
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupConjugationSquare

/-!
# Actual section conjugation is the original fibre action

The lift of a base loop and the original fibre coordinate form a genuine
homotopy square in the diagonal quotient. Its fixed-point trajectory is
the literal section loop. Its endpoint is the original fibre inclusion
composed with inverse-deck transport. This proves the conjugation action
on actual fundamental groups, rather than assuming a semidirect-product
presentation or a matrix action.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F] [ContinuousConstSMul G F]

/-- Conjugation by the actual fixed-point section acts on the actual
fibre fundamental group through the inverse endpoint deck element.
The order agrees with Mathlib's reversed multiplication of loop classes. -/
theorem sectionFundamentalGroupHom_conjugate_fibre
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (c : F) (hc : ∀ g : G, g • c = c) (b : B)
    (β : FundamentalGroup (BaseSpace G B) (baseQuotient G B b))
    (v : FundamentalGroup F c) :
    sectionFundamentalGroupHom c hc b β * fibreFundamentalGroupHom b c v *
        (sectionFundamentalGroupHom c hc b β)⁻¹ =
      fibreFundamentalGroupHom b c
        (fibreActionFundamentalGroupHom c hc (deckTransportHom hq b β) v) := by
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective β
  let g : G := deckTransportHom hq b (.mk γ)
  have hend : (hq.isCoveringMap.monodromy (.mk γ) ⟨b, rfl⟩ : B) = g⁻¹ • b :=
    (deckTransportHom_monodromy hq b (.mk γ)).symm
  let i : C(F, Space G B F) :=
    ⟨fibreInclusion G B F b, fibreInclusion_continuous G B F b⟩
  let a : C(F, F) := ⟨fun f : F => g • f, continuous_const_smul g⟩
  let H : i.Homotopy (i.comp a) := liftedFibreHomotopy (F := F) hq b γ g hend
  have h₁ : (i.comp a) c = i c := congrArg i (hc g)
  let s : FundamentalGroup (Space G B F) (i c) :=
    .mk ((H.evalAt c).cast rfl h₁.symm)
  have hs : s = sectionFundamentalGroupHom c hc b (.mk γ) := by
    change Path.Homotopic.Quotient.mk ((H.evalAt c).cast rfl h₁.symm) =
      Path.Homotopic.Quotient.mk (γ.map (zeroSection_continuous c hc))
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    change quotient G B F (hq.isCoveringMap.liftPath γ b γ.source t, c) =
      zeroSection c hc (γ t)
    have hlift : baseQuotient G B (hq.isCoveringMap.liftPath γ b γ.source t) = γ t :=
      congrFun (hq.isCoveringMap.liftPath_lifts γ b γ.source) t
    exact congrArg (zeroSection c hc) hlift
  have hi (w : FundamentalGroup F c) :
      FundamentalGroup.mapOfEq i rfl w = fibreFundamentalGroupHom b c w := by
    rw [FundamentalGroup.mapOfEq_apply]
    exact Path.Homotopic.Quotient.cast_rfl_rfl _
  have hterminal : FundamentalGroup.mapOfEq (i.comp a) h₁ v =
      fibreFundamentalGroupHom b c (fibreActionFundamentalGroupHom c hc g v) := by
    have hcomp := fundamentalGroup_mapOfEq_comp a i c c (i c) (hc g) rfl v
    rw [hi] at hcomp
    exact hcomp
  have hconj := fundamentalGroup_conjugation_of_homotopy i (i.comp a) H c (i c) rfl h₁ v
  change s * FundamentalGroup.mapOfEq i rfl v * s⁻¹ =
    FundamentalGroup.mapOfEq (i.comp a) h₁ v at hconj
  rw [hs, hi, hterminal] at hconj
  exact hconj

end Wikipedia.HopfProblem.DiagonalQuotient
