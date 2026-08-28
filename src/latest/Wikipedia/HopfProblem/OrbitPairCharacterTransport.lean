import Wikipedia.HopfProblem.OrbitPairCharacterPairDomain
import Wikipedia.HopfProblem.OrbitPairLocalTransportLifting

/-!
# Continuous local transport on the actual finite-character circle bundle

Phase alignment descends through the actual open quotient in its
second representative. The resulting transport preserves the target
orbit and is exactly the identity on the diagonal.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] unitCircleMulAction

variable (s : Finset SmoothOrbitCharacter)

def finiteRepresentativeTransport (p : finitePairDomain s) : finiteCharacterDomain s :=
  complexPhase (characterPairing s p.val.1.val p.val.2.val) p.property • p.val.2

theorem finiteRepresentativeTransport_continuous : Continuous (finiteRepresentativeTransport s) := by
  have hp : Continuous (fun p : finitePairDomain s => characterPairing s p.val.1.val p.val.2.val) :=
    (characterPairing_continuous s).comp
      ((continuous_subtype_val.comp continuous_subtype_val.fst).prodMk
        (continuous_subtype_val.comp continuous_subtype_val.snd))
  exact (complexPhase_continuous hp (fun p => p.property)).smul continuous_subtype_val.snd

theorem finiteRepresentativeTransport_projection (p : finitePairDomain s) :
    finiteCharacterProjection s (finiteRepresentativeTransport s p) =
      finiteCharacterProjection s p.val.2 := finiteCharacterProjection_smul s _ _

theorem finiteRepresentativeTransport_eq_of_projection_eq :
    ∀ p q : finitePairDomain s,
      finiteTransportInputProjection s p = finiteTransportInputProjection s q →
        finiteRepresentativeTransport s p = finiteRepresentativeTransport s q := by
  rintro ⟨⟨x, y⟩, hxy⟩ ⟨⟨z, w⟩, hzw⟩ he
  have hxz : x = z := congrArg (fun p : FiniteTransportInput s => p.val.1) he
  subst z
  have hyw : finiteCharacterProjection s y = finiteCharacterProjection s w :=
    congrArg (fun p : FiniteTransportInput s => p.val.2) he
  obtain ⟨u, rfl⟩ := (finiteCharacterProjection_eq_iff s y w).mp hyw
  apply Subtype.ext
  exact characterMatching_right_invariant s u x.val w.val hzw hxy

def finiteTransportLift (z : FiniteTransportInput s) : finitePairDomain s :=
  (finiteTransportInputProjection_surjective s z).choose

theorem finiteTransportLift_projection (z : FiniteTransportInput s) :
    finiteTransportInputProjection s (finiteTransportLift s z) = z :=
  (finiteTransportInputProjection_surjective s z).choose_spec

def finiteTransportMap (z : FiniteTransportInput s) : finiteCharacterDomain s :=
  finiteRepresentativeTransport s (finiteTransportLift s z)

theorem finiteTransportMap_projection (p : finitePairDomain s) :
    finiteTransportMap s (finiteTransportInputProjection s p) = finiteRepresentativeTransport s p :=
  finiteRepresentativeTransport_eq_of_projection_eq s _ _
    (finiteTransportLift_projection s (finiteTransportInputProjection s p))

theorem finiteTransportMap_continuous : Continuous (finiteTransportMap s) := by
  apply (finiteTransportInputProjection_isOpenQuotientMap s).isQuotientMap.continuous_iff.mpr
  have he : finiteTransportMap s ∘ finiteTransportInputProjection s = finiteRepresentativeTransport s :=
    funext (finiteTransportMap_projection s)
  rw [he]
  exact finiteRepresentativeTransport_continuous s

theorem finiteTransportMap_orbit (z : FiniteTransportInput s) :
    finiteCharacterProjection s (finiteTransportMap s z) = z.val.2 := by
  obtain ⟨p, rfl⟩ := finiteTransportInputProjection_surjective s z
  rw [finiteTransportMap_projection]
  exact finiteRepresentativeTransport_projection s p

theorem finiteTransportMap_self (x : finiteCharacterDomain s) :
    finiteTransportMap s ⟨(x, finiteCharacterProjection s x), finiteTransportDomain_diagonal s _⟩ = x := by
  let p : finitePairDomain s := ⟨(x, x), characterPairing_self_ne_zero s x⟩
  change finiteTransportMap s (finiteTransportInputProjection s p) = x
  rw [finiteTransportMap_projection]
  apply Subtype.ext
  exact characterMatching_self s x

/-- Constructed transport on the original circle bundle over the finite character image. -/
def finiteCharacterLocalTransport : LocalTransport (finiteCharacterProjection s) where
  domain := finiteTransportDomain s
  diagonal := finiteTransportDomain_diagonal s
  transport := ⟨finiteTransportMap s, finiteTransportMap_continuous s⟩
  project := finiteTransportMap_orbit s
  self := finiteTransportMap_self s

end Wikipedia.HopfProblem.OrbitPair
