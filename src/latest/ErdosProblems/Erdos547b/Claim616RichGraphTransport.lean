/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616

/-!
# Literal graph-equality transport used by rich Claim 6.16 adapters
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616RichAdapter

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616

universe u

/-- Transport a subgraph along literal equality of its ambient graphs. -/
def transportSubgraph
    {K : Type u} {R S : SimpleGraph K} (h : R = S)
    (M : R.Subgraph) : S.Subgraph :=
  h ▸ M

@[simp] theorem transportSubgraph_rfl
    {K : Type u} {R : SimpleGraph K} (M : R.Subgraph) :
    transportSubgraph rfl M = M :=
  rfl

@[simp] theorem matchingSupport_transportSubgraph
    {K : Type u} [Fintype K] [DecidableEq K]
    {R S : SimpleGraph K} (h : R = S) (M : R.Subgraph) :
    matchingSupport (transportSubgraph h M) = matchingSupport M := by
  subst S
  rfl

/-- The part of a matching decomposition used by the coordinate backend,
transported together with its actual root-facing orientation and the two
strict source-degree facts.  Naming both decision procedures makes the
graph equality elimination independent of their implementation. -/
structure CoordinateSourceTransport
    {K : Type u} [Fintype K] [DecidableEq K]
    {R S : SimpleGraph K}
    (dR : DecidableRel R.Adj) (dS : DecidableRel S.Adj)
    (h : R = S)
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    (C67 : @Claim67Certificate K inferInstance inferInstance R dR L miss)
    (degreeA : Finset (MatchingEdge C67.M) → ℝ)
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA)
    (C : Finset K) (sourceDensity : K → K → ℝ) (N : ℝ) (A B : K) where
  targetDegreeA :
    Finset (MatchingEdge
      (transportClaim67Certificate h dR dS C67).M) → ℝ
  target : MatchingDecomposition L O miss
    (transportClaim67Certificate h dR dS C67)
    lowerV1 upperV1 upperV2 mbBound targetDegreeA
  Mout_eq : target.Mout = transportSubgraph h D.Mout
  Mb_eq : target.Mb = transportSubgraph h D.Mb
  V1_eq : target.V1 = D.V1
  V2_eq : target.V2 = D.V2
  certificate_O_eq :
    (transportClaim67Certificate h dR dS C67).O = C67.O
  MoneEdges_card_eq :
    (MatchingDecomposition.MoneEdges target C).card =
      (MatchingDecomposition.MoneEdges D C).card
  mbEdges_card_eq : target.mbEdges.card = D.mbEdges.card
  mbSide : {e : MatchingEdge
    (transportClaim67Certificate h dR dS C67).M //
      e ∈ target.mbEdges} → Fin 2
  V1_adj : ∀ x ∈ target.V1, S.Adj A x
  mb_adj : ∀ e, S.Adj B
    (matchingEdgeEndpoint e.1.1 (mbSide e))
  remaining_pos : 0 < sourceDegree
    (transportClaim67Certificate h dR dS C67).M L sourceDensity N A
    (MatchingDecomposition.MoneEdges target C)
  reserved_pos : 0 < sourceDegree
    (transportClaim67Certificate h dR dS C67).M L sourceDensity N B
    target.mbEdges

/-- Equality transport of the exact coordinate source facts.  There is no
graph isomorphism and no replacement decomposition premise. -/
noncomputable def coordinateSourceTransport
    {K : Type u} [Fintype K] [DecidableEq K]
    {R S : SimpleGraph K}
    (dR : DecidableRel R.Adj) (dS : DecidableRel S.Adj)
    (h : R = S)
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    (C67 : @Claim67Certificate K inferInstance inferInstance R dR L miss)
    (degreeA : Finset (MatchingEdge C67.M) → ℝ)
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA)
    (C : Finset K) (sourceDensity : K → K → ℝ) (N : ℝ) (A B : K)
    (mbSide : {e : MatchingEdge C67.M // e ∈ D.mbEdges} → Fin 2)
    (hV1 : ∀ x ∈ D.V1, R.Adj A x)
    (hMb : ∀ e, R.Adj B (matchingEdgeEndpoint e.1.1 (mbSide e)))
    (hremaining : 0 < sourceDegree C67.M L sourceDensity N A
      (MatchingDecomposition.MoneEdges D C))
    (hreserved : 0 < sourceDegree C67.M L sourceDensity N B D.mbEdges) :
    CoordinateSourceTransport dR dS h C67 degreeA D C sourceDensity N A B := by
  subst S
  have hd : dR = dS := Subsingleton.elim _ _
  subst dS
  simpa [transportClaim67Certificate, changeClaim67Decidable] using
    (show CoordinateSourceTransport dR dR rfl C67 degreeA D C sourceDensity
        N A B from
      { targetDegreeA := degreeA
        target := D
        Mout_eq := rfl
        Mb_eq := rfl
        V1_eq := rfl
        V2_eq := rfl
        certificate_O_eq := rfl
        MoneEdges_card_eq := rfl
        mbEdges_card_eq := rfl
        mbSide := mbSide
        V1_adj := hV1
        mb_adj := hMb
        remaining_pos := hremaining
        reserved_pos := hreserved })

/-- The exact transported data consumed by the current rich indexed-host
constructor.  The target degree function is the literal transported source
degree, not a separately supplied capacity oracle. -/
structure IndexedHostDecompositionTransport
    {K : Type u} [Fintype K] [DecidableEq K]
    {R S : SimpleGraph K}
    (dR : DecidableRel R.Adj) (dS : DecidableRel S.Adj)
    (h : R = S)
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound rhoK : ℕ}
    (C67 : @Claim67Certificate K inferInstance inferInstance R dR L miss)
    (sourceDensity : K → K → ℝ) (N : ℝ) (A : K)
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      (sourceDegree C67.M L sourceDensity N A))
    (eta : ℝ) where
  target : MatchingDecomposition L O miss
    (transportClaim67Certificate h dR dS C67)
    lowerV1 upperV1 upperV2 mbBound
    (sourceDegree (transportClaim67Certificate h dR dS C67).M L
      sourceDensity N A)
  Mout_eq : target.Mout = transportSubgraph h D.Mout
  Mb_eq : target.Mb = transportSubgraph h D.Mb
  V1_eq : target.V1 = D.V1
  V2_eq : target.V2 = D.V2
  certificate_O_eq :
    (transportClaim67Certificate h dR dS C67).O = C67.O
  min_subset_clean : target.minEdges ⊆
    sourceCleanEdges (transportClaim67Certificate h dR dS C67).M L O
      sourceDensity A eta target.mbEdges
  sourceDensityAdj : ∀ x, 0 < sourceDensity A x → S.Adj A x
  crossing : rhoK * target.V2.card + target.V1.card * (9 * rhoK) <
    (S.interedges target.V1 target.V2).card

/-- Equality transport of the matching decomposition and the three facts
needed to build its concrete indexed host. -/
noncomputable def indexedHostDecompositionTransport
    {K : Type u} [Fintype K] [DecidableEq K]
    {R S : SimpleGraph K}
    (dR : DecidableRel R.Adj) (dS : DecidableRel S.Adj)
    (h : R = S)
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound rhoK : ℕ}
    (C67 : @Claim67Certificate K inferInstance inferInstance R dR L miss)
    (sourceDensity : K → K → ℝ) (N : ℝ) (A : K)
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      (sourceDegree C67.M L sourceDensity N A))
    (eta : ℝ)
    (hclean : D.minEdges ⊆
      sourceCleanEdges C67.M L O sourceDensity A eta D.mbEdges)
    (hadj : ∀ x, 0 < sourceDensity A x → R.Adj A x)
    (hcross : rhoK * D.V2.card + D.V1.card * (9 * rhoK) <
      (R.interedges D.V1 D.V2).card) :
    IndexedHostDecompositionTransport (rhoK := rhoK) dR dS h C67
      sourceDensity N A D eta := by
  subst S
  have hd : dR = dS := Subsingleton.elim _ _
  subst dS
  simpa [transportClaim67Certificate, changeClaim67Decidable] using
    (show IndexedHostDecompositionTransport (rhoK := rhoK) dR dR rfl C67
        sourceDensity N A D eta from
      { target := D
        Mout_eq := rfl
        Mb_eq := rfl
        V1_eq := rfl
        V2_eq := rfl
        certificate_O_eq := rfl
        min_subset_clean := hclean
        sourceDensityAdj := hadj
        crossing := hcross })

/-- A transported host decomposition recast to a propositionally equal
target certificate.  This second, certificate-level transport is separated
from graph transport so no concrete graph expression is eliminated. -/
structure IndexedHostCertificateTransport
    {K : Type u} [Fintype K] [DecidableEq K]
    {R S : SimpleGraph K}
    {dR : DecidableRel R.Adj} {dS : DecidableRel S.Adj}
    {h : R = S}
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound rhoK : ℕ}
    {C67 : @Claim67Certificate K inferInstance inferInstance R dR L miss}
    {sourceDensity : K → K → ℝ} {N : ℝ} {A : K}
    {D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      (sourceDegree C67.M L sourceDensity N A)}
    {eta : ℝ}
    (X : IndexedHostDecompositionTransport (rhoK := rhoK) dR dS h C67
      sourceDensity N A D eta)
    (C67host : @Claim67Certificate K inferInstance inferInstance S dS L miss)
    where
  target : MatchingDecomposition L C67host.O miss C67host
    lowerV1 upperV1 upperV2 mbBound
    (sourceDegree C67host.M L sourceDensity N A)
  min_subset_clean : target.minEdges ⊆
    sourceCleanEdges C67host.M L C67host.O sourceDensity A eta target.mbEdges
  sourceDensityAdj : ∀ x, 0 < sourceDensity A x → S.Adj A x
  crossing : rhoK * target.V2.card + target.V1.card * (9 * rhoK) <
    (S.interedges target.V1 target.V2).card
  V1_eq : target.V1 = D.V1
  V2_eq : target.V2 = D.V2
  Mout_eq : target.Mout = transportSubgraph h D.Mout
  Mb_eq : target.Mb = transportSubgraph h D.Mb

/-- Recast the graph-transported record along equality of the target
certificate and its stored source set.  Both right-hand objects are generic
variables here, so the two substitutions are nondependent. -/
noncomputable def indexedHostCertificateTransport
    {K : Type u} [Fintype K] [DecidableEq K]
    {R S : SimpleGraph K}
    {dR : DecidableRel R.Adj} {dS : DecidableRel S.Adj}
    {h : R = S}
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound rhoK : ℕ}
    {C67 : @Claim67Certificate K inferInstance inferInstance R dR L miss}
    {sourceDensity : K → K → ℝ} {N : ℝ} {A : K}
    {D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      (sourceDegree C67.M L sourceDensity N A)}
    {eta : ℝ}
    (X : IndexedHostDecompositionTransport (rhoK := rhoK) dR dS h C67
      sourceDensity N A D eta)
    (C67host : @Claim67Certificate K inferInstance inferInstance S dS L miss)
    (hC67 : transportClaim67Certificate h dR dS C67 = C67host)
    (hO : O = C67host.O) :
    IndexedHostCertificateTransport X C67host := by
  subst C67host
  subst O
  exact
    { target := X.target
      min_subset_clean := X.min_subset_clean
      sourceDensityAdj := X.sourceDensityAdj
      crossing := X.crossing
      V1_eq := X.V1_eq
      V2_eq := X.V2_eq
      Mout_eq := X.Mout_eq
      Mb_eq := X.Mb_eq }

end Erdos547b.ZhaoClaim616RichAdapter
