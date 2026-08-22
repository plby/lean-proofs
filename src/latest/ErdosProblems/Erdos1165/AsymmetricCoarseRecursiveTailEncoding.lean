/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseRightProfilePrefix

/-!
# Canonical recursive encodings of successful coarse tails

Every successful coarse return tuple determines a constrained profile, its
weak-composition genealogy, all supported top-level endpoints, and one
literal recursive code at every bridge coordinate.  The assembled recursive
word recovers the original coarse bridge, so this encoding is injective.

This is the countable reindexing needed before the recursive profile row can
be summed: it replaces a source-defined family of bridge words by the
ordinary code spaces whose exact masses are the recursive kernels.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricCoarseRecursiveTailEncoding

open AnnularLiteralNestedProfileTailUpper
open AnnularOffspringKernelRadial AnnularProfileClocks
open AnnularProfileLiteralAtoms
open AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileCodeAssembly AnnularRecursiveProfileShape
open AnnularRecursiveProfileEndpointTail
open AnnularRecursiveProfileSourceSegment
open AsymmetricCoarseCompletionCode AsymmetricCoarseRecursiveSourceCode
open AsymmetricCoarseRightProfilePrefix
open AsymmetricCoarseSuccessfulTailAtoms
open AppendixFirstMoment MarkedBridgeFactorization ProfileGapChain
open ProfileListExponent ProfileSmallBall ProfileWeightUpper ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Complete canonical recursive data carried by one successful tail over a
fixed coarse completion code. -/
structure CoarseRecursiveTailEncoding
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) where
  profile : Profile n
  constrained : IsConstrainedProfile profileDelta profile
  count_eq : profileAtScale profile (k + 1) = code.1.returnCount
  chain : GapChain
    (code.1.returnCount :: (profileSegmentValues profile (k + 1)).tail)
  entrance : Fin code.1.returnCount →
    ProfileCycleMiddlePoint n (k + 1) y
  endpoint : Fin code.1.returnCount →
    ProfileCycleOuterPoint n (k + 1) y
  entrance_eq : ∀ j, (entrance j).1 = code.1.skeleton.2.1 j
  endpoint_eq : ∀ j, (endpoint j).1 = code.1.skeleton.2.2 j
  fits : ∀ j, profileRefinementTreeFits n (k + 1)
    (profileRefinementTrees code.1.returnCount
      (profileSegmentValues profile (k + 1)).tail chain j)
  gapCode : ∀ j, RecursiveProfileGapCode n (k + 1) y
    (profileRefinementTrees code.1.returnCount
      (profileSegmentValues profile (k + 1)).tail chain j)
    (entrance j) (endpoint j)

/-- The assembled stopped word at one coordinate of an encoding. -/
def CoarseRecursiveTailEncoding.bridgeWord
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (encoding : CoarseRecursiveTailEncoding code)
    (j : Fin code.1.returnCount) : StoppedWord :=
  (recursiveProfileGapBoundaryExitWordCode n (k + 1) y hn (by omega)
    (profileRefinementTrees code.1.returnCount
      (profileSegmentValues encoding.profile (k + 1)).tail
      encoding.chain j)
    (encoding.fits j) (encoding.entrance j) (encoding.endpoint j)
    (encoding.gapCode j)).1

/-- Canonical encoding extracted from an actual successful coarse tuple. -/
def encodeSuccessfulCoarseTail
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    CoarseRecursiveTailEncoding code where
  profile := coarseSuccessfulProfile code tail
  constrained := internalProfile_isConstrained tail.2.2
  count_eq := by
    exact (coarseSuccessfulReturnCount_eq_profileAtScale
      hkTwo code tail).symm
  chain := coarseSuccessfulGapChain hn hkTwo hdelta code tail
  entrance := coarseSuccessfulRecursiveEntrance
    hn hkTwo hdelta code tail
  endpoint := coarseSuccessfulRecursiveEndpoint
    hn hkTwo hdelta code tail
  entrance_eq := coarseSuccessfulRecursiveEntrance_eq_skeleton
    hn hkTwo hdelta code tail
  endpoint_eq := coarseSuccessfulRecursiveEndpoint_eq_skeleton
    hn hkTwo hdelta code tail
  fits := coarseSuccessfulCanonicalRecursiveTree_fits
    hn hkTwo hdelta code tail
  gapCode := coarseSuccessfulCanonicalRecursiveCode
    hn hkTwo hdelta code tail

/-- Decoding an encoded coordinate recovers its literal source bridge. -/
theorem bridgeWord_encodeSuccessfulCoarseTail
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    (encodeSuccessfulCoarseTail hn hkTwo hdelta code tail).bridgeWord
        hn hkTwo j =
      (tail.1 j).1.1 := by
  exact coarseSuccessfulCanonicalRecursiveBoundaryCode_eq_bridge
    hn hkTwo hdelta code tail j

/-- The canonical recursive encoding loses no successful coarse tuple. -/
theorem encodeSuccessfulCoarseTail_injective
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    Function.Injective (encodeSuccessfulCoarseTail
      hn hkTwo hdelta code) := by
  intro left right hencoding
  apply Subtype.ext
  funext j
  apply Subtype.ext
  apply Subtype.ext
  have hwords := congrArg
    (fun encoding : CoarseRecursiveTailEncoding code ↦
      encoding.bridgeWord hn hkTwo j) hencoding
  rw [bridgeWord_encodeSuccessfulCoarseTail
      hn hkTwo hdelta code left j,
    bridgeWord_encodeSuccessfulCoarseTail
      hn hkTwo hdelta code right j] at hwords
  exact hwords

/-- Recursive product mass attached to a canonical tail encoding. -/
def CoarseRecursiveTailEncoding.mass
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    (encoding : CoarseRecursiveTailEncoding code) : ℝ≥0∞ :=
  ∏ j, recursiveProfileGapCodeMass n (k + 1) y
    (profileRefinementTrees code.1.returnCount
      (profileSegmentValues encoding.profile (k + 1)).tail
      encoding.chain j)
    (encoding.entrance j) (encoding.endpoint j) (encoding.gapCode j)

/-- On source encodings, recursive product mass is literally the product of
the original stopped bridge masses. -/
theorem mass_encodeSuccessfulCoarseTail
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    (encodeSuccessfulCoarseTail hn hkTwo hdelta code tail).mass =
      ∏ j, stoppedWordMass (tail.1 j).1.1 := by
  apply Finset.prod_congr rfl
  intro j _
  exact coarseSuccessfulCanonicalRecursiveCodeMass_eq_bridge
    hn hkTwo hdelta code tail j

/-- Proof-free ambient key for a recursive encoding.  The endpoint is left
unrestricted so that its finite sum is exactly the endpoint-retaining
recursive row; the entrance remains tied to the retained coarse skeleton. -/
def CoarseRecursiveTailKey
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :=
  Σ profile : {m : Profile n //
      IsConstrainedProfile profileDelta m ∧
        profileAtScale m (k + 1) = code.1.returnCount},
    Σ chain : GapChain
        (code.1.returnCount :: (profileSegmentValues profile.1 (k + 1)).tail),
      Σ entrance : {e : Fin code.1.returnCount →
          ProfileCycleMiddlePoint n (k + 1) y //
          ∀ j, (e j).1 = code.1.skeleton.2.1 j},
        Σ endpoint : Fin code.1.returnCount →
            ProfileCycleOuterPoint n (k + 1) y,
          ∀ j, RecursiveProfileGapCode n (k + 1) y
            (profileRefinementTrees code.1.returnCount
              (profileSegmentValues profile.1 (k + 1)).tail chain j)
            (entrance.1 j) (endpoint j)

/-- Forget only proof fields and the endpoint-equality restriction from a
canonical recursive encoding. -/
def CoarseRecursiveTailEncoding.toKey
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    (encoding : CoarseRecursiveTailEncoding code) :
    CoarseRecursiveTailKey code :=
  ⟨⟨encoding.profile, encoding.constrained, encoding.count_eq⟩,
    encoding.chain, ⟨encoding.entrance, encoding.entrance_eq⟩,
    encoding.endpoint, encoding.gapCode⟩

/-- Product mass on the proof-free ambient key. -/
def CoarseRecursiveTailKey.mass
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    (key : CoarseRecursiveTailKey code) : ℝ≥0∞ :=
  ∏ j, recursiveProfileGapCodeMass n (k + 1) y
    (profileRefinementTrees code.1.returnCount
      (profileSegmentValues key.1.1 (k + 1)).tail key.2.1 j)
    (key.2.2.1.1 j) (key.2.2.2.1 j) (key.2.2.2.2 j)

@[simp] theorem toKey_mass
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    (encoding : CoarseRecursiveTailEncoding code) :
    encoding.toKey.mass = encoding.mass := by
  rfl

/-- The ambient key retains every data field of the encoding; only
proof-irrelevant certificates were erased. -/
theorem CoarseRecursiveTailEncoding.toKey_injective
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)} :
    Function.Injective
      (CoarseRecursiveTailEncoding.toKey
        (code := code)) := by
  intro left right h
  cases left
  cases right
  cases h
  rfl

/-- Reindexing by the proof-free ambient key can only enlarge the recursive
mass row. -/
theorem tsum_recursiveEncodingMass_le_keyMass
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    (∑' encoding : CoarseRecursiveTailEncoding code, encoding.mass) ≤
      ∑' key : CoarseRecursiveTailKey code, key.mass := by
  simpa only [toKey_mass] using
    ENNReal.tsum_comp_le_tsum_of_injective
      (CoarseRecursiveTailEncoding.toKey_injective (code := code))
      CoarseRecursiveTailKey.mass

private theorem tsum_pi_prod
    {q : ℕ} {Code : Fin q → Type*} [∀ j, Countable (Code j)]
    (weight : (j : Fin q) → Code j → ℝ≥0∞) :
    (∑' code : (j : Fin q) → Code j,
        ∏ j, weight j (code j)) =
      ∏ j, ∑' value, weight j value := by
  classical
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        (∑' code : (j : Fin (q + 1)) → Code j,
            ∏ j, weight j (code j)) =
            ∑' pair : Code 0 × ((j : Fin q) → Code j.succ),
              ∏ j, weight j ((Fin.consEquiv Code) pair j) := by
                exact (Equiv.tsum_eq (Fin.consEquiv Code)
                  (fun code ↦ ∏ j, weight j (code j))).symm
        _ = ∑' pair : Code 0 × ((j : Fin q) → Code j.succ),
              weight 0 pair.1 * ∏ j, weight j.succ (pair.2 j) := by
                apply tsum_congr
                intro pair
                rw [Fin.prod_univ_succ]
                simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
        _ = ∑' head : Code 0, ∑' tail : (j : Fin q) → Code j.succ,
              weight 0 head * ∏ j, weight j.succ (tail j) :=
                @ENNReal.tsum_prod (Code 0)
                  ((j : Fin q) → Code j.succ)
                  (fun head tail ↦
                    weight 0 head * ∏ j, weight j.succ (tail j))
        _ = ∑' head : Code 0, weight 0 head *
              ∑' tail : (j : Fin q) → Code j.succ,
                ∏ j, weight j.succ (tail j) := by
                  congr 1
                  funext head
                  exact ENNReal.tsum_mul_left
        _ = ∑' head : Code 0, weight 0 head *
              ∏ j : Fin q, ∑' value, weight j.succ value := by
                rw [ih (Code := fun j : Fin q ↦ Code j.succ)
                  (fun j value ↦ weight j.succ value)]
        _ = (∑' head : Code 0, weight 0 head) *
              ∏ j : Fin q, ∑' value, weight j.succ value :=
                ENNReal.tsum_mul_right
        _ = ∏ j : Fin (q + 1), ∑' value, weight j value := by
              rw [Fin.prod_univ_succ]

/-- Summing the proof-free keys is exactly the endpoint-retaining recursive
row, with the unique retained entrance represented as a finite subtype. -/
theorem tsum_keyMass_eq_endpointRows
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    (∑' key : CoarseRecursiveTailKey code, key.mass) =
      ∑' profile : {m : Profile n //
          IsConstrainedProfile profileDelta m ∧
            profileAtScale m (k + 1) = code.1.returnCount},
        ∑ entrance : {e : Fin code.1.returnCount →
            ProfileCycleMiddlePoint n (k + 1) y //
            ∀ j, (e j).1 = code.1.skeleton.2.1 j},
          ∑ endpoint : Fin code.1.returnCount →
              ProfileCycleOuterPoint n (k + 1) y,
            recursiveProfileEndpointRow n (k + 1) y
              code.1.returnCount
              (profileSegmentValues profile.1 (k + 1)).tail
              entrance.1 endpoint := by
  classical
  unfold CoarseRecursiveTailKey CoarseRecursiveTailKey.mass
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro profile
  simp_rw [ENNReal.tsum_sigma']
  simp_rw [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro entrance _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro endpoint _
  unfold recursiveProfileEndpointRow
  apply Finset.sum_congr rfl
  intro chain _
  letI (j : Fin code.1.returnCount) : Countable
      (RecursiveProfileGapCode n (k + 1) y
        (profileRefinementTrees code.1.returnCount
          (profileSegmentValues profile.1 (k + 1)).tail chain j)
        (entrance.1 j) (endpoint j)) :=
    recursiveProfileGapCodeCountable n (k + 1) y
      (profileRefinementTrees code.1.returnCount
        (profileSegmentValues profile.1 (k + 1)).tail chain j)
      (entrance.1 j) (endpoint j)
  rw [tsum_pi_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact tsum_recursiveProfileGapCodeMass n (k + 1) y
    (profileRefinementTrees code.1.returnCount
      (profileSegmentValues profile.1 (k + 1)).tail chain j)
    (entrance.1 j) (endpoint j)

/-- Proof-free recursive key restricted to the unique right-hand profile
prefix retained by the coarse code. -/
def CoarseRecursiveFixedPrefixKey
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :=
  Σ profile : {m : Profile n //
      IsConstrainedProfile profileDelta m ∧
        profileAtScale m (k + 1) = code.1.returnCount ∧
        profilePrefix hkTwo hk m =
          retainedYProfilePrefix hn hkTwo hdelta code},
    Σ chain : GapChain
        (code.1.returnCount :: (profileSegmentValues profile.1 (k + 1)).tail),
      Σ entrance : {e : Fin code.1.returnCount →
          ProfileCycleMiddlePoint n (k + 1) y //
          ∀ j, (e j).1 = code.1.skeleton.2.1 j},
        Σ endpoint : Fin code.1.returnCount →
            ProfileCycleOuterPoint n (k + 1) y,
          ∀ j, RecursiveProfileGapCode n (k + 1) y
            (profileRefinementTrees code.1.returnCount
              (profileSegmentValues profile.1 (k + 1)).tail chain j)
            (entrance.1 j) (endpoint j)

/-- Product mass on the fixed-prefix recursive key. -/
def CoarseRecursiveFixedPrefixKey.mass
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {hn : 2 ≤ n} {hkTwo : 2 ≤ k + 1}
    {hdelta : profileDelta ≤ 1}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    (key : CoarseRecursiveFixedPrefixKey hn hkTwo hdelta code) : ℝ≥0∞ :=
  ∏ j, recursiveProfileGapCodeMass n (k + 1) y
    (profileRefinementTrees code.1.returnCount
      (profileSegmentValues key.1.1 (k + 1)).tail key.2.1 j)
    (key.2.2.1.1 j) (key.2.2.2.1 j) (key.2.2.2.2 j)

/-- Forget the fixed-prefix certificate while retaining every computational
field of the recursive key. -/
def CoarseRecursiveFixedPrefixKey.toAmbient
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {hn : 2 ≤ n} {hkTwo : 2 ≤ k + 1}
    {hdelta : profileDelta ≤ 1}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    (key : CoarseRecursiveFixedPrefixKey hn hkTwo hdelta code) :
    CoarseRecursiveTailKey code :=
  ⟨⟨key.1.1, key.1.2.1, key.1.2.2.1⟩,
    key.2.1, key.2.2.1, key.2.2.2.1, key.2.2.2.2⟩

theorem CoarseRecursiveFixedPrefixKey.toAmbient_injective
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {hn : 2 ≤ n} {hkTwo : 2 ≤ k + 1}
    {hdelta : profileDelta ≤ 1}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)} :
    Function.Injective
      (CoarseRecursiveFixedPrefixKey.toAmbient
        (hn := hn) (hkTwo := hkTwo) (hdelta := hdelta) (code := code)) := by
  intro left right h
  apply Sigma.ext
  · apply Subtype.ext
    have hp : left.1.1 = right.1.1 :=
      congrArg (fun p ↦ p.1) (Sigma.ext_iff.mp h).1
    exact hp
  · exact (Sigma.ext_iff.mp h).2

/-- Canonical fixed-prefix key extracted directly from a successful coarse
tail. -/
def fixedPrefixKeyOfSuccessfulTail
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    CoarseRecursiveFixedPrefixKey hn hkTwo hdelta code :=
  let encoding := encodeSuccessfulCoarseTail hn hkTwo hdelta code tail
  ⟨⟨encoding.profile, encoding.constrained, encoding.count_eq,
      profilePrefix_coarseSuccessfulProfile_eq_retained
        hn hkTwo hdelta code tail⟩,
    encoding.chain, ⟨encoding.entrance, encoding.entrance_eq⟩,
    encoding.endpoint, encoding.gapCode⟩

@[simp] theorem mass_fixedPrefixKeyOfSuccessfulTail
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    (fixedPrefixKeyOfSuccessfulTail hn hkTwo hdelta code tail).mass =
      ∏ j, stoppedWordMass (tail.1 j).1.1 := by
  exact mass_encodeSuccessfulCoarseTail hn hkTwo hdelta code tail

/-- The fixed-prefix key still retains all data needed to decode the source
tail. -/
theorem fixedPrefixKeyOfSuccessfulTail_injective
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    Function.Injective
      (fixedPrefixKeyOfSuccessfulTail hn hkTwo hdelta code) := by
  intro left right hkey
  apply encodeSuccessfulCoarseTail_injective hn hkTwo hdelta code
  apply CoarseRecursiveTailEncoding.toKey_injective
  have hamb := congrArg
    (CoarseRecursiveFixedPrefixKey.toAmbient
      (hn := hn) (hkTwo := hkTwo) (hdelta := hdelta) (code := code)) hkey
  exact hamb

/-- The successful bridge-product sum injects directly into the exact
fixed-prefix recursive row. -/
theorem tsum_successfulBridgeMass_le_fixedPrefixKeyMass
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    (∑' tail : CoarseSuccessfulReturnTuple code,
        ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
      ∑' key : CoarseRecursiveFixedPrefixKey hn hkTwo hdelta code,
        key.mass := by
  simpa only [mass_fixedPrefixKeyOfSuccessfulTail
      hn hkTwo hdelta code] using
    ENNReal.tsum_comp_le_tsum_of_injective
      (fixedPrefixKeyOfSuccessfulTail_injective hn hkTwo hdelta code)
      CoarseRecursiveFixedPrefixKey.mass

/-- Tonelli expansion of the fixed-prefix keys into the endpoint-retaining
recursive profile rows. -/
theorem tsum_fixedPrefixKeyMass_eq_endpointRows
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    (∑' key : CoarseRecursiveFixedPrefixKey hn hkTwo hdelta code,
        key.mass) =
      ∑' profile : {m : Profile n //
          IsConstrainedProfile profileDelta m ∧
            profileAtScale m (k + 1) = code.1.returnCount ∧
            profilePrefix hkTwo hk m =
              retainedYProfilePrefix hn hkTwo hdelta code},
        ∑ entrance : {e : Fin code.1.returnCount →
            ProfileCycleMiddlePoint n (k + 1) y //
            ∀ j, (e j).1 = code.1.skeleton.2.1 j},
          ∑ endpoint : Fin code.1.returnCount →
              ProfileCycleOuterPoint n (k + 1) y,
            recursiveProfileEndpointRow n (k + 1) y
              code.1.returnCount
              (profileSegmentValues profile.1 (k + 1)).tail
              entrance.1 endpoint := by
  classical
  unfold CoarseRecursiveFixedPrefixKey CoarseRecursiveFixedPrefixKey.mass
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro profile
  simp_rw [ENNReal.tsum_sigma']
  simp_rw [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro entrance _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro endpoint _
  unfold recursiveProfileEndpointRow
  apply Finset.sum_congr rfl
  intro chain _
  letI (j : Fin code.1.returnCount) : Countable
      (RecursiveProfileGapCode n (k + 1) y
        (profileRefinementTrees code.1.returnCount
          (profileSegmentValues profile.1 (k + 1)).tail chain j)
        (entrance.1 j) (endpoint j)) :=
    recursiveProfileGapCodeCountable n (k + 1) y
      (profileRefinementTrees code.1.returnCount
        (profileSegmentValues profile.1 (k + 1)).tail chain j)
      (entrance.1 j) (endpoint j)
  rw [tsum_pi_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact tsum_recursiveProfileGapCodeMass n (k + 1) y
    (profileRefinementTrees code.1.returnCount
      (profileSegmentValues profile.1 (k + 1)).tail chain j)
    (entrance.1 j) (endpoint j)

/-- Injective reindexing bounds the source-defined successful bridge sum by
the complete canonical recursive encoding row. -/
theorem tsum_successfulBridgeMass_le_recursiveEncodingMass
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)) :
    (∑' tail : CoarseSuccessfulReturnTuple code,
        ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
      ∑' encoding : CoarseRecursiveTailEncoding code, encoding.mass := by
  simpa only [mass_encodeSuccessfulCoarseTail hn hkTwo hdelta code] using
    ENNReal.tsum_comp_le_tsum_of_injective
      (encodeSuccessfulCoarseTail_injective hn hkTwo hdelta code)
      CoarseRecursiveTailEncoding.mass

end

end Erdos1165.AsymmetricCoarseRecursiveTailEncoding
