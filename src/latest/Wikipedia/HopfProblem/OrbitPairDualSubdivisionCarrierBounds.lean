import Wikipedia.HopfProblem.OrbitPairSubdivisionDegreeParameters

/-!
# Initial and proper-face carriers in dual subdivision

In a normal dual-subdivision parameter the first face is the full original
simplex. A nondegenerate face chain is strictly decreasing. Consequently,
an operator containing the first vertex keeps the normal carrier, whereas
an operator omitting it has a strictly smaller normalized carrier.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open SubdivisionSupport SubdivisionParameters

theorem dual_full_iff {n k : ℕ} (t : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌) :
    Full (dualLaw k) t ↔ (dualFaceSupport t).finset = Finset.univ := by
  constructor
  · intro ht
    change chainVertexSet (dualFaceSupport t) = Set.univ at ht
    ext i
    simp only [Finset.mem_univ, iff_true]
    have hi : i.down ∈ chainVertexSet (dualFaceSupport t) := by
      rw [ht]
      exact Set.mem_univ _
    exact hi
  · exact chainVertexSet_full (dualFaceSupport t)

theorem dual_full_card {n k : ℕ} (t : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌)
    (ht : Full (dualLaw k) t) : (dualFaceSupport t).finset.card = n + 1 := by
  rw [(dual_full_iff t).mp ht]
  simp only [Finset.card_univ, Fintype.card_ulift, Fintype.card_fin]

theorem dualFaceSupport_degree {n l k : ℕ} (f : ⦋l⦌ ⟶ ⦋k⦌)
    (t : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌) :
    dualFaceSupport ((dualStandard.obj ⦋n⦌).map f.op t) = t.obj (f.toOrderHom 0) := rfl

theorem dual_full_degree_of_zero {n l k : ℕ} (f : ⦋l⦌ ⟶ ⦋k⦌)
    (hf : f.toOrderHom 0 = 0) (t : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌)
    (ht : Full (dualLaw k) t) : Full (dualLaw l) ((dualStandard.obj ⦋n⦌).map f.op t) := by
  change chainVertexSet (t.obj (f.toOrderHom 0)) = Set.univ
  rw [hf]
  exact ht

theorem dual_face_card_lt_of_ne_zero {n k : ℕ} (t : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌)
    (ht : t ∈ (dualStandard.obj ⦋n⦌).nonDegenerate k) (hfull : Full (dualLaw k) t)
    (i : Fin (k + 1)) (hi : i ≠ 0) : (t.obj i).finset.card < n + 1 := by
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono t).mp ht
  have hlt : (t.obj i).finset ⊂ (t.obj 0).finset := hs (Fin.pos_iff_ne_zero.mpr hi)
  have hc := Finset.card_lt_card hlt
  exact hc.trans_eq (dual_full_card t hfull)

theorem dual_support_dim_degree_lt {n l k : ℕ} (f : ⦋l⦌ ⟶ ⦋k⦌)
    (hf : f.toOrderHom 0 ≠ 0) (t : (dualStandard.{u}.obj ⦋n⦌) _⦋k⦌)
    (ht : t ∈ (dualStandard.obj ⦋n⦌).nonDegenerate k) (hfull : Full (dualLaw k) t) :
    (dualFaceSupport ((dualStandard.obj ⦋n⦌).map f.op t)).finset.card - 1 < n := by
  have hc := dual_face_card_lt_of_ne_zero t ht hfull (f.toOrderHom 0) hf
  let F : NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) := t.obj (f.toOrderHom 0)
  have hp : 0 < F.finset.card := F.nonempty.card_pos
  change F.finset.card < n + 1 at hc
  change F.finset.card - 1 < n
  omega

theorem dual_degree_isNormal_of_zero (X : SSet.{u}) {l k : ℕ} (f : ⦋l⦌ ⟶ ⦋k⦌)
    (hf : f.toOrderHom 0 = 0) (p : Parameters dualStandard X k)
    (hp : IsNormal (dualLaw k) X p) :
    IsNormal (dualLaw l) X (degreeParameters dualStandard X f p) :=
  ⟨hp.1, dual_full_degree_of_zero f hf p.2 hp.2⟩

theorem dual_normalize_degree_dim_lt (X : SSet.{u}) {l k : ℕ} (f : ⦋l⦌ ⟶ ⦋k⦌)
    (hf : f.toOrderHom 0 ≠ 0) (p : Parameters dualStandard X k)
    (hp : IsNormal (dualLaw k) X p)
    (ht : p.2 ∈ (dualStandard.obj ⦋p.1.1⦌).nonDegenerate k) :
    (normalize (dualLaw l) (dualFace l) X (degreeParameters dualStandard X f p)).1.1 < p.1.1 := by
  have hle := normalize_dim_le_face dualStandard X (dualLaw l) (dualFace l)
    (degreeParameters dualStandard X f p)
  exact hle.trans_lt (dual_support_dim_degree_lt f hf p.2 ht hp.2)

end Wikipedia.HopfProblem.OrbitPair.Subdivision
