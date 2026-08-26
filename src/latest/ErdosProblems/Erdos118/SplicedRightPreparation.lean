import ErdosProblems.Erdos118.RankedRightPreparation

/-! Retain the full spliced root geometry while decoding the saved
right-target root response at the localized lower body. -/

namespace Erdos118.SplicedRightPreparation

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open AlignedRightPreparation (RootCertificate)

theorem at_localized {H K : Set ℕ} (hKH : K ⊆ H) {B C : SimpleGraph G}
    (X : Pending) (I : RootCertificate H B X)
    {P : Pending} {k v r d : ℕ} {A : RootResponses.Setup k}
    (Z : StrictLocalization.Prepared K C P A v d)
    (R : SplicedRootReserve.Reserve H I.bound k I.size v r A.stem)
    (hd : I.bound ≤ d) (hA : ∀ x ∈ A.stem.ordinary, x ∈ H ∧ I.bound < x) :
    ∃ R' : SplicedRootReserve.Reserve H I.bound k I.size v r Z.body.stem,
      R'.labels = R.labels ∧
        Nonempty (RankedRightPreparation.Target I Z.body (RootReplayReserve.ofSpliced R')) := by
  have hext := (SkippedCuts.run_extensions Z.run).2
  have hroot : Z.body.stem.root = A.stem.root :=
    (List.cons_prefix_cons.mp hext.ordinary).1.symm
  let R' := R.move Z.body.stem hroot Z.bodyRoot
  have hf : ∀ x ∈ Z.body.stem.ordinary, x ∈ H ∧ I.bound < x := by
    obtain ⟨u, w, _, hw, _, hwf⟩ := Z.fresh
    intro x hx
    change x ∈ State.ordinary (.body Z.body) at hx
    rw [hw] at hx
    exact (List.mem_append.mp hx).elim (hA x)
      (fun hx ↦ ⟨hKH (hwf x hx).1, hd.trans_lt (hwf x hx).2⟩)
  exact ⟨R', rfl, RankedRightPreparation.at_shared B X I Z.body
    (RootReplayReserve.ofSpliced R') Z.bodyRank hf⟩

end Erdos118.SplicedRightPreparation
