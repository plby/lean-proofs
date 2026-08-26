/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The main theorems on Erdős problem #501: the existential sentence `Erdos501_ex_f` is forced by the
random algebra on `𝔠⁺` coordinates, and a positive answer is relatively consistent with `ZFC`.
-/
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Transfer
import ErdosProblems.Erdos501.Flypitch4.Erdos501.ColRandom

set_option relaxedAutoImplicit true

/-!
# Erdős problem #501: the main theorems

Combining the semantic unfolding of the sentences (`Semantics.lean`), the internal reals `Rdot` of
`V (randomAlgebra ι)` (`InternalReals.lean`) and the recursion of Theorem 3.2 on names
(`Recursion.lean`, `Assembly.lean`, `erdosProperty_Rdot`), we obtain:

* `erdos501_ex_forced : 𝔠⁺ ≤ #ι → ⊤ ⊩[V (randomAlgebra ι)] Erdos501_ex_f` — **adding `𝔠⁺` random
  reals forces "there is a complete ordered field with the Erdős property"**;
* `erdos501_ex_of_random : ⊤ ⊩[V 𝔹_random_succ_continuum] Erdos501_ex_f`, for the concrete index
  set `RandomIndex` of `ColRandom.lean` (`#RandomIndex = 𝔠⁺`);
* `neg_Erdos501_ex_f_unprovable : ¬ (ZFC ⊢ₛ' ∼Erdos501_ex_f)` — **`ZFC` does not refute a positive
  answer to Erdős #501 (first question)** — by Boolean-valued soundness.

and, for the universal form `Erdos501_f` (`∀ R …, COF → Erdős`, the sentence of `Sentence.lean`),
by the internal isomorphism of every internal complete ordered field with `Rdot` and the transport
of the Erdős property along it (unit (F8): `InternalField.lean`, `InternalIso.lean`,
`Transfer.lean`, `erdos501_forced`):

* `erdos501_of_random : ⊤ ⊩[V 𝔹_random_succ_continuum] Erdos501_f` — **adding `𝔠⁺` random reals
  forces the universal sentence**;
* `neg_Erdos501_f_unprovable : ¬ (ZFC ⊢ₛ' ∼Erdos501_f)`.

All of these are proved without `sorry`.

Note that no collapse is needed: the paper's `Col(ω₁, ℝ)` step served to obtain `CH` for the
Δ-system argument at `ω₂`, which the formalization replaces by using `𝔠⁺` random reals directly
(`exists_homogeneous_envelopes`, `Envelopes.lean`).  The paper's two-step forcing notion
`𝔹_col_random` is defined in `ColRandom.lean` for reference only; nothing is proved about it.
-/

open Fol Flypitch bSet
open scoped Flypitch Fol

namespace Flypitch.Erdos501

open RandomForcing

/-! ### The existential form is forced -/

/-- **Adding `𝔠⁺` random reals forces the existence of a complete ordered field with the Erdős
property.**  The witness is the internal reals `Rdot` of `InternalReals.lean`, a complete ordered
field by `completeOrderedField_Rdot`, with the Erdős property by `erdosProperty_Rdot`
(Theorem 3.2 of the paper, run on names). -/
theorem erdos501_ex_forced {ι : Type} (hι : Order.succ Cardinal.continuum ≤ Cardinal.mk ι) :
    ⊤ ⊩[V (randomAlgebra ι)] Erdos501_ex_f :=
  forced_Erdos501_ex_f_of Rdot plusDot timesDot ltDot zeroDot oneDot
    (completeOrderedField_and_erdosProperty_Rdot hι)

/-- The same for the concrete index set `RandomIndex` (`#RandomIndex = 𝔠⁺`) of `ColRandom.lean`. -/
theorem erdos501_ex_of_random : ⊤ ⊩[V 𝔹_random_succ_continuum] Erdos501_ex_f :=
  erdos501_ex_forced mk_RandomIndex.ge

/-- `V 𝔹_random_succ_continuum` is a Boolean-valued model of `ZFC` (the fundamental theorem of
forcing). -/
theorem V_random_models_ZFC : ⊤ ⊩ₜ[V 𝔹_random_succ_continuum] ZFC :=
  bSet_models_ZFC

instance V_random_nonempty : Nonempty (V 𝔹_random_succ_continuum) := ⟨bSet.empty⟩

/-- **Relative consistency of a positive answer to Erdős #501 (first question)**: `ZFC` does not
prove the negation of "there is a complete ordered field with the Erdős property". -/
theorem neg_Erdos501_ex_f_unprovable : ¬ (ZFC ⊢ₛ' (bd_not Erdos501_ex_f : sentence L_ZFC)) := by
  apply unprovable_of_model_neg (V 𝔹_random_succ_continuum) bSet_models_ZFC nontrivial_bot_lt_top
  rw [forced_in_not]
  exact erdos501_ex_of_random

/-! ### The universal form -/

/-- **Adding `𝔠⁺` random reals forces the universal sentence `Erdos501_f`** (every complete ordered
field has the Erdős property): `erdos501_forced` (`Transfer.lean`), for the concrete index set
`RandomIndex`. -/
theorem erdos501_of_random : ⊤ ⊩[V 𝔹_random_succ_continuum] Erdos501_f :=
  erdos501_forced mk_RandomIndex.ge

/-- **Relative consistency of a positive answer to Erdős #501 (first question), universal form**:
`ZFC` does not prove `∼Erdos501_f`. -/
theorem neg_Erdos501_f_unprovable : ¬ (ZFC ⊢ₛ' (bd_not Erdos501_f : sentence L_ZFC)) := by
  apply unprovable_of_model_neg (V 𝔹_random_succ_continuum) bSet_models_ZFC nontrivial_bot_lt_top
  rw [forced_in_not]
  exact erdos501_of_random

end Flypitch.Erdos501
