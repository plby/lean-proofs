import ErdosProblems.Erdos577.PathMasks
import ErdosProblems.Erdos577.FiniteExchange

/-! Explicit positive witnesses for the eight-vertex path exchange.
Every displayed finite graph fact is checked by the Lean kernel.
-/

namespace Erdos577.PathExchange

open Finset

private theorem witness_0 : LocalExchange (graph 282) univ := by
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_1 : LocalExchange (graph 300) univ := by
  refine ⟨{1, 2, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_2 : LocalExchange (graph 390) univ := by
  refine ⟨{1, 2, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_3 : LocalExchange (graph 540) univ := by
  refine ⟨{1, 2, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_4 : LocalExchange (graph 549) univ := by
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_5 : LocalExchange (graph 585) univ := by
  refine ⟨{1, 2, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_6 : LocalExchange (graph 840) univ := by
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_7 : LocalExchange (graph 900) univ := by
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_8 : LocalExchange (graph 1065) univ := by
  refine ⟨{1, 2, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_9 : LocalExchange (graph 1098) univ := by
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_10 : LocalExchange (graph 1155) univ := by
  refine ⟨{1, 2, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_11 : LocalExchange (graph 1314) univ := by
  refine ⟨{2, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_12 : LocalExchange (graph 1416) univ := by
  refine ⟨{2, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_13 : LocalExchange (graph 1560) univ := by
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_14 : LocalExchange (graph 1665) univ := by
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_15 : LocalExchange (graph 2070) univ := by
  refine ⟨{1, 2, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_16 : LocalExchange (graph 2115) univ := by
  refine ⟨{1, 2, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_17 : LocalExchange (graph 2181) univ := by
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_18 : LocalExchange (graph 2340) univ := by
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_19 : LocalExchange (graph 2370) univ := by
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_20 : LocalExchange (graph 2577) univ := by
  refine ⟨{2, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_21 : LocalExchange (graph 2628) univ := by
  refine ⟨{2, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_22 : LocalExchange (graph 3090) univ := by
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_23 : LocalExchange (graph 3105) univ := by
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_24 : LocalExchange (graph 4118) univ := by
  refine ⟨{1, 2, 3, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_25 : LocalExchange (graph 4122) univ := by
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_26 : LocalExchange (graph 4124) univ := by
  refine ⟨{1, 2, 3, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_27 : LocalExchange (graph 4362) univ := by
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_28 : LocalExchange (graph 4388) univ := by
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_29 : LocalExchange (graph 4418) univ := by
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_30 : LocalExchange (graph 4424) univ := by
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_31 : LocalExchange (graph 4484) univ := by
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_32 : LocalExchange (graph 4512) univ := by
  refine ⟨{1, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_33 : LocalExchange (graph 4620) univ := by
  refine ⟨{2, 3, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_34 : LocalExchange (graph 4676) univ := by
  refine ⟨{2, 3, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_35 : LocalExchange (graph 4680) univ := by
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_36 : LocalExchange (graph 4740) univ := by
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_37 : LocalExchange (graph 4744) univ := by
  refine ⟨{2, 3, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_38 : LocalExchange (graph 4800) univ := by
  refine ⟨{2, 3, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_39 : LocalExchange (graph 6150) univ := by
  refine ⟨{2, 3, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_40 : LocalExchange (graph 6178) univ := by
  refine ⟨{2, 3, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_41 : LocalExchange (graph 6180) univ := by
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_42 : LocalExchange (graph 6210) univ := by
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_43 : LocalExchange (graph 6212) univ := by
  refine ⟨{2, 3, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_44 : LocalExchange (graph 6240) univ := by
  refine ⟨{2, 3, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_45 : LocalExchange (graph 8229) univ := by
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_46 : LocalExchange (graph 8233) univ := by
  refine ⟨{1, 2, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_47 : LocalExchange (graph 8236) univ := by
  refine ⟨{1, 2, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_48 : LocalExchange (graph 8460) univ := by
  refine ⟨{2, 3, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_49 : LocalExchange (graph 8516) univ := by
  refine ⟨{2, 3, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_50 : LocalExchange (graph 8520) univ := by
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_51 : LocalExchange (graph 8580) univ := by
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_52 : LocalExchange (graph 8584) univ := by
  refine ⟨{2, 3, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_53 : LocalExchange (graph 8640) univ := by
  refine ⟨{2, 3, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_54 : LocalExchange (graph 8709) univ := by
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_55 : LocalExchange (graph 8728) univ := by
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_56 : LocalExchange (graph 8776) univ := by
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_57 : LocalExchange (graph 8784) univ := by
  refine ⟨{1, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_58 : LocalExchange (graph 8833) univ := by
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_59 : LocalExchange (graph 8836) univ := by
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_60 : LocalExchange (graph 9225) univ := by
  refine ⟨{2, 3, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_61 : LocalExchange (graph 9233) univ := by
  refine ⟨{2, 3, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_62 : LocalExchange (graph 9240) univ := by
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_63 : LocalExchange (graph 9345) univ := by
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_64 : LocalExchange (graph 9352) univ := by
  refine ⟨{2, 3, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_65 : LocalExchange (graph 9360) univ := by
  refine ⟨{2, 3, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_66 : LocalExchange (graph 12360) univ := by
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_67 : LocalExchange (graph 12420) univ := by
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_68 : LocalExchange (graph 13316) univ := by
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_69 : LocalExchange (graph 13440) univ := by
  refine ⟨{1, 2, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_70 : LocalExchange (graph 14344) univ := by
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_71 : LocalExchange (graph 14400) univ := by
  refine ⟨{1, 2, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_72 : LocalExchange (graph 16451) univ := by
  refine ⟨{1, 2, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_73 : LocalExchange (graph 16457) univ := by
  refine ⟨{1, 2, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_74 : LocalExchange (graph 16458) univ := by
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_75 : LocalExchange (graph 16905) univ := by
  refine ⟨{2, 3, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_76 : LocalExchange (graph 16913) univ := by
  refine ⟨{2, 3, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_77 : LocalExchange (graph 16920) univ := by
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_78 : LocalExchange (graph 17025) univ := by
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_79 : LocalExchange (graph 17032) univ := by
  refine ⟨{2, 3, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_80 : LocalExchange (graph 17040) univ := by
  refine ⟨{2, 3, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_81 : LocalExchange (graph 17418) univ := by
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_82 : LocalExchange (graph 17426) univ := by
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_83 : LocalExchange (graph 17432) univ := by
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_84 : LocalExchange (graph 17441) univ := by
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_85 : LocalExchange (graph 17537) univ := by
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_86 : LocalExchange (graph 17568) univ := by
  refine ⟨{1, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_87 : LocalExchange (graph 18435) univ := by
  refine ⟨{2, 3, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_88 : LocalExchange (graph 18449) univ := by
  refine ⟨{2, 3, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_89 : LocalExchange (graph 18450) univ := by
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_90 : LocalExchange (graph 18465) univ := by
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_91 : LocalExchange (graph 18466) univ := by
  refine ⟨{2, 3, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_92 : LocalExchange (graph 18480) univ := by
  refine ⟨{2, 3, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_93 : LocalExchange (graph 20514) univ := by
  refine ⟨{3, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_94 : LocalExchange (graph 20616) univ := by
  refine ⟨{3, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_95 : LocalExchange (graph 20994) univ := by
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_96 : LocalExchange (graph 21024) univ := by
  refine ⟨{3, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_97 : LocalExchange (graph 22536) univ := by
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_98 : LocalExchange (graph 22656) univ := by
  refine ⟨{3, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_99 : LocalExchange (graph 24600) univ := by
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_100 : LocalExchange (graph 24705) univ := by
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_101 : LocalExchange (graph 24833) univ := by
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_102 : LocalExchange (graph 24960) univ := by
  refine ⟨{1, 2, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_103 : LocalExchange (graph 26632) univ := by
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_104 : LocalExchange (graph 26640) univ := by
  refine ⟨{1, 2, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_105 : LocalExchange (graph 32899) univ := by
  refine ⟨{1, 2, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_106 : LocalExchange (graph 32901) univ := by
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_107 : LocalExchange (graph 32902) univ := by
  refine ⟨{1, 2, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_108 : LocalExchange (graph 33030) univ := by
  refine ⟨{2, 3, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_109 : LocalExchange (graph 33058) univ := by
  refine ⟨{2, 3, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_110 : LocalExchange (graph 33060) univ := by
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_111 : LocalExchange (graph 33090) univ := by
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_112 : LocalExchange (graph 33092) univ := by
  refine ⟨{2, 3, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_113 : LocalExchange (graph 33120) univ := by
  refine ⟨{2, 3, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_114 : LocalExchange (graph 33795) univ := by
  refine ⟨{2, 3, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_115 : LocalExchange (graph 33809) univ := by
  refine ⟨{2, 3, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_116 : LocalExchange (graph 33810) univ := by
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_117 : LocalExchange (graph 33825) univ := by
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_118 : LocalExchange (graph 33826) univ := by
  refine ⟨{2, 3, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_119 : LocalExchange (graph 33840) univ := by
  refine ⟨{2, 3, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_120 : LocalExchange (graph 34821) univ := by
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_121 : LocalExchange (graph 34834) univ := by
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_122 : LocalExchange (graph 34849) univ := by
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_123 : LocalExchange (graph 34852) univ := by
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_124 : LocalExchange (graph 34882) univ := by
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_125 : LocalExchange (graph 34896) univ := by
  refine ⟨{1, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 3, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_126 : LocalExchange (graph 36900) univ := by
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_127 : LocalExchange (graph 36930) univ := by
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_128 : LocalExchange (graph 37378) univ := by
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_129 : LocalExchange (graph 37440) univ := by
  refine ⟨{1, 2, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_130 : LocalExchange (graph 37892) univ := by
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_131 : LocalExchange (graph 37920) univ := by
  refine ⟨{1, 2, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_132 : LocalExchange (graph 40977) univ := by
  refine ⟨{3, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_133 : LocalExchange (graph 41028) univ := by
  refine ⟨{3, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{0, 1, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_134 : LocalExchange (graph 41217) univ := by
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_135 : LocalExchange (graph 41232) univ := by
  refine ⟨{3, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_136 : LocalExchange (graph 41988) univ := by
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inl (QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel))

private theorem witness_137 : LocalExchange (graph 42048) univ := by
  refine ⟨{3, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_138 : LocalExchange (graph 49170) univ := by
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_139 : LocalExchange (graph 49185) univ := by
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_140 : LocalExchange (graph 49409) univ := by
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_141 : LocalExchange (graph 49440) univ := by
  refine ⟨{1, 2, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_142 : LocalExchange (graph 49666) univ := by
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_143 : LocalExchange (graph 49680) univ := by
  refine ⟨{1, 2, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{3, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_144 : LocalExchange (graph 963) univ := by
  refine ⟨{0, 4, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_145 : LocalExchange (graph 1686) univ := by
  refine ⟨{0, 5, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_146 : LocalExchange (graph 2409) univ := by
  refine ⟨{0, 4, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_147 : LocalExchange (graph 3132) univ := by
  refine ⟨{0, 6, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_148 : LocalExchange (graph 12483) univ := by
  refine ⟨{0, 4, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_149 : LocalExchange (graph 13379) univ := by
  refine ⟨{0, 4, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_150 : LocalExchange (graph 14467) univ := by
  refine ⟨{0, 4, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_151 : LocalExchange (graph 15363) univ := by
  refine ⟨{0, 4, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_152 : LocalExchange (graph 15408) univ := by
  refine ⟨{1, 4, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 6, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_153 : LocalExchange (graph 24726) univ := by
  refine ⟨{0, 5, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_154 : LocalExchange (graph 24854) univ := by
  refine ⟨{0, 5, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_155 : LocalExchange (graph 26758) univ := by
  refine ⟨{0, 5, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_156 : LocalExchange (graph 26886) univ := by
  refine ⟨{0, 5, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_157 : LocalExchange (graph 26976) univ := by
  refine ⟨{1, 5, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 4, 7}, by decide +kernel, by decide +kernel⟩

private theorem witness_158 : LocalExchange (graph 36969) univ := by
  refine ⟨{0, 4, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_159 : LocalExchange (graph 37417) univ := by
  refine ⟨{0, 4, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_160 : LocalExchange (graph 37961) univ := by
  refine ⟨{0, 4, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_161 : LocalExchange (graph 38409) univ := by
  refine ⟨{0, 4, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_162 : LocalExchange (graph 38544) univ := by
  refine ⟨{1, 4, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 5, 6}, by decide +kernel, by decide +kernel⟩

private theorem witness_163 : LocalExchange (graph 49212) univ := by
  refine ⟨{0, 6, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_164 : LocalExchange (graph 49436) univ := by
  refine ⟨{0, 6, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 4}, by decide +kernel, by decide +kernel⟩

private theorem witness_165 : LocalExchange (graph 49708) univ := by
  refine ⟨{0, 6, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{1, 2, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_166 : LocalExchange (graph 49932) univ := by
  refine ⟨{0, 6, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 4, 5}, by decide +kernel, by decide +kernel⟩

private theorem witness_167 : LocalExchange (graph 50112) univ := by
  refine ⟨{1, 6, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact Or.inr ⟨{2, 4, 5}, by decide +kernel, by decide +kernel⟩

private def group_0 : List ℕ := [
  282, 300, 390, 540, 549, 585, 840, 900,
  1065, 1098, 1155, 1314, 1416, 1560, 1665, 2070]

private theorem group_sound_0 {m : ℕ} (h : m ∈ group_0) :
    LocalExchange (graph m) univ := by
  simp only [group_0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_0
  · exact witness_1
  · exact witness_2
  · exact witness_3
  · exact witness_4
  · exact witness_5
  · exact witness_6
  · exact witness_7
  · exact witness_8
  · exact witness_9
  · exact witness_10
  · exact witness_11
  · exact witness_12
  · exact witness_13
  · exact witness_14
  · exact witness_15

private def group_1 : List ℕ := [
  2115, 2181, 2340, 2370, 2577, 2628, 3090, 3105,
  4118, 4122, 4124, 4362, 4388, 4418, 4424, 4484]

private theorem group_sound_1 {m : ℕ} (h : m ∈ group_1) :
    LocalExchange (graph m) univ := by
  simp only [group_1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_16
  · exact witness_17
  · exact witness_18
  · exact witness_19
  · exact witness_20
  · exact witness_21
  · exact witness_22
  · exact witness_23
  · exact witness_24
  · exact witness_25
  · exact witness_26
  · exact witness_27
  · exact witness_28
  · exact witness_29
  · exact witness_30
  · exact witness_31

private def group_2 : List ℕ := [
  4512, 4620, 4676, 4680, 4740, 4744, 4800, 6150,
  6178, 6180, 6210, 6212, 6240, 8229, 8233, 8236]

private theorem group_sound_2 {m : ℕ} (h : m ∈ group_2) :
    LocalExchange (graph m) univ := by
  simp only [group_2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_32
  · exact witness_33
  · exact witness_34
  · exact witness_35
  · exact witness_36
  · exact witness_37
  · exact witness_38
  · exact witness_39
  · exact witness_40
  · exact witness_41
  · exact witness_42
  · exact witness_43
  · exact witness_44
  · exact witness_45
  · exact witness_46
  · exact witness_47

private def group_3 : List ℕ := [
  8460, 8516, 8520, 8580, 8584, 8640, 8709, 8728,
  8776, 8784, 8833, 8836, 9225, 9233, 9240, 9345]

private theorem group_sound_3 {m : ℕ} (h : m ∈ group_3) :
    LocalExchange (graph m) univ := by
  simp only [group_3, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_48
  · exact witness_49
  · exact witness_50
  · exact witness_51
  · exact witness_52
  · exact witness_53
  · exact witness_54
  · exact witness_55
  · exact witness_56
  · exact witness_57
  · exact witness_58
  · exact witness_59
  · exact witness_60
  · exact witness_61
  · exact witness_62
  · exact witness_63

private def group_4 : List ℕ := [
  9352, 9360, 12360, 12420, 13316, 13440, 14344, 14400,
  16451, 16457, 16458, 16905, 16913, 16920, 17025, 17032]

private theorem group_sound_4 {m : ℕ} (h : m ∈ group_4) :
    LocalExchange (graph m) univ := by
  simp only [group_4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_64
  · exact witness_65
  · exact witness_66
  · exact witness_67
  · exact witness_68
  · exact witness_69
  · exact witness_70
  · exact witness_71
  · exact witness_72
  · exact witness_73
  · exact witness_74
  · exact witness_75
  · exact witness_76
  · exact witness_77
  · exact witness_78
  · exact witness_79

private def group_5 : List ℕ := [
  17040, 17418, 17426, 17432, 17441, 17537, 17568, 18435,
  18449, 18450, 18465, 18466, 18480, 20514, 20616, 20994]

private theorem group_sound_5 {m : ℕ} (h : m ∈ group_5) :
    LocalExchange (graph m) univ := by
  simp only [group_5, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_80
  · exact witness_81
  · exact witness_82
  · exact witness_83
  · exact witness_84
  · exact witness_85
  · exact witness_86
  · exact witness_87
  · exact witness_88
  · exact witness_89
  · exact witness_90
  · exact witness_91
  · exact witness_92
  · exact witness_93
  · exact witness_94
  · exact witness_95

private def group_6 : List ℕ := [
  21024, 22536, 22656, 24600, 24705, 24833, 24960, 26632,
  26640, 32899, 32901, 32902, 33030, 33058, 33060, 33090]

private theorem group_sound_6 {m : ℕ} (h : m ∈ group_6) :
    LocalExchange (graph m) univ := by
  simp only [group_6, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_96
  · exact witness_97
  · exact witness_98
  · exact witness_99
  · exact witness_100
  · exact witness_101
  · exact witness_102
  · exact witness_103
  · exact witness_104
  · exact witness_105
  · exact witness_106
  · exact witness_107
  · exact witness_108
  · exact witness_109
  · exact witness_110
  · exact witness_111

private def group_7 : List ℕ := [
  33092, 33120, 33795, 33809, 33810, 33825, 33826, 33840,
  34821, 34834, 34849, 34852, 34882, 34896, 36900, 36930]

private theorem group_sound_7 {m : ℕ} (h : m ∈ group_7) :
    LocalExchange (graph m) univ := by
  simp only [group_7, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_112
  · exact witness_113
  · exact witness_114
  · exact witness_115
  · exact witness_116
  · exact witness_117
  · exact witness_118
  · exact witness_119
  · exact witness_120
  · exact witness_121
  · exact witness_122
  · exact witness_123
  · exact witness_124
  · exact witness_125
  · exact witness_126
  · exact witness_127

private def group_8 : List ℕ := [
  37378, 37440, 37892, 37920, 40977, 41028, 41217, 41232,
  41988, 42048, 49170, 49185, 49409, 49440, 49666, 49680]

private theorem group_sound_8 {m : ℕ} (h : m ∈ group_8) :
    LocalExchange (graph m) univ := by
  simp only [group_8, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_128
  · exact witness_129
  · exact witness_130
  · exact witness_131
  · exact witness_132
  · exact witness_133
  · exact witness_134
  · exact witness_135
  · exact witness_136
  · exact witness_137
  · exact witness_138
  · exact witness_139
  · exact witness_140
  · exact witness_141
  · exact witness_142
  · exact witness_143

private def group_9 : List ℕ := [
  963, 1686, 2409, 3132, 12483, 13379, 14467, 15363,
  15408, 24726, 24854, 26758, 26886, 26976, 36969, 37417]

private theorem group_sound_9 {m : ℕ} (h : m ∈ group_9) :
    LocalExchange (graph m) univ := by
  simp only [group_9, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_144
  · exact witness_145
  · exact witness_146
  · exact witness_147
  · exact witness_148
  · exact witness_149
  · exact witness_150
  · exact witness_151
  · exact witness_152
  · exact witness_153
  · exact witness_154
  · exact witness_155
  · exact witness_156
  · exact witness_157
  · exact witness_158
  · exact witness_159

private def group_10 : List ℕ := [
  37961, 38409, 38544, 49212, 49436, 49708, 49932, 50112]

private theorem group_sound_10 {m : ℕ} (h : m ∈ group_10) :
    LocalExchange (graph m) univ := by
  simp only [group_10, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_160
  · exact witness_161
  · exact witness_162
  · exact witness_163
  · exact witness_164
  · exact witness_165
  · exact witness_166
  · exact witness_167

theorem masks_sound {m : ℕ} (h : m ∈ masks) : LocalExchange (graph m) univ := by
  have hg :
      m ∈ group_0 ∨
      m ∈ group_1 ∨
      m ∈ group_2 ∨
      m ∈ group_3 ∨
      m ∈ group_4 ∨
      m ∈ group_5 ∨
      m ∈ group_6 ∨
      m ∈ group_7 ∨
      m ∈ group_8 ∨
      m ∈ group_9 ∨
      m ∈ group_10 := by
    change m ∈
      group_0 ++
      group_1 ++
      group_2 ++
      group_3 ++
      group_4 ++
      group_5 ++
      group_6 ++
      group_7 ++
      group_8 ++
      group_9 ++
      group_10 at h
    simpa only [List.mem_append, or_assoc] using h
  rcases hg with hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg
  · exact group_sound_0 hg
  · exact group_sound_1 hg
  · exact group_sound_2 hg
  · exact group_sound_3 hg
  · exact group_sound_4 hg
  · exact group_sound_5 hg
  · exact group_sound_6 hg
  · exact group_sound_7 hg
  · exact group_sound_8 hg
  · exact group_sound_9 hg
  · exact group_sound_10 hg

/-- The complete local exchange theorem on the labeled eight-vertex model. -/
theorem finite_exchange (m : Fin 65536) (h : 9 ≤ crossCount m.val) :
    LocalExchange (graph m.val) univ := by
  have hc := coverage m h
  obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hc
  exact (masks_sound hw).mono (graph_mono (beq_iff_eq.mp hsub))

end Erdos577.PathExchange
