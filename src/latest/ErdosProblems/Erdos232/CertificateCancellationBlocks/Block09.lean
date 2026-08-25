/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock09_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights09, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt09 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 41216 (43490003) =
      weightedMaskMass a 5242888 (43490003) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (41216, 5242888, 43490003) (by decide)]
  have h001 : weightedMaskMass a 41218 (-21815204) =
      weightedMaskMass a 589956 (-21815204) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (41218, 589956, -21815204) (by decide)]
  have h002 : weightedMaskMass a 41220 (-20029353) =
      weightedMaskMass a 1311240 (-20029353) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (41220, 1311240, -20029353) (by decide)]
  have h003 : weightedMaskMass a 41220 (42745045) =
      weightedMaskMass a 1572996 (42745045) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (41220, 1572996, 42745045) (by decide)]
  have h004 : weightedMaskMass a 41224 (6831432) =
      weightedMaskMass a 245760 (6831432) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (41224, 245760, 6831432) (by decide)]
  have h005 : weightedMaskMass a 41232 (32068850) =
      weightedMaskMass a 233472 (32068850) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (41232, 233472, 32068850) (by decide)]
  have h006 : weightedMaskMass a 41240 (6143927) =
      weightedMaskMass a 249856 (6143927) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (41240, 249856, 6143927) (by decide)]
  have h007 : weightedMaskMass a 49160 (-138175998) =
      weightedMaskMass a 147520 (-138175998) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49160, 147520, -138175998) (by decide)]
  have h008 : weightedMaskMass a 49160 (51321554) =
      weightedMaskMass a 540736 (51321554) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49160, 540736, 51321554) (by decide)]
  have h009 : weightedMaskMass a 49161 (-56841406) =
      weightedMaskMass a 540737 (-56841406) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49161, 540737, -56841406) (by decide)]
  have h010 : weightedMaskMass a 49161 (191617380) =
      weightedMaskMass a 2244672 (191617380) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49161, 2244672, 191617380) (by decide)]
  have h011 : weightedMaskMass a 49170 (129733778) =
      weightedMaskMass a 196642 (129733778) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49170, 196642, 129733778) (by decide)]
  have h012 : weightedMaskMass a 49170 (-61971372) =
      weightedMaskMass a 540708 (-61971372) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49170, 540708, -61971372) (by decide)]
  have h013 : weightedMaskMass a 49170 (89231465) =
      weightedMaskMass a 1057288 (89231465) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49170, 1057288, 89231465) (by decide)]
  have h014 : weightedMaskMass a 49170 (-115632363) =
      weightedMaskMass a 1083648 (-115632363) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49170, 1083648, -115632363) (by decide)]
  have h015 : weightedMaskMass a 49172 (165621861) =
      weightedMaskMass a 132162 (165621861) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49172, 132162, 165621861) (by decide)]
  have h016 : weightedMaskMass a 49172 (153772508) =
      weightedMaskMass a 196674 (153772508) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49172, 196674, 153772508) (by decide)]
  have h017 : weightedMaskMass a 49172 (31606482) =
      weightedMaskMass a 540692 (31606482) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49172, 540692, 31606482) (by decide)]
  have h018 : weightedMaskMass a 49172 (301090) =
      weightedMaskMass a 1048852 (301090) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49172, 1048852, 301090) (by decide)]
  have h019 : weightedMaskMass a 49172 (-211684744) =
      weightedMaskMass a 1097984 (-211684744) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49172, 1097984, -211684744) (by decide)]
  have h020 : weightedMaskMass a 49176 (13124661) =
      weightedMaskMass a 151616 (13124661) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49176, 151616, 13124661) (by decide)]
  have h021 : weightedMaskMass a 49176 (-25100790) =
      weightedMaskMass a 540740 (-25100790) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49176, 540740, -25100790) (by decide)]
  have h022 : weightedMaskMass a 49217 (89681071) =
      weightedMaskMass a 90120 (89681071) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49217, 90120, 89681071) (by decide)]
  have h023 : weightedMaskMass a 49217 (-147887233) =
      weightedMaskMass a 540681 (-147887233) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49217, 540681, -147887233) (by decide)]
  have h024 : weightedMaskMass a 49218 (-57773739) =
      weightedMaskMass a 540712 (-57773739) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49218, 540712, -57773739) (by decide)]
  have h025 : weightedMaskMass a 49218 (68186714) =
      weightedMaskMass a 1073160 (68186714) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49218, 1073160, 68186714) (by decide)]
  have h026 : weightedMaskMass a 49220 (-11210596) =
      weightedMaskMass a 540696 (-11210596) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49220, 540696, -11210596) (by decide)]
  have h027 : weightedMaskMass a 49280 (145733400) =
      weightedMaskMass a 131264 (145733400) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49280, 131264, 145733400) (by decide)]
  have h028 : weightedMaskMass a 49280 (121085192) =
      weightedMaskMass a 131648 (121085192) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49280, 131648, 121085192) (by decide)]
  have h029 : weightedMaskMass a 49280 (-173525917) =
      weightedMaskMass a 557064 (-173525917) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49280, 557064, -173525917) (by decide)]
  have h030 : weightedMaskMass a 49280 (-260797329) =
      weightedMaskMass a 557120 (-260797329) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49280, 557120, -260797329) (by decide)]
  have h031 : weightedMaskMass a 49280 (64617846) =
      weightedMaskMass a 1048864 (64617846) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49280, 1048864, 64617846) (by decide)]
  have h032 : weightedMaskMass a 49280 (122556) =
      weightedMaskMass a 3145760 (122556) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49280, 3145760, 122556) (by decide)]
  have h033 : weightedMaskMass a 49281 (7309327) =
      weightedMaskMass a 561216 (7309327) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49281, 561216, 7309327) (by decide)]
  have h034 : weightedMaskMass a 49281 (1535128) =
      weightedMaskMass a 1049376 (1535128) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49281, 1049376, 1535128) (by decide)]
  have h035 : weightedMaskMass a 49281 (142563377) =
      weightedMaskMass a 2228800 (142563377) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49281, 2228800, 142563377) (by decide)]
  have h036 : weightedMaskMass a 49281 (-42803868) =
      weightedMaskMass a 3145764 (-42803868) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49281, 3145764, -42803868) (by decide)]
  have h037 : weightedMaskMass a 49282 (-85043974) =
      weightedMaskMass a 622600 (-85043974) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49282, 622600, -85043974) (by decide)]
  have h038 : weightedMaskMass a 49282 (17035733) =
      weightedMaskMass a 1050912 (17035733) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49282, 1050912, 17035733) (by decide)]
  have h039 : weightedMaskMass a 49282 (71968194) =
      weightedMaskMass a 2654272 (71968194) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49282, 2654272, 71968194) (by decide)]
  have h040 : weightedMaskMass a 49282 (69380264) =
      weightedMaskMass a 3145762 (69380264) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49282, 3145762, 69380264) (by decide)]
  have h041 : weightedMaskMass a 49284 (-158648533) =
      weightedMaskMass a 1065248 (-158648533) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49284, 1065248, -158648533) (by decide)]
  have h042 : weightedMaskMass a 49284 (298608833) =
      weightedMaskMass a 1605640 (298608833) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49284, 1605640, 298608833) (by decide)]
  have h043 : weightedMaskMass a 49284 (-13749006) =
      weightedMaskMass a 3145768 (-13749006) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49284, 3145768, -13749006) (by decide)]
  have h044 : weightedMaskMass a 49410 (-38261414) =
      weightedMaskMass a 69666 (-38261414) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49410, 69666, -38261414) (by decide)]
  have h045 : weightedMaskMass a 49410 (15364964) =
      weightedMaskMass a 622596 (15364964) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49410, 622596, 15364964) (by decide)]
  have h046 : weightedMaskMass a 49410 (-17445260) =
      weightedMaskMass a 1050896 (-17445260) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49410, 1050896, -17445260) (by decide)]
  have h047 : weightedMaskMass a 49410 (89291887) =
      weightedMaskMass a 2654224 (89291887) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49410, 2654224, 89291887) (by decide)]
  have h048 : weightedMaskMass a 49412 (31944426) =
      weightedMaskMass a 69698 (31944426) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49412, 69698, 31944426) (by decide)]
  have h049 : weightedMaskMass a 49412 (-180008498) =
      weightedMaskMass a 1065232 (-180008498) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49412, 1065232, -180008498) (by decide)]
  have h050 : weightedMaskMass a 49412 (122027273) =
      weightedMaskMass a 1081364 (122027273) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49412, 1081364, 122027273) (by decide)]
  have h051 : weightedMaskMass a 49412 (241267518) =
      weightedMaskMass a 1605636 (241267518) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49412, 1605636, 241267518) (by decide)]
  have h052 : weightedMaskMass a 49412 (-75870569) =
      weightedMaskMass a 2359816 (-75870569) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49412, 2359816, -75870569) (by decide)]
  have h053 : weightedMaskMass a 49416 (173083537) =
      weightedMaskMass a 213056 (173083537) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49416, 213056, 173083537) (by decide)]
  have h054 : weightedMaskMass a 49426 (-73992102) =
      weightedMaskMass a 200738 (-73992102) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49426, 200738, -73992102) (by decide)]
  have h055 : weightedMaskMass a 49426 (9891076) =
      weightedMaskMass a 1083664 (9891076) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49426, 1083664, 9891076) (by decide)]
  have h056 : weightedMaskMass a 49428 (-76773069) =
      weightedMaskMass a 200770 (-76773069) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49428, 200770, -76773069) (by decide)]
  have h057 : weightedMaskMass a 49428 (-138407282) =
      weightedMaskMass a 1081620 (-138407282) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49428, 1081620, -138407282) (by decide)]
  have h058 : weightedMaskMass a 49428 (195482606) =
      weightedMaskMass a 1098000 (195482606) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49428, 1098000, 195482606) (by decide)]
  have h059 : weightedMaskMass a 49432 (-45270136) =
      weightedMaskMass a 217152 (-45270136) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (49432, 217152, -45270136) (by decide)]
  have h060 : weightedMaskMass a 53249 (-44764357) =
      weightedMaskMass a 73746 (-44764357) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53249, 73746, -44764357) (by decide)]
  have h061 : weightedMaskMass a 53249 (-5576339) =
      weightedMaskMass a 73748 (-5576339) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53249, 73748, -5576339) (by decide)]
  have h062 : weightedMaskMass a 53249 (73573783) =
      weightedMaskMass a 73752 (73573783) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53249, 73752, 73573783) (by decide)]
  have h063 : weightedMaskMass a 53249 (-86175756) =
      weightedMaskMass a 4724736 (-86175756) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53249, 4724736, -86175756) (by decide)]
  have h064 : weightedMaskMass a 268289 (-1316681) =
      weightedMaskMass a 530433 (-1316681) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (268289, 530433, -1316681) (by decide)]
  have h065 : weightedMaskMass a 268289 (-51947844) =
      weightedMaskMass a 2361348 (-51947844) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (268289, 2361348, -51947844) (by decide)]
  have h066 : weightedMaskMass a 268289 (23395306) =
      weightedMaskMass a 2490372 (23395306) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (268289, 2490372, 23395306) (by decide)]
  have h067 : weightedMaskMass a 53250 (-96931111) =
      weightedMaskMass a 73762 (-96931111) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53250, 73762, -96931111) (by decide)]
  have h068 : weightedMaskMass a 53250 (39506580) =
      weightedMaskMass a 1056792 (39506580) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53250, 1056792, 39506580) (by decide)]
  have h069 : weightedMaskMass a 53250 (54665419) =
      weightedMaskMass a 1574913 (54665419) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53250, 1574913, 54665419) (by decide)]
  have h070 : weightedMaskMass a 53252 (-56952225) =
      weightedMaskMass a 73794 (-56952225) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53252, 73794, -56952225) (by decide)]
  have h071 : weightedMaskMass a 53313 (-25897446) =
      weightedMaskMass a 90136 (-25897446) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53313, 90136, -25897446) (by decide)]
  have h072 : weightedMaskMass a 53314 (13771949) =
      weightedMaskMass a 1073176 (13771949) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53314, 1073176, 13771949) (by decide)]
  have h073 : weightedMaskMass a 53504 (31110524) =
      weightedMaskMass a 77826 (31110524) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53504, 77826, 31110524) (by decide)]
  have h074 : weightedMaskMass a 53506 (18798992) =
      weightedMaskMass a 77858 (18798992) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53506, 77858, 18798992) (by decide)]
  have h075 : weightedMaskMass a 53508 (22579475) =
      weightedMaskMass a 77890 (22579475) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (53508, 77890, 22579475) (by decide)]
  have h076 : weightedMaskMass a 57344 (83321703) =
      weightedMaskMass a 163904 (83321703) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57344, 163904, 83321703) (by decide)]
  have h077 : weightedMaskMass a 57344 (-128718027) =
      weightedMaskMass a 557184 (-128718027) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57344, 557184, -128718027) (by decide)]
  have h078 : weightedMaskMass a 57344 (-24508707) =
      weightedMaskMass a 3407872 (-24508707) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57344, 3407872, -24508707) (by decide)]
  have h079 : weightedMaskMass a 57344 (24611074) =
      weightedMaskMass a 4227136 (24611074) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57344, 4227136, 24611074) (by decide)]
  have h080 : weightedMaskMass a 57344 (51143511) =
      weightedMaskMass a 4718600 (51143511) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57344, 4718600, 51143511) (by decide)]
  have h081 : weightedMaskMass a 57345 (55449208) =
      weightedMaskMass a 2261056 (55449208) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57345, 2261056, 55449208) (by decide)]
  have h082 : weightedMaskMass a 57345 (-20556153) =
      weightedMaskMass a 4229184 (-20556153) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57345, 4229184, -20556153) (by decide)]
  have h083 : weightedMaskMass a 57346 (-25224760) =
      weightedMaskMass a 622720 (-25224760) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57346, 622720, -25224760) (by decide)]
  have h084 : weightedMaskMass a 57348 (112920330) =
      weightedMaskMass a 1605760 (112920330) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57348, 1605760, 112920330) (by decide)]
  have h085 : weightedMaskMass a 57348 (-89112348) =
      weightedMaskMass a 3408384 (-89112348) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57348, 3408384, -89112348) (by decide)]
  have h086 : weightedMaskMass a 57352 (76854310) =
      weightedMaskMass a 180288 (76854310) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57352, 180288, 76854310) (by decide)]
  have h087 : weightedMaskMass a 57353 (-87005746) =
      weightedMaskMass a 2277440 (-87005746) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57353, 2277440, -87005746) (by decide)]
  have h088 : weightedMaskMass a 57360 (13879205) =
      weightedMaskMass a 168000 (13879205) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57360, 168000, 13879205) (by decide)]
  have h089 : weightedMaskMass a 57368 (-59925454) =
      weightedMaskMass a 184384 (-59925454) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57368, 184384, -59925454) (by decide)]
  have h090 : weightedMaskMass a 57600 (18544664) =
      weightedMaskMass a 229440 (18544664) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57600, 229440, 18544664) (by decide)]
  have h091 : weightedMaskMass a 57600 (119330197) =
      weightedMaskMass a 557188 (119330197) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57600, 557188, 119330197) (by decide)]
  have h092 : weightedMaskMass a 57600 (-3604730) =
      weightedMaskMass a 3407880 (-3604730) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57600, 3407880, -3604730) (by decide)]
  have h093 : weightedMaskMass a 57600 (-27043108) =
      weightedMaskMass a 5767176 (-27043108) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57600, 5767176, -27043108) (by decide)]
  have h094 : weightedMaskMass a 57602 (-4031640) =
      weightedMaskMass a 622724 (-4031640) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57602, 622724, -4031640) (by decide)]
  have h095 : weightedMaskMass a 57604 (-191524668) =
      weightedMaskMass a 1605764 (-191524668) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57604, 1605764, -191524668) (by decide)]
  have h096 : weightedMaskMass a 57604 (98351167) =
      weightedMaskMass a 3408392 (98351167) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57604, 3408392, 98351167) (by decide)]
  have h097 : weightedMaskMass a 57608 (-119286888) =
      weightedMaskMass a 245824 (-119286888) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57608, 245824, -119286888) (by decide)]
  have h098 : weightedMaskMass a 57616 (-42604293) =
      weightedMaskMass a 233536 (-42604293) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57616, 233536, -42604293) (by decide)]
  have h099 : weightedMaskMass a 57624 (33275052) =
      weightedMaskMass a 249920 (33275052) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (57624, 249920, 33275052) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt09 s.val : ℝ)) = (((((((weightedMaskMass a 41216 (43490003) + (-weightedMaskMass a 5242888 (43490003) + weightedMaskMass a 41218 (-21815204))) + (-weightedMaskMass a 589956 (-21815204) + (weightedMaskMass a 41220 (-20029353) + -weightedMaskMass a 1311240 (-20029353)))) + ((weightedMaskMass a 41220 (42745045) + (-weightedMaskMass a 1572996 (42745045) + weightedMaskMass a 41224 (6831432))) + (-weightedMaskMass a 245760 (6831432) + (weightedMaskMass a 41232 (32068850) + -weightedMaskMass a 233472 (32068850))))) + (((weightedMaskMass a 41240 (6143927) + (-weightedMaskMass a 249856 (6143927) + weightedMaskMass a 49160 (-138175998))) + (-weightedMaskMass a 147520 (-138175998) + (weightedMaskMass a 49160 (51321554) + -weightedMaskMass a 540736 (51321554)))) + ((weightedMaskMass a 49161 (-56841406) + (-weightedMaskMass a 540737 (-56841406) + weightedMaskMass a 49161 (191617380))) + ((-weightedMaskMass a 2244672 (191617380) + weightedMaskMass a 49170 (129733778)) + (-weightedMaskMass a 196642 (129733778) + weightedMaskMass a 49170 (-61971372)))))) + ((((-weightedMaskMass a 540708 (-61971372) + (weightedMaskMass a 49170 (89231465) + -weightedMaskMass a 1057288 (89231465))) + (weightedMaskMass a 49170 (-115632363) + (-weightedMaskMass a 1083648 (-115632363) + weightedMaskMass a 49172 (165621861)))) + ((-weightedMaskMass a 132162 (165621861) + (weightedMaskMass a 49172 (153772508) + -weightedMaskMass a 196674 (153772508))) + (weightedMaskMass a 49172 (31606482) + (-weightedMaskMass a 540692 (31606482) + weightedMaskMass a 49172 (301090))))) + (((-weightedMaskMass a 1048852 (301090) + (weightedMaskMass a 49172 (-211684744) + -weightedMaskMass a 1097984 (-211684744))) + (weightedMaskMass a 49176 (13124661) + (-weightedMaskMass a 151616 (13124661) + weightedMaskMass a 49176 (-25100790)))) + ((-weightedMaskMass a 540740 (-25100790) + (weightedMaskMass a 49217 (89681071) + -weightedMaskMass a 90120 (89681071))) + ((weightedMaskMass a 49217 (-147887233) + -weightedMaskMass a 540681 (-147887233)) + (weightedMaskMass a 49218 (-57773739) + -weightedMaskMass a 540712 (-57773739))))))) + (((((weightedMaskMass a 49218 (68186714) + (-weightedMaskMass a 1073160 (68186714) + weightedMaskMass a 49220 (-11210596))) + (-weightedMaskMass a 540696 (-11210596) + (weightedMaskMass a 49280 (145733400) + -weightedMaskMass a 131264 (145733400)))) + ((weightedMaskMass a 49280 (121085192) + (-weightedMaskMass a 131648 (121085192) + weightedMaskMass a 49280 (-173525917))) + (-weightedMaskMass a 557064 (-173525917) + (weightedMaskMass a 49280 (-260797329) + -weightedMaskMass a 557120 (-260797329))))) + (((weightedMaskMass a 49280 (64617846) + (-weightedMaskMass a 1048864 (64617846) + weightedMaskMass a 49280 (122556))) + (-weightedMaskMass a 3145760 (122556) + (weightedMaskMass a 49281 (7309327) + -weightedMaskMass a 561216 (7309327)))) + ((weightedMaskMass a 49281 (1535128) + (-weightedMaskMass a 1049376 (1535128) + weightedMaskMass a 49281 (142563377))) + ((-weightedMaskMass a 2228800 (142563377) + weightedMaskMass a 49281 (-42803868)) + (-weightedMaskMass a 3145764 (-42803868) + weightedMaskMass a 49282 (-85043974)))))) + ((((-weightedMaskMass a 622600 (-85043974) + (weightedMaskMass a 49282 (17035733) + -weightedMaskMass a 1050912 (17035733))) + (weightedMaskMass a 49282 (71968194) + (-weightedMaskMass a 2654272 (71968194) + weightedMaskMass a 49282 (69380264)))) + ((-weightedMaskMass a 3145762 (69380264) + (weightedMaskMass a 49284 (-158648533) + -weightedMaskMass a 1065248 (-158648533))) + (weightedMaskMass a 49284 (298608833) + (-weightedMaskMass a 1605640 (298608833) + weightedMaskMass a 49284 (-13749006))))) + (((-weightedMaskMass a 3145768 (-13749006) + (weightedMaskMass a 49410 (-38261414) + -weightedMaskMass a 69666 (-38261414))) + (weightedMaskMass a 49410 (15364964) + (-weightedMaskMass a 622596 (15364964) + weightedMaskMass a 49410 (-17445260)))) + ((-weightedMaskMass a 1050896 (-17445260) + (weightedMaskMass a 49410 (89291887) + -weightedMaskMass a 2654224 (89291887))) + ((weightedMaskMass a 49412 (31944426) + -weightedMaskMass a 69698 (31944426)) + (weightedMaskMass a 49412 (-180008498) + -weightedMaskMass a 1065232 (-180008498)))))))) + ((((((weightedMaskMass a 49412 (122027273) + (-weightedMaskMass a 1081364 (122027273) + weightedMaskMass a 49412 (241267518))) + (-weightedMaskMass a 1605636 (241267518) + (weightedMaskMass a 49412 (-75870569) + -weightedMaskMass a 2359816 (-75870569)))) + ((weightedMaskMass a 49416 (173083537) + (-weightedMaskMass a 213056 (173083537) + weightedMaskMass a 49426 (-73992102))) + (-weightedMaskMass a 200738 (-73992102) + (weightedMaskMass a 49426 (9891076) + -weightedMaskMass a 1083664 (9891076))))) + (((weightedMaskMass a 49428 (-76773069) + (-weightedMaskMass a 200770 (-76773069) + weightedMaskMass a 49428 (-138407282))) + (-weightedMaskMass a 1081620 (-138407282) + (weightedMaskMass a 49428 (195482606) + -weightedMaskMass a 1098000 (195482606)))) + ((weightedMaskMass a 49432 (-45270136) + (-weightedMaskMass a 217152 (-45270136) + weightedMaskMass a 53249 (-44764357))) + ((-weightedMaskMass a 73746 (-44764357) + weightedMaskMass a 53249 (-5576339)) + (-weightedMaskMass a 73748 (-5576339) + weightedMaskMass a 53249 (73573783)))))) + ((((-weightedMaskMass a 73752 (73573783) + (weightedMaskMass a 53249 (-86175756) + -weightedMaskMass a 4724736 (-86175756))) + (weightedMaskMass a 268289 (-1316681) + (-weightedMaskMass a 530433 (-1316681) + weightedMaskMass a 268289 (-51947844)))) + ((-weightedMaskMass a 2361348 (-51947844) + (weightedMaskMass a 268289 (23395306) + -weightedMaskMass a 2490372 (23395306))) + (weightedMaskMass a 53250 (-96931111) + (-weightedMaskMass a 73762 (-96931111) + weightedMaskMass a 53250 (39506580))))) + (((-weightedMaskMass a 1056792 (39506580) + (weightedMaskMass a 53250 (54665419) + -weightedMaskMass a 1574913 (54665419))) + (weightedMaskMass a 53252 (-56952225) + (-weightedMaskMass a 73794 (-56952225) + weightedMaskMass a 53313 (-25897446)))) + ((-weightedMaskMass a 90136 (-25897446) + (weightedMaskMass a 53314 (13771949) + -weightedMaskMass a 1073176 (13771949))) + ((weightedMaskMass a 53504 (31110524) + -weightedMaskMass a 77826 (31110524)) + (weightedMaskMass a 53506 (18798992) + -weightedMaskMass a 77858 (18798992))))))) + (((((weightedMaskMass a 53508 (22579475) + (-weightedMaskMass a 77890 (22579475) + weightedMaskMass a 57344 (83321703))) + (-weightedMaskMass a 163904 (83321703) + (weightedMaskMass a 57344 (-128718027) + -weightedMaskMass a 557184 (-128718027)))) + ((weightedMaskMass a 57344 (-24508707) + (-weightedMaskMass a 3407872 (-24508707) + weightedMaskMass a 57344 (24611074))) + (-weightedMaskMass a 4227136 (24611074) + (weightedMaskMass a 57344 (51143511) + -weightedMaskMass a 4718600 (51143511))))) + (((weightedMaskMass a 57345 (55449208) + (-weightedMaskMass a 2261056 (55449208) + weightedMaskMass a 57345 (-20556153))) + (-weightedMaskMass a 4229184 (-20556153) + (weightedMaskMass a 57346 (-25224760) + -weightedMaskMass a 622720 (-25224760)))) + ((weightedMaskMass a 57348 (112920330) + (-weightedMaskMass a 1605760 (112920330) + weightedMaskMass a 57348 (-89112348))) + ((-weightedMaskMass a 3408384 (-89112348) + weightedMaskMass a 57352 (76854310)) + (-weightedMaskMass a 180288 (76854310) + weightedMaskMass a 57353 (-87005746)))))) + ((((-weightedMaskMass a 2277440 (-87005746) + (weightedMaskMass a 57360 (13879205) + -weightedMaskMass a 168000 (13879205))) + (weightedMaskMass a 57368 (-59925454) + (-weightedMaskMass a 184384 (-59925454) + weightedMaskMass a 57600 (18544664)))) + ((-weightedMaskMass a 229440 (18544664) + (weightedMaskMass a 57600 (119330197) + -weightedMaskMass a 557188 (119330197))) + (weightedMaskMass a 57600 (-3604730) + (-weightedMaskMass a 3407880 (-3604730) + weightedMaskMass a 57600 (-27043108))))) + (((-weightedMaskMass a 5767176 (-27043108) + (weightedMaskMass a 57602 (-4031640) + -weightedMaskMass a 622724 (-4031640))) + (weightedMaskMass a 57604 (-191524668) + (-weightedMaskMass a 1605764 (-191524668) + weightedMaskMass a 57604 (98351167)))) + ((-weightedMaskMass a 3408392 (98351167) + (weightedMaskMass a 57608 (-119286888) + -weightedMaskMass a 245824 (-119286888))) + ((weightedMaskMass a 57616 (-42604293) + -weightedMaskMass a 233536 (-42604293)) + (weightedMaskMass a 57624 (33275052) + -weightedMaskMass a 249920 (33275052))))))))) := by
      simp only [atomCongruenceContributionInt09, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
