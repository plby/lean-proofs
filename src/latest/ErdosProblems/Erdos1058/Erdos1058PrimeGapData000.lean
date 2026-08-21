import ErdosProblems.Erdos1058.Erdos1058PrimeGapBase

namespace Erdos1058

namespace PrimeGap210Certificate

def primeGapData_0_0 : List ℕ := [439, 647, 857, 1063, 1259, 1459, 1669, 1879, 2089, 2297, 2503, 2713, 2917, 3121, 3331, 3541, 3739, 3947, 4157, 4363, 4567, 4759, 4969, 5179, 5387, 5591, 5801, 6011, 6221, 6427, 6637, 6841, 7043, 7253, 7459, 7669, 7879, 8089, 8297, 8501, 8707, 8893, 9103, 9311, 9521, 9721, 9931, 10141, 10343, 10531, 10739, 10949, 11159, 11369, 11579, 11789, 11987, 12197, 12401, 12611, 12821, 13009, 13219, 13421, 13627, 13831, 14033, 14243, 14449, 14657, 14867, 15077, 15287, 15497, 15683, 15889, 16097, 16301, 16493, 16703, 16903, 17107, 17317, 17519, 17729, 17939, 18149, 18353, 18553, 18757, 18959, 19163, 19373, 19583, 19793, 19997, 20201, 20411, 20611, 20809]

lemma primeGapData_0_0_primes : primeGapData_0_0.Forall Nat.Prime := by
  norm_num [primeGapData_0_0]

lemma primeGapData_0_0_chain : primeGapData_0_0.IsChain GapStep := by
  norm_num [primeGapData_0_0, List.IsChain, GapStep]

def primeGapData_0_1 : List ℕ := [21019, 21227, 21433, 21617, 21821, 22031, 22229, 22433, 22643, 22853, 23063, 23269, 23473, 23677, 23887, 24097, 24281, 24481, 24691, 24889, 25097, 25307, 25471, 25679, 25889, 26099, 26309, 26513, 26723, 26927, 27127, 27337, 27541, 27751, 27961, 28163, 28351, 28559, 28759, 28961, 29167, 29363, 29573, 29761, 29959, 30169, 30367, 30577, 30781, 30983, 31193, 31397, 31607, 31817, 32027, 32237, 32443, 32653, 32843, 33053, 33247, 33457, 33647, 33857, 34061, 34267, 34471, 34679, 34883, 35089, 35291, 35491, 35677, 35879, 36083, 36293, 36497, 36697, 36901, 37097, 37307, 37517, 37717, 37907, 38113, 38321, 38501, 38711, 38921, 39119, 39323, 39521, 39727, 39937, 40129, 40289, 40499, 40709, 40903, 41113]

lemma primeGapData_0_1_primes : primeGapData_0_1.Forall Nat.Prime := by
  norm_num [primeGapData_0_1]

lemma primeGapData_0_1_chain : primeGapData_0_1.IsChain GapStep := by
  norm_num [primeGapData_0_1, List.IsChain, GapStep]

def primeGapData_0_2 : List ℕ := [41299, 41507, 41687, 41897, 42101, 42307, 42509, 42719, 42929, 43133, 43331, 43541, 43721, 43913, 44123, 44293, 44501, 44711, 44917, 45127, 45337, 45541, 45751, 45959, 46153, 46351, 46559, 46769, 46957, 47161, 47363, 47569, 47779, 47981, 48187, 48397, 48593, 48799, 49009, 49211, 49417, 49627, 49831, 50033, 50231, 50441, 50651, 50857, 51061, 51263, 51473, 51683, 51893, 52103, 52313, 52517, 52727, 52937, 53147, 53353, 53551, 53759, 53959, 54167, 54377, 54583, 54787, 54983, 55171, 55381, 55589, 55799, 56009, 56209, 56417, 56611, 56821, 56999, 57203, 57413, 57601, 57809, 58013, 58217, 58427, 58631, 58831, 59029, 59239, 59447, 59651, 59833, 60041, 60251, 60457, 60661, 60869, 61057, 61261, 61471]

lemma primeGapData_0_2_primes : primeGapData_0_2.Forall Nat.Prime := by
  norm_num [primeGapData_0_2]

lemma primeGapData_0_2_chain : primeGapData_0_2.IsChain GapStep := by
  norm_num [primeGapData_0_2, List.IsChain, GapStep]

def primeGapData_0_3 : List ℕ := [61681, 61879, 62081, 62273, 62483, 62687, 62897, 63103, 63313, 63521, 63727, 63929, 64123, 64333, 64513, 64717, 64927, 65129, 65327, 65537, 65731, 65929, 66137, 66347, 66553, 66763, 66973, 67181, 67391, 67601, 67807, 67993, 68171, 68371, 68581, 68791, 69001, 69203, 69403, 69593, 69779, 69959, 70163, 70373, 70583, 70793, 70999, 71209, 71419, 71597, 71807, 71999, 72173, 72383, 72577, 72767, 72977, 73181, 73387, 73597, 73783, 73973, 74177, 74383, 74587, 74797, 74959, 75169, 75377, 75583, 75793, 76003, 76213, 76423, 76631, 76837, 77047, 77249, 77447, 77647, 77849, 78059, 78259, 78467, 78653, 78857, 79063, 79273, 79481, 79691, 79901, 80111, 80317, 80527, 80737, 80933, 81131, 81331, 81533, 81737]

lemma primeGapData_0_3_primes : primeGapData_0_3.Forall Nat.Prime := by
  norm_num [primeGapData_0_3]

lemma primeGapData_0_3_chain : primeGapData_0_3.IsChain GapStep := by
  norm_num [primeGapData_0_3, List.IsChain, GapStep]

def primeGapData_0_4 : List ℕ := [81943, 82153, 82361, 82571, 82781, 82981, 83177, 83383, 83591, 83791, 83987, 84191, 84401, 84589, 84793, 84991, 85201, 85411, 85621, 85831, 86029, 86239, 86441, 86629, 86837, 87041, 87251, 87443, 87649, 87853, 88037, 88241, 88427, 88609, 88819, 89021, 89231, 89431, 89633, 89839, 90031, 90239, 90439, 90647, 90847, 91033, 91243, 91453, 91639, 91841, 92051, 92251, 92461, 92671, 92867, 93077, 93287, 93497, 93703, 93913, 94121, 94331, 94541, 94747, 94951, 95153, 95339, 95549, 95747, 95957, 96167, 96377, 96587, 96797, 97007, 97213, 97423, 97613, 97813, 98017, 98227, 98429, 98639, 98849, 99053, 99259, 99469, 99679, 99881, 100069, 100279, 100483, 100693, 100853, 101063, 101273, 101483, 101693, 101891, 102101]

lemma primeGapData_0_4_primes : primeGapData_0_4.Forall Nat.Prime := by
  norm_num [primeGapData_0_4]

lemma primeGapData_0_4_chain : primeGapData_0_4.IsChain GapStep := by
  norm_num [primeGapData_0_4, List.IsChain, GapStep]

def primeGapDataGroup0 : List ℕ :=
  primeGapData_0_0 ++ primeGapData_0_1 ++ primeGapData_0_2 ++ primeGapData_0_3 ++ primeGapData_0_4

lemma primeGapDataGroup0_primes : primeGapDataGroup0.Forall Nat.Prime := by
  simp only [primeGapDataGroup0, List.forall_append]
  exact ⟨⟨⟨⟨primeGapData_0_0_primes, primeGapData_0_1_primes⟩, primeGapData_0_2_primes⟩, primeGapData_0_3_primes⟩, primeGapData_0_4_primes⟩

lemma primeGapDataGroup0_chain : primeGapDataGroup0.IsChain GapStep := by
  apply primeGapData_0_0_chain.append
  · apply primeGapData_0_1_chain.append
    · apply primeGapData_0_2_chain.append
      · exact primeGapData_0_3_chain.append primeGapData_0_4_chain (by
          norm_num [primeGapData_0_3, primeGapData_0_4, GapStep])
      · norm_num [primeGapData_0_2, primeGapData_0_3, GapStep]
    · norm_num [primeGapData_0_1, primeGapData_0_2, GapStep]
  · norm_num [primeGapData_0_0, primeGapData_0_1, GapStep]

lemma primeGapDataGroup0_head : primeGapDataGroup0.head? = some 439 := by
  simp [primeGapDataGroup0, primeGapData_0_0]

lemma primeGapDataGroup0_last : primeGapDataGroup0.getLast? = some 102101 := by
  simp [primeGapDataGroup0, primeGapData_0_4]

end PrimeGap210Certificate

end Erdos1058
