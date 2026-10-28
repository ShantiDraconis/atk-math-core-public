import ATK.FltRegular.SmallNumbers.Cyclotomic
import ATK.FltRegular.SmallNumbers.OrderOf
import ATK.FltRegular.FltRegular
import ATK.FltRegular.NumberTheory.RegularPrimes
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ComputeDegree
import ATK.PolyLista
import ATK.FermatDezenoveCertA
import ATK.FermatDezenoveCertB
import ATK.FermatDezenoveCertC
import ATK.FermatDezenoveCertD
import ATK.FermatDezenoveCertE

/-!
# ATK — Último teorema de Fermat para `n = 19`

Mesmo método de `ATK.FermatDezessete` (critério `pid6` de flt-regular, certificados por reflexão
em `ATK.PolyLista`):

* `minkowski_dezenove`: a cota de Minkowski de `ℚ(ζ₁₉)` (grau 18, discriminante `±19¹⁷`, 9
  lugares complexos) tem parte inteira `105933`;
* `excecoes`: conferido pelo kernel (`decide +kernel`), todo `p ≤ 105933` com alguma potência
  `pⁱ ≤ 105933`, `pⁱ ≡ 1 (mód 19)`, `i ≥ 1`, está na lista `primosCertificados` (558 primos:
  552 de grau 1, 4 de grau 2, 2 de grau 3), é `1`, ou tem um divisor primo `≤ 325`;
* `certificado_p` para cada primo da lista: um gerador do ideal primo e as identidades
  polinomiais em `ℤ[X]` do critério, reduzidas a igualdades de listas de inteiros que o kernel
  confere por cálculo (geradores achados fora do kernel por redução de reticulados);
* **`pid_dezenove`**: `𝓞(ℚ(ζ₁₉))` é principal; `regular_dezenove`; **`flt_dezenove`: FLT(19)**.
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid ATK.PolyLista
  ATK.FermatDezenoveBase

namespace ATK.FermatDezenove

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {19} ℚ K]

/-- Os 558 primos com certificado. -/
def primosCertificados : List ℕ := [7, 11, 37, 113, 151, 191, 227, 229, 419, 457, 571, 647, 761, 1103, 1217, 1483, 1559, 1597,
  1787, 1901, 2053, 2129, 2243, 2281, 2357, 2699, 2851, 2927, 3041, 3079, 3307, 3877, 4219,
  4409, 4447, 4523, 4561, 4637, 4751, 4789, 4903, 5701, 6043, 6271, 6689, 6803, 6841, 6917,
  7069, 7297, 7411, 7487, 7639, 7753, 7829, 7867, 8171, 8209, 8513, 8627, 8741, 8779, 8893,
  8969, 9007, 9311, 9349, 9463, 9539, 9767, 10223, 10337, 10831, 11059, 11173, 11287, 11743,
  11933, 11971, 12161, 12503, 12541, 12959, 13187, 13339, 13567, 13681, 13757, 14251, 14327,
  14479, 14593, 14669, 14783, 14821, 14897, 15277, 15391, 15467, 15581, 15619, 15733, 15809,
  15923, 16189, 16417, 16493, 16607, 16759, 16987, 17291, 17443, 17519, 17747, 18013, 18089,
  18127, 18583, 18773, 19001, 19267, 19381, 19457, 19571, 19609, 19913, 20369, 20407, 20483,
  20521, 20749, 20939, 21319, 21433, 21661, 21737, 21851, 22003, 22079, 22193, 22307, 22573,
  22877, 23029, 23143, 23333, 23371, 23447, 23561, 23599, 23789, 23827, 24169, 24359, 24473,
  24967, 25309, 25423, 25537, 25841, 26107, 26183, 26297, 26449, 26981, 27361, 27437, 27551,
  27779, 27817, 27893, 28349, 28387, 28463, 28729, 28843, 29033, 29147, 29527, 29641, 29717,
  29983, 30059, 30097, 30211, 30553, 30781, 30971, 31123, 31237, 31541, 31769, 31883, 32377,
  32491, 32719, 32833, 32909, 33023, 33289, 33403, 33479, 34429, 34543, 34847, 34961, 35227,
  35531, 35569, 35759, 35797, 35911, 36671, 36709, 36899, 37013, 37507, 37811, 37963, 38039,
  38153, 38609, 38723, 39103, 39217, 39293, 39521, 39749, 39863, 39901, 40129, 40357, 40433,
  40471, 40699, 40813, 40927, 41117, 41231, 41269, 41611, 41687, 41801, 41953, 42181, 42257,
  42409, 42751, 42979, 43093, 43207, 43283, 43321, 43397, 43777, 43853, 43891, 44119, 44537,
  44651, 44879, 44917, 45259, 45677, 45943, 46133, 46171, 46399, 46589, 46703, 46817, 47387,
  47501, 47653, 47843, 47881, 48109, 48299, 48337, 48413, 48527, 48679, 48869, 48907, 49211,
  49363, 49477, 49667, 50047, 50123, 50503, 51263, 51719, 51871, 52289, 52517, 52631, 52783,
  52859, 52973, 53087, 53201, 53239, 53353, 53657, 53923, 54037, 54151, 54493, 54721, 54949,
  55291, 55633, 55823, 56393, 56431, 56659, 56773, 56963, 57077, 57191, 57457, 57571, 58027,
  58217, 58369, 58711, 58787, 58901, 59053, 59167, 59243, 59281, 59357, 59471, 59509, 59699,
  60041, 60383, 60497, 60611, 60649, 60763, 60953, 61333, 61409, 61561, 61637, 61751, 61979,
  62017, 62131, 62207, 62473, 62549, 62701, 62929, 63347, 63499, 63689, 63727, 63803, 63841,
  64373, 64601, 65171, 65323, 65437, 65551, 66083, 66463, 66653, 66919, 67033, 67261, 67489,
  67679, 68059, 68477, 68743, 68819, 69313, 69389, 69427, 69959, 69997, 70111, 70529, 71023,
  71327, 71479, 71593, 71707, 71821, 72277, 72353, 72467, 72733, 72923, 73037, 73189, 73303,
  73379, 73417, 73607, 73721, 74101, 74177, 74747, 74861, 75013, 75431, 75583, 75659, 75773,
  76001, 76039, 76343, 76837, 76913, 77141, 77369, 77521, 77711, 77863, 77977, 78167, 78509,
  78623, 78737, 78889, 79193, 79231, 79687, 79801, 80447, 80599, 80713, 80789, 81017, 81131,
  81283, 81359, 81701, 81853, 81929, 81967, 82499, 82613, 82651, 82727, 83221, 83449, 83563,
  83639, 83791, 84247, 84437, 84551, 84589, 85121, 85159, 85577, 85691, 85843, 86413, 86869,
  87211, 87553, 87629, 87743, 88237, 88427, 88807, 88883, 88997, 89491, 89567, 89681, 89833,
  89909, 90023, 90289, 90403, 90631, 90821, 91163, 91733, 91771, 91961, 92189, 92227, 92569,
  92683, 92987, 93139, 93253, 93329, 93481, 93557, 93937, 94583, 94621, 94811, 94849, 95153,
  95191, 95267, 95419, 95723, 95989, 96179, 96293, 96331, 96749, 96787, 97547, 97813, 97927,
  98041, 98269, 98459, 98573, 98801, 98953, 99181, 99257, 99371, 99409, 99523, 99713, 100169,
  100207, 100511, 100549, 100853, 101081, 101119, 101347, 101537, 101879, 101917, 102031,
  102107, 102259, 102563, 102677, 102829, 103171, 103399, 103703, 103969, 104311, 104729,
  105071, 105337, 105527, 105907]

/-- Os primos até `325 = ⌊√105933⌋`. -/
def primosPequenos : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
  101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
  197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
  311, 313, 317]

/-- `p` tem alguma potência `pⁱ ≤ 105933`, `i ≥ 1`, congruente a `1` módulo 19 (para `p > 325` só
`i = 1` é possível). -/
def condicao (p : ℕ) : Bool :=
  if p ≤ 325 then
    (List.range 18).any fun i => decide (1 ≤ i) && decide (p ^ i ≤ 105933) && decide (p ^ i % 19 = 1)
  else decide (p % 19 = 1)

/-- O teste conferido pelo kernel, com uma lista `L` de primos certificados. -/
def teste (L : List ℕ) (p : ℕ) : Bool :=
  !(condicao p) || L.contains p || p == 1 ||
    primosPequenos.any fun q => decide (q < p) && decide (p % q = 0)

theorem teste_mono {L L' : List ℕ} (h : ∀ x ∈ L, x ∈ L') {p : ℕ} (hp : teste L p = true) :
    teste L' p = true := by
  simp only [teste, Bool.or_eq_true, List.contains_iff_mem, beq_iff_eq] at hp ⊢
  rcases hp with ((h1 | h2) | h3) | h4
  · exact Or.inl (Or.inl (Or.inl h1))
  · exact Or.inl (Or.inl (Or.inr (h _ h2)))
  · exact Or.inl (Or.inr h3)
  · exact Or.inr h4

theorem teste_0 : ∀ p, 0 ≤ p → p < 1000 → teste [7, 11, 37, 113, 151, 191, 227, 229, 419, 457, 571, 647, 761] p = true := by
  decide +kernel

theorem sub_0 : ∀ x ∈ ([7, 11, 37, 113, 151, 191, 227, 229, 419, 457, 571, 647, 761] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_1 : ∀ p, 1000 ≤ p → p < 2000 → teste [1103, 1217, 1483, 1559, 1597, 1787, 1901] p = true := by
  decide +kernel

theorem sub_1 : ∀ x ∈ ([1103, 1217, 1483, 1559, 1597, 1787, 1901] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_2 : ∀ p, 2000 ≤ p → p < 3000 → teste [2053, 2129, 2243, 2281, 2357, 2699, 2851, 2927] p = true := by
  decide +kernel

theorem sub_2 : ∀ x ∈ ([2053, 2129, 2243, 2281, 2357, 2699, 2851, 2927] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_3 : ∀ p, 3000 ≤ p → p < 4000 → teste [3041, 3079, 3307, 3877] p = true := by
  decide +kernel

theorem sub_3 : ∀ x ∈ ([3041, 3079, 3307, 3877] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_4 : ∀ p, 4000 ≤ p → p < 5000 → teste [4219, 4409, 4447, 4523, 4561, 4637, 4751, 4789, 4903] p = true := by
  decide +kernel

theorem sub_4 : ∀ x ∈ ([4219, 4409, 4447, 4523, 4561, 4637, 4751, 4789, 4903] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_5 : ∀ p, 5000 ≤ p → p < 6000 → teste [5701] p = true := by
  decide +kernel

theorem sub_5 : ∀ x ∈ ([5701] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_6 : ∀ p, 6000 ≤ p → p < 7000 → teste [6043, 6271, 6689, 6803, 6841, 6917] p = true := by
  decide +kernel

theorem sub_6 : ∀ x ∈ ([6043, 6271, 6689, 6803, 6841, 6917] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_7 : ∀ p, 7000 ≤ p → p < 8000 → teste [7069, 7297, 7411, 7487, 7639, 7753, 7829, 7867] p = true := by
  decide +kernel

theorem sub_7 : ∀ x ∈ ([7069, 7297, 7411, 7487, 7639, 7753, 7829, 7867] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_8 : ∀ p, 8000 ≤ p → p < 9000 → teste [8171, 8209, 8513, 8627, 8741, 8779, 8893, 8969] p = true := by
  decide +kernel

theorem sub_8 : ∀ x ∈ ([8171, 8209, 8513, 8627, 8741, 8779, 8893, 8969] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_9 : ∀ p, 9000 ≤ p → p < 10000 → teste [9007, 9311, 9349, 9463, 9539, 9767] p = true := by
  decide +kernel

theorem sub_9 : ∀ x ∈ ([9007, 9311, 9349, 9463, 9539, 9767] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_10 : ∀ p, 10000 ≤ p → p < 11000 → teste [10223, 10337, 10831] p = true := by
  decide +kernel

theorem sub_10 : ∀ x ∈ ([10223, 10337, 10831] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_11 : ∀ p, 11000 ≤ p → p < 12000 → teste [11059, 11173, 11287, 11743, 11933, 11971] p = true := by
  decide +kernel

theorem sub_11 : ∀ x ∈ ([11059, 11173, 11287, 11743, 11933, 11971] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_12 : ∀ p, 12000 ≤ p → p < 13000 → teste [12161, 12503, 12541, 12959] p = true := by
  decide +kernel

theorem sub_12 : ∀ x ∈ ([12161, 12503, 12541, 12959] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_13 : ∀ p, 13000 ≤ p → p < 14000 → teste [13187, 13339, 13567, 13681, 13757] p = true := by
  decide +kernel

theorem sub_13 : ∀ x ∈ ([13187, 13339, 13567, 13681, 13757] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_14 : ∀ p, 14000 ≤ p → p < 15000 → teste [14251, 14327, 14479, 14593, 14669, 14783, 14821, 14897] p = true := by
  decide +kernel

theorem sub_14 : ∀ x ∈ ([14251, 14327, 14479, 14593, 14669, 14783, 14821, 14897] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_15 : ∀ p, 15000 ≤ p → p < 16000 → teste [15277, 15391, 15467, 15581, 15619, 15733, 15809, 15923] p = true := by
  decide +kernel

theorem sub_15 : ∀ x ∈ ([15277, 15391, 15467, 15581, 15619, 15733, 15809, 15923] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_16 : ∀ p, 16000 ≤ p → p < 17000 → teste [16189, 16417, 16493, 16607, 16759, 16987] p = true := by
  decide +kernel

theorem sub_16 : ∀ x ∈ ([16189, 16417, 16493, 16607, 16759, 16987] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_17 : ∀ p, 17000 ≤ p → p < 18000 → teste [17291, 17443, 17519, 17747] p = true := by
  decide +kernel

theorem sub_17 : ∀ x ∈ ([17291, 17443, 17519, 17747] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_18 : ∀ p, 18000 ≤ p → p < 19000 → teste [18013, 18089, 18127, 18583, 18773] p = true := by
  decide +kernel

theorem sub_18 : ∀ x ∈ ([18013, 18089, 18127, 18583, 18773] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_19 : ∀ p, 19000 ≤ p → p < 20000 → teste [19001, 19267, 19381, 19457, 19571, 19609, 19913] p = true := by
  decide +kernel

theorem sub_19 : ∀ x ∈ ([19001, 19267, 19381, 19457, 19571, 19609, 19913] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_20 : ∀ p, 20000 ≤ p → p < 21000 → teste [20369, 20407, 20483, 20521, 20749, 20939] p = true := by
  decide +kernel

theorem sub_20 : ∀ x ∈ ([20369, 20407, 20483, 20521, 20749, 20939] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_21 : ∀ p, 21000 ≤ p → p < 22000 → teste [21319, 21433, 21661, 21737, 21851] p = true := by
  decide +kernel

theorem sub_21 : ∀ x ∈ ([21319, 21433, 21661, 21737, 21851] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_22 : ∀ p, 22000 ≤ p → p < 23000 → teste [22003, 22079, 22193, 22307, 22573, 22877] p = true := by
  decide +kernel

theorem sub_22 : ∀ x ∈ ([22003, 22079, 22193, 22307, 22573, 22877] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_23 : ∀ p, 23000 ≤ p → p < 24000 → teste [23029, 23143, 23333, 23371, 23447, 23561, 23599, 23789, 23827] p = true := by
  decide +kernel

theorem sub_23 : ∀ x ∈ ([23029, 23143, 23333, 23371, 23447, 23561, 23599, 23789, 23827] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_24 : ∀ p, 24000 ≤ p → p < 25000 → teste [24169, 24359, 24473, 24967] p = true := by
  decide +kernel

theorem sub_24 : ∀ x ∈ ([24169, 24359, 24473, 24967] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_25 : ∀ p, 25000 ≤ p → p < 26000 → teste [25309, 25423, 25537, 25841] p = true := by
  decide +kernel

theorem sub_25 : ∀ x ∈ ([25309, 25423, 25537, 25841] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_26 : ∀ p, 26000 ≤ p → p < 27000 → teste [26107, 26183, 26297, 26449, 26981] p = true := by
  decide +kernel

theorem sub_26 : ∀ x ∈ ([26107, 26183, 26297, 26449, 26981] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_27 : ∀ p, 27000 ≤ p → p < 28000 → teste [27361, 27437, 27551, 27779, 27817, 27893] p = true := by
  decide +kernel

theorem sub_27 : ∀ x ∈ ([27361, 27437, 27551, 27779, 27817, 27893] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_28 : ∀ p, 28000 ≤ p → p < 29000 → teste [28349, 28387, 28463, 28729, 28843] p = true := by
  decide +kernel

theorem sub_28 : ∀ x ∈ ([28349, 28387, 28463, 28729, 28843] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_29 : ∀ p, 29000 ≤ p → p < 30000 → teste [29033, 29147, 29527, 29641, 29717, 29983] p = true := by
  decide +kernel

theorem sub_29 : ∀ x ∈ ([29033, 29147, 29527, 29641, 29717, 29983] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_30 : ∀ p, 30000 ≤ p → p < 31000 → teste [30059, 30097, 30211, 30553, 30781, 30971] p = true := by
  decide +kernel

theorem sub_30 : ∀ x ∈ ([30059, 30097, 30211, 30553, 30781, 30971] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_31 : ∀ p, 31000 ≤ p → p < 32000 → teste [31123, 31237, 31541, 31769, 31883] p = true := by
  decide +kernel

theorem sub_31 : ∀ x ∈ ([31123, 31237, 31541, 31769, 31883] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_32 : ∀ p, 32000 ≤ p → p < 33000 → teste [32377, 32491, 32719, 32833, 32909] p = true := by
  decide +kernel

theorem sub_32 : ∀ x ∈ ([32377, 32491, 32719, 32833, 32909] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_33 : ∀ p, 33000 ≤ p → p < 34000 → teste [33023, 33289, 33403, 33479] p = true := by
  decide +kernel

theorem sub_33 : ∀ x ∈ ([33023, 33289, 33403, 33479] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_34 : ∀ p, 34000 ≤ p → p < 35000 → teste [34429, 34543, 34847, 34961] p = true := by
  decide +kernel

theorem sub_34 : ∀ x ∈ ([34429, 34543, 34847, 34961] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_35 : ∀ p, 35000 ≤ p → p < 36000 → teste [35227, 35531, 35569, 35759, 35797, 35911] p = true := by
  decide +kernel

theorem sub_35 : ∀ x ∈ ([35227, 35531, 35569, 35759, 35797, 35911] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_36 : ∀ p, 36000 ≤ p → p < 37000 → teste [36671, 36709, 36899] p = true := by
  decide +kernel

theorem sub_36 : ∀ x ∈ ([36671, 36709, 36899] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_37 : ∀ p, 37000 ≤ p → p < 38000 → teste [37013, 37507, 37811, 37963] p = true := by
  decide +kernel

theorem sub_37 : ∀ x ∈ ([37013, 37507, 37811, 37963] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_38 : ∀ p, 38000 ≤ p → p < 39000 → teste [38039, 38153, 38609, 38723] p = true := by
  decide +kernel

theorem sub_38 : ∀ x ∈ ([38039, 38153, 38609, 38723] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_39 : ∀ p, 39000 ≤ p → p < 40000 → teste [39103, 39217, 39293, 39521, 39749, 39863, 39901] p = true := by
  decide +kernel

theorem sub_39 : ∀ x ∈ ([39103, 39217, 39293, 39521, 39749, 39863, 39901] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_40 : ∀ p, 40000 ≤ p → p < 41000 → teste [40129, 40357, 40433, 40471, 40699, 40813, 40927] p = true := by
  decide +kernel

theorem sub_40 : ∀ x ∈ ([40129, 40357, 40433, 40471, 40699, 40813, 40927] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_41 : ∀ p, 41000 ≤ p → p < 42000 → teste [41117, 41231, 41269, 41611, 41687, 41801, 41953] p = true := by
  decide +kernel

theorem sub_41 : ∀ x ∈ ([41117, 41231, 41269, 41611, 41687, 41801, 41953] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_42 : ∀ p, 42000 ≤ p → p < 43000 → teste [42181, 42257, 42409, 42751, 42979] p = true := by
  decide +kernel

theorem sub_42 : ∀ x ∈ ([42181, 42257, 42409, 42751, 42979] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_43 : ∀ p, 43000 ≤ p → p < 44000 → teste [43093, 43207, 43283, 43321, 43397, 43777, 43853, 43891] p = true := by
  decide +kernel

theorem sub_43 : ∀ x ∈ ([43093, 43207, 43283, 43321, 43397, 43777, 43853, 43891] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_44 : ∀ p, 44000 ≤ p → p < 45000 → teste [44119, 44537, 44651, 44879, 44917] p = true := by
  decide +kernel

theorem sub_44 : ∀ x ∈ ([44119, 44537, 44651, 44879, 44917] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_45 : ∀ p, 45000 ≤ p → p < 46000 → teste [45259, 45677, 45943] p = true := by
  decide +kernel

theorem sub_45 : ∀ x ∈ ([45259, 45677, 45943] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_46 : ∀ p, 46000 ≤ p → p < 47000 → teste [46133, 46171, 46399, 46589, 46703, 46817] p = true := by
  decide +kernel

theorem sub_46 : ∀ x ∈ ([46133, 46171, 46399, 46589, 46703, 46817] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_47 : ∀ p, 47000 ≤ p → p < 48000 → teste [47387, 47501, 47653, 47843, 47881] p = true := by
  decide +kernel

theorem sub_47 : ∀ x ∈ ([47387, 47501, 47653, 47843, 47881] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_48 : ∀ p, 48000 ≤ p → p < 49000 → teste [48109, 48299, 48337, 48413, 48527, 48679, 48869, 48907] p = true := by
  decide +kernel

theorem sub_48 : ∀ x ∈ ([48109, 48299, 48337, 48413, 48527, 48679, 48869, 48907] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_49 : ∀ p, 49000 ≤ p → p < 50000 → teste [49211, 49363, 49477, 49667] p = true := by
  decide +kernel

theorem sub_49 : ∀ x ∈ ([49211, 49363, 49477, 49667] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_50 : ∀ p, 50000 ≤ p → p < 51000 → teste [50047, 50123, 50503] p = true := by
  decide +kernel

theorem sub_50 : ∀ x ∈ ([50047, 50123, 50503] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_51 : ∀ p, 51000 ≤ p → p < 52000 → teste [51263, 51719, 51871] p = true := by
  decide +kernel

theorem sub_51 : ∀ x ∈ ([51263, 51719, 51871] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_52 : ∀ p, 52000 ≤ p → p < 53000 → teste [52289, 52517, 52631, 52783, 52859, 52973] p = true := by
  decide +kernel

theorem sub_52 : ∀ x ∈ ([52289, 52517, 52631, 52783, 52859, 52973] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_53 : ∀ p, 53000 ≤ p → p < 54000 → teste [53087, 53201, 53239, 53353, 53657, 53923] p = true := by
  decide +kernel

theorem sub_53 : ∀ x ∈ ([53087, 53201, 53239, 53353, 53657, 53923] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_54 : ∀ p, 54000 ≤ p → p < 55000 → teste [54037, 54151, 54493, 54721, 54949] p = true := by
  decide +kernel

theorem sub_54 : ∀ x ∈ ([54037, 54151, 54493, 54721, 54949] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_55 : ∀ p, 55000 ≤ p → p < 56000 → teste [55291, 55633, 55823] p = true := by
  decide +kernel

theorem sub_55 : ∀ x ∈ ([55291, 55633, 55823] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_56 : ∀ p, 56000 ≤ p → p < 57000 → teste [56393, 56431, 56659, 56773, 56963] p = true := by
  decide +kernel

theorem sub_56 : ∀ x ∈ ([56393, 56431, 56659, 56773, 56963] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_57 : ∀ p, 57000 ≤ p → p < 58000 → teste [57077, 57191, 57457, 57571] p = true := by
  decide +kernel

theorem sub_57 : ∀ x ∈ ([57077, 57191, 57457, 57571] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_58 : ∀ p, 58000 ≤ p → p < 59000 → teste [58027, 58217, 58369, 58711, 58787, 58901] p = true := by
  decide +kernel

theorem sub_58 : ∀ x ∈ ([58027, 58217, 58369, 58711, 58787, 58901] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_59 : ∀ p, 59000 ≤ p → p < 60000 → teste [59053, 59167, 59243, 59281, 59357, 59471, 59509, 59699] p = true := by
  decide +kernel

theorem sub_59 : ∀ x ∈ ([59053, 59167, 59243, 59281, 59357, 59471, 59509, 59699] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_60 : ∀ p, 60000 ≤ p → p < 61000 → teste [60041, 60383, 60497, 60611, 60649, 60763, 60953] p = true := by
  decide +kernel

theorem sub_60 : ∀ x ∈ ([60041, 60383, 60497, 60611, 60649, 60763, 60953] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_61 : ∀ p, 61000 ≤ p → p < 62000 → teste [61333, 61409, 61561, 61637, 61751, 61979] p = true := by
  decide +kernel

theorem sub_61 : ∀ x ∈ ([61333, 61409, 61561, 61637, 61751, 61979] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_62 : ∀ p, 62000 ≤ p → p < 63000 → teste [62017, 62131, 62207, 62473, 62549, 62701, 62929] p = true := by
  decide +kernel

theorem sub_62 : ∀ x ∈ ([62017, 62131, 62207, 62473, 62549, 62701, 62929] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_63 : ∀ p, 63000 ≤ p → p < 64000 → teste [63347, 63499, 63689, 63727, 63803, 63841] p = true := by
  decide +kernel

theorem sub_63 : ∀ x ∈ ([63347, 63499, 63689, 63727, 63803, 63841] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_64 : ∀ p, 64000 ≤ p → p < 65000 → teste [64373, 64601] p = true := by
  decide +kernel

theorem sub_64 : ∀ x ∈ ([64373, 64601] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_65 : ∀ p, 65000 ≤ p → p < 66000 → teste [65171, 65323, 65437, 65551] p = true := by
  decide +kernel

theorem sub_65 : ∀ x ∈ ([65171, 65323, 65437, 65551] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_66 : ∀ p, 66000 ≤ p → p < 67000 → teste [66083, 66463, 66653, 66919] p = true := by
  decide +kernel

theorem sub_66 : ∀ x ∈ ([66083, 66463, 66653, 66919] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_67 : ∀ p, 67000 ≤ p → p < 68000 → teste [67033, 67261, 67489, 67679] p = true := by
  decide +kernel

theorem sub_67 : ∀ x ∈ ([67033, 67261, 67489, 67679] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_68 : ∀ p, 68000 ≤ p → p < 69000 → teste [68059, 68477, 68743, 68819] p = true := by
  decide +kernel

theorem sub_68 : ∀ x ∈ ([68059, 68477, 68743, 68819] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_69 : ∀ p, 69000 ≤ p → p < 70000 → teste [69313, 69389, 69427, 69959, 69997] p = true := by
  decide +kernel

theorem sub_69 : ∀ x ∈ ([69313, 69389, 69427, 69959, 69997] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_70 : ∀ p, 70000 ≤ p → p < 71000 → teste [70111, 70529] p = true := by
  decide +kernel

theorem sub_70 : ∀ x ∈ ([70111, 70529] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_71 : ∀ p, 71000 ≤ p → p < 72000 → teste [71023, 71327, 71479, 71593, 71707, 71821] p = true := by
  decide +kernel

theorem sub_71 : ∀ x ∈ ([71023, 71327, 71479, 71593, 71707, 71821] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_72 : ∀ p, 72000 ≤ p → p < 73000 → teste [72277, 72353, 72467, 72733, 72923] p = true := by
  decide +kernel

theorem sub_72 : ∀ x ∈ ([72277, 72353, 72467, 72733, 72923] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_73 : ∀ p, 73000 ≤ p → p < 74000 → teste [73037, 73189, 73303, 73379, 73417, 73607, 73721] p = true := by
  decide +kernel

theorem sub_73 : ∀ x ∈ ([73037, 73189, 73303, 73379, 73417, 73607, 73721] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_74 : ∀ p, 74000 ≤ p → p < 75000 → teste [74101, 74177, 74747, 74861] p = true := by
  decide +kernel

theorem sub_74 : ∀ x ∈ ([74101, 74177, 74747, 74861] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_75 : ∀ p, 75000 ≤ p → p < 76000 → teste [75013, 75431, 75583, 75659, 75773] p = true := by
  decide +kernel

theorem sub_75 : ∀ x ∈ ([75013, 75431, 75583, 75659, 75773] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_76 : ∀ p, 76000 ≤ p → p < 77000 → teste [76001, 76039, 76343, 76837, 76913] p = true := by
  decide +kernel

theorem sub_76 : ∀ x ∈ ([76001, 76039, 76343, 76837, 76913] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_77 : ∀ p, 77000 ≤ p → p < 78000 → teste [77141, 77369, 77521, 77711, 77863, 77977] p = true := by
  decide +kernel

theorem sub_77 : ∀ x ∈ ([77141, 77369, 77521, 77711, 77863, 77977] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_78 : ∀ p, 78000 ≤ p → p < 79000 → teste [78167, 78509, 78623, 78737, 78889] p = true := by
  decide +kernel

theorem sub_78 : ∀ x ∈ ([78167, 78509, 78623, 78737, 78889] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_79 : ∀ p, 79000 ≤ p → p < 80000 → teste [79193, 79231, 79687, 79801] p = true := by
  decide +kernel

theorem sub_79 : ∀ x ∈ ([79193, 79231, 79687, 79801] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_80 : ∀ p, 80000 ≤ p → p < 81000 → teste [80447, 80599, 80713, 80789] p = true := by
  decide +kernel

theorem sub_80 : ∀ x ∈ ([80447, 80599, 80713, 80789] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_81 : ∀ p, 81000 ≤ p → p < 82000 → teste [81017, 81131, 81283, 81359, 81701, 81853, 81929, 81967] p = true := by
  decide +kernel

theorem sub_81 : ∀ x ∈ ([81017, 81131, 81283, 81359, 81701, 81853, 81929, 81967] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_82 : ∀ p, 82000 ≤ p → p < 83000 → teste [82499, 82613, 82651, 82727] p = true := by
  decide +kernel

theorem sub_82 : ∀ x ∈ ([82499, 82613, 82651, 82727] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_83 : ∀ p, 83000 ≤ p → p < 84000 → teste [83221, 83449, 83563, 83639, 83791] p = true := by
  decide +kernel

theorem sub_83 : ∀ x ∈ ([83221, 83449, 83563, 83639, 83791] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_84 : ∀ p, 84000 ≤ p → p < 85000 → teste [84247, 84437, 84551, 84589] p = true := by
  decide +kernel

theorem sub_84 : ∀ x ∈ ([84247, 84437, 84551, 84589] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_85 : ∀ p, 85000 ≤ p → p < 86000 → teste [85121, 85159, 85577, 85691, 85843] p = true := by
  decide +kernel

theorem sub_85 : ∀ x ∈ ([85121, 85159, 85577, 85691, 85843] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_86 : ∀ p, 86000 ≤ p → p < 87000 → teste [86413, 86869] p = true := by
  decide +kernel

theorem sub_86 : ∀ x ∈ ([86413, 86869] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_87 : ∀ p, 87000 ≤ p → p < 88000 → teste [87211, 87553, 87629, 87743] p = true := by
  decide +kernel

theorem sub_87 : ∀ x ∈ ([87211, 87553, 87629, 87743] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_88 : ∀ p, 88000 ≤ p → p < 89000 → teste [88237, 88427, 88807, 88883, 88997] p = true := by
  decide +kernel

theorem sub_88 : ∀ x ∈ ([88237, 88427, 88807, 88883, 88997] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_89 : ∀ p, 89000 ≤ p → p < 90000 → teste [89491, 89567, 89681, 89833, 89909] p = true := by
  decide +kernel

theorem sub_89 : ∀ x ∈ ([89491, 89567, 89681, 89833, 89909] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_90 : ∀ p, 90000 ≤ p → p < 91000 → teste [90023, 90289, 90403, 90631, 90821] p = true := by
  decide +kernel

theorem sub_90 : ∀ x ∈ ([90023, 90289, 90403, 90631, 90821] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_91 : ∀ p, 91000 ≤ p → p < 92000 → teste [91163, 91733, 91771, 91961] p = true := by
  decide +kernel

theorem sub_91 : ∀ x ∈ ([91163, 91733, 91771, 91961] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_92 : ∀ p, 92000 ≤ p → p < 93000 → teste [92189, 92227, 92569, 92683, 92987] p = true := by
  decide +kernel

theorem sub_92 : ∀ x ∈ ([92189, 92227, 92569, 92683, 92987] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_93 : ∀ p, 93000 ≤ p → p < 94000 → teste [93139, 93253, 93329, 93481, 93557, 93937] p = true := by
  decide +kernel

theorem sub_93 : ∀ x ∈ ([93139, 93253, 93329, 93481, 93557, 93937] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_94 : ∀ p, 94000 ≤ p → p < 95000 → teste [94583, 94621, 94811, 94849] p = true := by
  decide +kernel

theorem sub_94 : ∀ x ∈ ([94583, 94621, 94811, 94849] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_95 : ∀ p, 95000 ≤ p → p < 96000 → teste [95153, 95191, 95267, 95419, 95723, 95989] p = true := by
  decide +kernel

theorem sub_95 : ∀ x ∈ ([95153, 95191, 95267, 95419, 95723, 95989] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_96 : ∀ p, 96000 ≤ p → p < 97000 → teste [96179, 96293, 96331, 96749, 96787] p = true := by
  decide +kernel

theorem sub_96 : ∀ x ∈ ([96179, 96293, 96331, 96749, 96787] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_97 : ∀ p, 97000 ≤ p → p < 98000 → teste [97547, 97813, 97927] p = true := by
  decide +kernel

theorem sub_97 : ∀ x ∈ ([97547, 97813, 97927] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_98 : ∀ p, 98000 ≤ p → p < 99000 → teste [98041, 98269, 98459, 98573, 98801, 98953] p = true := by
  decide +kernel

theorem sub_98 : ∀ x ∈ ([98041, 98269, 98459, 98573, 98801, 98953] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_99 : ∀ p, 99000 ≤ p → p < 100000 → teste [99181, 99257, 99371, 99409, 99523, 99713] p = true := by
  decide +kernel

theorem sub_99 : ∀ x ∈ ([99181, 99257, 99371, 99409, 99523, 99713] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_100 : ∀ p, 100000 ≤ p → p < 101000 → teste [100169, 100207, 100511, 100549, 100853] p = true := by
  decide +kernel

theorem sub_100 : ∀ x ∈ ([100169, 100207, 100511, 100549, 100853] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_101 : ∀ p, 101000 ≤ p → p < 102000 → teste [101081, 101119, 101347, 101537, 101879, 101917] p = true := by
  decide +kernel

theorem sub_101 : ∀ x ∈ ([101081, 101119, 101347, 101537, 101879, 101917] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_102 : ∀ p, 102000 ≤ p → p < 103000 → teste [102031, 102107, 102259, 102563, 102677, 102829] p = true := by
  decide +kernel

theorem sub_102 : ∀ x ∈ ([102031, 102107, 102259, 102563, 102677, 102829] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_103 : ∀ p, 103000 ≤ p → p < 104000 → teste [103171, 103399, 103703, 103969] p = true := by
  decide +kernel

theorem sub_103 : ∀ x ∈ ([103171, 103399, 103703, 103969] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_104 : ∀ p, 104000 ≤ p → p < 105000 → teste [104311, 104729] p = true := by
  decide +kernel

theorem sub_104 : ∀ x ∈ ([104311, 104729] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

theorem teste_105 : ∀ p, 105000 ≤ p → p < 105934 → teste [105071, 105337, 105527, 105907] p = true := by
  decide +kernel

theorem sub_105 : ∀ x ∈ ([105071, 105337, 105527, 105907] : List ℕ), x ∈ primosCertificados := by
  decide +kernel

/-- **Exceções**: `teste primosCertificados p` vale para todo `p ≤ 105933`. -/
theorem excecoes (p : ℕ) (hp : p ≤ 105933) : teste primosCertificados p = true := by
  rcases lt_or_ge p 1000 with h0 | h0
  · exact teste_mono sub_0 (teste_0 p (by omega) h0)
  rcases lt_or_ge p 2000 with h1 | h1
  · exact teste_mono sub_1 (teste_1 p (by omega) h1)
  rcases lt_or_ge p 3000 with h2 | h2
  · exact teste_mono sub_2 (teste_2 p (by omega) h2)
  rcases lt_or_ge p 4000 with h3 | h3
  · exact teste_mono sub_3 (teste_3 p (by omega) h3)
  rcases lt_or_ge p 5000 with h4 | h4
  · exact teste_mono sub_4 (teste_4 p (by omega) h4)
  rcases lt_or_ge p 6000 with h5 | h5
  · exact teste_mono sub_5 (teste_5 p (by omega) h5)
  rcases lt_or_ge p 7000 with h6 | h6
  · exact teste_mono sub_6 (teste_6 p (by omega) h6)
  rcases lt_or_ge p 8000 with h7 | h7
  · exact teste_mono sub_7 (teste_7 p (by omega) h7)
  rcases lt_or_ge p 9000 with h8 | h8
  · exact teste_mono sub_8 (teste_8 p (by omega) h8)
  rcases lt_or_ge p 10000 with h9 | h9
  · exact teste_mono sub_9 (teste_9 p (by omega) h9)
  rcases lt_or_ge p 11000 with h10 | h10
  · exact teste_mono sub_10 (teste_10 p (by omega) h10)
  rcases lt_or_ge p 12000 with h11 | h11
  · exact teste_mono sub_11 (teste_11 p (by omega) h11)
  rcases lt_or_ge p 13000 with h12 | h12
  · exact teste_mono sub_12 (teste_12 p (by omega) h12)
  rcases lt_or_ge p 14000 with h13 | h13
  · exact teste_mono sub_13 (teste_13 p (by omega) h13)
  rcases lt_or_ge p 15000 with h14 | h14
  · exact teste_mono sub_14 (teste_14 p (by omega) h14)
  rcases lt_or_ge p 16000 with h15 | h15
  · exact teste_mono sub_15 (teste_15 p (by omega) h15)
  rcases lt_or_ge p 17000 with h16 | h16
  · exact teste_mono sub_16 (teste_16 p (by omega) h16)
  rcases lt_or_ge p 18000 with h17 | h17
  · exact teste_mono sub_17 (teste_17 p (by omega) h17)
  rcases lt_or_ge p 19000 with h18 | h18
  · exact teste_mono sub_18 (teste_18 p (by omega) h18)
  rcases lt_or_ge p 20000 with h19 | h19
  · exact teste_mono sub_19 (teste_19 p (by omega) h19)
  rcases lt_or_ge p 21000 with h20 | h20
  · exact teste_mono sub_20 (teste_20 p (by omega) h20)
  rcases lt_or_ge p 22000 with h21 | h21
  · exact teste_mono sub_21 (teste_21 p (by omega) h21)
  rcases lt_or_ge p 23000 with h22 | h22
  · exact teste_mono sub_22 (teste_22 p (by omega) h22)
  rcases lt_or_ge p 24000 with h23 | h23
  · exact teste_mono sub_23 (teste_23 p (by omega) h23)
  rcases lt_or_ge p 25000 with h24 | h24
  · exact teste_mono sub_24 (teste_24 p (by omega) h24)
  rcases lt_or_ge p 26000 with h25 | h25
  · exact teste_mono sub_25 (teste_25 p (by omega) h25)
  rcases lt_or_ge p 27000 with h26 | h26
  · exact teste_mono sub_26 (teste_26 p (by omega) h26)
  rcases lt_or_ge p 28000 with h27 | h27
  · exact teste_mono sub_27 (teste_27 p (by omega) h27)
  rcases lt_or_ge p 29000 with h28 | h28
  · exact teste_mono sub_28 (teste_28 p (by omega) h28)
  rcases lt_or_ge p 30000 with h29 | h29
  · exact teste_mono sub_29 (teste_29 p (by omega) h29)
  rcases lt_or_ge p 31000 with h30 | h30
  · exact teste_mono sub_30 (teste_30 p (by omega) h30)
  rcases lt_or_ge p 32000 with h31 | h31
  · exact teste_mono sub_31 (teste_31 p (by omega) h31)
  rcases lt_or_ge p 33000 with h32 | h32
  · exact teste_mono sub_32 (teste_32 p (by omega) h32)
  rcases lt_or_ge p 34000 with h33 | h33
  · exact teste_mono sub_33 (teste_33 p (by omega) h33)
  rcases lt_or_ge p 35000 with h34 | h34
  · exact teste_mono sub_34 (teste_34 p (by omega) h34)
  rcases lt_or_ge p 36000 with h35 | h35
  · exact teste_mono sub_35 (teste_35 p (by omega) h35)
  rcases lt_or_ge p 37000 with h36 | h36
  · exact teste_mono sub_36 (teste_36 p (by omega) h36)
  rcases lt_or_ge p 38000 with h37 | h37
  · exact teste_mono sub_37 (teste_37 p (by omega) h37)
  rcases lt_or_ge p 39000 with h38 | h38
  · exact teste_mono sub_38 (teste_38 p (by omega) h38)
  rcases lt_or_ge p 40000 with h39 | h39
  · exact teste_mono sub_39 (teste_39 p (by omega) h39)
  rcases lt_or_ge p 41000 with h40 | h40
  · exact teste_mono sub_40 (teste_40 p (by omega) h40)
  rcases lt_or_ge p 42000 with h41 | h41
  · exact teste_mono sub_41 (teste_41 p (by omega) h41)
  rcases lt_or_ge p 43000 with h42 | h42
  · exact teste_mono sub_42 (teste_42 p (by omega) h42)
  rcases lt_or_ge p 44000 with h43 | h43
  · exact teste_mono sub_43 (teste_43 p (by omega) h43)
  rcases lt_or_ge p 45000 with h44 | h44
  · exact teste_mono sub_44 (teste_44 p (by omega) h44)
  rcases lt_or_ge p 46000 with h45 | h45
  · exact teste_mono sub_45 (teste_45 p (by omega) h45)
  rcases lt_or_ge p 47000 with h46 | h46
  · exact teste_mono sub_46 (teste_46 p (by omega) h46)
  rcases lt_or_ge p 48000 with h47 | h47
  · exact teste_mono sub_47 (teste_47 p (by omega) h47)
  rcases lt_or_ge p 49000 with h48 | h48
  · exact teste_mono sub_48 (teste_48 p (by omega) h48)
  rcases lt_or_ge p 50000 with h49 | h49
  · exact teste_mono sub_49 (teste_49 p (by omega) h49)
  rcases lt_or_ge p 51000 with h50 | h50
  · exact teste_mono sub_50 (teste_50 p (by omega) h50)
  rcases lt_or_ge p 52000 with h51 | h51
  · exact teste_mono sub_51 (teste_51 p (by omega) h51)
  rcases lt_or_ge p 53000 with h52 | h52
  · exact teste_mono sub_52 (teste_52 p (by omega) h52)
  rcases lt_or_ge p 54000 with h53 | h53
  · exact teste_mono sub_53 (teste_53 p (by omega) h53)
  rcases lt_or_ge p 55000 with h54 | h54
  · exact teste_mono sub_54 (teste_54 p (by omega) h54)
  rcases lt_or_ge p 56000 with h55 | h55
  · exact teste_mono sub_55 (teste_55 p (by omega) h55)
  rcases lt_or_ge p 57000 with h56 | h56
  · exact teste_mono sub_56 (teste_56 p (by omega) h56)
  rcases lt_or_ge p 58000 with h57 | h57
  · exact teste_mono sub_57 (teste_57 p (by omega) h57)
  rcases lt_or_ge p 59000 with h58 | h58
  · exact teste_mono sub_58 (teste_58 p (by omega) h58)
  rcases lt_or_ge p 60000 with h59 | h59
  · exact teste_mono sub_59 (teste_59 p (by omega) h59)
  rcases lt_or_ge p 61000 with h60 | h60
  · exact teste_mono sub_60 (teste_60 p (by omega) h60)
  rcases lt_or_ge p 62000 with h61 | h61
  · exact teste_mono sub_61 (teste_61 p (by omega) h61)
  rcases lt_or_ge p 63000 with h62 | h62
  · exact teste_mono sub_62 (teste_62 p (by omega) h62)
  rcases lt_or_ge p 64000 with h63 | h63
  · exact teste_mono sub_63 (teste_63 p (by omega) h63)
  rcases lt_or_ge p 65000 with h64 | h64
  · exact teste_mono sub_64 (teste_64 p (by omega) h64)
  rcases lt_or_ge p 66000 with h65 | h65
  · exact teste_mono sub_65 (teste_65 p (by omega) h65)
  rcases lt_or_ge p 67000 with h66 | h66
  · exact teste_mono sub_66 (teste_66 p (by omega) h66)
  rcases lt_or_ge p 68000 with h67 | h67
  · exact teste_mono sub_67 (teste_67 p (by omega) h67)
  rcases lt_or_ge p 69000 with h68 | h68
  · exact teste_mono sub_68 (teste_68 p (by omega) h68)
  rcases lt_or_ge p 70000 with h69 | h69
  · exact teste_mono sub_69 (teste_69 p (by omega) h69)
  rcases lt_or_ge p 71000 with h70 | h70
  · exact teste_mono sub_70 (teste_70 p (by omega) h70)
  rcases lt_or_ge p 72000 with h71 | h71
  · exact teste_mono sub_71 (teste_71 p (by omega) h71)
  rcases lt_or_ge p 73000 with h72 | h72
  · exact teste_mono sub_72 (teste_72 p (by omega) h72)
  rcases lt_or_ge p 74000 with h73 | h73
  · exact teste_mono sub_73 (teste_73 p (by omega) h73)
  rcases lt_or_ge p 75000 with h74 | h74
  · exact teste_mono sub_74 (teste_74 p (by omega) h74)
  rcases lt_or_ge p 76000 with h75 | h75
  · exact teste_mono sub_75 (teste_75 p (by omega) h75)
  rcases lt_or_ge p 77000 with h76 | h76
  · exact teste_mono sub_76 (teste_76 p (by omega) h76)
  rcases lt_or_ge p 78000 with h77 | h77
  · exact teste_mono sub_77 (teste_77 p (by omega) h77)
  rcases lt_or_ge p 79000 with h78 | h78
  · exact teste_mono sub_78 (teste_78 p (by omega) h78)
  rcases lt_or_ge p 80000 with h79 | h79
  · exact teste_mono sub_79 (teste_79 p (by omega) h79)
  rcases lt_or_ge p 81000 with h80 | h80
  · exact teste_mono sub_80 (teste_80 p (by omega) h80)
  rcases lt_or_ge p 82000 with h81 | h81
  · exact teste_mono sub_81 (teste_81 p (by omega) h81)
  rcases lt_or_ge p 83000 with h82 | h82
  · exact teste_mono sub_82 (teste_82 p (by omega) h82)
  rcases lt_or_ge p 84000 with h83 | h83
  · exact teste_mono sub_83 (teste_83 p (by omega) h83)
  rcases lt_or_ge p 85000 with h84 | h84
  · exact teste_mono sub_84 (teste_84 p (by omega) h84)
  rcases lt_or_ge p 86000 with h85 | h85
  · exact teste_mono sub_85 (teste_85 p (by omega) h85)
  rcases lt_or_ge p 87000 with h86 | h86
  · exact teste_mono sub_86 (teste_86 p (by omega) h86)
  rcases lt_or_ge p 88000 with h87 | h87
  · exact teste_mono sub_87 (teste_87 p (by omega) h87)
  rcases lt_or_ge p 89000 with h88 | h88
  · exact teste_mono sub_88 (teste_88 p (by omega) h88)
  rcases lt_or_ge p 90000 with h89 | h89
  · exact teste_mono sub_89 (teste_89 p (by omega) h89)
  rcases lt_or_ge p 91000 with h90 | h90
  · exact teste_mono sub_90 (teste_90 p (by omega) h90)
  rcases lt_or_ge p 92000 with h91 | h91
  · exact teste_mono sub_91 (teste_91 p (by omega) h91)
  rcases lt_or_ge p 93000 with h92 | h92
  · exact teste_mono sub_92 (teste_92 p (by omega) h92)
  rcases lt_or_ge p 94000 with h93 | h93
  · exact teste_mono sub_93 (teste_93 p (by omega) h93)
  rcases lt_or_ge p 95000 with h94 | h94
  · exact teste_mono sub_94 (teste_94 p (by omega) h94)
  rcases lt_or_ge p 96000 with h95 | h95
  · exact teste_mono sub_95 (teste_95 p (by omega) h95)
  rcases lt_or_ge p 97000 with h96 | h96
  · exact teste_mono sub_96 (teste_96 p (by omega) h96)
  rcases lt_or_ge p 98000 with h97 | h97
  · exact teste_mono sub_97 (teste_97 p (by omega) h97)
  rcases lt_or_ge p 99000 with h98 | h98
  · exact teste_mono sub_98 (teste_98 p (by omega) h98)
  rcases lt_or_ge p 100000 with h99 | h99
  · exact teste_mono sub_99 (teste_99 p (by omega) h99)
  rcases lt_or_ge p 101000 with h100 | h100
  · exact teste_mono sub_100 (teste_100 p (by omega) h100)
  rcases lt_or_ge p 102000 with h101 | h101
  · exact teste_mono sub_101 (teste_101 p (by omega) h101)
  rcases lt_or_ge p 103000 with h102 | h102
  · exact teste_mono sub_102 (teste_102 p (by omega) h102)
  rcases lt_or_ge p 104000 with h103 | h103
  · exact teste_mono sub_103 (teste_103 p (by omega) h103)
  rcases lt_or_ge p 105000 with h104 | h104
  · exact teste_mono sub_104 (teste_104 p (by omega) h104)
  exact teste_mono sub_105 (teste_105 p (by omega) (by omega))


/-- Fora da lista, um primo `p ≠ 19` tem ordem módulo 19 maior que `log_p 105933`. -/
theorem ordem_grande {p : ℕ} (hple : p ≤ 105933) (hp : p.Prime) (hL : p ∉ primosCertificados)
    {i : ℕ} (hi : i ≤ Nat.log p 105933) (hi1 : 1 ≤ i) : p ^ i % 19 ≠ 1 := by
  intro heq
  have hpow : p ^ i ≤ 105933 := Nat.pow_le_of_le_log (by norm_num) hi
  have h2 := hp.two_le
  have hiR : i < 18 := by
    by_contra hc
    push Not at hc
    have : 2 ^ 18 ≤ p ^ i := (Nat.pow_le_pow_left h2 18).trans (Nat.pow_le_pow_right (by omega) hc)
    omega
  have hc : condicao p = true := by
    by_cases hsp : p ≤ 325
    · simp only [condicao, hsp, ite_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨i, hiR, ⟨hi1, hpow⟩, heq⟩
    · have hi1' : i = 1 := by
        by_contra hne
        have h2i : 2 ≤ i := by omega
        have : p ^ 2 ≤ p ^ i := Nat.pow_le_pow_right (by omega) h2i
        have : (325 + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
      subst hi1'
      simp only [condicao, hsp, ite_false, decide_eq_true_eq]
      simpa using heq
  have hok := excecoes p hple
  simp only [teste, hc, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.contains_iff_mem,
    beq_iff_eq, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with (hm | h1) | ⟨q, hq, hqp, hmod⟩
  · exact hL hm
  · subst h1; exact Nat.not_prime_one hp
  · have hq2 : 2 ≤ q := by
      simp only [primosPequenos, List.mem_cons, List.not_mem_nil, or_false] at hq
      omega
    rcases hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
variable (K) in
/-- **`𝓞(ℚ(ζ₁₉))` é principal.** -/
theorem pid_dezenove : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 19
  rw [minkowski_dezenove, ciclotomico_dezenove]
  intro p hple hp hpn
  have hple' : p ≤ 105933 := (Finset.mem_Icc.mp hple).2
  by_cases hL : p ∈ primosCertificados
  · unfold primosCertificados at hL
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_7
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_11
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_37
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_113
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_151
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_191
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_227
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_229
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_419
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_457
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_571
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_647
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_761
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_1103
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_1217
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_1483
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_1559
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_1597
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_1787
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_1901
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_2053
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_2129
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_2243
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_2281
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_2357
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_2699
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_2851
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_2927
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_3041
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_3079
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_3307
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_3877
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_4219
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_4409
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_4447
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_4523
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_4561
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_4637
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_4751
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_4789
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_4903
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_5701
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_6043
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_6271
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_6689
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_6803
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_6841
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_6917
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_7069
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_7297
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_7411
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_7487
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_7639
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_7753
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_7829
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_7867
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_8171
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_8209
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_8513
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_8627
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_8741
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_8779
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_8893
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_8969
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_9007
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_9311
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_9349
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_9463
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_9539
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_9767
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_10223
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_10337
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_10831
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_11059
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_11173
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_11287
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_11743
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_11933
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_11971
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_12161
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_12503
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_12541
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_12959
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_13187
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_13339
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_13567
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_13681
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_13757
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_14251
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_14327
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_14479
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_14593
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_14669
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_14783
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_14821
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_14897
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_15277
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_15391
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_15467
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_15581
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_15619
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_15733
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_15809
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_15923
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_16189
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_16417
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_16493
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_16607
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_16759
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_16987
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_17291
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertA.certificado_17443
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_17519
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_17747
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_18013
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_18089
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_18127
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_18583
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_18773
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_19001
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_19267
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_19381
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_19457
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_19571
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_19609
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_19913
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_20369
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_20407
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_20483
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_20521
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_20749
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_20939
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_21319
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_21433
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_21661
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_21737
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_21851
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_22003
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_22079
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_22193
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_22307
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_22573
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_22877
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_23029
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_23143
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_23333
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_23371
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_23447
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_23561
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_23599
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_23789
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_23827
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_24169
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_24359
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_24473
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_24967
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_25309
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_25423
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_25537
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_25841
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_26107
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_26183
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_26297
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_26449
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_26981
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_27361
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_27437
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_27551
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_27779
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_27817
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_27893
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_28349
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_28387
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_28463
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_28729
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_28843
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_29033
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_29147
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_29527
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_29641
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_29717
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_29983
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_30059
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_30097
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_30211
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_30553
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_30781
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_30971
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_31123
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_31237
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_31541
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_31769
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_31883
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_32377
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_32491
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_32719
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_32833
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_32909
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_33023
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_33289
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_33403
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_33479
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_34429
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_34543
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_34847
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_34961
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_35227
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_35531
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_35569
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_35759
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_35797
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_35911
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_36671
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_36709
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_36899
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_37013
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_37507
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_37811
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_37963
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_38039
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_38153
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_38609
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_38723
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertB.certificado_39103
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_39217
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_39293
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_39521
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_39749
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_39863
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_39901
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_40129
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_40357
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_40433
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_40471
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_40699
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_40813
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_40927
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_41117
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_41231
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_41269
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_41611
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_41687
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_41801
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_41953
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_42181
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_42257
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_42409
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_42751
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_42979
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_43093
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_43207
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_43283
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_43321
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_43397
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_43777
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_43853
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_43891
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_44119
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_44537
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_44651
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_44879
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_44917
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_45259
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_45677
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_45943
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_46133
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_46171
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_46399
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_46589
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_46703
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_46817
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_47387
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_47501
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_47653
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_47843
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_47881
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_48109
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_48299
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_48337
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_48413
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_48527
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_48679
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_48869
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_48907
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_49211
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_49363
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_49477
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_49667
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_50047
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_50123
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_50503
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_51263
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_51719
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_51871
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_52289
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_52517
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_52631
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_52783
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_52859
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_52973
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_53087
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_53201
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_53239
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_53353
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_53657
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_53923
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_54037
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_54151
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_54493
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_54721
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_54949
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_55291
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_55633
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_55823
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_56393
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_56431
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_56659
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_56773
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_56963
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_57077
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_57191
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_57457
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_57571
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_58027
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_58217
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_58369
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_58711
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_58787
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_58901
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_59053
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_59167
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_59243
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_59281
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_59357
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_59471
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertC.certificado_59509
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_59699
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_60041
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_60383
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_60497
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_60611
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_60649
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_60763
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_60953
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_61333
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_61409
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_61561
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_61637
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_61751
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_61979
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_62017
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_62131
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_62207
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_62473
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_62549
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_62701
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_62929
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_63347
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_63499
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_63689
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_63727
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_63803
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_63841
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_64373
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_64601
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_65171
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_65323
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_65437
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_65551
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_66083
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_66463
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_66653
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_66919
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_67033
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_67261
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_67489
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_67679
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_68059
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_68477
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_68743
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_68819
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_69313
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_69389
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_69427
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_69959
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_69997
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_70111
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_70529
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_71023
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_71327
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_71479
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_71593
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_71707
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_71821
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_72277
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_72353
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_72467
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_72733
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_72923
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_73037
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_73189
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_73303
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_73379
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_73417
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_73607
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_73721
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_74101
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_74177
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_74747
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_74861
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_75013
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_75431
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_75583
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_75659
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_75773
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_76001
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_76039
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_76343
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_76837
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_76913
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_77141
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_77369
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_77521
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_77711
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_77863
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_77977
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_78167
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_78509
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_78623
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_78737
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_78889
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_79193
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_79231
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_79687
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_79801
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_80447
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_80599
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_80713
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_80789
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_81017
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_81131
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_81283
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_81359
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_81701
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_81853
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_81929
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_81967
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertD.certificado_82499
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_82613
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_82651
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_82727
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_83221
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_83449
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_83563
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_83639
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_83791
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_84247
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_84437
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_84551
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_84589
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_85121
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_85159
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_85577
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_85691
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_85843
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_86413
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_86869
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_87211
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_87553
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_87629
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_87743
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_88237
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_88427
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_88807
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_88883
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_88997
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_89491
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_89567
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_89681
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_89833
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_89909
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_90023
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_90289
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_90403
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_90631
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_90821
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_91163
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_91733
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_91771
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_91961
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_92189
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_92227
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_92569
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_92683
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_92987
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_93139
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_93253
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_93329
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_93481
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_93557
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_93937
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_94583
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_94621
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_94811
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_94849
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_95153
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_95191
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_95267
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_95419
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_95723
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_95989
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_96179
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_96293
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_96331
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_96749
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_96787
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_97547
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_97813
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_97927
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_98041
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_98269
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_98459
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_98573
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_98801
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_98953
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_99181
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_99257
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_99371
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_99409
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_99523
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_99713
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_100169
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_100207
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_100511
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_100549
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_100853
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_101081
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_101119
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_101347
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_101537
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_101879
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_101917
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_102031
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_102107
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_102259
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_102563
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_102677
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_102829
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_103171
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_103399
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_103703
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_103969
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_104311
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_104729
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_105071
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_105337
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_105527
    rw [List.mem_cons] at hL
    rcases hL with rfl | hL
    · exact Or.inr ATK.FermatDezenoveCertE.certificado_105907
    exact absurd hL List.not_mem_nil
  · left
    exact orderOf_lt_of _ (fun i hi hi1 => ordem_grande hple' hp hL hi hi1)

set_option backward.isDefEq.respectTransparency false in
/-- **`19` é um primo regular.** -/
theorem regular_dezenove : IsRegularPrime 19 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (pid_dezenove (CyclotomicField _ ℚ))

/-- **Último teorema de Fermat para `n = 19`.** -/
theorem flt_dezenove : FermatLastTheoremFor 19 :=
  @flt_regular 19 fact_prime_dezenove regular_dezenove (by norm_num)

end ATK.FermatDezenove

#print axioms ATK.FermatDezenove.teste_mono
#print axioms ATK.FermatDezenove.teste_0
#print axioms ATK.FermatDezenove.sub_0
#print axioms ATK.FermatDezenove.teste_1
#print axioms ATK.FermatDezenove.sub_1
#print axioms ATK.FermatDezenove.teste_2
#print axioms ATK.FermatDezenove.sub_2
#print axioms ATK.FermatDezenove.teste_3
#print axioms ATK.FermatDezenove.sub_3
#print axioms ATK.FermatDezenove.teste_4
#print axioms ATK.FermatDezenove.sub_4
#print axioms ATK.FermatDezenove.teste_5
#print axioms ATK.FermatDezenove.sub_5
#print axioms ATK.FermatDezenove.teste_6
#print axioms ATK.FermatDezenove.sub_6
#print axioms ATK.FermatDezenove.teste_7
#print axioms ATK.FermatDezenove.sub_7
#print axioms ATK.FermatDezenove.teste_8
#print axioms ATK.FermatDezenove.sub_8
#print axioms ATK.FermatDezenove.teste_9
#print axioms ATK.FermatDezenove.sub_9
#print axioms ATK.FermatDezenove.teste_10
#print axioms ATK.FermatDezenove.sub_10
#print axioms ATK.FermatDezenove.teste_11
#print axioms ATK.FermatDezenove.sub_11
#print axioms ATK.FermatDezenove.teste_12
#print axioms ATK.FermatDezenove.sub_12
#print axioms ATK.FermatDezenove.teste_13
#print axioms ATK.FermatDezenove.sub_13
#print axioms ATK.FermatDezenove.teste_14
#print axioms ATK.FermatDezenove.sub_14
#print axioms ATK.FermatDezenove.teste_15
#print axioms ATK.FermatDezenove.sub_15
#print axioms ATK.FermatDezenove.teste_16
#print axioms ATK.FermatDezenove.sub_16
#print axioms ATK.FermatDezenove.teste_17
#print axioms ATK.FermatDezenove.sub_17
#print axioms ATK.FermatDezenove.teste_18
#print axioms ATK.FermatDezenove.sub_18
#print axioms ATK.FermatDezenove.teste_19
#print axioms ATK.FermatDezenove.sub_19
#print axioms ATK.FermatDezenove.teste_20
#print axioms ATK.FermatDezenove.sub_20
#print axioms ATK.FermatDezenove.teste_21
#print axioms ATK.FermatDezenove.sub_21
#print axioms ATK.FermatDezenove.teste_22
#print axioms ATK.FermatDezenove.sub_22
#print axioms ATK.FermatDezenove.teste_23
#print axioms ATK.FermatDezenove.sub_23
#print axioms ATK.FermatDezenove.teste_24
#print axioms ATK.FermatDezenove.sub_24
#print axioms ATK.FermatDezenove.teste_25
#print axioms ATK.FermatDezenove.sub_25
#print axioms ATK.FermatDezenove.teste_26
#print axioms ATK.FermatDezenove.sub_26
#print axioms ATK.FermatDezenove.teste_27
#print axioms ATK.FermatDezenove.sub_27
#print axioms ATK.FermatDezenove.teste_28
#print axioms ATK.FermatDezenove.sub_28
#print axioms ATK.FermatDezenove.teste_29
#print axioms ATK.FermatDezenove.sub_29
#print axioms ATK.FermatDezenove.teste_30
#print axioms ATK.FermatDezenove.sub_30
#print axioms ATK.FermatDezenove.teste_31
#print axioms ATK.FermatDezenove.sub_31
#print axioms ATK.FermatDezenove.teste_32
#print axioms ATK.FermatDezenove.sub_32
#print axioms ATK.FermatDezenove.teste_33
#print axioms ATK.FermatDezenove.sub_33
#print axioms ATK.FermatDezenove.teste_34
#print axioms ATK.FermatDezenove.sub_34
#print axioms ATK.FermatDezenove.teste_35
#print axioms ATK.FermatDezenove.sub_35
#print axioms ATK.FermatDezenove.teste_36
#print axioms ATK.FermatDezenove.sub_36
#print axioms ATK.FermatDezenove.teste_37
#print axioms ATK.FermatDezenove.sub_37
#print axioms ATK.FermatDezenove.teste_38
#print axioms ATK.FermatDezenove.sub_38
#print axioms ATK.FermatDezenove.teste_39
#print axioms ATK.FermatDezenove.sub_39
#print axioms ATK.FermatDezenove.teste_40
#print axioms ATK.FermatDezenove.sub_40
#print axioms ATK.FermatDezenove.teste_41
#print axioms ATK.FermatDezenove.sub_41
#print axioms ATK.FermatDezenove.teste_42
#print axioms ATK.FermatDezenove.sub_42
#print axioms ATK.FermatDezenove.teste_43
#print axioms ATK.FermatDezenove.sub_43
#print axioms ATK.FermatDezenove.teste_44
#print axioms ATK.FermatDezenove.sub_44
#print axioms ATK.FermatDezenove.teste_45
#print axioms ATK.FermatDezenove.sub_45
#print axioms ATK.FermatDezenove.teste_46
#print axioms ATK.FermatDezenove.sub_46
#print axioms ATK.FermatDezenove.teste_47
#print axioms ATK.FermatDezenove.sub_47
#print axioms ATK.FermatDezenove.teste_48
#print axioms ATK.FermatDezenove.sub_48
#print axioms ATK.FermatDezenove.teste_49
#print axioms ATK.FermatDezenove.sub_49
#print axioms ATK.FermatDezenove.teste_50
#print axioms ATK.FermatDezenove.sub_50
#print axioms ATK.FermatDezenove.teste_51
#print axioms ATK.FermatDezenove.sub_51
#print axioms ATK.FermatDezenove.teste_52
#print axioms ATK.FermatDezenove.sub_52
#print axioms ATK.FermatDezenove.teste_53
#print axioms ATK.FermatDezenove.sub_53
#print axioms ATK.FermatDezenove.teste_54
#print axioms ATK.FermatDezenove.sub_54
#print axioms ATK.FermatDezenove.teste_55
#print axioms ATK.FermatDezenove.sub_55
#print axioms ATK.FermatDezenove.teste_56
#print axioms ATK.FermatDezenove.sub_56
#print axioms ATK.FermatDezenove.teste_57
#print axioms ATK.FermatDezenove.sub_57
#print axioms ATK.FermatDezenove.teste_58
#print axioms ATK.FermatDezenove.sub_58
#print axioms ATK.FermatDezenove.teste_59
#print axioms ATK.FermatDezenove.sub_59
#print axioms ATK.FermatDezenove.teste_60
#print axioms ATK.FermatDezenove.sub_60
#print axioms ATK.FermatDezenove.teste_61
#print axioms ATK.FermatDezenove.sub_61
#print axioms ATK.FermatDezenove.teste_62
#print axioms ATK.FermatDezenove.sub_62
#print axioms ATK.FermatDezenove.teste_63
#print axioms ATK.FermatDezenove.sub_63
#print axioms ATK.FermatDezenove.teste_64
#print axioms ATK.FermatDezenove.sub_64
#print axioms ATK.FermatDezenove.teste_65
#print axioms ATK.FermatDezenove.sub_65
#print axioms ATK.FermatDezenove.teste_66
#print axioms ATK.FermatDezenove.sub_66
#print axioms ATK.FermatDezenove.teste_67
#print axioms ATK.FermatDezenove.sub_67
#print axioms ATK.FermatDezenove.teste_68
#print axioms ATK.FermatDezenove.sub_68
#print axioms ATK.FermatDezenove.teste_69
#print axioms ATK.FermatDezenove.sub_69
#print axioms ATK.FermatDezenove.teste_70
#print axioms ATK.FermatDezenove.sub_70
#print axioms ATK.FermatDezenove.teste_71
#print axioms ATK.FermatDezenove.sub_71
#print axioms ATK.FermatDezenove.teste_72
#print axioms ATK.FermatDezenove.sub_72
#print axioms ATK.FermatDezenove.teste_73
#print axioms ATK.FermatDezenove.sub_73
#print axioms ATK.FermatDezenove.teste_74
#print axioms ATK.FermatDezenove.sub_74
#print axioms ATK.FermatDezenove.teste_75
#print axioms ATK.FermatDezenove.sub_75
#print axioms ATK.FermatDezenove.teste_76
#print axioms ATK.FermatDezenove.sub_76
#print axioms ATK.FermatDezenove.teste_77
#print axioms ATK.FermatDezenove.sub_77
#print axioms ATK.FermatDezenove.teste_78
#print axioms ATK.FermatDezenove.sub_78
#print axioms ATK.FermatDezenove.teste_79
#print axioms ATK.FermatDezenove.sub_79
#print axioms ATK.FermatDezenove.teste_80
#print axioms ATK.FermatDezenove.sub_80
#print axioms ATK.FermatDezenove.teste_81
#print axioms ATK.FermatDezenove.sub_81
#print axioms ATK.FermatDezenove.teste_82
#print axioms ATK.FermatDezenove.sub_82
#print axioms ATK.FermatDezenove.teste_83
#print axioms ATK.FermatDezenove.sub_83
#print axioms ATK.FermatDezenove.teste_84
#print axioms ATK.FermatDezenove.sub_84
#print axioms ATK.FermatDezenove.teste_85
#print axioms ATK.FermatDezenove.sub_85
#print axioms ATK.FermatDezenove.teste_86
#print axioms ATK.FermatDezenove.sub_86
#print axioms ATK.FermatDezenove.teste_87
#print axioms ATK.FermatDezenove.sub_87
#print axioms ATK.FermatDezenove.teste_88
#print axioms ATK.FermatDezenove.sub_88
#print axioms ATK.FermatDezenove.teste_89
#print axioms ATK.FermatDezenove.sub_89
#print axioms ATK.FermatDezenove.teste_90
#print axioms ATK.FermatDezenove.sub_90
#print axioms ATK.FermatDezenove.teste_91
#print axioms ATK.FermatDezenove.sub_91
#print axioms ATK.FermatDezenove.teste_92
#print axioms ATK.FermatDezenove.sub_92
#print axioms ATK.FermatDezenove.teste_93
#print axioms ATK.FermatDezenove.sub_93
#print axioms ATK.FermatDezenove.teste_94
#print axioms ATK.FermatDezenove.sub_94
#print axioms ATK.FermatDezenove.teste_95
#print axioms ATK.FermatDezenove.sub_95
#print axioms ATK.FermatDezenove.teste_96
#print axioms ATK.FermatDezenove.sub_96
#print axioms ATK.FermatDezenove.teste_97
#print axioms ATK.FermatDezenove.sub_97
#print axioms ATK.FermatDezenove.teste_98
#print axioms ATK.FermatDezenove.sub_98
#print axioms ATK.FermatDezenove.teste_99
#print axioms ATK.FermatDezenove.sub_99
#print axioms ATK.FermatDezenove.teste_100
#print axioms ATK.FermatDezenove.sub_100
#print axioms ATK.FermatDezenove.teste_101
#print axioms ATK.FermatDezenove.sub_101
#print axioms ATK.FermatDezenove.teste_102
#print axioms ATK.FermatDezenove.sub_102
#print axioms ATK.FermatDezenove.teste_103
#print axioms ATK.FermatDezenove.sub_103
#print axioms ATK.FermatDezenove.teste_104
#print axioms ATK.FermatDezenove.sub_104
#print axioms ATK.FermatDezenove.teste_105
#print axioms ATK.FermatDezenove.sub_105
#print axioms ATK.FermatDezenove.excecoes
#print axioms ATK.FermatDezenove.ordem_grande
#print axioms ATK.FermatDezenove.pid_dezenove
#print axioms ATK.FermatDezenove.regular_dezenove
#print axioms ATK.FermatDezenove.flt_dezenove
