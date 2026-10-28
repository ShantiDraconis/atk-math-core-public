/-
ATK-RH — `CapturaRH` sem a hipótese de positividade.

`ATK.CapturaRH.soma_log` e `ATK.CapturaRH.captura_log_iff` foram provados sob a hipótese
`hpos : ∀ N, 0 < DN N` (que até aqui só saía do piso da literatura, `PisoLog`).  Com
`ATK.RelacionalDN.DN_pos` (incondicional) a hipótese é descarregada:

* `soma_log_incondicional`: `Σ_{j<N} −log(1 − η_j) = log(D_0/D_N)`;
* **`captura_log_iff_incondicional`: O1 (`UniformLogBound`) ⟺ captura logarítmica acumulada
  `Σ_{j<N} −log(1 − η_j) ≥ log log(N+2) − C`**, sem hipóteses;
* `η_lt_one`: cada captura relativa é estritamente menor que 1 (nenhuma etapa fecha sozinha).

O1 continua OPEN; isto só remove uma hipótese auxiliar.
-/
import ATK.CapturaRH
import ATK.RelacionalDN

namespace ATK.CapturaIncondicional

open ATK.Conditional.Riemann ATK.CapturaRH Finset

theorem soma_log_incondicional (N : ℕ) :
    ∑ j ∈ range N, -Real.log (1 - η j) = Real.log (DN 0 / DN N) :=
  soma_log ATK.RelacionalDN.DN_pos N

/-- **O1 ⟺ captura logarítmica acumulada**, sem hipótese de positividade. -/
theorem captura_log_iff_incondicional :
    UniformLogBound ↔ ∃ C : ℝ, ∀ N : ℕ,
      Real.log (Real.log ((N : ℝ) + 2)) - C ≤ ∑ j ∈ range N, -Real.log (1 - η j) :=
  captura_log_iff ATK.RelacionalDN.DN_pos

/-- Cada captura relativa é `< 1`: nenhuma etapa leva `D` a zero. -/
theorem η_lt_one (N : ℕ) : η N < 1 := by
  have h := passo N
  have h1 := ATK.RelacionalDN.DN_pos (N + 1)
  have h0 := ATK.RelacionalDN.DN_pos N
  by_contra hc
  have hc' : 1 - η N ≤ 0 := by linarith [not_lt.mp hc]
  have : (1 - η N) * DN N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc' h0.le
  linarith

end ATK.CapturaIncondicional

#print axioms ATK.CapturaIncondicional.soma_log_incondicional
#print axioms ATK.CapturaIncondicional.captura_log_iff_incondicional
#print axioms ATK.CapturaIncondicional.η_lt_one
