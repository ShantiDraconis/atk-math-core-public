import ATK.ZeroClasses.Abscissa
import ATK.ZeroClasses.PontesRH

/-!
# ATK — Ponte 1 na forma correta: `c` é a abscissa de convergência de `Σ μ(n) n^{−s}` (rodada 102)

A "ponte de Euler" pedida (`∏_p (1 − p^{−c−iγ})^{−1}` só "fecha" se `c = ½`) não é um enunciado: o produto só
converge absolutamente em `Re s > 1` e diverge em `s = ½` (`PontesRH.euler_meio_diverge`). A forma correta
é a abscissa de convergência das séries de Dirichlet de `1/ζ` e de `−ζ′/ζ − ζ`, já certificada na rodada 62
(`ATK.ZeroClasses.Abscissa`): para `½ ≤ θ < 1`,

  `c ≤ θ ⟺ Σ μ(n) n^{−s} converge em todo Re s > θ ⟺ Σ (Λ(n) − 1) n^{−s} converge em todo Re s > θ`,

com `c` a abscissa sem zeros de `ATK.ZeroClasses.PontesRH`. Em `θ = ½` isso é RH (`rh_iff_mu`, `rh_iff_cL`).
Classificação: reformulação. RH continua `OPEN_MATH`.
-/

namespace ATK.ZeroClasses.PontesRHAbscissa

open ATK.ZeroClasses.PontesRH

/-- As duas definições de `SemZeros` coincidem. -/
theorem semZeros_iff_quasi (θ : ℝ) : SemZeros θ ↔ ATK.ZeroClasses.QuasiRH.SemZeros θ := Iff.rfl

/-- **Ponte 1 corrigida (Möbius)**: para `½ ≤ θ < 1`, `c ≤ θ ⟺ Σ μ(n) n^{−s}` converge em `Re s > θ`. -/
theorem c_le_iff_mu {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    c ≤ θ ↔ ∀ s : ℂ, θ < s.re →
      ATK.ZeroClasses.Abscissa.Converge ATK.ZeroClasses.LittlewoodMu.mu s :=
  ((semZeros_iff θ).symm.trans (semZeros_iff_quasi θ)).trans
    (ATK.ZeroClasses.Abscissa.semZeros_iff_mu hθ hθ1)

/-- **Ponte 1 corrigida (von Mangoldt)**: para `½ ≤ θ < 1`, `c ≤ θ ⟺ Σ (Λ(n) − 1) n^{−s}` converge em
`Re s > θ`. -/
theorem c_le_iff_cL {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    c ≤ θ ↔ ∀ s : ℂ, θ < s.re →
      ATK.ZeroClasses.Abscissa.Converge ATK.ZeroClasses.VonKoch.cL s :=
  ((semZeros_iff θ).symm.trans (semZeros_iff_quasi θ)).trans
    (ATK.ZeroClasses.Abscissa.semZeros_iff_cL hθ hθ1)

/-- **RH ⟺ `c = ½` ⟺ `Σ μ(n) n^{−s}` converge em `Re s > ½`.** -/
theorem rh_iff_c_iff_mu :
    (RiemannHypothesis ↔ c = 1 / 2) ∧
      (c = 1 / 2 ↔ ∀ s : ℂ, 1 / 2 < s.re →
        ATK.ZeroClasses.Abscissa.Converge ATK.ZeroClasses.LittlewoodMu.mu s) := by
  refine ⟨rh_iff_c, ?_⟩
  have h := c_le_iff_mu (θ := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨fun hc => h.mp hc.le, fun hs => le_antisymm (h.mpr hs) meio_le_c⟩

end ATK.ZeroClasses.PontesRHAbscissa

#print axioms ATK.ZeroClasses.PontesRHAbscissa.semZeros_iff_quasi
#print axioms ATK.ZeroClasses.PontesRHAbscissa.c_le_iff_mu
#print axioms ATK.ZeroClasses.PontesRHAbscissa.c_le_iff_cL
#print axioms ATK.ZeroClasses.PontesRHAbscissa.rh_iff_c_iff_mu
