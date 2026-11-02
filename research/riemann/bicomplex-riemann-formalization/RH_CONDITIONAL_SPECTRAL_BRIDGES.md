# RH-conditional and spectral bridges: theorem skeleton and audit

## Scope and status

This note develops the strongest legitimate bridges in the recovered chain. It distinguishes classical theorems under the Riemann Hypothesis (RH), exact bicomplex coordinate facts, and open spectral constructions. It does not claim RH, a Hilbert–Pólya operator, or a new proof of any classical consequence.

- **CLASSICAL THEOREM**: established mathematics, not proved by this repository's Lean files.
- **CONDITIONAL**: valid only under displayed assumptions.
- **EXACT ALGEBRA**: follows from the stated definitions.
- **OPEN BRIDGE**: the theorem schema is clear, but its analytic/spectral construction is missing.
- **FALSE INFERENCE**: does not follow from the preceding equations.

See also the [formula catalog](FORMULA_CATALOG.md), [analytic bridge register](ANALYTIC_BRIDGES.md), [exact bridge obligations](FORMAL_BRIDGE_CONTRACTS.md), and [scaling analogy audit](SCALING_ANALOGY_AUDIT.md).

## 1. The conditional bicomplex statement that really follows

Use the package convention
\[
i^2=j^2=-1,\quad ij=ji=k,\quad k^2=1,\qquad
e_\pm=\frac{1\pm k}{2}.
\]
For real \(\sigma,b,t\), the idempotent coordinates of
\(z=\sigma+it+kb\) are
\[
z=(\sigma+b+it)e_+ +(\sigma-b+it)e_-.
\]
Thus \(b\) is a coordinate displacement in this chosen model. It is not automatically a physical parameter.

Define the proposed component lift of a complex function \(f\) by
\[
F_f(\sigma,t,b)
=f(\sigma+b+it)e_+ + f(\sigma-b+it)e_-.
\]
Since \(e_+,e_-\) are linearly independent idempotents,
\[
F_f=0\quad\Longleftrightarrow\quad
f(\sigma+b+it)=0\ \land\ f(\sigma-b+it)=0.
\]
If exactly one component is zero, \(F_f\) is a **nonzero zero divisor**, not zero.

Let \(f=\xi\), or use zeta only after restricting both arguments to nontrivial zeros and avoiding its pole/trivial-zero cases. Under RH, if this full lifted value is zero, then both component arguments are zeros on the critical line:
\[
\sigma+b=\frac12,\qquad \sigma-b=\frac12.
\]
Adding and subtracting gives
\[
\sigma=\frac12,\qquad b=0.
\]
This is a valid **CONDITIONAL** theorem about the defined lift: RH + full componentwise zero + both components in the nontrivial zero set implies \(b=0\).

It does not show RH. It also does not show every arbitrary bicomplex input has \(b=0\). The converse direction is not an RH proof: \(b=0\) only makes the two component arguments coincide, and says nothing about where a zero of \(f\) lies.

Proof skeleton:
1. Unpack \(F_f=0\) into its two component-zero propositions.
2. Apply RH to obtain \(\sigma+b=1/2\) and \(\sigma-b=1/2\).
3. Add the equations to obtain \(2\sigma=1\); subtract them to obtain \(2b=0\).
4. Conclude \(\sigma=1/2\) and \(b=0\).

The current generic component theorem proves only the algebraic shape of step 1. This package has no analytic definition of \(\xi\), no RH theorem, and no concrete instance of this conditional result. Existing Lean declarations remain **WRITTEN_UNCHECKED** unless a successful workflow covers their exact commit; this zeta instance is an **OPEN BRIDGE**.

### The 0.3/0.7 pair

If \(\sigma=1/2,b=-0.2\), the two real coordinates are \(0.3\) and \(0.7\). Functional-equation symmetry can pair zeros at those real parts at the same height, but that pair makes the two components separately zero; it does not make their idempotent sum zero. The lifted value is zero only if both components vanish. If one vanishes and the other does not, the output is nonzero.

The identity
\[
(1+k)(1-k)=0
\]
describes annihilating algebraic idempotent directions. It does not create a zeta zero, move a zero, or prove a physical cancellation.

## 2. Zero symmetries: the rectangle is an orbit, not a trap

For the completed zeta function,
\[
\xi(s)=\xi(1-s),\qquad
\xi(\bar s)=\overline{\xi(s)}.
\]
If \(\rho=\beta+i\gamma\) is a zero, these imply zeros at
\[
\rho,\quad \bar\rho=\beta-i\gamma,\quad
1-\rho=1-\beta-i\gamma,\quad 1-\bar\rho=1-\beta+i\gamma,
\]
counting multiplicity. If \(\beta\ne1/2\), these generally form a four-point orbit. If \(\beta=1/2\), reflection fixes the real coordinate and the orbit reduces to the conjugate pair (for \(\gamma\ne0\)).

In centered coordinates \(u=\beta-1/2\), reflection is \(u\mapsto-u\); conjugation is \(\gamma\mapsto-\gamma\). This proves symmetry only. It does not imply \(u=0\).

**FALSE INFERENCE:** “Reflection sends \(\beta\) to \(1-\beta\), so a zero can exist only if \(\beta=1-\beta\).” A symmetry-invariant set may contain two distinct reflected points. To conclude all points are fixed by the reflection requires an additional theorem.

The Riemann–von Mangoldt count \(N(T)\) counts all nontrivial zeros with \(0<\operatorname{Im}\rho\le T\), including multiplicity. Its asymptotic formula is unconditional. If \(N_0(T)\) counts only zeros on \(\operatorname{Re}s=1/2\), then RH is equivalent to \(N_0(T)=N(T)\) for every relevant \(T\), with consistent endpoint and multiplicity conventions. The asymptotic for \(N(T)\) alone does not prove that equality.

## 3. What the Euler product proves, and what it does not

For \(\operatorname{Re}s>1\),
\[
\zeta(s)=\prod_p(1-p^{-s})^{-1}
\]
converges absolutely and is nonzero. Here \(|p^{-s}|=p^{-\operatorname{Re}s}<1\). This proves zero-freeness in that region.

For \(0<\operatorname{Re}s<1\), the Euler product does **not** converge as an ordinary product representation. The continued function \(\zeta(s)\) exists there, but one cannot compare its values by comparing individual factors \(p^{-\beta}\) and \(p^{-(1-\beta)}\).

The functional equation is an identity in \(s\), with gamma and trigonometric factors. It does not require prime factors to match term by term at \(s\) and \(1-s\). In particular, the different local magnitudes at \(\beta=0.7\) and \(1-\beta=0.3\) do not contradict the functional equation or rule out a zero.

Davenport–Heilbronn and certain Epstein zeta functions show that related Dirichlet series can have functional equations and off-line zeros. They are countermodels to “functional equation alone implies RH-like line location.” They are not zeros of Riemann \(\zeta\), are not evidence for an off-line Riemann zero, and do not derive the bicomplex divisor.

The exact boundary is:
- Euler product: nonvanishing in its absolute-convergence region \(\operatorname{Re}s>1\).
- Functional equation: reflection symmetry after analytic continuation.
- Neither statement alone proves RH.
- Their interaction with the arithmetic structure is substantial, but no step in this chain turns it into \(\beta=1/2\).

## 4. Conditional consequences if RH is assumed

Write \(A\ll_\varepsilon B\) for a bound with constant depending on \(\varepsilon\).

| Statement | Status under RH | Correct interpretation |
|---|---|---|
| \(\left|\pi(x)-\operatorname{Li}(x)\right|=O(\sqrt{x}\log x)\) | **CLASSICAL THEOREM; RH-equivalent criterion** | Global prime-counting error, not one zero term. |
| \(\psi(x)-x=O(\sqrt{x}\log^2x)\) | **CLASSICAL THEOREM; RH-equivalent criterion** | Standard von Koch form for Chebyshev's \(\psi\). |
| \(p_{n+1}-p_n=O(\sqrt{p_n}\log p_n)\) | **CLASSICAL THEOREM, RH implies** | Prime-gap consequence; not equivalent to RH. |
| \(|\zeta(1/2+it)|\ll_\varepsilon |t|^\varepsilon\) for every \(\varepsilon>0\) | **CLASSICAL THEOREM, RH implies Lindelöf** | Needs analytic growth arguments, not a direct substitution. |
| \(M(x)=\sum_{n\le x}\mu(n)=O_\varepsilon(x^{1/2+\varepsilon})\) for every \(\varepsilon>0\) | **CLASSICAL THEOREM; RH-equivalent criterion** | Weak Mertens bound; distinct from the false stronger \(|M(x)|\le\sqrt{x}\). |
| Every zero counted by \(N(T)\) is on the line | **RH restated** | \(N(T)\) counts all zeros; line membership is the extra assertion. |

These are conditional consequences or equivalent criteria, not additional evidence that RH is true. The current repository does not formalize their analytic estimates.

### Explicit formula under RH

With an appropriate symmetric limiting or smoothing convention, the explicit formula for \(\psi\) contains terms
\[
-\frac{x^\rho}{\rho},\qquad \rho=\beta+i\gamma.
\]
Their individual magnitudes are
\[
\left|\frac{x^\rho}{\rho}\right|
=\frac{x^\beta}{\sqrt{\beta^2+\gamma^2}}.
\]
Under RH, each zero has \(\beta=1/2\), so each numerator envelope is \(\sqrt{x}\). This does **not** make the total error just \(\sqrt{x}\). Summing over zeros, handling convergence and endpoints, and passing from \(\psi\) to \(\pi\) produce logarithmic factors and additional analytic work. Nor does the explicit formula become “an equality without error”: it remains an equality with a zero sum and lower-order terms.

An off-line zero of Riemann \(\zeta\) would contradict RH and the RH-equivalent global error bounds. For one fixed zero term, the envelope changes by \(x^{\beta-1/2}\); the full error is not obtained by treating that term as the whole sum. See the [scaling audit](SCALING_ANALOGY_AUDIT.md) for numerical comparisons and their limits.

## 5. Hilbert–Pólya: exact implication and missing construction

A precise spectral target requires:

1. A Hilbert space \(\mathcal H\) and a densely defined self-adjoint operator \(A\).
2. The required real spectrum, discrete spectral type, and multiplicities.
3. A regularized spectral determinant \(D_A(s)\), or another analytic spectral function.
4. An identity \(D_A(s)=g(s)\xi(s)\), where \(g\) is analytic and nonzero in the domain relevant to nontrivial zeros, or an equivalently exact zero-set correspondence.
5. A fixed parameter convention in which real eigenvalue \(\lambda\) corresponds to \(s=1/2+i\lambda\), accounting for every nontrivial zero and eigenvalue.

Then self-adjointness gives \(\lambda\in\mathbb R\), so every corresponding zero has real part \(1/2\). The valid implication is
\[
\text{self-adjoint operator}
+\text{exact exhaustive zero/spectrum correspondence}
\Longrightarrow \mathrm{RH}.
\]
The correspondence—not self-adjointness in isolation—is essential.

The reverse claim “RH implies the meaningful Hilbert–Pólya operator exists” is **not established**. Under RH one can tautologically define a diagonal self-adjoint operator on \(\ell^2\) whose entries are the zero ordinates. This construction uses RH as input and gives no independent arithmetic/dynamical operator or determinant, so it is not a proof route.

### Berry–Keating and \(H=xp\)

Berry–Keating proposed the classical Hamiltonian \(H_{\rm cl}=xp\) as a spectral heuristic motivated by the asymptotic density of zeta-zero ordinates. Its common symmetric quantization is
\[
\widehat H_{\rm BK}=\frac{XP+PX}{2},\qquad
P=-i\hbar\frac{d}{dx},
\]
with formal differential expression on \(L^2(\mathbb R_{>0},dx)\)
\[
-i\hbar\left(x\frac{d}{dx}+\frac12\right).
\]
The operator, domain, boundary conditions, and spectrum must all be specified. In the standard full-half-line realization, the dilation operator has continuous spectrum; it does not directly produce the discrete sequence of zeta ordinates. Cutoffs or other modifications require new proofs of self-adjointness and exact determinant/zero correspondence.

Thus “\(H=xp\) was proposed” is historical context; “its eigenvalues are the \(t_n\)” is not a theorem in this package. Berry–Keating is not a consequence of RH, and bare \(xp\) does not close the spectral bridge.

### The quantum commutator is not bicomplex \(j\)

In ordinary quantum mechanics,
\[
[X,P]=XP-PX=i\hbar I.
\]
This \(i\) is the scalar imaginary unit of a complex Hilbert space. It is not a second bicomplex unit \(j\), and the commutator does not implement \(\sigma\mapsto\sigma-b\). A bridge needs an explicit representation of the bicomplex algebra on a specified space, a defined operator involving it, domain/adjoint proofs, and an exact link to \(\xi\). None is present here.

## 6. Genuine bridges to other areas—and their limits

| Area | Valid statement | Missing identification |
|---|---|---|
| Linear stability / flutter | For a defined mode \(\dot q=(\sigma+i\omega)q\), \(\sigma>0\) gives exponential growth in that convention. | No theorem identifies \(\sigma\) with \(\operatorname{Re}s-1/2\) or the characteristic function with \(\xi(s)\). |
| Routh–Hurwitz | Roots in the right half-plane determine instability of a specified linear system. | A system pole is not automatically a zeta zero; the stability axis \(\operatorname{Re}z=0\) is not the zeta line without a zero-preserving map. |
| Lee–Yang | Under its hypotheses, certain ferromagnetic partition-function zeros lie on a unit circle. | A circle and a line in the \(s\)-plane are not interchangeable without an explicit map; antiferromagnetic examples do not produce zeta zeros. |
| Davenport–Heilbronn / Epstein | Related Dirichlet series can satisfy functional equations and still have off-line zeros. | They are different functions and imply nothing directly about Riemann \(\zeta\). |
| Application items 7–15 | Oscillators, SIR, acoustics, lasers, seismic waves, EEG, flutter, finance, and diffusion each have real models. | The common \(b,j\) coordinate and 0.3/0.7 meanings need a model map, units, data, and validation. See [cross-domain analysis](CROSS_DOMAIN_ANALYSIS.md). |

The transfer template in Formal/BridgeContracts.lean captures the missing logical form. For source zero predicate \(Z_S\), target zero predicate \(Z_T\), source line \(C_S\), target axis \(C_T\), and map \(T\), it requires
\[
Z_S(x)\iff Z_T(Tx),\qquad C_S(x)\iff C_T(Tx).
\]
Then a theorem that every target zero lies on its axis transfers to the source. Without a concrete map and both equivalences, this is only a contract.

## 7. Proof frontier: exact next producers

The direct frontier is not “prove \(b=0\) unconditionally”; that is false for arbitrary coordinates. The legitimate tasks are:

1. Define classical \(\xi(s)\), its domain, and its zero predicate.
2. Prove conjugation and functional-equation reflection for that exact object, tracking multiplicity.
3. Instantiate the component lift and prove RH implies full-lift-zero \(\Rightarrow b=0\), with nontrivial-zero hypotheses.
4. Formalize one RH-equivalent criterion, such as the all-\(x\) von Koch bound or the all-\(\varepsilon\) weak Mertens bound. Finite checks do not close a universal criterion.
5. For the spectral route, define an operator's Hilbert space, dense domain, action, self-adjointness proof, and discrete spectrum.
6. Prove the regularized determinant identity \(D_A(s)=g(s)\xi(s)\), with \(g(s)\ne0\), including multiplicities and exceptional factors.
7. Only then instantiate the existing exact bridge and transfer the target-axis theorem.

Items 1–6 are not present as proved Lean theorems in the archive. Items 3 and 7 have generic/conditional theorem shapes; item 7 remains a contract, not a concrete instance. The open producer is a genuine analytic or spectral construction, not coordinate arithmetic.

## References

- NIST Digital Library of Mathematical Functions: [Euler product](https://dlmf.nist.gov/25.2), [functional equation](https://dlmf.nist.gov/25.4), [zero distribution](https://dlmf.nist.gov/25.10), [prime-counting formulas](https://dlmf.nist.gov/25.16).
- H. von Koch, [Sur la distribution des nombres premiers](https://www.numdam.org/item/ASENS_1901_3_18__1_0/), 1901; [RH equivalence summary](https://dlmf.nist.gov/27.12).
- H. Cramér, RH-conditional prime-gap bound; see [Prime gaps and zeros of \(\zeta(s)\)](https://travorlzh.github.io/files/gaps-between-primes.pdf).
- E. C. Titchmarsh, [The Theory of the Riemann Zeta-Function, Chapter XIII](https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf): RH implies Lindelöf; the converse is not known.
- Titchmarsh, Theorem 14.25(c), for RH equivalence of \(M(x)=O(x^{1/2+\varepsilon})\) for every \(\varepsilon>0\); see [Cambridge Mathematical Proceedings](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/on-a-mertenstype-conjecture-for-number-fields/B01C7628DF4D57CAE8410901FD6A9321).
- M. V. Berry and J. P. Keating, [The Riemann zeros and eigenvalue asymptotics](https://doi.org/10.1137/S0036144598347497), SIAM Review 41 (1999), 236–266.
- Berry–Keating operator on \(L^2(\mathbb R_{>0})\), [self-adjoint realizations and continuous spectrum](https://cris.technion.ac.il/en/publications/the-berry-keating-operator-on-lsup2suprsubgtsub-dx-and-on-compact/).
- H. Davenport and H. Heilbronn, [On the zeros of certain Dirichlet series](https://doi.org/10.1112/jlms/s1-11.4.307), 1936.
- A. Laurinčikas, [On the zeros of Epstein zeta functions](https://doi.org/10.1515/forum-2012-0057).
