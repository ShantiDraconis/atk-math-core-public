# Unconditional zeta theorem ledger and conditional countermodels

## Purpose and scope

This ledger classifies the claims in the current bridge chain. It lists unconditional facts about the classical Riemann zeta function, RH-conditional consequences, numerical verification, and examples built from different functions or algebras.

“Conditional counterexample” is not a refutation of RH. If an example changes \(\zeta\), removes its defining arithmetic structure, or changes the number system, it answers a different mathematical question.

## A. Unconditional facts about classical \(\zeta\)

### U1. Definition by series and Euler product in \(\operatorname{Re}s>1\)

For \(\sigma=\operatorname{Re}s>1\),
\[
\zeta(s)=\sum_{n\ge1}n^{-s}
=\prod_p(1-p^{-s})^{-1}.
\]
Both expressions converge absolutely there. Since
\(\sum_p|p^{-s}|\le\sum_{n\ge2}n^{-\sigma}<\infty\), the product converges to a nonzero value. Therefore
\[
\zeta(s)\ne0\qquad(\operatorname{Re}s>1).
\]
This is an unconditional zero-free region. It is **not** a statement about zeros in \(0<\operatorname{Re}s<1\), where this Euler product does not converge as an ordinary product.

### U2. Meromorphic continuation and functional equation

The function \(\zeta\) continues meromorphically to \(\mathbb C\), with a simple pole at \(s=1\). The completed function
\[
\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)
\]
is entire and satisfies
\[
\xi(s)=\xi(1-s),\qquad
\xi(\bar s)=\overline{\xi(s)}.
\]
These identities are unconditional. If \(\rho=\beta+i\gamma\) is a nontrivial zero, they give the orbit
\[
\rho,\quad \bar\rho,\quad 1-\rho,\quad 1-\bar\rho
\]
with multiplicity. They do not imply \(\beta=1/2\): a symmetric set can contain two distinct reflected points.

### U3. Zero-free regions outside the critical strip and trivial zeros

The functional equation and standard gamma-factor analysis show that \(\zeta(s)\) has no zeros for \(\operatorname{Re}s\le0\) except the trivial zeros \(s=-2,-4,-6,\ldots\). The prime number theorem's classical zero-free theorem gives no zeros on \(\operatorname{Re}s=1\). Together with U1, the nontrivial zeros lie in the open critical strip \(0<\operatorname{Re}s<1\).

### U4. Riemann–von Mangoldt zero count

The number \(N(T)\) of all nontrivial zeros with \(0<\operatorname{Im}\rho\le T\), counted with multiplicity, satisfies
\[
N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}
-\frac{T}{2\pi}+O(\log T).
\]
This is an unconditional total-zero count. It does not say how many lie on the line. RH is the additional assertion that the on-line count equals the total count at every height.

### U5. Infinitely many zeros on the critical line

Hardy's theorem proves unconditionally that \(\zeta(1/2+it)\) has infinitely many zeros for real \(t\). Stronger unconditional results prove a positive proportion of zeros lie on the line. Neither result says that all nontrivial zeros lie there.

### U6. Rigorous finite-height verification

Platt and Trudgian used interval arithmetic to verify that every nontrivial zero with
\[
0<\operatorname{Im}\rho\le3\times10^{12}
\]
has \(\operatorname{Re}\rho=1/2\), and that the zeros in that range are simple. This is a rigorous finite-height theorem/computation. It does not cover arbitrary height and therefore does not prove RH. Quoting a count such as “the first \(10^{13}\) zeros” should be accompanied by the precise height and certification source.

## B. RH-conditional theorems

Assuming RH, classical analysis yields, among other results,
\[
\pi(x)-\operatorname{Li}(x)=O(\sqrt{x}\log x),
\qquad
\psi(x)-x=O(\sqrt{x}\log^2x),
\]
\[
p_{n+1}-p_n=O(\sqrt{p_n}\log p_n),
\qquad
|\zeta(1/2+it)|\ll_\varepsilon |t|^\varepsilon
\quad\text{for every }\varepsilon>0,
\]
and
\[
M(x)=\sum_{n\le x}\mu(n)=O_\varepsilon(x^{1/2+\varepsilon})
\quad\text{for every }\varepsilon>0.
\]
The prime-counting error and weak Mertens estimate are RH-equivalent formulations; the prime-gap estimate and Lindelöf bound are consequences. These are theorems **under the assumption RH**. They do not prove their own assumption.

The explicit formula remains an equality containing a zero sum under either truth value of RH. Under RH, each numerator \(|x^\rho|\) is \(x^{1/2}\); summing the zero terms with convergence conventions yields logarithmic factors. One term's magnitude is not the total error in \(\pi(x)\).

## C. What Davenport–Heilbronn and Epstein do prove

For the Davenport–Heilbronn function, Voronin's result gives
\[
N_{\rm DH}(\alpha,\beta;T)\gg T
\]
in fixed strips \(1/2<\alpha<\operatorname{Re}s<\beta<1\). This proves infinitely many off-line zeros of that function. Related Epstein zeta functions for quadratic forms with class number \(>1\), including \(Q(x,y)=x^2+5y^2\) with discriminant \(-20\) and class number 2, also have infinitely many off-line zeros.

These are counterexamples to the overbroad assertion that a Riemann-type functional equation alone forces zeros onto its symmetry line. They are not counterexamples to RH, because their functions are not classical \(\zeta(s)\). Their zeros cannot be inserted into the Riemann prime explicit formula.

A finite computed list of Davenport–Heilbronn zeros is never the complete list if an infinitude theorem applies. A computation may be exhaustive below a fixed height only if an argument-principle/Turing-type certificate proves both the zeros found and the total count there. Symmetry adds reflected partners, not new theorems about the midpoint.

## D. Symmetry, averages, and the proposed nonsymmetric sum

For a function with reflection and conjugation symmetries, an off-line zero \(\beta+i\gamma\) has a same-height partner \(1-\beta+i\gamma\). Their mean is \(1/2+i\gamma\). This only proves that the *arithmetic midpoint* lies on the symmetry line. It does not prove
\[
F(1/2+i\gamma)=0.
\]
The average of two zeros is not generally a zero.

For a function without reflection symmetry, there may be no reflected partner, so there is no forced average of real parts. This absence of a symmetry relation does not produce prescribed zeros.

The proposed
\[
G(s)=\zeta(s)+\zeta(s+1)
\]
is a different meromorphic function, with poles at \(s=1\) and \(s=0\), and does not inherit the completed-zeta equation \(\xi(s)=\xi(1-s)\) as written. A pair of real parts \(0.0988\) and \(0.1422\) has arithmetic mean \(0.1205\), but without full complex ordinates, zero certificates, and a theorem describing all roots, it does not establish an infinite zero family or a general “mean never \(1/2\)” rule. Even certified zeros of \(G\) would not be zeros of \(\zeta\).

Likewise, a bicomplex identity with \(k^2=1\) changes the algebraic object. It neither changes \(\zeta\)'s classical definition nor refutes RH. The conditional component-lift lemma in [RH conditional and spectral bridges](RH_CONDITIONAL_SPECTRAL_BRIDGES.md) says only: assuming RH and assuming both components of a specified lift are nontrivial zeta/xi zeros, then the real shift \(b\) must be zero.

## E. Status of the central question

The unconditional statements above are theorems. The universal statement
\[
\forall \rho\quad
\bigl(\xi(\rho)=0\ \land\ 0<\operatorname{Re}\rho<1\bigr)
\Longrightarrow\operatorname{Re}\rho=\tfrac12
\]
is RH and remains unresolved in this archive.

It is inaccurate to say “unconditionally RH cannot be refuted.” Its truth is open. A rigorous off-line zero of classical \(\zeta\) would refute it. Finite verification, examples from different functions, zero-divisor algebra, and conditional consequences neither supply that counterexample nor prove it cannot exist.

“Refuting RH conditionally by breaking the Euler product or functional equation” is not a refutation of RH: it changes the object or removes a hypothesis of a different theorem. The proper label is **counterexample to a generalization**, not **conditional refutation of RH**.

## F. Formalization boundary in this repository

The Lean files in this package formalize elementary bicomplex identities, scaled-coordinate arithmetic, generic componentwise zero conditions, and abstract conditional transfer contracts. They do not define analytic continuation of \(\zeta\), its completed function \(\xi\), the explicit formula, or the global zero set. The classical theorems in sections A–C are documented with sources; they are not certified Lean declarations here.

The next genuine formal producer would be a complete analytic development of a chosen theorem or an exact spectral construction, including definitions, domains, convergence, multiplicity, and proof dependencies. Relabeling a conditional or finite statement as unconditional would not close that gap.

## References

- NIST DLMF, [zeta zeros and symmetries](https://dlmf.nist.gov/25.10), [definition/Euler product](https://dlmf.nist.gov/25.2), and [zero-counting/explicit-formula material](https://dlmf.nist.gov/25.16).
- A. Platt and T. Trudgian, [The Riemann hypothesis is true up to \(3\cdot10^{12}\)](https://doi.org/10.1112/blms.12460), *Bulletin of the London Mathematical Society* (2021).
- Hardy's theorem and proof context: [A note on Hardy's theorem](https://hrj.episciences.org/2634).
- Davenport–Heilbronn/Voronin count and symmetry examples: [Gritsenko's survey/result record](https://www.mathnet.ru/php/archive.phtml?jrnid=cheb&option_lang=eng&paperid=604).
- Epstein zero counts: [Laurinčikas, On the zeros of Epstein zeta functions](https://doi.org/10.1515/forum-2012-0057).
- RH-conditional prime gaps: [Cramér bound summary](https://travorlzh.github.io/files/gaps-between-primes.pdf).
- RH-conditional Lindelöf result: Titchmarsh, [The Theory of the Riemann Zeta-Function, Chapter XIII](https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf).
