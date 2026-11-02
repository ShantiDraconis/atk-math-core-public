# Scaling analogies audit: (x^{0.2}), superdiffusion, and blast waves

## Purpose and evidence labels

This note audits the proposed interpretation of the factor (x^{0.2}) as a physical “explosion with memory.” It gives the exact arithmetic, states the assumptions behind each scaling model, and marks where a numerical resemblance stops being a scientific bridge.

Labels used here:

- **IDENTITY**: follows exactly from the displayed definitions.
- **CONDITIONAL MODEL RESULT**: follows if the stated model and assumptions hold.
- **EMPIRICAL CLAIM**: requires measured data, a fitted model, and uncertainty.
- **MODEL ANALOGY**: shared exponent or equation form, without a causal or mathematical identification.
- **UNSUPPORTED AS STATED**: the cited example does not establish the proposed exponent or mechanism.
- **OPEN**: not resolved by this analysis.

Nothing in this note is evidence for or against the Riemann Hypothesis (RH).

## 1. The exact arithmetic, and what it does not say

For any positive (x),
[
rac{x^{0.7}}{x^{0.5}}=x^{0.2}.
]
This is an **IDENTITY**. At (x=100), the ratio is (100^{0.2}approx2.5119). At (x=10^{12}), it is (10^{2.4}approx251.1886).

A formal exponent shift can be written
[
sigma_{m eff}=sigma-b,qquad
sigma=0.5,quad b=-0.2
quadLongrightarrowquad sigma_{m eff}=0.7.
]
This too is exact coordinate arithmetic. It does not change spatial dimension, introduce memory, or identify a physical process. The letter (b) has no common physical meaning across different applications unless each model defines it independently with units and a measurement procedure.

The bicomplex algebraic identity
[
(1+k)(1-k)=1-k^2=0quad	ext{when }k^2=1
]
is an **IDENTITY** in the split-complex algebra. A zero divisor is not, by itself, a pressure cancellation, a mechanical mode cancellation, or a physical singularity. A physical cancellation needs a governing equation and compatible quantities (for example, two pressure fields with specified amplitudes and phases).

## 2. Fractional Brownian motion versus Lévy flight

Let (B_H(t)) be fractional Brownian motion with Hurst parameter (0<H<1), normalized so that
[
mathbb E[(B_H(t)-B_H(0))^2]=C t^{2H},quad C>0.
]
Its increments are stationary and it is self-similar:
[
(B_H(ct))_{tge0}overset{d}= (c^H B_H(t))_{tge0}.
]
For (H=1/2), this is ordinary Brownian scaling and the mean-square displacement (MSD) is proportional to (t). For (H=0.7), the MSD is proportional to (t^{1.4}); increments are positively correlated at separated times. This is a **CONDITIONAL MODEL RESULT**, not evidence that a specific real particle, market, or blast follows fBm.

The term “superdiffusion” is often used when MSD grows faster than linearly, but one must first specify the stochastic process and confirm that its second moment exists. A Lévy flight with a non-Gaussian (alpha)-stable step law ((0<alpha<2)) generally has infinite variance, so its MSD is not a finite quantity. Thus “(H=0.7) Lévy flight with MSD (t^{1.4})” conflates distinct models. fBm with (H=0.7), a Lévy flight, and a Lévy walk have different increment laws and moment behavior.

There is also a units/variable issue: (x^{0.2}) is a factor in a number-theoretic expression. Reading (x) as physical time (t) is an analogy requiring an explicit model map; the symbols do not supply that map.

## 3. Sedov–Taylor blast scaling

Consider an idealized energy-conserving strong blast in (d) spatial dimensions, with ambient density (ho(r)=A r^{-omega}). At shock radius (R), a dimensional energy balance has the form
[
Easymp ho(R)R^dleft(rac{R}{t}ight)^2
  = A R^{d+2-omega}t^{-2}.
]
When (E,A) are constant and the similarity assumptions apply,
[
R(t)propto (E/A)^{1/(d+2-omega)}
                 t^{,2/(d+2-omega)}.
]
This is a **CONDITIONAL MODEL RESULT**. It assumes a strong shock, self-similar flow, fixed energy, a power-law ambient density, and (d+2-omega>0).

For a uniform ambient medium ((omega=0)):

| Geometry | (d) | (R(t)) exponent |
|---|---:|---:|
| Spherical | 3 | (2/5=0.4) |
| Cylindrical | 2 | (1/2=0.5) |
| Planar | 1 | (2/3approx0.6667) |

The planar value is near (0.7), but it is not (0.7) exactly. A spherical blast in a density profile with (omega=15/7) would have exponent (2/(5-15/7)=0.7), provided the model assumptions remain valid. This demonstrates that exponents depend on geometry and ambient density. It does **not** mean a change in a zeta exponent changes physical dimension.

### Energy needed for a radius ratio

At fixed time and density profile, (Rpropto E^{1/(d+2-omega)}). If a radius is multiplied by (q=x^{0.2}), the required energy ratio in this model is
[
rac{E_2}{E_1}=q^{d+2-omega}=x^{0.2(d+2-omega)}.
]
For a uniform planar model, this is (x^{0.6}): about (15.85) at (x=100), and (10^{7.2}approx15{,}848{,}932) at (x=10^{12}). The second value is about **15.8 million**, not 15,800. For a uniform spherical model, the ratios would be (x^1): (100) and (10^{12}). These are dimensional-model comparisons, not an energy estimate for a real blast.

## 4. Supernova ejecta interacting with a stellar wind

In the Chevalier self-similar ejecta-dominated model, take outer ejecta density proportional to (r^{-n}), circumstellar density proportional to (r^{-s}), and a suitable power-law regime. The contact/shock radii scale as
[
R(t)propto t^m,qquad m=rac{n-3}{n-s}.
]
For a steady stellar wind (s=2), (m=(n-3)/(n-2)). With commonly used outer-ejecta indices (n=7) to (12), this gives (m=0.8) to (0.9), not a universal (0.7). A value near (0.7) can occur for other parameters (for example (n=16/3,s=2)); the model alone does not establish that Cassiopeia A or Tycho has that exponent. Each remnant requires a fitted expansion history, an evolutionary-stage assessment, and uncertainty bounds.

**Status:** the Chevalier model is a valid example of a power-law expansion whose exponent depends on density profiles. The claim “a real wind-fed supernova remnant expands as (t^{0.7})” is **UNSUPPORTED AS STATED** without object-specific measurements and a fit.

## 5. Supershear rupture

Supershear describes rupture speed exceeding the relevant shear-wave speed in some part of a fault. It is a kinematic property; it does not define a universal moment-versus-time power law. Seismic moment is
[
M_0(t)=muint_{A(t)} D(mathbf r,t),dA,
]
where (mu) is rigidity and (D) is slip. To infer a power law from rupture length, one must also model the evolving area, slip distribution, and rupture velocity. A constant-stress-drop, geometrically similar crack can yield a scaling such as (M_0propto L^3); with (Lpropto t), that conditional model gives (M_0propto t^3), not a universal (t^{2.1}).

For the 2002 Denali earthquake, published analyses differ by segment and method: one kinematic model inferred near-shear speed overall and discussed possible shallow/segment supershear, while another analysis found an effective (sim5) km/s supershear segment. Neither establishes “moment (t^{2.1})” or a (0.7)-per-axis law.

**Status:** supershear is a real rupture regime; the proposed (t^{2.1}) identification is **UNSUPPORTED AS STATED**.

## 6. Deflagration, detonation, and thermobaric claims

Deflagration and detonation are distinct combustion/propagation regimes. Their front positions do not have a universal (t^{0.5}) or (t^{0.7}) law independent of geometry, mixture, confinement, and flow conditions. Blast waves may have a positive overpressure phase followed by a negative-pressure phase in some settings. That later pressure phase is governed by gas dynamics and boundary conditions; it is not the algebraic zero divisor ((1+k)(1-k)).

No scaling fit or source supplied here supports the claims that a fuel-air/thermobaric event universally follows (t^{0.7}), or that negative pressure mathematically cancels positive pressure. Those statements are **UNSUPPORTED AS STATED**. Any real-world claim would need a specific measured pressure-time or front-position dataset and a model fit; no operational explosive analysis is needed for this analogy.

## 7. Volcanic plume

Satellite analyses estimate that the 15 January 2022 Hunga Tonga plume reached roughly 55–57 km at its highest extent; another study reports at least 58 km. Those are height observations. A maximum height alone cannot establish (H(t)propto t^{0.7}), erupted mass (M(t)propto t^{0.7}), or a universal plume exponent. Plume dynamics depend on source flux, buoyancy, entrainment, stratification, phase changes, and the distinction between overshooting top and umbrella cloud.

**Status:** the extreme plume height is observed; the (t^{0.7}) scaling is **UNSUPPORTED AS STATED** without a defined observable, time series, fit interval, and uncertainty.

## 8. Finance and Hurst exponents

For a self-similar stochastic model with volatility scale
[
operatorname{sd}(X_{t+T}-X_t)=cT^H,
]
changing (H) from (0.5) to (0.7), while holding (c) and units fixed, changes the scale ratio over horizon (T) by (T^{0.2}). This is a **CONDITIONAL MODEL RESULT**. It is not a general statement that markets with an estimated (H=0.7) are bubbles or will crash. Conclusions depend on the series (returns, absolute returns, volatility, or prices), sampling interval, estimator, finite-sample bias, regime changes, and confidence interval. Evidence for long memory in raw financial returns is contested and sensitive to short-range dependence.

A Hurst exponent estimated for a data series is not the real part (eta) of a hypothetical zeta zero. One must not substitute the financial estimate into the explicit formula.

## 9. What the explicit formula actually permits

For the von Mangoldt summatory function, a schematic explicit formula contains zero terms of the form
[
-rac{x^ho}{ho},qquad ho=eta+igamma.
]
A rigorous statement requires specifying the summation convention/smoothing and handling prime-power discontinuities. The magnitude of one such term is
[
left|rac{x^ho}{ho}ight|
 =rac{x^eta}{sqrt{eta^2+gamma^2}}.
]
At fixed (gamma), changing a hypothetical (eta=0.5) to (0.7) multiplies this **individual term magnitude** by (x^{0.2}), with only a small denominator change. For (gamma=14.13), the approximate magnitudes are (0.71) versus (1.78) at (x=100), and (7.1	imes10^4) versus (1.78	imes10^7) at (x=10^{12}).

This calculation does **not** say that the total error in (psi(x)) or (pi(x)) becomes exactly 2.5 or 251 times larger. Other zeros contribute, phases can cancel, terms are interpreted through a limiting/smoothing procedure, and (pi(x)) is related to (psi(x)) by additional transformations. The statement is a conditional comparison of one summand only.

The algebraic product (x^{eta+igamma}=x^eta e^{igammalog x}) likewise has an oscillatory phase and an envelope (x^eta); it does not encode Brownian motion, fBm, Lévy motion, blast dynamics, or market leverage.

## 10. Formal bridge verdict

| Proposed bridge | Status | What would be needed to strengthen it |
|---|---|---|
| (x^{0.7}/x^{0.5}=x^{0.2}) | **IDENTITY** | Nothing beyond (x>0). |
| (H=0.7Rightarrowmathrm{MSD}propto t^{1.4}) | **CONDITIONAL MODEL RESULT** for fBm | Specify fBm and verify fit/moment assumptions for data. |
| (x^{0.2}) is a physical memory signature | **MODEL ANALOGY** only | An explicit, dimensionally consistent map and independent validation. |
| Planar Sedov–Taylor gives exponent near (0.7) | **CONDITIONAL MODEL RESULT**, exact exponent (2/3) | State geometry, density profile, energy regime, and compare measured trajectory. |
| Chevalier wind interaction proves Cas A/Tycho (t^{0.7}) | **UNSUPPORTED AS STATED** | Object-specific expansion data, fitted epoch, model comparison, and uncertainty. |
| Denali supershear means moment (t^{2.1}) | **UNSUPPORTED AS STATED** | Derive exponent from a specified rupture/slip model and fit time-resolved moment data. |
| Thermobaric negative pressure is ((1+k)(1-k)=0) | **UNSUPPORTED AS STATED** | A physical field equation; algebra alone cannot establish it. |
| Hunga Tonga reached 57 km, therefore plume mass follows (t^{0.7}) | **UNSUPPORTED AS STATED** | Define height/mass observable and fit the relevant time series. |
| Finance (H=0.7) means bubble/crash | **UNSUPPORTED AS STATED** | Series definition, robust estimation, causal mechanism, and out-of-sample validation. |
| A hypothetical zero with (eta=0.7) has a summand envelope (x^{0.7}) | **CONDITIONAL EXPLICIT-FORMULA CALCULATION** | State zero and formula convention; this is not evidence such a zero exists. |

**Conclusion:** A measured or modeled (t^{0.7}) may occur in a particular system. Matching an exponent is a **MODEL ANALOGY**, not a shared mechanism. The zeta exponent (eta), a Hurst parameter (H), and a blast/plume expansion exponent (m) have different definitions and cannot be equated by notation. No physical example here proves an off-critical-line zero or changes the status of RH.
