# Cross-domain applied systems analysis

## Scope

This is an analysis of nine application areas on their own scientific terms. It does not use them as evidence for, or a model of, the Riemann Hypothesis. Similar mathematical notation does not make physical parameters interchangeable. The proposed 0.3/0.7 pair is a chosen arithmetic example, not a measured universal threshold.

## Shared mathematical tools

For a continuous-time model `xdot = f(x; θ)`, choose a state (x_*), linearize (A=Df(x_*)), and study (dot η=Aη). A mode (e^{λt}) grows for (Re λ>0), decays for (Re λ<0), and is marginal at (Re λ=0), under this convention. For (λ=α+iω), the frequency is (ω/(2π)) and (α) is an amplitude growth rate. A 10 Hz signal, reproduction number, chemical concentration, laser gain, or leverage ratio is not automatically (α).

For a structural system, (Mddot q+Cdot q+Kq=F); stability follows from the corresponding state-space spectrum. For a wave written (u=e^{i(kx-ωt)}) with (k=k_r+ik_i), amplitude is multiplied by (e^{-k_i x}): positive (k_i) means attenuation toward positive (x) in this convention. Boundary conditions and propagation direction matter.

## Domain models, laws, and valid bridges

### 7. Belousov–Zhabotinsky (BZ) chemistry

Use mass-action kinetics (dot c=S v(c;k)), with concentrations (c), stoichiometric matrix (S), and reaction rates (v). The Field–Körös–Noyes (FKN) mechanism and reduced Oregonator model explain oscillatory regimes and limit cycles in a driven, open chemical system. Useful measurements are concentration or calibrated optical time series, temperature, pH/acidity, reagent/catalyst concentrations, mixing, and reactor geometry. Estimate period, phase response, and Floquet stability; predict held-out perturbation runs.

**Bridge:** Compare nonlinear oscillator methods with EEG or laser dynamics only at the level of explicitly defined state-space models. Bromate is not a universal coupling parameter (b). A color oscillation does not establish a 0.5-to-0.7 shift or a shared physical law.

### 8. SIR epidemics

The homogeneous SIR equations are
[
dot S=-\beta SI/N,\quad \dot I=\beta SI/N-\gamma I,\quad \dot R=\gamma I.
]
With initial susceptible count (S_0), (R_0=\beta S_0/(\gamma N)); the early growth rate is (r\approx\gamma(R_0-1)). Thus (R_0=0.7<1) is subcritical in this model and predicts initial decline, not an exponentially growing outbreak. Heterogeneity, time-varying contacts, latent periods, importations, and reporting delays require richer models.

**Bridge:** Compare next-generation matrix spectral radii in epidemic and social-contagion models only after defining nodes, exposures, and event times. Vaccination is a change in susceptible/contact structure, not automatically one corner of a four-point rectangle.

### 9. Room acoustics and echo

For an ideal rigid rectangular room,
[
f_{n_xn_yn_z}=\frac{c}{2}\sqrt{(n_x/L_x)^2+(n_y/L_y)^2+(n_z/L_z)^2}.
]
A common diffuse-field estimate is Sabine's (T_{60}\approx0.161 V/A) in SI units, with (A=\sum_i α_iS_i). Its assumptions matter; it is not a universal modal law. Local cancellation is (p_{total}=p_1+p_2\approx0) at a location and frequency when pressure amplitudes and phases match. It does not mean sound vanishes from the room. A passive mode does not grow without active feedback or energy input.

**Bridge:** Estimate modal frequencies, damping and spatial response from calibrated room impulse responses; compare held-out microphone positions to a wave/room model. The bicomplex identity ((1+k)(1-k)=0) is not a sound-cancellation equation.

### 10. Laser modes

For a simple cavity of length (L), mirror power reflectivities (R_1,R_2), distributed intensity gain (g), and distributed loss (α_i), a round-trip threshold is
[
R_1R_2\exp(2(g-α_i)L)=1,quad
g_{th}=α_i+\frac{1}{2L}\ln\frac1{R_1R_2}.
]
Above threshold, gain saturation and mode competition matter. The sign of a complex-frequency growth rate depends on whether time dependence is written (e^{-iωt}) or (e^{+iωt}).

**Bridge:** Derive a coupled-mode matrix from named cavity modes, mirror transmission, losses, phase and pump; test predicted threshold/splitting against spectra and power. Nonzero coupling is not the same as misalignment.

### 11. Seismic waves and faults

Elastic wave equations use density and elastic moduli to determine P/S wave speeds. At a material interface, continuity and traction conditions determine reflected and transmitted amplitudes. A complex wavenumber can model attenuation or evanescence; it depends on frequency, medium, branch, direction, and boundary conditions. Fault rupture/friction, scattering, and interface transmission are distinct mechanisms.

**Bridge:** Use event/station metadata and calibrated waveforms to estimate velocity/attenuation, then compare boundary-condition predictions with observed reflection/transmission. Attenuation does not imply that a wave vanishes on one side and reappears on the other.

### 12. EEG, alpha, seizure and sleep

EEG is a voltage measurement. Alpha is commonly around 8–13 Hz and can be prominent in relaxed wakefulness with eyes closed; a 10 Hz component is not a seizure diagnosis. Sleep staging combines EEG with eye movements and muscle tone; N3 is associated with slow-wave activity. Seizure classification is electroclinical and considers onset, evolution, video/clinical signs and suitable EEG review.

**Bridge:** Predefine montage, filters, artifact rules, spectral/coherence features, clinical labels, subject-level train/test splits and uncertainty. A frequency peak cannot diagnose epilepsy or sleep stage.

### 13. Aeroelastic flutter

A coupled model may take the form
[
M\ddot q+C\dot q+Kq=Q_{aero}(q,\dot q;U),
]
where (U) is flow speed. After linearization, flutter onset is commonly a coupled eigenvalue crossing into positive real part, often with nonzero imaginary part. Static divergence is a different instability. A failure prediction also needs nonlinear response, damping, strength, and test conditions.

**Bridge:** Identify bending/torsion modes and validate predicted flutter speed against wind-tunnel or approved test data. ((1+k)(1-k)=0) does not model torsion cancelling flexure. Tacoma Narrows requires its own engineering/history sources and should not be reduced to that identity.

### 14. Finance: leverage, bubbles and crashes

Leverage conventions include assets/equity and debt/equity; state which is used. Minsky's hedge/speculative/Ponzi categories describe income relative to debt commitments. A crisis can involve collateral, short-term funding, liquidity, defaults, common asset sales and counterparty networks. Trades with opposite sides do not thereby cancel systemic exposure; legal netting may reduce some exposures but does not eliminate default or funding risk.

**Bridge:** Define the ratio, denominator, frequency, sample, outcome, and lag structure before analysis. Compare balance-sheet measures and stress data against official crisis investigations. The claim that 2008 was a “0.7/0.3 rectangle” is unsupported.

### 15. Online diffusion

Define the event (view, share, adoption), network edge, exposure window, and outcome. For independent transmission one may define an expected offspring count; threshold/complex-contagion models instead require reinforcement from multiple contacts. Reach, speed, depth, and structural virality are different statistics. Algorithms require measured exposure and a causal design.

**Bridge:** Reconstruct cascade trees, distinguish broadcasts from multi-generation diffusion, and use randomized exposure or a credible natural experiment to estimate algorithm effects. An algorithm/sharing 2×2 table is a design, not evidence.

## Cross-domain method bridges

| Method link | Areas | What genuinely transfers | What still differs |
|---|---|---|---|
| Linear stability and eigenvalues | BZ, SIR, laser, EEG signal models, flutter | Linearization, modes, stability margin, parameter sweep | State variables, units, nonlinear mechanism, clinical/physical interpretation |
| Waves, modes, and boundaries | Acoustics, seismology, optics, structural vibration | Complex amplitudes, dispersion, reflection/transmission, damping | PDEs, constitutive laws, geometry, boundary conditions |
| Network contagion | Epidemics, online diffusion, counterparty/default networks | Graphs and spectral/cascade tools | What a node, edge, transmission, and consequence mean |
| Feedback and gain/loss | BZ, laser, flutter, finance | Explicit loop, delay, saturation, flow balance | Energy and cash-flow are not the same conserved quantity |
| Inverse problems | EEG, acoustics, seismology, finance, social media | Noise, identifiability, calibration, uncertainty, held-out prediction | Correlation/spectrum alone does not identify cause |

Label any bridge **IDENTITY** (exact equivalence under a stated transform), **MODEL ANALOGY**, **EMPIRICAL ASSOCIATION**, **CAUSAL BRIDGE**, or **OPEN**. Shared mathematical form alone earns only MODEL ANALOGY. See [source materials](SOURCE_MATERIALS.md) and [validation protocols](VALIDATION_PROTOCOLS.md).
