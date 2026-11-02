# Validation protocols for the nine applied analyses

These are research designs with falsifiable outcomes, not clinical, financial, or safety advice.

## Shared evidence package

For each study, archive: question/outcome; model equations and units; source provenance, license and SHA-256; preprocessing/exclusions; calibration/training split; held-out validation; uncertainty and sensitivity; code/environment/seeds; failed models and negative results. Do not choose parameters because they resemble 0.3 or 0.7. Do not treat in-sample fit as causal evidence.

| # | Measurements and materials | Model/test | Failure condition |
|---:|---|---|---|
| 7 BZ | Concentration or calibrated optical traces; temperature, acidity, concentrations, catalyst, stirring, reactor geometry, sampling. | Fit mass-action/Oregonator model on some runs; predict period, phase, response to perturbation on held-out runs. | Prediction misses declared uncertainty or oscillation is an optical/mixing artifact. |
| 8 SIR | Incidence/hospitalizations, population denominator, tests, vaccination, contacts/mobility, reporting delays/interventions. | Fit SIR/SEIR or structured next-generation model; compare (R_t) and forecasts to held-out periods/regions and baselines. | Forecast/calibration fails or reporting changes/confounding explain the apparent threshold. (R_t<1) is conditional on the model; not proof of extinction. |
| 9 Acoustics | Calibrated room impulse responses, dimensions, surfaces/absorption, source/mic positions, temperature, noise floor. | Estimate modes/damping/RT60; test model predictions at held-out positions and frequencies. | Predicted peaks/decay/nulls miss data or diffuse-field assumptions fail. |
| 10 Laser | Pump, spectrum/power, cavity length, mirror reflectivity, gain/loss, temperature, alignment, time-resolved mode data. | Fit round-trip threshold and specified coupled-mode model; predict threshold/splitting on held-out pump settings. | Misalignment/thermal drift confounds coupling or predicted thresholds fail. |
| 11 Seismic | Event catalog, calibrated waveforms, station response, phase picks, geometry, velocity/attenuation uncertainty. | Estimate complex slowness under a declared convention; compare interface reflection/transmission to observed waveforms. | Phase/energy/arrival predictions fail or instruments/scattering explain attenuation. |
| 12 EEG | De-identified EEG, sampling/montage, synchronized clinical/video labels, artifact annotations, cohort metadata. | Pre-register features; split by patient/site; compare to expert ILAE/AASM scoring with calibration and uncertainty. | Results collapse on unseen people/sites or reflect leakage/artifact. A 10 Hz peak is not a diagnosis. |
| 13 Flutter | Mass/stiffness/damping, aerodynamic configuration, flow speed/density, modal/strain measurements, model scale. | Coupled state-space model predicts eigenvalue movement and flutter speed; validate against wind tunnel/approved test. | Prediction fails outside fit range or nonlinear effects invalidate the linear onset model. |
| 14 Finance | Balance sheets, equity/debt, maturities, collateral, defaults, spreads, asset prices, dated institution links. | Predefine leverage ratio/denominator, frequency and outcome; test lagged feedback and network spillovers on held-out stress episodes. | Post hoc ratio, look-ahead/survivorship bias, or assumed netting drives result; model fails other episodes. |
| 15 Social | Timestamped cascades/exposure/adoption, network graph, content metadata, recommendation exposure when permissioned, collection rules. | Separate reach/speed/depth/structural virality; randomized or credible quasi-experimental design for algorithm effects. | Incomplete cascade, unobserved exposure, homophily/bots/selection/API changes confound results. |

## Cross-area bridge tests

- **Eigenvalue bridge:** provide each Jacobian/state matrix, units, sign convention, equilibrium and measured parameters. Normalize only after deriving dimensionless groups.
- **Network bridge:** define nodes, edges, event, time step and next-generation/cascade operator. Disease transmission, default contagion and online sharing are not the same process.
- **Wave bridge:** state the PDE, constitutive law, geometry, damping and interface conditions; compare transfer functions to data.
- **Feedback bridge:** state loop gain, delay, saturation and energy/cash-flow accounting. A similar diagram does not imply identical conservation laws.
- **Intervention bridge:** state treatment/control, assignment, outcome and estimand. A four-cell scenario table is a design template, not a result.

Allowed evidence labels: **IDENTITY**, **MODEL ANALOGY**, **EMPIRICAL ASSOCIATION**, **CAUSAL BRIDGE**, **OPEN**. A claim can advance only when the evidence required for its stronger label is supplied.
