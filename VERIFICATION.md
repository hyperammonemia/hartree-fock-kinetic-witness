# Scope of the formal proofs

The continuum library defines `ContinuumHamiltonian.FixedRadialReversal` for complex spinors in the specified physical field. It also proves intermediate results for weak exterior comparison, Gaussian integrals, the three-dimensional density probe and the kinetic remainder. The library's coverage table identifies the hypotheses needed for each application. The previous five-module audit below records the earlier scalar and integral results. [Continuum coverage table](continuum/README.md) · [Precise physical statement](continuum/ContinuumHamiltonian.lean)

The physical question compares kinetic expectation values at two different global minimizers of one fixed Hamiltonian. Minimizing the total energy alone gives an ordering of total energies. A comparison of their kinetic contributions needs control of the wavefunctions. The analytic note supplies this through a density tail bound and a change of variables. [Eq. (7) of the original article](https://dft.uci.edu/pubs/CLB22.pdf) · [Six-section derivation](continuum-witness.md)

| Lean source | Mathematical content |
|---|---|
| [RadialCertificate.lean](RadialCertificate.lean) | Derives the removal-energy gap from variational inequalities, controls the double-excitation amplitude of a determinant through its principal-angle data, and proves the final strict kinetic sign from scalar bounds. |
| [ContinuumForms.lean](ContinuumForms.lean) | A whole-space directional integration-by-parts identity for real functions under explicit differentiability and integrability hypotheses. It also bounds the integral of a squared sine over a unit interval and the exterior comparison exponent. |
| [FinitePotential.lean](FinitePotential.lean) | Defines the finite radial parameters, positive orbital and local external potential on three-dimensional Euclidean space. The sign theorem takes the density-tail estimate, state error and two kinetic remainders as hypotheses. |
| [FiniteOscillatoryWindow.lean](FiniteOscillatoryWindow.lean) | For continuous nonnegative weight bounded below by $m$ over a unit interval, gives a lower bound $m/4$ on the sinusoidally weighted integral at frequency $k\ge2$. |
| [KineticAmplification.lean](KineticAmplification.lean) | Uses the Riemann–Lebesgue lemma and $L^1$ convergence of density profiles to obtain strict kinetic ordering under hypotheses on the leading gradients and their remainders. This is an auxiliary limiting result. |

A separate Std-only supplement proves that a common one-body multiplier preserves two-spinor determinant form. It also derives a conditional energy penalty from spectral-gap and exchange inequalities. Its three declarations have a separate two-kernel replay. [Slater supplement](supplement/README.md)

`RayleighReweighting.normalized_energy` bounds the change in a normalized energy under a pointwise perturbation of its weight. The state mass and the positive energy density may use different measures. Section 5 of the construction gives the energy form used in this application. [Lean statement](supplement/RayleighReweighting.lean) · [Compiler and axiom log](supplement/rayleigh-reweighting.txt) · [Review of its application](radial-audit.md#rayleigh-quotient-and-physical-normalization)

The complete formalization would have to instantiate the many-electron Schrödinger operator, the antisymmetric Slater variational class and both ground-state optimizations. The spectral gap, global determinant estimate, Gaussian and oscillator identities, weak marginal inequality, exterior comparison and gradient error estimates must then be proved for those precise states. The analytic note gives the proposed arguments, and the independent audit addresses each section. [Independent audit](independent-review.md) · [Lean checks](verification/lean-check.txt)

The quintic cutoff in the specified example gives a $C^2$ orbital multiplier and a continuous external potential. The audit describes a smooth cutoff variant. The unscaled calculation uses a weak Coulomb coefficient $\lambda=1/100$. A unitary dilation restores electron–electron interaction $1/|x-y|$ and scales both kinetic energies by the same positive factor. The resulting field belongs to the general multiplicative class in the paper. It has no claim to model an equilibrium molecule.

The literature and reporting workflow used T. Kassis, V. Agarwal, Y. He, D. Patel and A. M. Brueckner (2026), *Scientific Agent Skills*. [Software reference](https://arxiv.org/abs/2609.00065)
