# A radial test of the Hartree–Fock kinetic-energy conjecture

Crisostomo, Levy and Burke asked whether the kinetic energy of the globally minimizing Hartree–Fock Slater determinant can exceed the exact ground-state kinetic energy for a real-space Hamiltonian. Their Eq. (7) conjectures $T_{\rm exact}-T_{\rm HF}\ge0$. We give a proposed counterexample for a **general local external potential** in three dimensions. The six-section analytic argument and an independent AI-assisted audit are available for scrutiny. The full continuum result awaits formalization and external review. [Original article](https://doi.org/10.1063/5.0105684) · [Authors’ PDF](https://dft.uci.edu/pubs/CLB22.pdf) · [Derivation](continuum-witness.md) · [Independent audit](independent-review.md)

The example has two electrons interacting by $1/|x-y|$. Its fixed confining external potential is radial and continuous. The proposed Hartree–Fock minimizer is a unique spin-singlet determinant up to phase, even when general complex spin orbitals are admitted. The external potential contains a deliberately constructed oscillatory region very far out in its tail. Binding by a sum of attractive point-nuclear Coulomb potentials remains a separate physical question.

## How the construction works

1. Prescribe a positive orbital in an oscillator trap and choose the local potential from its Laplacian and its Hartree potential. A one-particle spectral gap and a bound on double excitations give a strict energy margin over all other determinants.
2. In the reference trap a two-state variational upper bound and a radial one-electron lower bound give a positive removal-energy difference. A comparison inequality for the exact marginal then puts its density below the Hartree–Fock density on a specified shell.
3. Add a rapidly oscillating, small-amplitude factor to the prescribed orbital. A change of variables in the total-energy forms controls the exact minimizer. The **physical kinetic energy** still sees the derivatives of the oscillations, with the larger contribution coming from the state carrying excess density on the shell.

The parameters are specified symbolically and held finite. At the given scale, direct floating-point simulation cannot resolve the shell probability or oscillation frequency. The derivation instead gives strict estimates with an explicit positive margin. [Construction and estimates](continuum-witness.md)

A second pass by the constructor examines normalization, the exterior boundary term and general complex spin orbitals. It includes a Lean proof of the normalization bound for distinct probability and energy measures. [Detailed checks](radial-audit.md) · [Normalization theorem](supplement/RayleighReweighting.lean)

## What Lean checks

The formal evidence includes the scalar variational margins and the final sign under their hypotheses. Additional modules treat the ground-state transformation and kinetic amplification with actual integrals. The outstanding physical statements concern the continuum many-electron operator, its exact and global Hartree–Fock optimizers, and their identification with the estimates in the final inequality. [Formal coverage](VERIFICATION.md) · [Search summary](llms.txt)

The archived source uses Lean 4.36.0 and a pinned mathlib. With the matching toolchain, run

```sh
python tools/fetch_cache.py
python tools/check_lean.py --output verification/lean-check.txt
```

Several Codex sessions developed and cross-checked the analysis. No human referee report is attached. The published question, variational model and remaining proof obligations are explicit so that subsequent researchers can audit the construction independently.

## 中文摘要

Hartree–Fock 理论把基态限制在单个 Slater 行列式中，得到的总能量有变分上界。这个上界能否进一步约束动能，是 Crisostomo、Levy 和 Burke 提出的独立问题。我们给出一个三维双电子的解析反例候选：两电子仍以真实库仑力排斥，外场是特意构造的径向束缚势。推导利用远处壳层里的密度差和快速振荡，使 Hartree–Fock 动能超过精确动能。Lean 已覆盖的内容和仍须在连续模型上证明的估计逐项列在验证说明中。普通点电荷原子核产生的外势仍是单独的问题。[解析推导](continuum-witness.md) · [形式验证范围](VERIFICATION.md)
