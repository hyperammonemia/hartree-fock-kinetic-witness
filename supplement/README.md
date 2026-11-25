# A common orbital multiplier and a conditional Slater energy bound

The real-space construction suggests asking what happens if *every* occupied spin orbital is multiplied by the same positive spatial function. The determinant then gains the product of the multipliers at the two electron coordinates. The first theorem proves this identity over any commutative ring, so it also applies to complex-valued spin orbitals. [Source](WeightedSlater.lean)

The other two declarations give the scalar consequences of a one-particle spectral gap, a kinetic estimate and a Hardy–Young bound on exchange. If $d>0$ is the gap and the coupling obeys $2gq(d+1+2e)\le d$, the displayed hypotheses in `WeightedSlater.energy_margin` imply $dB\le4\Delta E$. In the intended application $B$ is the squared Hilbert–Schmidt distance of a trial rank-two projector to the closed-shell projector. Establishing the analytic hypotheses for particular projectors is a separate step. [Definitions and hypotheses](WeightedSlater.lean)

Run `lake env lean --trust=0 supplement/WeightedSlater.lean` from the repository root. The standalone file imports only Std. All three declarations were exported and accepted by the default Lean kernel and by con-leche in verified mode. [Independent replay](weighted-slater-check.txt)
