# Tests of the radial Hartree–Fock construction

I found no failed inequality or inadmissible trial state in the finite radial construction. The result under review is an analytic candidate for general local external fields with physical Coulomb repulsion. The specific remaining formal obligation is to connect the continuum minimizing states to the estimates in the machine-checked sign theorem. This is a second pass by the researcher who constructed the example. A separate project reviewer examined the same six sections. The source under test has SHA-256 `72c0334dd49c70ac944622a35cb66f84557ee92d1d7f358b92d54fd01e501432`. [Construction](continuum-witness.md) · [Other researcher's review](independent-review.md)

| Attempt to invalidate the result | Test and finding |
| --- | --- |
| Exclude the field under the published conjecture | Section II defines the external term as a sum of local one-body multipliers. Section V requires continuum coordinates and Coulomb interelectronic repulsion, and singles out point-nuclear attractions for their practical interest. Section I requires unbroken symmetries and a single HF determinant. Hooke's atom is an explicit confining example. The candidate obeys the general-field reading. The point-nuclear question remains open. The journal abstract and DOI were checked against the publisher record. Equation-level wording was checked in the NSF-deposited accepted manuscript, pp. 1, 2 and 6. [Journal article](https://doi.org/10.1063/5.0105684) · [NSF accepted manuscript](https://par.nsf.gov/servlets/purl/10396205) |
| Substitute a different external field or let it depend on the minimizing state | Expanding the one-body potential yields the radial derivative term $-r f'/f$ in addition to $\Delta f/(2f)$ and the fixed $-\lambda J_f$. Dropping either would change this example. The prescribed Gaussian, cutoff and constants determine $J_f$ before either minimization. The numerator and denominator in the Lean Newton integral use the same unnormalized orbital. A common orbital normalization cancels in the Laplacian ratio too. [Definition in Lean](FinitePotential.lean) |
| Create a singularity at the origin or lose confinement at the enormous shell | The cutoff is identically zero near $r=0$. Everywhere $f\ge1-b>0$. Outside the bounded shell, $\Delta(uf)/(2uf)=(r^2-3)/2$. For each fixed parameter the derivative perturbation is bounded and compactly supported, and $J_f$ is bounded. The quintic cutoff gives a continuous external field. The specified mollified cutoff gives a smooth field with the same envelope bounds. |
| Use an inadmissible test at a node or at infinity | The weak fiber test uses $U/(s^2+\varepsilon^2)^{1/2}$. The exterior comparison uses a zero-trace positive part and a compact outer cutoff. The resulting boundary error is at most $2L^{-2}\|z\|_2^2$. The details below require only the oscillator form domain. |
| Lose the energy contrast by normalizing the transformed state | Its squared normalization is $Z=\int F^2|Y|^2$. The positive energy numerator has its own measure. The new Lean theorem permits arbitrary relative placement of these measures and proves the claimed $20b$ error. Hartree and gradient normalization errors are checked separately below. [Lean theorem](supplement/RayleighReweighting.lean) · [Compilation and axiom log](supplement/rayleigh-reweighting.txt) |
| Lower HF energy by complex orbital rotations, spin mixing or an orthogonal determinant | The two complementary Gram determinants control the reference and double-excitation weights for every complex occupied plane. The energy penalty is at least $0.3(1-|\langle D_f,\Phi\rangle|^2)$. Equality of the trial and reference energies fixes the occupied projector and the determinant ray. Individual orbital bases still have $U(2)$ freedom. |
| Lose the final sign by a factor of two, a finite-frequency phase or coordinate dilation | Particle density integrates to two. The physical kinetic energy is one half the squared gradient norm. The integral of $\sin^2(kr)$ over any unit interval is at least $1/4$ for $k\ge2$. For $0<m\le1$ the final normalized kinetic difference is at least $4899m/5000>0$. Physical dilation multiplies both kinetic energies by the same positive number. [Finite-frequency theorem](ContinuumForms.lean) |

## The potential and its scale

Writing the radial Laplacian out for $r>0$ gives

$$
v_f(r)=\frac{r^2-3}{2}
  +\frac{f''(r)+2f'(r)/r}{2f(r)}-r\frac{f'(r)}{f(r)}-\lambda J_f(r).
$$

The electron coordinates $y=\lambda x$ yield the field $\lambda^{-2}v_f(y/\lambda)$ and pair repulsion $1/|y_1-y_2|$. This field has the spatial rotation, parity, spin and time-reversal symmetries used in the argument. The atomic virial shortcut assumes a homogeneous Coulomb external field. The radial derivative terms above preclude its use. The accepted-manuscript PDF retrieved from NSF has SHA-256 `fc95b0d1788ff36bcbbfbd2629dc91749395c6f0466d420bb2371d1dafa4fea2`. The NSF record identifies its relationship to the journal publication. [NSF record](https://par.nsf.gov/biblio/10396205) · [Author-hosted text](https://dft.uci.edu/pubs/CLB22.pdf)

## Exterior comparison in the form domain

Let $\Psi$ be the positive normalized reference spatial ground state, $U(x)=\Psi(x,\cdot)$, $s=\|U\|_{L^2_y}$, and $s_\varepsilon=(s^2+\varepsilon^2)^{1/2}$. The oscillator form gives $\nabla_x U\in L^2$, $|x|s\in L^2$, and $|\nabla s|\le\|\nabla_xU\|_{L^2_y}$ almost everywhere. For $0\le\xi\in C_c^\infty$, test the weak eigenvalue equation with $\xi U/s_\varepsilon$. For fixed $\varepsilon>0$ the $y$ derivatives, oscillator moment and Coulomb form are controlled by the bounded multiplier. In the $x$ derivative the additional term is controlled by $\varepsilon^{-1}|\nabla s|$ after taking the fiber norm. Thus the test is admissible. The real part of the $x$-gradient integrand equals

$$
\nabla\xi\cdot\nabla s_\varepsilon+
\frac{\xi}{s_\varepsilon}\bigl(\|\nabla_x U\|_{L^2_y}^2-|\nabla s_\varepsilon|^2\bigr).
$$

The bracket is nonnegative. The remaining fiber Hamiltonian is at least $E_1$ because the pair repulsion is positive. Write $V_{\rm eff}=r^2/2-3/2-\lambda J+E_1-E_2$. Passing to the limit on the compact support yields $\frac12\int\nabla\xi\cdot\nabla s+\int \xi V_{\rm eff}s\le0$. The potential term before this limit contains $s^2/s_\varepsilon\le s$, and $\nabla s_\varepsilon$ is bounded by the fiber gradient. This proves the sign directly.

On the interval $[10^5,10^5+1]$, radial $H^1$ regularity gives a continuous representative. Normalization in $4\pi r^2dr$ supplies a trace radius $q_0$ with $s(q_0)\le1$. The exterior comparison function $w=u(r)(q_0/r)^\alpha/u(q_0)$, $\alpha=10^{-7}$, satisfies $w(q_0)=1$ and $w'=-(r+\alpha/r)w$. Both $w$ and its first derivative, and also $rw$, are square integrable on the exterior. There $d=E_1-E_2>5\cdot10^{-7}$, $\lambda J\le10^{-7}$, and $h_0w/w=-\alpha+\alpha(1-\alpha)/(2r^2)$. Hence $w$ is a supersolution and $V_{\rm eff}\ge1$ on the comparison domain.

Put $\Omega=\{|x|>q_0\}$, $z=(s-w)_+$. The Lipschitz chain rule, zero trace on the smooth inner sphere and the moment bounds give $z\in H^1_0(\Omega)$, $|x|z\in L^2(\Omega)$. Choose $0\le\chi_L\le1$ equal to one for $r\le L$, zero for $r\ge2L$, with $|\nabla\chi_L|\le2/L$. The nonnegative test $\chi_L^2z$ follows by $H^1_0$ approximation on the bounded shell, where the potential is bounded. Subtraction of the two weak inequalities gives

$$
\frac12\int_\Omega|\nabla(\chi_Lz)|^2+\int_\Omega V_{\rm eff}\chi_L^2 z^2
\le \frac12\int_\Omega z^2|\nabla\chi_L|^2
\le \frac{2}{L^2}\|z\|_2^2.
$$

Sending $L$ to infinity yields $z=0$. The cutoff estimate controls the entire outer boundary contribution. The numerical exponent bound on $w/u$ then yields $s\le u/2$ throughout the shell, up to a null set as needed by the density integral. Recomputing the removal estimates as fractions gives $(E_1-E_2)/\lambda^2\ge 23500/1000001-50/(99\cdot32)>1/200$. [Removal and log bounds](continuum-witness.md)

## Rayleigh quotient and physical normalization

Write $F=f_1f_2$, $t=F^2$, $\|Y\|_2=1$, and $d\mu=|Y|^2 dx_1dx_2$. For the nonnegative transformed gradient and pair terms use their baseline energy measure $d\nu$, with mass $A(Y)$. Ground-state integration by parts gives their normalized value as $\int t\,d\nu/Z$, $Z=\int t\,d\mu$. The one-body density correction has a separate normalization $\int u^2f^2$.

For $0<b\le1/100$, $(1-b)^4\le t\le(1+b)^4$ gives $|t-1|\le5b$. Even disjoint atomic supports for $\mu$ and $\nu$ leave the maximum possible upward relative change at $10b/(1-5b)\le20b$. The bound applies also when $A(Y)=0$. The ratio $f^2/\int u^2f^2$ differs from one by at most $4b/(1-b)^2<6b$, by its two endpoint ratios. Thus $\|J_f-J\|_\infty\le12b$. In the signed Hartree term, the normalized density has mass one. Replacing $J_f$ by $J$ costs at most $24\lambda b$; removing $t/Z$ then costs at most $80\lambda b$. Their sum is $1.04b$. The quoted bound $20bA(Y)+2b$ follows.

The reference trial gives $A(\Psi)\le0.04$ and $E_{2,f}\le E_2+2.8b$. Since $t/Z\ge(7/9)^4>1/3$ and the new ground energy is negative, $A(Y_f)\le0.12$ and $Q(Y_f)-E_2\le7.2b$. Positivity of the overlap and the baseline gap $0.96$ imply $\|Y_f-\Psi\|_2\le5\sqrt b$. For the **physical gradient**, $\|FY\|_2=\sqrt Z$, and comparing $(1\pm b)/(1\mp b)^2$ to one gives $|f_j/\sqrt Z-1|< 5b$. The remainder in the scaled gradient norm is at most $28b$; the squared-norm error is at most $56\sqrt2\,b+784b^2<100b$. These checks use the finite value $k=b^{-2}$.

## General complex spinors and uniqueness

Let $V:\mathbb C^2\to L^2(\mathbb R^3;\mathbb C^2)$ have orthonormal columns spanning the arbitrary trial occupied plane, $P_0$ project onto $u_f\otimes\mathbb C^2$, and $G=V^*P_0V$. The squared reference overlap is $\det G$. The squared norm of the fully excited part is $\det(I-G)$, by the complex Gram determinant formula for an exterior product. Both eigenvalues of $G$ lie in $[0,1]$. Thus $\sqrt{\det(I-G)}\le1-\det G=\delta$, including rank-zero or rank-one compressions.

The tempting competing state $\sqrt{1-t^2}D_f+itD_{\rm out}$, where $D_{\rm out}$ occupies two orthogonal external orbitals, would have double-excitation norm $t=\sqrt\delta$. For $0<t<1$ its exterior square with itself is nonzero, which excludes decomposability as a Slater determinant. There are actual competing determinants that saturate the bound at $\delta=1$. For equal nonzero principal angles $\theta$, their double-excitation norm divided by $\delta$ equals $1/(1+\cos^2\theta)$, including the orthogonal limit. A rotation of only one occupied orbital gives double-excitation norm zero.

For $L=W-J_{f,1}-J_{f,2}+D_C$, integrating $L(x,y)u_f(y)^2$ in $y$ gives zero for every $x$. With spin indices retained this calculation annihilates both singly occupied projections of $LD_f$. It bounds the off-diagonal term by $2\lambda\|LD_f\|\delta\le16\lambda\delta$. The complementary diagonal term is bounded below by $-4\lambda\delta$. The gap on the antisymmetric complement contributes at least $\delta/2$. The resulting $0.3\delta$ controls distance to the minimizing ray. Distinct determinants can approach it continuously and have arbitrarily small excess energy. The exact ground state is separately unique up to phase by positivity improvement on the connected scalar configuration space, exchange symmetry, and the one-dimensional singlet spin space.

## Machine check and open step

The new theorem `RayleighReweighting.normalized_energy` works with an actual probability measure, a separate finite positive measure and their real Bochner integrals. It derives a positive lower bound for the squared norm and an error of $20b\,\nu(X)$ under the pointwise envelope and integrability assumptions. It applies even when the measures are mutually singular. Lean 4.36.0 checked the declaration against pinned mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and reported only `propext`, `Classical.choice` and `Quot.sound`. The proof can be rebuilt from the project root with the following command. [Source](supplement/RayleighReweighting.lean) · [Log](supplement/rayleigh-reweighting.txt)

```sh
lake env lean -j1 --trust=0 -DwarningAsError=true supplement/RayleighReweighting.lean
```

Identification of $\nu$ with the physical gradient and Coulomb measures for the actual minimizers, the weak exterior comparison, and the fermionic Gram calculation remain analytic arguments. The exact Hamiltonian parameters are too large for an ordinary floating-point diagonalization to distinguish the shell effect.
