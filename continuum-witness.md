# A finite radial potential for testing the continuum HF kinetic conjecture

**Research result for independent verification.** The estimates below give an explicit two-electron Hamiltonian in three dimensions and imply $T_{\rm HF}>T_{\rm exact}$. Its unique minimizing HF determinant, up to a phase, is a spin singlet and preserves the spatial symmetries. The construction targets general one-body multiplicative potentials in Eq. (1) of Crisostomo, Levy and Burke. A separate question concerns sums of attractive nuclear Coulomb potentials. The analytic argument is given here for review. The Lean companion proves the scalar certificates from specified hypotheses. Its statements and audit log delimit the formal result. [CLB, Sections I, II and V](https://dft.uci.edu/pubs/CLB22.pdf)

## 1. Specify the physical Hamiltonian

First work in oscillator coordinates. Define $u(x)=\pi^{-3/4}e^{-|x|^2/2}$, $\lambda=1/100$ and

$$
 R=\exp(10^{18}),\quad m=\exp(-(R+3)^2),\quad b=(m/1000)^2,\quad k=b^{-2}.
$$

Let $q(t)$ equal 0 for $t\le0$, $6t^5-15t^4+10t^3$ for $0<t<1$, and 1 for $t\ge1$. Put $g(r)=q(r-R)q(R+3-r)$. Then $g$ is $C^2$, $0\le g\le1$, $|g'|\le2$, and $g=1$ on $[R+1,R+2]$. Define

$$
 f(x)=1+b\,g(|x|)\cos(k|x|),\qquad
 u_f=\frac{uf}{\|uf\|_2},\qquad J_f(x)=\int\frac{u_f(y)^2}{|x-y|}\,dy,
 \qquad v_f=\frac{\Delta u_f}{2u_f}-\lambda J_f .
$$

The potential is fixed before either minimization. It is real, radial, continuous, finite at every point and confining. For an explicitly $C^\infty$ variant, let $\zeta(t)$ be the unit-mass multiple of $e^{-1/(1-16t^2)}1_{\{|t|<1/4\}}$, defined as zero outside the open interval. Replace $q$ by the integral from $-\infty$ to $t$ of $2(1_{[1/4,3/4]}*\zeta)$. This derivative is nonnegative, has mass one, has support in $[0,1]$, and is bounded by 2. The same support, plateau and derivative estimates for $g$ follow, so every bound below holds for this fixed smooth potential as well. The unscaled Hamiltonian is $H_f=\sum_{i=1}^2(-\Delta_i/2+v_f(x_i))+\lambda/|x_1-x_2|$. For the physical coordinates $y_i=\lambda x_i$, take

$$
 H_{\rm phys}=\sum_{i=1}^2\left[-\tfrac12\Delta_{y_i}+
            \lambda^{-2}v_f(y_i/\lambda)\right]+\frac{1}{|y_1-y_2|}.
$$

Unitary dilation gives $H_{\rm phys}\simeq\lambda^{-2}H_f$ and multiplies both kinetic energies by the same positive $\lambda^{-2}$. The huge constants allow conservative analytic estimates without numerically resolving a small tail. Every parameter and both optimizations belong to one finite Hamiltonian.

## 2. The unique global HF determinant

Write $h_f=-\Delta/2+\Delta u_f/(2u_f)$. Its nonnegative form at $u_f z$ is $\tfrac12\int u_f^2|\nabla z|^2$, by integration by parts. For $f=1$, $h_0=-\Delta/2+|x|^2/2-3/2$ has normalized ground orbital $u$ and gap 1. The Gaussian Poincaré inequality is the corresponding gap bound in the variable $z$. Comparing the weighted gradient integral and the variance $\min_c\int u_f^2|z-c|^2$ with their Gaussian values leaves a gap at least $(7/9)^2>1/2$, since $7/8\le f\le9/8$. This applies to all spatial orbitals, including complex ones.

Let $D_f$ be the normalized spin-singlet Slater determinant occupying $u_f$ twice. In this section $D_C=\int u_f^2 J_f$ is a scalar, $W=|x_1-x_2|^{-1}$, and $L=W-J_f(x_1)-J_f(x_2)+D_C$. The energy of $D_f$ is $-\lambda D_C$. Relative to that energy the full Hamiltonian equals $h_f(1)+h_f(2)+\lambda L$. Integrating over either occupied orbital shows that $LD_f$ lies in the sector with both electrons excited out of the occupied spinor plane. In particular its reference and single-excitation components vanish.

For the unmodified Gaussian, $J(x)=\operatorname{erf}(|x|)/|x|$ with its continuous value at zero, $\|J\|_\infty=2/\sqrt\pi$, and $\|W(u\otimes u)\|_2=1$. Indeed $x-y$ has the standard three-dimensional normal distribution for independent $u^2$-distributed $x,y$. The density ratio $u_f^2/u^2\le(9/7)^2$ gives $\|J_f\|_\infty<2$, $\|W D_f\|_2<2$ and $\|LD_f\|_2\le8$. Also $L\ge-4$.

For an arbitrary normalized determinant $\Phi$, let $\delta=1-|\langle D_f,\Phi\rangle|^2$. Choose principal vectors between its two-dimensional occupied space and that of $D_f$. If $a,b'$ are the squared sines of their principal angles, then the double-excitation norm is $\sqrt{ab'}$ and $\delta=1-(1-a)(1-b')\ge\max(a,b')$. This includes degenerate principal angles and general spinors. Resolve $\Phi=cD_f+\eta$ with $\|\eta\|^2=\delta$. The two-body sum of $h_f$ on antisymmetric spin states has the single zero mode $D_f$ and gap at least $1/2$. The off-diagonal matrix element of $L$ is bounded by $8\delta$ using the double-excitation norm. Consequently

$$
 \langle\Phi,H_f\Phi\rangle-\langle D_f,H_fD_f\rangle
 \ \ge\ (1/2-4\lambda-16\lambda)\delta
 \ =\ 3\delta/10.
$$

This gives a global statement over the entire determinant manifold. Classical uniqueness results for large-charge atomic HF use related spectral-gap arguments, with a nuclear Coulomb external potential. [Griesemer and Hantsch](https://arxiv.org/abs/1012.5179)

## 3. A positive removal-energy difference in the reference trap

Here $f=1$. Write $D=\sqrt{2/\pi}$, $H=h_0(1)+h_0(2)+\lambda(W-J(x_1)-J(x_2))$, $E_2=\inf\sigma(H)$ and $E_1=\inf\sigma(h_0-\lambda J)$. The scalar two-electron ground state $\Psi$ is simple, strictly positive and symmetric by positivity improvement and exchange symmetry. Tensoring it with the singlet gives the fermionic ground state. Confinement gives compact resolvent. The same positivity argument makes the one-electron ground state radial.

Two integrals used below are $\int u^2J=D$ and $\int u^2J^2=2/3$. For the first, integrate $1/|x-y|$ against a standard three-dimensional Gaussian for $x-y$. For the second, the radial integral is $(4/\sqrt\pi)\int_0^\infty e^{-r^2}\operatorname{erf}(r)^2\,dr=2/3$ by differentiating $\operatorname{erf}^3$. Thus $\sigma^2=\operatorname{Var}_{u^2}(J)=2/3-2/\pi<1/32$ by $\pi<22/7$.

For the one-electron lower bound decompose the normalized radial ground state as $xu+\eta$, $\eta\perp u$. The radial oscillator on this complement has gap 2. The diagonal part there, after shifting by $\lambda D$, is bounded below by $(2-2\lambda)\|\eta\|^2$. The magnitude of the off-diagonal coupling is at most $\lambda |x|\sigma\|\eta\|$. With $z=\|\eta\|/\lambda$ and $e=(E_1+\lambda D)/\lambda^2$ this gives $50e\ge99z^2-100\sigma |x|z$, hence $99e\ge-50\sigma^2$ by completing the square.

For the upper bound let $p_i(x)=\sqrt2 x_i u(x)$, $B=\sum_{i=1}^3 p_i\otimes p_i/\sqrt3$, and $D_0=u\otimes u$ in the spatial singlet sector. $B$ is a normalized oscillator state with two excitation quanta. The transition matrix element is $a=\langle B,W D_0\rangle=D/(2\sqrt3)>11/50$. To see this, take $X=(x+y)/2$ and $z=x-y$. These Gaussian random vectors are independent, with component variances $1/4$ and $1$. Isotropy and $\mathbb E|z|=2D$ give $\mathbb E[2x_i y_i/|z|]=D/6$. The one-body $J$ terms have vanishing transition elements.

The kinetic energy of $B$ is $5/2$ by the oscillator virial identity. Hardy's inequality in the relative variable gives $\|WB\|_2^2\le4\|\nabla_z B\|_2^2\le4\langle B,TB\rangle=10$. Hence $d_B=\langle B,(W-J_1-J_2)B\rangle+D\le5$. With the trial vector $D_0-(\lambda/10)B$ and $t=(E_2+\lambda D)/\lambda^2$, its Rayleigh quotient gives

$$
 1000001\,t\le20000+100d_B-200000a .
$$

Together the two bounds yield

$$
 d:=E_1-E_2>\lambda^2/200=1/2000000.
$$

The bounds concern the full continuum energies. Only the two-body upper bound uses a two-vector trial space.

## 4. Locate a region of strict excess HF density

Let $s(x)=(\int|\Psi(x,y)|^2\,dy)^{1/2}$, so $\|s\|_2=1$ and $\rho_{\rm exact}=2s^2$. The Hilbert-space norm inequality for the Laplacian gives the weak scalar inequality

$$
 (h_0-\lambda J+d)s\le0 .
$$

In detail, differentiating the fiber norm gives $-\Delta s/2\le\langle\Psi,-\Delta_x\Psi/2\rangle_y/s$ in the weak sense. The remaining fiber Hamiltonian is bounded below by $E_1$ since $W\ge0$. One can regularize the norm by $(s^2+\varepsilon^2)^{1/2}$ in compactly supported tests and pass to the limit. This also follows from the effective equation for the square root of the density. [Levy, Perdew and Sahni](https://doi.org/10.1103/PhysRevA.30.2745)

The marginal is radial. Choose a trace radius $q_0\in[10^5,10^5+1]$ with $s(q_0)\le1$, which exists by radial normalization. Set $\alpha=10^{-7}$ and $w(r)=u(r)(q_0/r)^\alpha/u(q_0)$. For $r\ge q_0$ we have $\lambda J(r)\le\lambda/r\le10^{-7}$ and

$$
 \frac{h_0w}{w}=-\alpha+\frac{\alpha(1-\alpha)}{2r^2}.
$$

Thus $(h_0-\lambda J+d)w\ge0$. Its zeroth-order coefficient is positive throughout this exterior region. Testing the difference inequality by $(s-w)_+$, which has zero inner-boundary trace and belongs to the exterior form domain, yields $s\le w$. At $r\ge R$,

$$
 \log(w/u)\le \tfrac34\log\pi+\tfrac12(10^5+1)^2+
           \alpha\log(10^5+1)-\alpha\,10^{18}<-\log2 .
$$

It follows that $s\le u/2$ throughout the support of $g$.

## 5. Control the exact state after the potential changes

Set $F=f(x_1)f(x_2)$ and $w_F=F^2$. For normalized spatial $Y$, let $\mathcal R_f(Y)$ be the energy of $FY/\|FY\|_2$. Define

$$
 A(Y)=\langle Y,(h_0(1)+h_0(2)+\lambda W)Y\rangle,\qquad
 Q(Y)=\langle Y,HY\rangle=A(Y)-\lambda\langle J_1+J_2\rangle_Y.
$$

Writing $Y=(u\otimes u)Z$ in the ground-state form shows that each positive integrand of $A$ is multiplied by $w_F/\langle w_F\rangle_Y$ in $\mathcal R_f$. This includes the gradient integrands $\tfrac12(u\otimes u)^2|\nabla_i Z|^2$ and $\lambda W|Y|^2$. The only other terms are the similarly weighted averages of $-\lambda(J_{f,1}+J_{f,2})$. Integration by parts first applies to compactly supported smooth test functions and extends by form closure. For fixed finite parameters, $f,F$ and their inverses are bounded with bounded first derivatives. The change in the oscillator potential is bounded because the derivative terms of $f$ have compact support and $J_f$ is bounded. This preserves the oscillator form domain. Multiplication by $u\otimes u$ is an isometry from its own weighted $L^2$ space.

The multiplier bounds are $|w_F-1|\le5b$, $\langle w_F\rangle_Y>1/2$, $|w_F/\langle w_F\rangle_Y-1|\le20b$, and $|f^2/\int u^2 f^2-1|\le6b$. The last gives $\|J_f-J\|_\infty\le12b$. Since $\|J_1+J_2\|_\infty<4$ and $\lambda=1/100$, these imply

$$
 |\mathcal R_f(Y)-Q(Y)|\le20b A(Y)+2b .
$$

At the reference ground state, $A(\Psi)\le0.04$ since $E_2\le-\lambda D<0$. Hence $E_{2,f}\le E_2+3b$. Write the new normalized positive ground state as $FY_f/\|FY_f\|_2$, $\|Y_f\|_2=1$. Its energy is negative by the $D_f$ trial. Because $w_F/\langle w_F\rangle_Y\ge(7/9)^4>1/3$ and $\|J_f\|_\infty<2$, we have $A(Y_f)\le0.12$ and $Q(Y_f)\le E_2+8b$. In particular $T(Y_f)\le A(Y_f)+3<4$.

On the full scalar two-particle space $H\ge h_0(1)+h_0(2)-0.04$, so the second eigenvalue is at least $0.96$ by min-max. The ground energy is negative. Applying the spectral gap to $Y_f$ and using the nonnegative overlap with $\Psi$ gives

$$
 \|Y_f-\Psi\|_2\le5\sqrt b .
$$

## 6. Compare the actual kinetic energies at finite frequency

Put $G_k(Y)=\langle\sum_i g(r_i)^2\sin^2(kr_i)\rangle_Y$. For both $Y=Y_f$ and $Y=D_0$, the scaled physical gradient of $FY/\|FY\|$ has components

$$
 \frac{F}{bk\|FY\|}\nabla_iY+
 \frac{f(x_j)}{\|FY\|}\left[k^{-1} g'(r_i)\cos(kr_i)
       -g(r_i)\sin(kr_i)\right]\widehat{x_i}\,Y,\qquad j\ne i .
$$

The comparison vector with components $-g(r_i)\sin(kr_i)\widehat{x_i}Y$ has squared norm $G_k(Y)\le2$. Here $\|F/\|FY\|\|_\infty<2$, $|f(x_j)/\|FY\|-1|\le5b$ and $\sum_i\|\nabla_iY\|^2<8$. The difference between the two vectors has norm at most $6/(bk)+12/k+8b\le28b$ for $k=b^{-2}$. Since $b<0.01$, taking squared norms gives the finite estimate

$$
 \left|\frac{2T(FY/\|FY\|)}{(bk)^2}-G_k(Y)\right|\le100b .
$$

The multiplication operator in $G_k$ has norm at most 2, whence $|G_k(Y_f)-G_k(\Psi)|\le20\sqrt b$. On the support of $g$, the density excess $2(u^2-s^2)$ is at least $3u^2/2$. Integrate over $[R+1,R+2]$, where the cutoff equals 1. There $\int_{R+1}^{R+2}\sin^2(kr)\,dr\ge1/2-1/(2k)\ge1/4$. The radial Jacobian and Gaussian lower bound then give

$$
 G_k(D_0)-G_k(\Psi)\ge
 \frac{3}{2\sqrt\pi}(R+1)^2e^{-(R+2)^2}\ge m .
$$

For this one Hamiltonian the normalized kinetic difference therefore obeys

$$
 \frac{2(T_{\rm HF}-T_{\rm exact})}{(bk)^2}\ge
 m-200b-20\sqrt b>0.
$$

The physical-coordinate assertion follows by the dilation in Section 1. For reproducibility, retain the symbolic exponentials defining $R,m,b,k$. Ordinary floating-point arithmetic cannot represent them.

## Verification boundary

[RadialCertificate.lean](RadialCertificate.lean) proves the Gaussian moment inequalities from their three identities, the completed-square lower bound, the removal gap from the variational data, the principal-angle amplitude inequality, the HF margin from form bounds, the ground-state distance estimate and the final finite sign from the density and kinetic estimates. The continuum operators, existence and positivity of minimizers, product and marginal form calculations, oscillator and Gaussian identities, exterior comparison, and gradient remainder estimates above are mathematical arguments for independent review. The Lean file takes the corresponding scalar inputs as hypotheses. It contains no formal negation quantified over continuum Hamiltonians.
